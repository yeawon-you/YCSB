/*
 * Copyright (c) 2018 - 2019 YCSB contributors. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you
 * may not use this file except in compliance with the License. You
 * may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
 * implied. See the License for the specific language governing
 * permissions and limitations under the License. See accompanying
 * LICENSE file.
 */

package site.ycsb.db.rocksdb;

import org.rocksdb.PerfContext;
import org.rocksdb.PerfLevel;
import org.rocksdb.RocksDB;
import org.rocksdb.Statistics;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.BufferedWriter;
import java.io.IOException;
import java.lang.invoke.MethodHandle;
import java.lang.invoke.MethodHandles;
import java.lang.invoke.MethodType;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Properties;
import java.util.TreeMap;
import java.util.concurrent.ConcurrentLinkedQueue;

/**
 * [YW-Custom][BREAKDOWN] y2 time breakdown (DS_ARM_y2 4.5). Off unless rocksdb.breakdown=true.
 *
 * <p>Per op, on the YCSB client thread: Java segment timers (System.nanoTime) filled by
 * RocksDBClient, then one JNI call (PerfContext.snapshot) copies the thread's PerfContext; the
 * difference to the previous snapshot is added to that op type's accumulator for the current
 * wall-clock second. When the second changes, the thread hands its accumulators to a queue.
 * A writer thread (off the op path) merges the threads once per second and writes bd_ops.tsv,
 * and polls Statistics into bd_stats.tsv (changed values only).</p>
 *
 * <p>The PerfContext methods used here (snapshot, fieldNames, enablePerLevel,
 * setItblJobBreakdown) exist only in the y2 engine jars; the binding compiles against the stock
 * rocksdbjni, so they are resolved at run time. A jar without them fails the open.</p>
 */
final class RocksDBBreakdown {
  private static final Logger LOGGER = LoggerFactory.getLogger(RocksDBBreakdown.class);

  static final String PROP_ENABLE = "rocksdb.breakdown";
  static final String PROP_DIR = "rocksdb.breakdown.dir";

  static final int OP_READ = 0;
  static final int OP_SCAN = 1;
  static final int OP_UPDATE = 2;
  static final int OP_INSERT = 3;
  static final int OP_DELETE = 4;
  private static final String[] OP_NAMES = {"READ", "SCAN", "UPDATE", "INSERT", "DELETE"};

  // Java-side segments of one binding call (ns, except SEG_ROWS).
  static final int SEG_KEY = 0;         // toRocksKey (MD5); update calls it twice
  static final int SEG_GET = 1;         // native get
  static final int SEG_DESER = 2;       // deserializeValues (read / update; scan has its own)
  static final int SEG_MERGE = 3;       // update: result.putAll(values)
  static final int SEG_SER = 4;         // serializeValues
  static final int SEG_PUT = 5;         // native put
  static final int SEG_DELETE = 6;      // native delete
  static final int SEG_ITER_NEW = 7;    // native newIterator
  static final int SEG_SEEK = 8;        // native seek
  static final int SEG_NEXT = 9;        // native isValid + next, summed over the scan
  static final int SEG_VALUE = 10;      // native value() copy, summed over the scan
  static final int SEG_SCAN_DESER = 11; // scan: HashMap + deserializeValues + result.add
  static final int SEG_ITER_CLOSE = 12; // native iterator close
  static final int SEG_ROWS = 13;       // scan: rows returned (count)
  private static final int NSEG = 14;
  private static final String[] SEG_NAMES = {
      "java_key_ns", "native_get_ns", "java_deser_ns", "java_merge_ns", "java_ser_ns",
      "native_put_ns", "native_delete_ns", "native_iter_new_ns", "native_seek_ns",
      "native_next_ns", "native_value_ns", "java_scan_deser_ns", "native_iter_close_ns",
      "scan_rows"};

  // Accumulator layout: ops, op_total_ns, segments, PerfContext field deltas.
  private static final int A_OPS = 0;
  private static final int A_TOTAL = 1;
  private static final int A_SEG = 2;
  private static final int A_PERF = A_SEG + NSEG;
  // Seconds a row waits before it is written, so late hand-offs of idle threads still merge.
  private static final long WRITE_LAG_SEC = 3;

  private static volatile boolean enabled = false;
  private static MethodHandle snapshotMh;
  private static MethodHandle enablePerLevelMh;
  private static String[] perfNames;
  private static int width;
  private static long epochBaseNs;
  private static Writer writer;

  private RocksDBBreakdown() {
  }

  static boolean requested(final Properties props) {
    return Boolean.parseBoolean(props.getProperty(PROP_ENABLE, "false"));
  }

  static boolean isEnabled() {
    return enabled;
  }

  /**
   * Resolves the y2 JNI methods, turns on the ITBL background totals when the jar has them,
   * opens the output files and starts the writer. Call before RocksDB.open, once per process.
   */
  static synchronized void start(final Properties props, final Statistics statistics) {
    if (enabled || !requested(props)) {
      return;
    }
    final String dir = props.getProperty(PROP_DIR);
    if (dir == null) {
      throw new IllegalStateException(PROP_ENABLE + "=true needs " + PROP_DIR);
    }
    final MethodHandles.Lookup lk = MethodHandles.publicLookup();
    try {
      snapshotMh = lk.findVirtual(PerfContext.class, "snapshot",
          MethodType.methodType(int.class, long[].class));
      enablePerLevelMh = lk.findVirtual(PerfContext.class, "enablePerLevel",
          MethodType.methodType(void.class));
      final MethodHandle namesMh = lk.findStatic(PerfContext.class, "fieldNames",
          MethodType.methodType(String[].class));
      perfNames = (String[]) namesMh.invokeExact();
    } catch (final Throwable t) {
      throw new IllegalStateException("[YW-Custom][BREAKDOWN] engine jar has no y2 PerfContext "
          + "methods (snapshot/fieldNames/enablePerLevel) - build the y2 jar", t);
    }
    boolean itbl = false;
    try {
      final MethodHandle itblMh = lk.findStatic(PerfContext.class, "setItblJobBreakdown",
          MethodType.methodType(void.class, boolean.class));
      itblMh.invokeExact(true);
      itbl = true;
    } catch (final NoSuchMethodException e) {
      itbl = false;  // baseline jar: no ITBL background totals
    } catch (final Throwable t) {
      throw new IllegalStateException("[YW-Custom][BREAKDOWN] setItblJobBreakdown failed", t);
    }
    width = A_PERF + perfNames.length;
    epochBaseNs = System.currentTimeMillis() * 1_000_000L - System.nanoTime();
    try {
      writer = new Writer(Paths.get(dir), statistics);
    } catch (final IOException e) {
      throw new IllegalStateException("[YW-Custom][BREAKDOWN] cannot open output in " + dir, e);
    }
    writer.start();
    enabled = true;
    LOGGER.info("[YW-Custom][BREAKDOWN] on: dir={} perf_fields={} itbl_job_breakdown={} "
        + "perf_level=ENABLE_TIME_EXCEPT_FOR_MUTEX per_level=on", dir, perfNames.length, itbl);
  }

  /** Stops the writer after writing everything handed off so far. Call before closing the DB. */
  static synchronized void stop() {
    if (!enabled) {
      return;
    }
    enabled = false;
    writer.finish();
    writer = null;
  }

  /** Called on the YCSB client thread (DB.init runs there). */
  static Tls attach(final RocksDB db) {
    db.setPerfLevel(PerfLevel.ENABLE_TIME_EXCEPT_FOR_MUTEX);
    final PerfContext pc = db.getPerfContext();
    try {
      enablePerLevelMh.invokeExact(pc);
    } catch (final Throwable t) {
      throw new IllegalStateException("[YW-Custom][BREAKDOWN] enablePerLevel failed", t);
    }
    final Tls tls = new Tls(pc);
    writer.noteThread("client");
    return tls;
  }

  private static String threadTid() {
    try {
      final String link = Files.readSymbolicLink(Paths.get("/proc/thread-self")).toString();
      return link.substring(link.lastIndexOf('/') + 1);
    } catch (final IOException | UnsupportedOperationException e) {
      return "?";
    }
  }

  /** One client thread's state. Not thread-safe: used only by its own thread. */
  static final class Tls {
    private final PerfContext pc;
    private long[] prev;
    private long[] cur;
    private final long[] seg = new long[NSEG];
    private final long[][] acc = new long[OP_NAMES.length][];
    private long sec = -1;

    private Tls(final PerfContext perfContext) {
      this.pc = perfContext;
      this.prev = new long[perfNames.length];
      this.cur = new long[perfNames.length];
      snap(prev);
    }

    private void snap(final long[] out) {
      try {
        final int n = (int) snapshotMh.invokeExact(pc, out);
        if (n != out.length) {
          throw new IllegalStateException("snapshot size " + n + " != " + out.length);
        }
      } catch (final RuntimeException e) {
        throw e;
      } catch (final Throwable t) {
        throw new IllegalStateException("[YW-Custom][BREAKDOWN] snapshot failed", t);
      }
    }

    void add(final int segment, final long value) {
      seg[segment] += value;
    }

    /** Ends one binding call that started at t0 (nanoTime) and ended at t1. */
    void end(final int op, final long t0, final long t1) {
      snap(cur);
      final long s = (t1 + epochBaseNs) / 1_000_000_000L;
      if (s != sec) {
        handOff();
        sec = s;
      }
      long[] a = acc[op];
      if (a == null) {
        a = new long[width];
        acc[op] = a;
      }
      a[A_OPS] += 1;
      a[A_TOTAL] += t1 - t0;
      for (int i = 0; i < NSEG; i++) {
        a[A_SEG + i] += seg[i];
        seg[i] = 0;
      }
      for (int j = 0; j < cur.length; j++) {
        a[A_PERF + j] += cur[j] - prev[j];
      }
      final long[] t = prev;
      prev = cur;
      cur = t;
    }

    private void handOff() {
      final Writer w = writer;
      for (int op = 0; op < acc.length; op++) {
        if (acc[op] != null) {
          if (w != null) {
            w.queue.add(new Chunk(sec, op, acc[op]));
          }
          acc[op] = null;
        }
      }
    }

    /** Hands off the last second; call from the client thread's cleanup. */
    void flush() {
      handOff();
    }
  }

  /** One thread's totals for one (second, op). */
  private static final class Chunk {
    private final long sec;
    private final int op;
    private final long[] acc;

    private Chunk(final long second, final int opType, final long[] totals) {
      this.sec = second;
      this.op = opType;
      this.acc = totals;
    }
  }

  /** Merges hand-offs per second and writes the files; polls Statistics once per second. */
  private static final class Writer extends Thread {
    private final ConcurrentLinkedQueue<Chunk> queue = new ConcurrentLinkedQueue<>();
    private final TreeMap<Long, long[][]> pending = new TreeMap<>();
    private final Map<String, Long> lastStats = new HashMap<>();
    private final Statistics statistics;
    private final BufferedWriter ops;
    private final BufferedWriter stats;
    private final BufferedWriter threads;
    private volatile boolean stopping = false;
    private long maxSec = -1;

    private Writer(final Path dir, final Statistics stat) throws IOException {
      super("yw-bd-writer");
      setDaemon(true);
      this.statistics = stat;
      Files.createDirectories(dir);
      ops = Files.newBufferedWriter(dir.resolve("bd_ops.tsv"), StandardCharsets.UTF_8);
      stats = Files.newBufferedWriter(dir.resolve("bd_stats.tsv"), StandardCharsets.UTF_8);
      threads = Files.newBufferedWriter(dir.resolve("bd_threads.tsv"), StandardCharsets.UTF_8);
      final StringBuilder h = new StringBuilder("sec\top\tops\top_total_ns");
      for (final String n : SEG_NAMES) {
        h.append('\t').append(n);
      }
      for (final String n : perfNames) {
        h.append('\t').append(n);
      }
      ops.write(h.append('\n').toString());
      stats.write("sec\tname\tvalue\n");
      threads.write("role\ttid\tjava_name\n");
    }

    private synchronized void noteThread(final String role) {
      try {
        threads.write(role + "\t" + threadTid() + "\t" + Thread.currentThread().getName() + "\n");
        threads.flush();
      } catch (final IOException e) {
        LOGGER.warn("[YW-Custom][BREAKDOWN] bd_threads.tsv: " + e.getMessage());
      }
    }

    @Override
    public void run() {
      noteThread("bd-writer");
      while (!stopping) {
        try {
          Thread.sleep(1000);
        } catch (final InterruptedException e) {
          break;
        }
        step(false);
      }
    }

    private void finish() {
      stopping = true;
      interrupt();
      try {
        join(10_000);
      } catch (final InterruptedException e) {
        Thread.currentThread().interrupt();
      }
      step(true);
      try {
        ops.close();
        stats.close();
        threads.close();
      } catch (final IOException e) {
        LOGGER.warn("[YW-Custom][BREAKDOWN] close: " + e.getMessage());
      }
    }

    private synchronized void step(final boolean all) {
      Chunk c = queue.poll();
      while (c != null) {
        long[][] row = pending.get(c.sec);
        if (row == null) {
          row = new long[OP_NAMES.length][];
          pending.put(c.sec, row);
        }
        if (row[c.op] == null) {
          row[c.op] = c.acc;
        } else {
          final long[] dst = row[c.op];
          for (int i = 0; i < dst.length; i++) {
            dst[i] += c.acc[i];
          }
        }
        maxSec = Math.max(maxSec, c.sec);
        c = queue.poll();
      }
      try {
        final Iterator<Map.Entry<Long, long[][]>> it = pending.entrySet().iterator();
        while (it.hasNext()) {
          final Map.Entry<Long, long[][]> e = it.next();
          if (!all && e.getKey() > maxSec - WRITE_LAG_SEC) {
            break;
          }
          for (int op = 0; op < OP_NAMES.length; op++) {
            final long[] a = e.getValue()[op];
            if (a == null) {
              continue;
            }
            final StringBuilder sb = new StringBuilder();
            sb.append(e.getKey()).append('\t').append(OP_NAMES[op]);
            for (final long v : a) {
              sb.append('\t').append(v);
            }
            ops.write(sb.append('\n').toString());
          }
          it.remove();
        }
        ops.flush();
        pollStats();
      } catch (final IOException e) {
        LOGGER.warn("[YW-Custom][BREAKDOWN] write: " + e.getMessage());
      }
    }

    // Statistics.toString() carries the native ticker / histogram names (the two engines' Java
    // TickerType byte values are not trusted, see RocksDBClient.sharedStatistics).
    // Ticker line: "<name> COUNT : <v>". Histogram line: "<name> P50 : .. COUNT : <n> SUM : <s>".
    private void pollStats() throws IOException {
      if (statistics == null) {
        return;
      }
      final long now = System.currentTimeMillis() / 1000L;
      for (final String line : statistics.toString().split("\n")) {
        final String[] tok = line.trim().split("\\s+");
        if (tok.length < 4) {
          continue;
        }
        for (int i = 1; i + 2 < tok.length; i++) {
          if ((tok[i].equals("COUNT") || tok[i].equals("SUM")) && tok[i + 1].equals(":")) {
            final String name;
            if (i == 1 && tok[i].equals("COUNT")) {
              name = tok[0];
            } else {
              name = tok[0] + "." + tok[i];
            }
            final long v;
            try {
              v = Long.parseLong(tok[i + 2]);
            } catch (final NumberFormatException e) {
              continue;
            }
            final Long last = lastStats.put(name, v);
            if (last == null || last != v) {
              stats.write(now + "\t" + name + "\t" + v + "\n");
            }
          }
        }
      }
      stats.flush();
    }
  }
}
