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

import site.ycsb.*;
import site.ycsb.Status;
import net.jcip.annotations.GuardedBy;
import org.rocksdb.*;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.*;
import java.nio.ByteBuffer;
import java.nio.file.*;
import java.security.MessageDigest; // [YW-Custom]
import java.security.NoSuchAlgorithmException; // [YW-Custom]
import java.util.*;
import java.util.Locale; // [YW-Custom]
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

import static java.nio.charset.StandardCharsets.UTF_8;

/**
 * RocksDB binding for <a href="http://rocksdb.org/">RocksDB</a>.
 *
 * See {@code rocksdb/README.md} for details.
 */
public class RocksDBClient extends DB {

  static final String PROPERTY_ROCKSDB_DIR = "rocksdb.dir";
  static final String PROPERTY_ROCKSDB_OPTIONS_FILE = "rocksdb.optionsfile";
  private static final String COLUMN_FAMILY_NAMES_FILENAME = "CF_NAMES";

  private static final Logger LOGGER = LoggerFactory.getLogger(RocksDBClient.class);

  @GuardedBy("RocksDBClient.class") private static Path rocksDbDir = null;
  @GuardedBy("RocksDBClient.class") private static Path optionsFile = null;
  @GuardedBy("RocksDBClient.class") private static RocksObject dbOptions = null;
  @GuardedBy("RocksDBClient.class") private static RocksDB rocksDb = null;
  @GuardedBy("RocksDBClient.class") private static int references = 0;

  // [YW-Custom] CF-level options set during initRocksDB(); applied in createColumnFamily() as well.
  @GuardedBy("RocksDBClient.class") private static int  cfNumLevels             = -1;
  @GuardedBy("RocksDBClient.class") private static long cfMaxBytesForLevelBase  = -1L;
  @GuardedBy("RocksDBClient.class") private static int  cfLevel0CompactionTrigger = -1;
  @GuardedBy("RocksDBClient.class") private static int  cfLevel0SlowdownTrigger   = -1;
  @GuardedBy("RocksDBClient.class") private static int  cfLevel0StopTrigger       = -1;
  // [YW-Custom] Additional CF-level options the upstream binding silently ignored.
  @GuardedBy("RocksDBClient.class") private static int  cfMaxWriteBufferNumber  = -1;
  @GuardedBy("RocksDBClient.class") private static CompressionType cfCompression = null;

  // [YW-Custom] Extra CF/table options (memtable size, level geometry, block cache, bloom filter).
  // Added 2026-09 after the audit found the standard panel had run with filter_policy=nullptr on
  // both systems and an optimizeLevelStyleCompaction() preset silently overriding RocksDB defaults.
  @GuardedBy("RocksDBClient.class") private static YwExtraOpts cfExtra = new YwExtraOpts();
  // Block cache and filter policy are native objects shared by every CF. They must stay strongly
  // referenced for the lifetime of the DB, otherwise the JVM finalizes them underneath us.
  @GuardedBy("RocksDBClient.class") private static Cache sharedBlockCache = null;
  @GuardedBy("RocksDBClient.class") private static Filter sharedFilterPolicy = null;

  // [YW-Custom] WriteOptions reused for every put/delete; set during init based on rocksdb.disablewal.
  @GuardedBy("RocksDBClient.class") private static WriteOptions writeOptions = null;

  // [YW-Custom] Optional statistics object (rocksdb.statistics=true). Kept strongly referenced for the
  // DB lifetime; dumped to stderr once at close via toString() so ticker names come from the native
  // side (the two forks' C++ ticker enums differ, so Java TickerType byte values are not trusted).
  @GuardedBy("RocksDBClient.class") private static Statistics sharedStatistics = null;

  private static final ConcurrentMap<String, ColumnFamily> COLUMN_FAMILIES = new ConcurrentHashMap<>();

  // [YW-Custom][BREAKDOWN] y2 (DS_ARM_y2 4.5): this client thread's breakdown state, null when off.
  private RocksDBBreakdown.Tls bd = null;
  private static final ConcurrentMap<String, Lock> COLUMN_FAMILY_LOCKS = new ConcurrentHashMap<>();

  @Override
  public void init() throws DBException {
    synchronized(RocksDBClient.class) {
      if(rocksDb == null) {
        rocksDbDir = Paths.get(getProperties().getProperty(PROPERTY_ROCKSDB_DIR));
        LOGGER.info("RocksDB data dir: " + rocksDbDir);

        String optionsFileString = getProperties().getProperty(PROPERTY_ROCKSDB_OPTIONS_FILE);
        if (optionsFileString != null) {
          optionsFile = Paths.get(optionsFileString);
          LOGGER.info("RocksDB options file: " + optionsFile);
        }

        try {
          if (optionsFile != null) {
            rocksDb = initRocksDBWithOptionsFile();
          } else {
            rocksDb = initRocksDB();
          }
        } catch (final IOException | RocksDBException e) {
          throw new DBException(e);
        }
      }

      references++;
    }
    // [YW-Custom][BREAKDOWN] PerfLevel / PerfContext are thread-local: attach on the client thread.
    if (RocksDBBreakdown.isEnabled()) {
      bd = RocksDBBreakdown.attach(rocksDb);
    }
  }

  /**
   * Initializes and opens the RocksDB database.
   *
   * Should only be called with a {@code synchronized(RocksDBClient.class)` block}.
   *
   * @return The initialized and open RocksDB instance.
   */
  private RocksDB initRocksDBWithOptionsFile() throws IOException, RocksDBException {
    if(!Files.exists(rocksDbDir)) {
      Files.createDirectories(rocksDbDir);
    }

    // [YW-Custom] Initialize WriteOptions for the options-file path too, so put/delete don't NPE.
    final boolean disableWal = parseBoolProp("rocksdb.disablewal", false);
    writeOptions = new WriteOptions().setDisableWAL(disableWal);

    final DBOptions options = new DBOptions();
    final List<ColumnFamilyDescriptor> cfDescriptors = new ArrayList<>();
    final List<ColumnFamilyHandle> cfHandles = new ArrayList<>();

    RocksDB.loadLibrary();
    final ConfigOptions configOptions = new ConfigOptions();
    OptionsUtil.loadOptionsFromFile(configOptions, optionsFile.toAbsolutePath().toString(), options, cfDescriptors);
    dbOptions = options;

    final RocksDB db = RocksDB.open(options, rocksDbDir.toAbsolutePath().toString(), cfDescriptors, cfHandles);

    for(int i = 0; i < cfDescriptors.size(); i++) {
      String cfName = new String(cfDescriptors.get(i).getName());
      final ColumnFamilyHandle cfHandle = cfHandles.get(i);
      final ColumnFamilyOptions cfOptions = cfDescriptors.get(i).getOptions();

      COLUMN_FAMILIES.put(cfName, new ColumnFamily(cfHandle, cfOptions));
    }

    return db;
  }

  /**
   * Initializes and opens the RocksDB database.
   *
   * Should only be called with a {@code synchronized(RocksDBClient.class)` block}.
   *
   * @return The initialized and open RocksDB instance.
   */
  private RocksDB initRocksDB() throws IOException, RocksDBException {
    if(!Files.exists(rocksDbDir)) {
      Files.createDirectories(rocksDbDir);
    }

    // [YW-Custom] Force native library load before constructing any RocksDB class. WriteOptions
    // and other lightweight option classes do not have their own static loadLibrary() block, so
    // they would NPE/UnsatisfiedLinkError if instantiated before Options triggers the auto-load.
    RocksDB.loadLibrary();

    // [YW-Custom] Read all configurable properties once; apply to every CF opened or created below.
    final int numLevels             = parseIntProp("rocksdb.numlevels", -1);
    final long maxBytesForLevelBase = parseLongProp("rocksdb.maxbytesforlevelbase", -1L);
    final int l0Trigger  = parseIntProp("rocksdb.level0compactiontrigger", -1);
    final int l0Slowdown = parseIntProp("rocksdb.level0slowdowntrigger", -1);
    final int l0Stop     = parseIntProp("rocksdb.level0stoptrigger", -1);
    final int maxWriteBufferNumber = parseIntProp("rocksdb.maxwritebuffernumber", -1);
    final CompressionType compression = parseCompressionProp("rocksdb.compression", null);
    final boolean useDirectReads = parseBoolProp("rocksdb.use_direct_reads", false);
    final boolean useDirectIoForFlushAndCompaction =
        parseBoolProp("rocksdb.use_direct_io_for_flush_and_compaction", false);
    final boolean disableWal = parseBoolProp("rocksdb.disablewal", false);
    cfNumLevels            = numLevels;
    cfMaxBytesForLevelBase = maxBytesForLevelBase;
    cfLevel0CompactionTrigger = l0Trigger;
    cfLevel0SlowdownTrigger   = l0Slowdown;
    cfLevel0StopTrigger       = l0Stop;
    cfMaxWriteBufferNumber = maxWriteBufferNumber;
    cfCompression          = compression;

    // [YW-Custom] Extra options. -1 / -1L / null all mean "leave the RocksDB default alone".
    // Note the deliberate distinction for bloombits: -1 = untouched (RocksDB default is nullptr),
    // 0 = explicitly no filter. The ITBL arm sets 0 because its L0 is indexed by the interval
    // table; the baseline arm sets 10. That asymmetry is a DESIGN difference, not a control leak
    // (see test_scripts/TEST_OVERVIEW.md, read_perf 'controlled vs design' table).
    cfExtra = new YwExtraOpts(getProperties());

    LOGGER.info("[YW-Custom] options summary: numLevels={} maxBytesForLevelBase={} l0Trigger={} "
        + "l0Slowdown={} l0Stop={} maxWriteBufferNumber={} compression={} useDirectReads={} "
        + "useDirectIoForFlushAndCompaction={} disableWal={}",
        numLevels, maxBytesForLevelBase, l0Trigger, l0Slowdown, l0Stop,
        maxWriteBufferNumber, compression, useDirectReads,
        useDirectIoForFlushAndCompaction, disableWal);
    LOGGER.info("[YW-Custom] extra options summary: {}", cfExtra);

    writeOptions = new WriteOptions().setDisableWAL(disableWal);

    final List<String> cfNames = loadColumnFamilyNames();
    final List<ColumnFamilyOptions> cfOptionss = new ArrayList<>();
    final List<ColumnFamilyDescriptor> cfDescriptors = new ArrayList<>();

    final CfOpts cfo = new CfOpts(numLevels, maxBytesForLevelBase,
        l0Trigger, l0Slowdown, l0Stop, maxWriteBufferNumber, compression);
    for(final String cfName : cfNames) {
      // [YW-Custom] optimizeLevelStyleCompaction() removed 2026-09. It pre-set write_buffer_size
      // (128MB), max_write_buffer_number (6), level0_file_num_compaction_trigger (2) and
      // max_bytes_for_level_base (512MB), so the baseline arm was never running "RocksDB default".
      // Anything not given as a property now keeps the genuine RocksDB default.
      final ColumnFamilyOptions cfOptions = new ColumnFamilyOptions();
      cfo.applyTo(cfOptions);
      cfExtra.applyTo(cfOptions);
      final ColumnFamilyDescriptor cfDescriptor = new ColumnFamilyDescriptor(
          cfName.getBytes(UTF_8),
          cfOptions
      );
      cfOptionss.add(cfOptions);
      cfDescriptors.add(cfDescriptor);
    }

    final int rocksThreads  = Runtime.getRuntime().availableProcessors() * 2;
    final int bgCompactions = parseIntProp("rocksdb.maxbackgroundcompactions", rocksThreads);
    final int bgFlushes     = parseIntProp("rocksdb.maxbackgroundflushes",     -1);
    final int parallelism   = parseIntProp("rocksdb.increaseparallelism",      rocksThreads);

    if(cfDescriptors.isEmpty()) {
      // [YW-Custom] optimizeLevelStyleCompaction() removed 2026-09 — see the CF-descriptor path above.
      final Options options = new Options()
          .setCreateIfMissing(true)
          .setCreateMissingColumnFamilies(true)
          .setIncreaseParallelism(parallelism)
          .setMaxBackgroundCompactions(bgCompactions)
          .setInfoLogLevel(InfoLogLevel.INFO_LEVEL);
      if (bgFlushes > 0) {
        options.setMaxBackgroundFlushes(bgFlushes);
      }
      // [YW-Custom] DB-level direct I/O knobs (Options extends DBOptions).
      if (useDirectReads) {
        options.setUseDirectReads(true);
      }
      if (useDirectIoForFlushAndCompaction) {
        options.setUseDirectIoForFlushAndCompaction(true);
      }
      // [YW-Custom] CF-level overrides (Options also extends ColumnFamilyOptions setters).
      if (numLevels > 0) {
        options.setNumLevels(numLevels);
      }
      if (maxBytesForLevelBase > 0) {
        options.setMaxBytesForLevelBase(maxBytesForLevelBase);
      }
      if (l0Trigger >= 0) {
        options.setLevel0FileNumCompactionTrigger(l0Trigger);
      }
      if (l0Slowdown >= 0) {
        options.setLevel0SlowdownWritesTrigger(l0Slowdown);
      }
      if (l0Stop >= 0) {
        options.setLevel0StopWritesTrigger(l0Stop);
      }
      if (maxWriteBufferNumber > 0) {
        options.setMaxWriteBufferNumber(maxWriteBufferNumber);
      }
      applyCompression(options, compression, numLevels);
      // [YW-Custom] memtable / level geometry / block cache / bloom filter.
      cfExtra.applyTo(options);
      applyMaxOpenFiles(options, getProperties());
      applyObservability(options, getProperties());
      dbOptions = options;
      final RocksDB db = RocksDB.open(options, rocksDbDir.toAbsolutePath().toString());
      maybeQuiesce(db, getProperties());
      return db;
    } else {
      final DBOptions options = new DBOptions()
          .setCreateIfMissing(true)
          .setCreateMissingColumnFamilies(true)
          .setIncreaseParallelism(parallelism)
          .setMaxBackgroundCompactions(bgCompactions)
          .setInfoLogLevel(InfoLogLevel.INFO_LEVEL);
      if (bgFlushes > 0) {
        options.setMaxBackgroundFlushes(bgFlushes);
      }
      // [YW-Custom] DB-level direct I/O knobs.
      if (useDirectReads) {
        options.setUseDirectReads(true);
      }
      if (useDirectIoForFlushAndCompaction) {
        options.setUseDirectIoForFlushAndCompaction(true);
      }
      applyMaxOpenFiles(options, getProperties());
      applyObservability(options, getProperties());
      dbOptions = options;

      final List<ColumnFamilyHandle> cfHandles = new ArrayList<>();
      final RocksDB db = RocksDB.open(options, rocksDbDir.toAbsolutePath().toString(), cfDescriptors, cfHandles);
      for(int i = 0; i < cfNames.size(); i++) {
        COLUMN_FAMILIES.put(cfNames.get(i), new ColumnFamily(cfHandles.get(i), cfOptionss.get(i)));
      }
      maybeQuiesce(db, getProperties());
      return db;
    }
  }

  // [YW-Custom] Self-applying holder for all configurable CF options. Encapsulates the values and
  // the logic to apply them to a ColumnFamilyOptions instance. -1 / -1L / null means "leave default".
  private static final class CfOpts {
    private final int numLevels;
    private final long maxBytesForLevelBase;
    private final int l0Trigger;
    private final int l0Slowdown;
    private final int l0Stop;
    private final int maxWriteBufferNumber;
    private final CompressionType compression;

    CfOpts(final int numLevels, final long maxBytesForLevelBase,
           final int l0Trigger, final int l0Slowdown, final int l0Stop,
           final int maxWriteBufferNumber, final CompressionType compression) {
      this.numLevels = numLevels;
      this.maxBytesForLevelBase = maxBytesForLevelBase;
      this.l0Trigger = l0Trigger;
      this.l0Slowdown = l0Slowdown;
      this.l0Stop = l0Stop;
      this.maxWriteBufferNumber = maxWriteBufferNumber;
      this.compression = compression;
    }

    void applyTo(final ColumnFamilyOptions opts) {
      if (numLevels > 0) {
        opts.setNumLevels(numLevels);
      }
      if (maxBytesForLevelBase > 0) {
        opts.setMaxBytesForLevelBase(maxBytesForLevelBase);
      }
      if (l0Trigger >= 0) {
        opts.setLevel0FileNumCompactionTrigger(l0Trigger);
      }
      if (l0Slowdown >= 0) {
        opts.setLevel0SlowdownWritesTrigger(l0Slowdown);
      }
      if (l0Stop >= 0) {
        opts.setLevel0StopWritesTrigger(l0Stop);
      }
      if (maxWriteBufferNumber > 0) {
        opts.setMaxWriteBufferNumber(maxWriteBufferNumber);
      }
      if (compression != null) {
        opts.setCompressionType(compression);
        // [YW-Custom] optimizeLevelStyleCompaction() pre-populates compression_per_level (LZ4 at L2+).
        // The per-level array takes precedence over setCompressionType, so we must override it too,
        // otherwise compression=NO_COMPRESSION only takes effect at L0/L1.
        final int effectiveNumLevels = numLevels > 0 ? numLevels : 7;
        final List<CompressionType> perLevel = new ArrayList<>(effectiveNumLevels);
        for (int i = 0; i < effectiveNumLevels; i++) {
          perLevel.add(compression);
        }
        opts.setCompressionPerLevel(perLevel);
      }
    }
  }

  // [YW-Custom] Self-applying holder for the options the upstream binding (and our earlier patch)
  // left at whatever optimizeLevelStyleCompaction() happened to set. Everything is tri-state:
  // -1 / -1L / -1.0 / null mean "do not touch, keep the RocksDB default".
  //
  // Why this exists: the 2026-05 standard panel ran with filter_policy=nullptr on BOTH systems
  // because no property reached BlockBasedTableConfig, and with write_buffer_size=128MB /
  // max_write_buffer_number=6 / level0_file_num_compaction_trigger=2 / max_bytes_for_level_base=512MB
  // because the preset set them. None of that was visible in the scripts.
  private static final class YwExtraOpts {
    private final long writeBufferSize;
    private final long targetFileSizeBase;
    private final double maxBytesForLevelMultiplier;
    private final Boolean levelDynamicBytes;
    private final long softPendingLimit;
    private final long hardPendingLimit;
    private final double bloomBits;
    private final long cacheSize;
    private final boolean cacheIndexAndFilterBlocks;
    private final boolean pinL0FilterAndIndexBlocks;
    private final long blockSize;
    private final double cacheHighPriRatio;
    private final boolean cacheIndexAndFilterWithHighPriority;
    // [YW-Custom][BREAKDOWN] y2: report_bg_io_stats (file write / fsync nanos in the flush and
    // compaction EVENT_LOG lines) whenever rocksdb.breakdown=true.
    private final boolean reportBgIoStats;

    // Empty holder used before init(); every field is "leave the RocksDB default alone".
    YwExtraOpts() {
      this(new Properties());
    }

    // Parses itself from the YCSB properties. Taking the whole Properties keeps the checkstyle
    // ParameterNumber rule happy and keeps the property names next to the fields they set.
    YwExtraOpts(final Properties props) {
      this.writeBufferSize = longProp(props, "rocksdb.writebuffersize", -1L);
      this.targetFileSizeBase = longProp(props, "rocksdb.targetfilesizebase", -1L);
      this.maxBytesForLevelMultiplier = doubleProp(props, "rocksdb.maxbytesforlevelmultiplier", -1.0);
      this.levelDynamicBytes = boolPropOrNull(props, "rocksdb.leveldynamicbytes");
      this.softPendingLimit = longProp(props, "rocksdb.softpendingcompactionbyteslimit", -1L);
      this.hardPendingLimit = longProp(props, "rocksdb.hardpendingcompactionbyteslimit", -1L);
      this.bloomBits = doubleProp(props, "rocksdb.bloombits", -1.0);
      this.cacheSize = longProp(props, "rocksdb.cachesize", -1L);
      this.cacheIndexAndFilterBlocks = boolProp(props, "rocksdb.cacheindexandfilterblocks", false);
      this.pinL0FilterAndIndexBlocks =
          boolProp(props, "rocksdb.pinl0filterandindexblocksincache", false);
      this.blockSize = longProp(props, "rocksdb.blocksize", -1L);
      // Java's LRUCache(capacity) convenience constructor passes highPriPoolRatio=0.0
      // (LRUCache.java:19) — NOT the C++ LRUCacheOptions default of 0.5. With 0.0 there is no
      // high-priority pool, so index/filter blocks are evicted by streaming data-block reads
      // even when cache_index_and_filter_blocks_with_high_priority is true. Always state it.
      this.cacheHighPriRatio = doubleProp(props, "rocksdb.cachehighpriratio", 0.0);
      this.cacheIndexAndFilterWithHighPriority =
          boolProp(props, "rocksdb.cacheindexandfilterblockswithhighpriority", true);
      this.reportBgIoStats = RocksDBBreakdown.requested(props);
    }

    private static long longProp(final Properties p, final String k, final long dflt) {
      final String v = p.getProperty(k);
      return v != null ? Long.parseLong(v.trim()) : dflt;
    }

    private static double doubleProp(final Properties p, final String k, final double dflt) {
      final String v = p.getProperty(k);
      return v != null ? Double.parseDouble(v.trim()) : dflt;
    }

    private static boolean boolProp(final Properties p, final String k, final boolean dflt) {
      final String v = p.getProperty(k);
      return v != null ? Boolean.parseBoolean(v.trim()) : dflt;
    }

    private static Boolean boolPropOrNull(final Properties p, final String k) {
      final String v = p.getProperty(k);
      return v != null ? Boolean.valueOf(Boolean.parseBoolean(v.trim())) : null;
    }

    private boolean touchesTable() {
      return bloomBits >= 0 || cacheSize >= 0 || blockSize > 0
          || cacheIndexAndFilterBlocks || pinL0FilterAndIndexBlocks;
    }

    // Builds the table config against the process-wide shared cache and filter. Called once per
    // column family; the BlockBasedTableConfig itself is a plain value holder, but the Cache and
    // Filter it points at must be the same native objects for every CF (and must outlive the DB).
    private BlockBasedTableConfig tableConfig() {
      final BlockBasedTableConfig tc = new BlockBasedTableConfig();
      if (cacheSize == 0) {
        // Matches db_bench --cache_size=0: no block cache. Index/filter blocks still live on the
        // heap outside the cache, which is exactly the trap the 0612 campaign documented.
        tc.setNoBlockCache(true);
      } else if (cacheSize > 0) {
        if (sharedBlockCache == null) {
          // (capacity, numShardBits=-1 auto, strictCapacityLimit=false, highPriPoolRatio)
          sharedBlockCache = new LRUCache(cacheSize, -1, false, cacheHighPriRatio);
        }
        tc.setBlockCache(sharedBlockCache);
      }
      if (bloomBits == 0) {
        tc.setFilterPolicy(null);
      } else if (bloomBits > 0) {
        if (sharedFilterPolicy == null) {
          sharedFilterPolicy = new BloomFilter(bloomBits);
        }
        tc.setFilterPolicy(sharedFilterPolicy);
      }
      tc.setCacheIndexAndFilterBlocks(cacheIndexAndFilterBlocks);
      tc.setCacheIndexAndFilterBlocksWithHighPriority(cacheIndexAndFilterWithHighPriority);
      tc.setPinL0FilterAndIndexBlocksInCache(pinL0FilterAndIndexBlocks);
      if (blockSize > 0) {
        tc.setBlockSize(blockSize);
      }
      return tc;
    }

    void applyTo(final ColumnFamilyOptions opts) {
      if (reportBgIoStats) {
        opts.setReportBgIoStats(true);
      }
      if (writeBufferSize > 0) {
        opts.setWriteBufferSize(writeBufferSize);
      }
      if (targetFileSizeBase > 0) {
        opts.setTargetFileSizeBase(targetFileSizeBase);
      }
      if (maxBytesForLevelMultiplier > 0) {
        opts.setMaxBytesForLevelMultiplier(maxBytesForLevelMultiplier);
      }
      if (levelDynamicBytes != null) {
        opts.setLevelCompactionDynamicLevelBytes(levelDynamicBytes);
      }
      if (softPendingLimit >= 0) {
        opts.setSoftPendingCompactionBytesLimit(softPendingLimit);
      }
      if (hardPendingLimit >= 0) {
        opts.setHardPendingCompactionBytesLimit(hardPendingLimit);
      }
      if (touchesTable()) {
        opts.setTableFormatConfig(tableConfig());
      }
    }

    // Options implements the same CF interfaces but does not extend ColumnFamilyOptions, so the
    // no-column-family open path needs its own overload.
    void applyTo(final Options opts) {
      if (reportBgIoStats) {
        opts.setReportBgIoStats(true);
      }
      if (writeBufferSize > 0) {
        opts.setWriteBufferSize(writeBufferSize);
      }
      if (targetFileSizeBase > 0) {
        opts.setTargetFileSizeBase(targetFileSizeBase);
      }
      if (maxBytesForLevelMultiplier > 0) {
        opts.setMaxBytesForLevelMultiplier(maxBytesForLevelMultiplier);
      }
      if (levelDynamicBytes != null) {
        opts.setLevelCompactionDynamicLevelBytes(levelDynamicBytes);
      }
      if (softPendingLimit >= 0) {
        opts.setSoftPendingCompactionBytesLimit(softPendingLimit);
      }
      if (hardPendingLimit >= 0) {
        opts.setHardPendingCompactionBytesLimit(hardPendingLimit);
      }
      if (touchesTable()) {
        opts.setTableFormatConfig(tableConfig());
      }
    }

    @Override
    public String toString() {
      return "writeBufferSize=" + writeBufferSize
          + " targetFileSizeBase=" + targetFileSizeBase
          + " maxBytesForLevelMultiplier=" + maxBytesForLevelMultiplier
          + " levelDynamicBytes=" + levelDynamicBytes
          + " softPendingLimit=" + softPendingLimit
          + " hardPendingLimit=" + hardPendingLimit
          + " bloomBits=" + bloomBits
          + " cacheSize=" + cacheSize
          + " cacheIndexAndFilterBlocks=" + cacheIndexAndFilterBlocks
          + " pinL0FilterAndIndexBlocksInCache=" + pinL0FilterAndIndexBlocks
          + " blockSize=" + blockSize
          + " cacheHighPriRatio=" + cacheHighPriRatio
          + " cacheIndexAndFilterWithHighPriority=" + cacheIndexAndFilterWithHighPriority;
    }
  }

  // [YW-Custom] max_open_files decides whether index/filter blocks are effectively unbounded.
  // RocksDB default is -1 (open every SST at DB::Open and never evict the readers), which with
  // cache_index_and_filter_blocks=false means all index+filter stay resident on the heap.
  // Made explicit so the memory regime is stated in the flags instead of inherited silently.
  private static void applyMaxOpenFiles(final Options opts, final Properties props) {
    final String v = props.getProperty("rocksdb.maxopenfiles");
    if (v != null) {
      opts.setMaxOpenFiles(Integer.parseInt(v.trim()));
    }
  }

  // [YW-Custom] Observability knobs (2026-09-23, trial 2).
  //   rocksdb.statistics=true        → Statistics (default level), dumped at close
  //   rocksdb.statsdumpperiodsec=N   → LOG stats dump period (ITBL GC-STATS rides on it)
  private static void applyObservability(final Options opts, final Properties props) {
    final String sd = props.getProperty("rocksdb.statsdumpperiodsec");
    if (sd != null) {
      opts.setStatsDumpPeriodSec(Integer.parseInt(sd.trim()));
    }
    if (Boolean.parseBoolean(props.getProperty("rocksdb.statistics", "false"))) {
      sharedStatistics = new Statistics();
      opts.setStatistics(sharedStatistics);
    }
    RocksDBBreakdown.start(props, sharedStatistics); // [YW-Custom][BREAKDOWN] no-op unless requested
  }

  private static void applyObservability(final DBOptions opts, final Properties props) {
    final String sd = props.getProperty("rocksdb.statsdumpperiodsec");
    if (sd != null) {
      opts.setStatsDumpPeriodSec(Integer.parseInt(sd.trim()));
    }
    if (Boolean.parseBoolean(props.getProperty("rocksdb.statistics", "false"))) {
      sharedStatistics = new Statistics();
      opts.setStatistics(sharedStatistics);
    }
    RocksDBBreakdown.start(props, sharedStatistics); // [YW-Custom][BREAKDOWN] no-op unless requested
  }

  // [YW-Custom] Quiesce (2026-09-23, trial 2): with rocksdb.quiesceonopen=true, block after open until
  // no flush/compaction is pending or running for rocksdb.quiesce.stablesecs (default 10) consecutive
  // seconds, or rocksdb.quiesce.timeoutsecs (default 7200) elapses. RocksJava 8.10 has no
  // waitForCompact, so this polls the same properties DB::WaitForCompact would observe. Used by the
  // harness as a separate, unmeasured invocation between load and run phases so both systems start
  // every measured phase with no compaction debt carried over.
  private static void maybeQuiesce(final RocksDB db, final Properties props) {
    if (!Boolean.parseBoolean(props.getProperty("rocksdb.quiesceonopen", "false"))) {
      return;
    }
    final int stableNeed = Integer.parseInt(props.getProperty("rocksdb.quiesce.stablesecs", "10").trim());
    final int timeout = Integer.parseInt(props.getProperty("rocksdb.quiesce.timeoutsecs", "7200").trim());
    final long t0 = System.nanoTime();
    int stable = 0;
    long lastLog = -1;
    while (true) {
      final long el = (System.nanoTime() - t0) / 1_000_000_000L;
      long pending = 0;
      long running = 0;
      long flushes = 0;
      long memPending = 0;
      try {
        running = db.getLongProperty("rocksdb.num-running-compactions");
        flushes = db.getLongProperty("rocksdb.num-running-flushes");
        for (final ColumnFamily cf : COLUMN_FAMILIES.values()) {
          pending += db.getLongProperty(cf.getHandle(), "rocksdb.compaction-pending");
          memPending += db.getLongProperty(cf.getHandle(), "rocksdb.mem-table-flush-pending");
        }
        pending += db.getLongProperty("rocksdb.compaction-pending");
        memPending += db.getLongProperty("rocksdb.mem-table-flush-pending");
      } catch (final RocksDBException e) {
        LOGGER.warn("[YW-Custom][QUIESCE] property read failed: " + e.getMessage());
      }
      final boolean idle = pending == 0 && running == 0 && flushes == 0 && memPending == 0;
      stable = idle ? stable + 1 : 0;
      if (el / 30 != lastLog) {
        lastLog = el / 30;
        LOGGER.info("[YW-Custom][QUIESCE] t={}s compaction_pending={} running_compactions={} "
            + "running_flushes={} memtable_flush_pending={} stable={}s",
            el, pending, running, flushes, memPending, stable);
      }
      if (stable >= stableNeed) {
        LOGGER.info("[YW-Custom][QUIESCE] done after {}s", el);
        return;
      }
      if (el >= timeout) {
        LOGGER.warn("[YW-Custom][QUIESCE] TIMEOUT after {}s (pending={} running={}) - proceeding",
            el, pending, running);
        return;
      }
      try {
        Thread.sleep(1000);
      } catch (final InterruptedException e) {
        Thread.currentThread().interrupt();
        return;
      }
    }
  }

  private static void applyMaxOpenFiles(final DBOptions opts, final Properties props) {
    final String v = props.getProperty("rocksdb.maxopenfiles");
    if (v != null) {
      opts.setMaxOpenFiles(Integer.parseInt(v.trim()));
    }
  }

  // [YW-Custom] Memory ledger, printed once just before the DB closes.
  //
  // Why: with cache_index_and_filter_blocks=false (the db_bench convention this project inherited)
  // index and filter blocks do NOT live in the block cache. They are owned by the open table
  // readers and, since max_open_files defaults to -1, every SST is opened at DB::Open and stays
  // open — so they are effectively unbounded heap. The block cache capacity then bounds only data
  // blocks, which means "cache = C vs C+M" does not describe the real memory difference between
  // the two systems. estimate-table-readers-mem is the number that does.
  //
  // Read this together with the ITBL interval table size (M) to get the total-metadata comparison
  // the memory budget argument actually needs.
  private static void logMemoryLedger() {
    if (rocksDb == null) {
      return;
    }
    final String[] props = {
        "rocksdb.estimate-table-readers-mem",   // index + filter held by open table readers (heap)
        "rocksdb.block-cache-usage",
        "rocksdb.block-cache-capacity",
        "rocksdb.block-cache-pinned-usage",
        "rocksdb.estimate-num-keys",
        "rocksdb.live-sst-files-size",
        "rocksdb.num-files-at-level0",
        "rocksdb.estimate-live-data-size",
    };
    // CF-scoped properties need the column family handle. YCSB writes into a CF named after the
    // table ("usertable"), created lazily in createColumnFamily(), so querying without a handle
    // hits the empty default CF and returns 0 for every SST/table-reader figure.
    for (final Map.Entry<String, ColumnFamily> e : COLUMN_FAMILIES.entrySet()) {
      emitLedger(e.getKey(), e.getValue().getHandle(), props);
    }
    // Default CF too, so the line set is complete even when no named CF was created.
    emitLedger("default", null, props);
  }

  private static void emitLedger(final String cfName, final ColumnFamilyHandle cf,
      final String[] props) {
    final StringBuilder sb = new StringBuilder("[YW-Custom][MEM-LEDGER] cf=").append(cfName);
    for (final String p : props) {
      String v;
      try {
        v = cf == null ? rocksDb.getProperty(p) : rocksDb.getProperty(cf, p);
      } catch (final RocksDBException e) {
        v = "err";
      }
      sb.append(' ').append(p.replace("rocksdb.", "")).append('=').append(v);
    }
    // LOGGER writes to stderr under slf4j-simple; a second System.err.println duplicates the line.
    LOGGER.info(sb.toString());
  }

  // [YW-Custom] setCompressionType alone is not enough: compression_per_level, once populated,
  // takes precedence, so a stale array would leave compression on at L2+. Write the whole array.
  private static void applyCompression(final Options opts, final CompressionType compression,
      final int numLevels) {
    if (compression == null) {
      return;
    }
    opts.setCompressionType(compression);
    final int effectiveNumLevels = numLevels > 0 ? numLevels : 7;
    final List<CompressionType> perLevel = new ArrayList<>(effectiveNumLevels);
    for (int i = 0; i < effectiveNumLevels; i++) {
      perLevel.add(compression);
    }
    opts.setCompressionPerLevel(perLevel);
  }

  private int parseIntProp(final String key, final int defaultValue) {
    final String val = getProperties().getProperty(key);
    return val != null ? Integer.parseInt(val) : defaultValue;
  }

  private long parseLongProp(final String key, final long defaultValue) {
    final String val = getProperties().getProperty(key);
    return val != null ? Long.parseLong(val) : defaultValue;
  }


  // [YW-Custom] Boolean prop: accepts "true"/"false" (case-insensitive). Anything else → defaultValue.
  private boolean parseBoolProp(final String key, final boolean defaultValue) {
    final String val = getProperties().getProperty(key);
    if (val == null) {
      return defaultValue;
    }
    return Boolean.parseBoolean(val);
  }

  // [YW-Custom] Compression prop: accepts RocksDB enum names (NO_COMPRESSION, SNAPPY_COMPRESSION,
  // LZ4_COMPRESSION, ZSTD_COMPRESSION, etc.). Case-insensitive; falls back to defaultValue on unknown.
  private CompressionType parseCompressionProp(final String key, final CompressionType defaultValue) {
    final String val = getProperties().getProperty(key);
    if (val == null) {
      return defaultValue;
    }
    try {
      return CompressionType.valueOf(val.trim().toUpperCase(Locale.ROOT));
    } catch (final IllegalArgumentException e) {
      LOGGER.warn("[YW-Custom] unknown rocksdb.compression value '" + val + "'; using default");
      return defaultValue;
    }
  }

  @Override
  public void cleanup() throws DBException {
    super.cleanup();

    // [YW-Custom][BREAKDOWN] hand off this thread's last second before the last client stops the writer.
    if (bd != null) {
      bd.flush();
      bd = null;
    }

    synchronized (RocksDBClient.class) {
      try {
        if (references == 1) {
          RocksDBBreakdown.stop();
          logMemoryLedger();
          if (sharedStatistics != null) {
            for (final String line : sharedStatistics.toString().split("\n")) {
              LOGGER.info("[YW-Custom][STATS] " + line);
            }
          }

          for (final ColumnFamily cf : COLUMN_FAMILIES.values()) {
            cf.getHandle().close();
          }

          rocksDb.close();
          rocksDb = null;

          dbOptions.close();
          dbOptions = null;

          // [YW-Custom] release WriteOptions allocated in initRocksDB.
          if (writeOptions != null) {
            writeOptions.close();
            writeOptions = null;
          }

          for (final ColumnFamily cf : COLUMN_FAMILIES.values()) {
            cf.getOptions().close();
          }
          saveColumnFamilyNames();
          COLUMN_FAMILIES.clear();

          rocksDbDir = null;
        }

      } catch (final IOException e) {
        throw new DBException(e);
      } finally {
        references--;
      }
    }
  }

  @Override
  public Status read(final String table, final String key, final Set<String> fields,
      final Map<String, ByteIterator> result) {
    if (bd != null) {
      return readBd(table, key, fields, result);
    }
    try {
      if (!COLUMN_FAMILIES.containsKey(table)) {
        createColumnFamily(table);
      }

      final ColumnFamilyHandle cf = COLUMN_FAMILIES.get(table).getHandle();
      final byte[] values = rocksDb.get(cf, toRocksKey(key)); // [YW-Custom]
      if(values == null) {
        return Status.NOT_FOUND;
      }
      deserializeValues(values, fields, result);
      return Status.OK;
    } catch(final RocksDBException e) {
      LOGGER.error(e.getMessage(), e);
      return Status.ERROR;
    }
  }

  @Override
  public Status scan(final String table, final String startkey, final int recordcount, final Set<String> fields,
        final Vector<HashMap<String, ByteIterator>> result) {
    if (bd != null) {
      return scanBd(table, startkey, recordcount, fields, result);
    }
    try {
      if (!COLUMN_FAMILIES.containsKey(table)) {
        createColumnFamily(table);
      }

      final ColumnFamilyHandle cf = COLUMN_FAMILIES.get(table).getHandle();
      try(final RocksIterator iterator = rocksDb.newIterator(cf)) {
        int iterations = 0;
        for (iterator.seek(toRocksKey(startkey)); iterator.isValid() && iterations < recordcount; // [YW-Custom]
             iterator.next()) {
          final HashMap<String, ByteIterator> values = new HashMap<>();
          deserializeValues(iterator.value(), fields, values);
          result.add(values);
          iterations++;
        }
      }

      return Status.OK;
    } catch(final RocksDBException e) {
      LOGGER.error(e.getMessage(), e);
      return Status.ERROR;
    }
  }

  @Override
  public Status update(final String table, final String key, final Map<String, ByteIterator> values) {
    //TODO(AR) consider if this would be faster with merge operator

    if (bd != null) {
      return updateBd(table, key, values);
    }
    try {
      if (!COLUMN_FAMILIES.containsKey(table)) {
        createColumnFamily(table);
      }

      final ColumnFamilyHandle cf = COLUMN_FAMILIES.get(table).getHandle();
      final Map<String, ByteIterator> result = new HashMap<>();
      final byte[] currentValues = rocksDb.get(cf, toRocksKey(key)); // [YW-Custom]
      if(currentValues == null) {
        return Status.NOT_FOUND;
      }
      deserializeValues(currentValues, null, result);

      //update
      result.putAll(values);

      //store
      rocksDb.put(cf, writeOptions, toRocksKey(key), serializeValues(result)); // [YW-Custom]

      return Status.OK;

    } catch(final RocksDBException | IOException e) {
      LOGGER.error(e.getMessage(), e);
      return Status.ERROR;
    }
  }

  @Override
  public Status insert(final String table, final String key, final Map<String, ByteIterator> values) {
    if (bd != null) {
      return insertBd(table, key, values);
    }
    try {
      if (!COLUMN_FAMILIES.containsKey(table)) {
        createColumnFamily(table);
      }

      final ColumnFamilyHandle cf = COLUMN_FAMILIES.get(table).getHandle();
      rocksDb.put(cf, writeOptions, toRocksKey(key), serializeValues(values)); // [YW-Custom]

      return Status.OK;
    } catch(final RocksDBException | IOException e) {
      LOGGER.error(e.getMessage(), e);
      return Status.ERROR;
    }
  }

  @Override
  public Status delete(final String table, final String key) {
    if (bd != null) {
      return deleteBd(table, key);
    }
    try {
      if (!COLUMN_FAMILIES.containsKey(table)) {
        createColumnFamily(table);
      }

      final ColumnFamilyHandle cf = COLUMN_FAMILIES.get(table).getHandle();
      rocksDb.delete(cf, writeOptions, toRocksKey(key)); // [YW-Custom]

      return Status.OK;
    } catch(final RocksDBException e) {
      LOGGER.error(e.getMessage(), e);
      return Status.ERROR;
    }
  }


  // [YW-Custom][BREAKDOWN] y2 instrumented copies of read/scan/update/insert/delete (DS_ARM_y2 4.5).
  // Same RocksDB calls in the same order as the plain methods above; each segment is timed with
  // System.nanoTime and the call ends with one PerfContext snapshot (RocksDBBreakdown.Tls.end).
  // op_total covers the whole binding call; op_total - segments = binding bookkeeping (CF lookup,
  // timer reads). YCSB's own latency also includes DBWrapper and the snapshot itself.

  private Status readBd(final String table, final String key, final Set<String> fields,
      final Map<String, ByteIterator> result) {
    final long t0 = System.nanoTime();
    try {
      if (!COLUMN_FAMILIES.containsKey(table)) {
        createColumnFamily(table);
      }
      final ColumnFamilyHandle cf = COLUMN_FAMILIES.get(table).getHandle();
      long a = System.nanoTime();
      final byte[] k = toRocksKey(key);
      long b = System.nanoTime();
      bd.add(RocksDBBreakdown.SEG_KEY, b - a);
      final byte[] values = rocksDb.get(cf, k);
      a = System.nanoTime();
      bd.add(RocksDBBreakdown.SEG_GET, a - b);
      if (values == null) {
        return Status.NOT_FOUND;
      }
      deserializeValues(values, fields, result);
      b = System.nanoTime();
      bd.add(RocksDBBreakdown.SEG_DESER, b - a);
      return Status.OK;
    } catch (final RocksDBException e) {
      LOGGER.error(e.getMessage(), e);
      return Status.ERROR;
    } finally {
      bd.end(RocksDBBreakdown.OP_READ, t0, System.nanoTime());
    }
  }

  private Status scanBd(final String table, final String startkey, final int recordcount,
      final Set<String> fields, final Vector<HashMap<String, ByteIterator>> result) {
    final long t0 = System.nanoTime();
    try {
      if (!COLUMN_FAMILIES.containsKey(table)) {
        createColumnFamily(table);
      }
      final ColumnFamilyHandle cf = COLUMN_FAMILIES.get(table).getHandle();
      long a = System.nanoTime();
      final byte[] k = toRocksKey(startkey);
      long b = System.nanoTime();
      bd.add(RocksDBBreakdown.SEG_KEY, b - a);
      final RocksIterator iterator = rocksDb.newIterator(cf);
      a = System.nanoTime();
      bd.add(RocksDBBreakdown.SEG_ITER_NEW, a - b);
      int iterations = 0;
      try {
        iterator.seek(k);
        b = System.nanoTime();
        bd.add(RocksDBBreakdown.SEG_SEEK, b - a);
        // Same call sequence as the plain loop: isValid, (row, next)*, and the final isValid.
        long next = 0;
        long value = 0;
        long deser = 0;
        a = b;
        while (true) {
          final boolean valid = iterator.isValid();
          if (!valid || iterations >= recordcount) {
            b = System.nanoTime();
            next += b - a;
            break;
          }
          b = System.nanoTime();
          next += b - a;
          final byte[] v = iterator.value();
          a = System.nanoTime();
          value += a - b;
          final HashMap<String, ByteIterator> values = new HashMap<>();
          deserializeValues(v, fields, values);
          result.add(values);
          b = System.nanoTime();
          deser += b - a;
          iterations++;
          iterator.next();
          a = System.nanoTime();
          next += a - b;
        }
        bd.add(RocksDBBreakdown.SEG_NEXT, next);
        bd.add(RocksDBBreakdown.SEG_VALUE, value);
        bd.add(RocksDBBreakdown.SEG_SCAN_DESER, deser);
        bd.add(RocksDBBreakdown.SEG_ROWS, iterations);
      } finally {
        a = System.nanoTime();
        iterator.close();
        bd.add(RocksDBBreakdown.SEG_ITER_CLOSE, System.nanoTime() - a);
      }
      return Status.OK;
    } catch (final RocksDBException e) {
      LOGGER.error(e.getMessage(), e);
      return Status.ERROR;
    } finally {
      bd.end(RocksDBBreakdown.OP_SCAN, t0, System.nanoTime());
    }
  }

  private Status updateBd(final String table, final String key, final Map<String, ByteIterator> values) {
    final long t0 = System.nanoTime();
    try {
      if (!COLUMN_FAMILIES.containsKey(table)) {
        createColumnFamily(table);
      }
      final ColumnFamilyHandle cf = COLUMN_FAMILIES.get(table).getHandle();
      final Map<String, ByteIterator> result = new HashMap<>();
      long a = System.nanoTime();
      final byte[] k1 = toRocksKey(key);
      long b = System.nanoTime();
      bd.add(RocksDBBreakdown.SEG_KEY, b - a);
      final byte[] currentValues = rocksDb.get(cf, k1);
      a = System.nanoTime();
      bd.add(RocksDBBreakdown.SEG_GET, a - b);
      if (currentValues == null) {
        return Status.NOT_FOUND;
      }
      deserializeValues(currentValues, null, result);
      b = System.nanoTime();
      bd.add(RocksDBBreakdown.SEG_DESER, b - a);
      result.putAll(values);
      a = System.nanoTime();
      bd.add(RocksDBBreakdown.SEG_MERGE, a - b);
      final byte[] k2 = toRocksKey(key);
      b = System.nanoTime();
      bd.add(RocksDBBreakdown.SEG_KEY, b - a);
      final byte[] sv = serializeValues(result);
      a = System.nanoTime();
      bd.add(RocksDBBreakdown.SEG_SER, a - b);
      rocksDb.put(cf, writeOptions, k2, sv);
      b = System.nanoTime();
      bd.add(RocksDBBreakdown.SEG_PUT, b - a);
      return Status.OK;
    } catch (final RocksDBException | IOException e) {
      LOGGER.error(e.getMessage(), e);
      return Status.ERROR;
    } finally {
      bd.end(RocksDBBreakdown.OP_UPDATE, t0, System.nanoTime());
    }
  }

  private Status insertBd(final String table, final String key, final Map<String, ByteIterator> values) {
    final long t0 = System.nanoTime();
    try {
      if (!COLUMN_FAMILIES.containsKey(table)) {
        createColumnFamily(table);
      }
      final ColumnFamilyHandle cf = COLUMN_FAMILIES.get(table).getHandle();
      long a = System.nanoTime();
      final byte[] k = toRocksKey(key);
      long b = System.nanoTime();
      bd.add(RocksDBBreakdown.SEG_KEY, b - a);
      final byte[] sv = serializeValues(values);
      a = System.nanoTime();
      bd.add(RocksDBBreakdown.SEG_SER, a - b);
      rocksDb.put(cf, writeOptions, k, sv);
      b = System.nanoTime();
      bd.add(RocksDBBreakdown.SEG_PUT, b - a);
      return Status.OK;
    } catch (final RocksDBException | IOException e) {
      LOGGER.error(e.getMessage(), e);
      return Status.ERROR;
    } finally {
      bd.end(RocksDBBreakdown.OP_INSERT, t0, System.nanoTime());
    }
  }

  private Status deleteBd(final String table, final String key) {
    final long t0 = System.nanoTime();
    try {
      if (!COLUMN_FAMILIES.containsKey(table)) {
        createColumnFamily(table);
      }
      final ColumnFamilyHandle cf = COLUMN_FAMILIES.get(table).getHandle();
      long a = System.nanoTime();
      final byte[] k = toRocksKey(key);
      long b = System.nanoTime();
      bd.add(RocksDBBreakdown.SEG_KEY, b - a);
      rocksDb.delete(cf, writeOptions, k);
      a = System.nanoTime();
      bd.add(RocksDBBreakdown.SEG_DELETE, a - b);
      return Status.OK;
    } catch (final RocksDBException e) {
      LOGGER.error(e.getMessage(), e);
      return Status.ERROR;
    } finally {
      bd.end(RocksDBBreakdown.OP_DELETE, t0, System.nanoTime());
    }
  }

  private void saveColumnFamilyNames() throws IOException {
    final Path file = rocksDbDir.resolve(COLUMN_FAMILY_NAMES_FILENAME);
    try(final PrintWriter writer = new PrintWriter(Files.newBufferedWriter(file, UTF_8))) {
      writer.println(new String(RocksDB.DEFAULT_COLUMN_FAMILY, UTF_8));
      for(final String cfName : COLUMN_FAMILIES.keySet()) {
        writer.println(cfName);
      }
    }
  }

  private List<String> loadColumnFamilyNames() throws IOException {
    final List<String> cfNames = new ArrayList<>();
    final Path file = rocksDbDir.resolve(COLUMN_FAMILY_NAMES_FILENAME);
    if(Files.exists(file)) {
      try (final LineNumberReader reader =
               new LineNumberReader(Files.newBufferedReader(file, UTF_8))) {
        String line = null;
        while ((line = reader.readLine()) != null) {
          cfNames.add(line);
        }
      }
    }
    return cfNames;
  }

  private Map<String, ByteIterator> deserializeValues(final byte[] values, final Set<String> fields,
      final Map<String, ByteIterator> result) {
    final ByteBuffer buf = ByteBuffer.allocate(4);

    int offset = 0;
    while(offset < values.length) {
      buf.put(values, offset, 4);
      buf.flip();
      final int keyLen = buf.getInt();
      buf.clear();
      offset += 4;

      final String key = new String(values, offset, keyLen);
      offset += keyLen;

      buf.put(values, offset, 4);
      buf.flip();
      final int valueLen = buf.getInt();
      buf.clear();
      offset += 4;

      if(fields == null || fields.contains(key)) {
        result.put(key, new ByteArrayByteIterator(values, offset, valueLen));
      }

      offset += valueLen;
    }

    return result;
  }

  // [YW-Custom] Hash YCSB string key to 16-byte binary key, equivalent to db_bench --random_byte_keys=1.
  // All CRUD methods use this so load and run phases are consistent.
  private static byte[] toRocksKey(final String key) {
    try {
      return MessageDigest.getInstance("MD5").digest(key.getBytes(UTF_8));
    } catch (final NoSuchAlgorithmException e) {
      throw new RuntimeException(e); // MD5 is always available in Java
    }
  }

  private byte[] serializeValues(final Map<String, ByteIterator> values) throws IOException {
    try(final ByteArrayOutputStream baos = new ByteArrayOutputStream()) {
      final ByteBuffer buf = ByteBuffer.allocate(4);

      for(final Map.Entry<String, ByteIterator> value : values.entrySet()) {
        final byte[] keyBytes = value.getKey().getBytes(UTF_8);
        final byte[] valueBytes = value.getValue().toArray();

        buf.putInt(keyBytes.length);
        baos.write(buf.array());
        baos.write(keyBytes);

        buf.clear();

        buf.putInt(valueBytes.length);
        baos.write(buf.array());
        baos.write(valueBytes);

        buf.clear();
      }
      return baos.toByteArray();
    }
  }

  private ColumnFamilyOptions getDefaultColumnFamilyOptions(final String destinationCfName) {
    final ColumnFamilyOptions cfOptions;

    if (COLUMN_FAMILIES.containsKey("default")) {
      LOGGER.warn("no column family options for \"" + destinationCfName + "\" " +
                  "in options file - using options from \"default\"");
      cfOptions = COLUMN_FAMILIES.get("default").getOptions();
    } else {
      LOGGER.warn("no column family options for either \"" + destinationCfName + "\" or " +
                  "\"default\" in options file - initializing with empty configuration");
      cfOptions = new ColumnFamilyOptions();
    }
    LOGGER.warn("Add a CFOptions section for \"" + destinationCfName + "\" to the options file, " +
                "or subsequent runs on this DB will fail.");

    return cfOptions;
  }

  private void createColumnFamily(final String name) throws RocksDBException {
    COLUMN_FAMILY_LOCKS.putIfAbsent(name, new ReentrantLock());

    final Lock l = COLUMN_FAMILY_LOCKS.get(name);
    l.lock();
    try {
      if(!COLUMN_FAMILIES.containsKey(name)) {
        final ColumnFamilyOptions cfOptions;

        if (optionsFile != null) {
          // RocksDB requires all options files to include options for the "default" column family;
          // apply those options to this column family
          cfOptions = getDefaultColumnFamilyOptions(name);
        } else {
          // [YW-Custom] optimizeLevelStyleCompaction() removed 2026-09 — see initRocksDB().
          cfOptions = new ColumnFamilyOptions();
          // [YW-Custom] Apply all CF options configured at open time (num_levels, L0 thresholds, etc.).
          new CfOpts(cfNumLevels, cfMaxBytesForLevelBase,
              cfLevel0CompactionTrigger, cfLevel0SlowdownTrigger, cfLevel0StopTrigger,
              cfMaxWriteBufferNumber, cfCompression).applyTo(cfOptions);
          cfExtra.applyTo(cfOptions);
        }

        final ColumnFamilyHandle cfHandle = rocksDb.createColumnFamily(
            new ColumnFamilyDescriptor(name.getBytes(UTF_8), cfOptions)
        );
        COLUMN_FAMILIES.put(name, new ColumnFamily(cfHandle, cfOptions));
      }
    } finally {
      l.unlock();
    }
  }

  private static final class ColumnFamily {
    private final ColumnFamilyHandle handle;
    private final ColumnFamilyOptions options;

    private ColumnFamily(final ColumnFamilyHandle handle, final ColumnFamilyOptions options) {
      this.handle = handle;
      this.options = options;
    }

    public ColumnFamilyHandle getHandle() {
      return handle;
    }

    public ColumnFamilyOptions getOptions() {
      return options;
    }
  }
}
