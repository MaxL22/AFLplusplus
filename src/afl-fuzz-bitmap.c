/*
   american fuzzy lop++ - bitmap related routines
   ----------------------------------------------

   Originally written by Michal Zalewski

   Now maintained by Marc Heuse <mh@mh-sec.de>,
                        Heiko Eissfeldt <heiko.eissfeldt@hexco.de> and
                        Andrea Fioraldi <andreafioraldi@gmail.com>

   Copyright 2016, 2017 Google Inc. All rights reserved.
   Copyright 2019-2026 AFLplusplus Project. All rights reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at:

     https://www.apache.org/licenses/LICENSE-2.0

   This is the real deal: the program takes an instrumented binary and
   attempts a variety of basic fuzzing tricks, paying close attention to
   how they affect the execution path.

 */

#include "afl-fuzz.h"
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include "asanfuzz.h"

u16 count_class_lookup16[65536];

/* Destructively simplify trace by eliminating hit count information
   and replacing it with 0x80 or 0x01 depending on whether the tuple
   is hit or not. Called on every new crash or timeout, should be
   reasonably fast. */
static const u8 simplify_lookup[256] = {

    [0] = 1, [1 ... 255] = 128

};

/* Destructively classify execution counts in a trace. This is used as a
   preprocessing step for any newly acquired traces. Called on every exec,
   must be fast. */

static const u8 count_class_lookup8[256] = {

    [0] = 0,
    [1] = 1,
    [2] = 2,
    [3] = 4,
    [4 ... 7] = 8,
    [8 ... 15] = 16,
    [16 ... 31] = 32,
    [32 ... 127] = 64,
    [128 ... 255] = 128

};

/* Import coverage processing routines. */

#ifdef WORD_SIZE_64
  #include "coverage-64.h"
#else
  #include "coverage-32.h"
#endif

#if !defined NAME_MAX
  #define NAME_MAX _XOPEN_NAME_MAX
#endif

/* Write bitmap to file. The bitmap is useful mostly for the secret
   -B option, to focus a separate fuzzing session on a particular
   interesting input without rediscovering all the others. */

void write_bitmap(afl_state_t *afl) {

  u8  fname[PATH_MAX];
  s32 fd;

  if (!afl->bitmap_changed) { return; }
  afl->bitmap_changed = 0;

  snprintf(fname, PATH_MAX, "%s/fuzz_bitmap", afl->out_dir);
  fd = open(fname, O_WRONLY | O_CREAT | O_TRUNC, afl->perm);

  if (fd < 0) { PFATAL("Unable to open '%s'", fname); }

  if (afl->chown_needed) {

    if (fchown(fd, -1, afl->fsrv.gid) == -1) { PFATAL("fchown() failed"); }

  }

  ck_write(fd, afl->virgin_bits, afl->fsrv.map_size, fname);

  // INDIR_CHANGE
  // Write the bitmap to resume
  // It is currently NOT fully implemented
  if (afl->shm.indir_mode) {

    // fsrv and not shm cus we want to write only the actual size
    ck_write(fd, afl->indir_virgin_bits, afl->fsrv.indir_map_size, fname);

  }

  close(fd);

}

/* Count the number of bits set in the provided bitmap. Used for the status
   screen several times every second, does not have to be fast. */

u32 count_bits(afl_state_t *afl, u8 *mem) {

  u32 *ptr = (u32 *)mem;
  u32  i = ((afl->fsrv.real_map_size + 3) >> 2);
  u32  ret = 0;

  while (i--) {

    u32 v = *(ptr++);

    /* This gets called on the inverse, virgin bitmap; optimize for sparse
       data. */

    if (likely(v == 0xffffffff)) {

      ret += 32;
      continue;

    }

#if __has_builtin(__builtin_popcount)
    ret += __builtin_popcount(v);
#else
    v -= ((v >> 1) & 0x55555555);
    v = (v & 0x33333333) + ((v >> 2) & 0x33333333);
    ret += (((v + (v >> 4)) & 0xF0F0F0F) * 0x01010101) >> 24;
#endif

  }

  return ret;

}

// INDIR_CHANGE: guard against inactive indirect mode and skip dummy slot 0
u32 count_indir_bits(afl_state_t *afl) {

  if (!afl->shm.indir_mode || !afl->indir_virgin_bits ||
      afl->fsrv.indir_map_size <= sizeof(indir_slot_t)) {

    return 0;

  }

  // INDIR_CHANGE: called on every UI refresh and fuzz_one log line; the
  // virgin map only changes through has_indir_new_bits_map() and calibration
  if (!afl->indir_count_dirty) { return afl->indir_count_cache; }
  afl->indir_count_dirty = 0;

  u32 *ptr = (u32 *)(afl->indir_virgin_bits + sizeof(indir_slot_t));
  u32  i = ((afl->fsrv.indir_map_size - sizeof(indir_slot_t)) >> 2);
  u32  ret = 0;

  // Counting zeros: we have the virgin map, bits are set to zero as they are
  // discovered
  while (i--) {

    u32 v = *(ptr++);
    ret += __builtin_popcount(~v);

  }

  afl->indir_count_cache = ret;
  return ret;

}

// INDIR_CHANGE: guard against inactive indirect mode or NULL mem pointer
/* Count the number of bits set in the indir bitmap. Called fairly sporadically,
   mostly to update the status screen or calibrate and examine confirmed
   new paths. */

u32 count_indir_bits_run(afl_state_t *afl, u8 *mem) {

  if (!afl->shm.indir_mode || !mem ||
      afl->fsrv.indir_map_size <= sizeof(indir_slot_t)) {

    return 0;

  }

  // INDIR_CHANGE: skip the slot-0 sink, like count_indir_bits()
  u32 *ptr = (u32 *)(mem + sizeof(indir_slot_t));
  u32  i = ((afl->fsrv.indir_map_size - sizeof(indir_slot_t)) >> 2);
  u32  ret = 0;

  while (i--) {

    u32 v = *(ptr++);
    ret += __builtin_popcount(v);

  }

  return ret;

}

/* Count the number of bytes set in the bitmap. Called fairly sporadically,
   mostly to update the status screen or calibrate and examine confirmed
   new paths. */

u32 count_bytes(afl_state_t *afl, u8 *mem) {

  u32 *ptr = (u32 *)mem;
  u32  i = ((afl->fsrv.real_map_size + 3) >> 2);
  u32  ret = 0;

  while (i--) {

    u32 v = *(ptr++);

    if (likely(!v)) { continue; }
    if (v & 0x000000ffU) { ++ret; }
    if (v & 0x0000ff00U) { ++ret; }
    if (v & 0x00ff0000U) { ++ret; }
    if (v & 0xff000000U) { ++ret; }

  }

  return ret;

}

/* Count the number of non-255 bytes set in the bitmap. Used strictly for the
   status screen, several calls per second or so. */

u32 count_non_255_bytes(afl_state_t *afl, u8 *mem) {

  u32 *ptr = (u32 *)mem;
  u32  i = ((afl->fsrv.real_map_size + 3) >> 2);
  u32  ret = 0;

  while (i--) {

    u32 v = *(ptr++);

    /* This is called on the virgin bitmap, so optimize for the most likely
       case. */

    if (likely(v == 0xffffffffU)) { continue; }
    if ((v & 0x000000ffU) != 0x000000ffU) { ++ret; }
    if ((v & 0x0000ff00U) != 0x0000ff00U) { ++ret; }
    if ((v & 0x00ff0000U) != 0x00ff0000U) { ++ret; }
    if ((v & 0xff000000U) != 0xff000000U) { ++ret; }

  }

  return ret;

}

void init_count_class16(void) {

  u32 b1, b2;

  for (b1 = 0; b1 < 256; b1++) {

    for (b2 = 0; b2 < 256; b2++) {

      count_class_lookup16[(b1 << 8) + b2] =
          (count_class_lookup8[b1] << 8) | count_class_lookup8[b2];

    }

  }

}

/* Check if the current execution path brings anything new to the table.
   Update virgin bits to reflect the finds. Returns 1 if the only change is
   the hit-count for a particular tuple; 2 if there are new tuples seen.
   Updates the map, so subsequent calls will always return 0.

   This function is called after every exec() on a fairly large buffer, so
   it needs to be fast. We do this in 32-bit and 64-bit flavors. */

inline u8 has_new_bits(afl_state_t *afl, u8 *virgin_map) {

#ifdef WORD_SIZE_64

  u64 *current = (u64 *)afl->fsrv.trace_bits;
  u64 *virgin = (u64 *)virgin_map;

  u32 i = ((afl->fsrv.real_map_size + 7) >> 3);

#else

  u32 *current = (u32 *)afl->fsrv.trace_bits;
  u32 *virgin = (u32 *)virgin_map;

  u32 i = ((afl->fsrv.real_map_size + 3) >> 2);

#endif                                                     /* ^WORD_SIZE_64 */

  u8 ret = 0;
  while (i--) {

    if (unlikely(*current)) discover_word(&ret, current, virgin);

    current++;
    virgin++;

  }

  if (unlikely(ret) && likely(virgin_map == afl->virgin_bits))
    afl->bitmap_changed = 1;

  return ret;

}

// INDIR_CHANGE: dedicated SIMD raw bitwise novelty check without
// classify_word()
#if defined(__AVX2__)
static inline u32 skim_indir(const u64 *virgin, const u64 *current,
                             const u64 *current_end) {

  for (; current + 4 <= current_end; virgin += 4, current += 4) {

    __m256i cur_val = _mm256_loadu_si256((const __m256i *)current);
    if (_mm256_testz_si256(cur_val, cur_val)) continue;  // All bytes zero

    __m256i vir_val = _mm256_loadu_si256((const __m256i *)virgin);
    __m256i and_val = _mm256_and_si256(cur_val, vir_val);
    if (!_mm256_testz_si256(and_val, and_val)) return 1;  // Novel bits found!

  }

  while (current < current_end) {

    if (unlikely(*current & *virgin)) return 1;
    current++;
    virgin++;

  }

  return 0;

}

#endif

// INDIR_CHANGE: non-mutating novelty check for calibration
inline u8 check_indir_new_bits_map(afl_state_t *afl,
                                   const u8    *indir_virgin_map) {

#if defined(__AVX2__) && defined(WORD_SIZE_64)
  const u64 *end =
      (const u64 *)(afl->fsrv.indir_bits + afl->fsrv.indir_map_size);
  return skim_indir((const u64 *)indir_virgin_map,
                    (const u64 *)afl->fsrv.indir_bits, end);
#else
  #ifdef WORD_SIZE_64
  u64 *current = (u64 *)afl->fsrv.indir_bits;
  u64 *virgin = (u64 *)indir_virgin_map;
  u32  i = (afl->fsrv.indir_map_size >> 3);
  #else
  u32 *current = (u32 *)afl->fsrv.indir_bits;
  u32 *virgin = (u32 *)indir_virgin_map;
  u32  i = (afl->fsrv.indir_map_size >> 2);
  #endif
  while (i--) {

    if (unlikely(*current & *virgin)) return 1;
    current++;
    virgin++;

  }

  return 0;
#endif

}

// INDIR_CHANGE: returns 1 if new indirect coverage is found, 0 otherwise
inline u8 has_indir_new_bits_map(afl_state_t *afl, u8 *indir_virgin_map) {

  // INDIR_CHANGE: indir_map_size is always a multiple of 64 (forkserver hello
  // and AFL_INDIR_MAP_SIZE are rounded up), no per-execution check needed

#if defined(__AVX2__) && defined(WORD_SIZE_64)
  const u64 *end =
      (const u64 *)(afl->fsrv.indir_bits + afl->fsrv.indir_map_size);
  if (!skim_indir((const u64 *)indir_virgin_map,
                  (const u64 *)afl->fsrv.indir_bits, end))
    return 0;
#endif

#ifdef WORD_SIZE_64
  u64 *current = (u64 *)afl->fsrv.indir_bits;
  u64 *virgin = (u64 *)indir_virgin_map;
  u32  i = (afl->fsrv.indir_map_size >> 3);  // divide by 8
#else
  u32 *current = (u32 *)afl->fsrv.indir_bits;
  u32 *virgin = (u32 *)indir_virgin_map;
  u32  i = (afl->fsrv.indir_map_size >> 2);  // divide by 4
#endif

  u8 ret = 0;

  while (i--) {

    if (unlikely(*current)) {

      if (unlikely(*current & *virgin)) {

        ret = 1;
        *virgin &= ~(*current);

      }

    }

    current++;
    virgin++;

  }

  if (unlikely(ret)) {

    afl->bitmap_changed = 1;
    afl->indir_count_dirty = 1;

  }

  return ret;

}

// INDIR_CHANGE: checksum of the indirect trace. Bytes known to be variable
// are cleared first (in fsrv.indir_bits too, they are masked in
// indir_virgin_bits anyway), so that flaky pairs do not change the checksum.
u64 hash_indir_trace(afl_state_t *afl) {

  u8 *bits = afl->fsrv.indir_bits;
  u8 *var = afl->indir_var_bytes;

#ifdef WORD_SIZE_64
  u64 *bits64 = (u64 *)bits, *var64 = (u64 *)var;
  for (u32 i = 0; i < (afl->fsrv.indir_map_size >> 3); ++i) {

    if (unlikely(var64[i] && bits64[i])) {

      for (u32 j = i << 3; j < (i << 3) + 8; ++j) {

        if (var[j]) { bits[j] = 0; }

      }

    }

  }

#else
  for (u32 i = 0; i < afl->fsrv.indir_map_size; ++i) {

    if (unlikely(var[i])) { bits[i] = 0; }

  }

#endif

  return hash64(bits, afl->fsrv.indir_map_size, HASH_CONST);

}

/* INDIR_CHANGE: check the indirect trace for novelty and record it in
   indir_virgin_bits when it counts. With edge novelty (new_bits != 0) new
   indirect bits are simply recorded. Indirect-only novelty is a weaker signal:
   it is only accepted when the edge path differs from the parent's (otherwise
   the input just re-pairs code the parent already runs) and at least one
   novel site is still below its cap of indirect-only saves. Rejected bits are
   not recorded, so a later input that passes can still claim them. Returns 1
   if new indirect bits were recorded. */

static u8 indir_novelty(afl_state_t *afl, u8 new_bits, u64 cksum) {

  if (likely(!check_indir_new_bits_map(afl, afl->indir_virgin_bits))) {

    return 0;

  }

  if (new_bits) { return has_indir_new_bits_map(afl, afl->indir_virgin_bits); }

  if (afl->queue_cur && !afl->syncing_party &&
      afl->queue_cur->exec_cksum == cksum) {

    return 0;

  }

  indir_slot_t *cur = (indir_slot_t *)afl->fsrv.indir_bits;
  indir_slot_t *virgin = (indir_slot_t *)afl->indir_virgin_bits;
  u32           slots = afl->fsrv.indir_map_size / sizeof(indir_slot_t);
  u32           i;

  if (afl->indir_max_per_site) {

    for (i = 1; i < slots; ++i) {

      if ((cur[i] & virgin[i]) &&
          afl->indir_site_saves[i] < afl->indir_max_per_site) {

        break;

      }

    }

    if (i == slots) { return 0; }

  }

  for (i = 1; i < slots; ++i) {

    if (cur[i] & virgin[i]) { ++afl->indir_site_saves[i]; }

  }

  return has_indir_new_bits_map(afl, afl->indir_virgin_bits);

}

/* A combination of classify_counts and has_new_bits. If 0 is returned, then the
 * trace bits are kept as-is. Otherwise, the trace bits are overwritten with
 * classified values.
 *
 * This accelerates the processing: in most cases, no interesting behavior
 * happen, and the trace bits will be discarded soon. This function optimizes
 * for such cases: one-pass scan on trace bits without modifying anything. Only
 * on rare cases it fall backs to the slow path: classify_counts() first, then
 * return has_new_bits(). */

static inline u8 has_new_bits_unclassified(afl_state_t *afl, u8 *virgin_map,
                                           bool *classified) {

  /* Handle the hot path first: no new coverage */
  u8 *end = afl->fsrv.trace_bits + afl->fsrv.map_size;

#ifdef WORD_SIZE_64

  if (!skim((u64 *)virgin_map, (u64 *)afl->fsrv.trace_bits, (u64 *)end))
    return 0;

#else

  if (!skim((u32 *)virgin_map, (u32 *)afl->fsrv.trace_bits, (u32 *)end))
    return 0;

#endif                                                     /* ^WORD_SIZE_64 */
  classify_counts(&afl->fsrv);
  *classified = true;
  return has_new_bits(afl, virgin_map);

}

/* Compact trace bytes into a smaller bitmap. We effectively just drop the
   count information here. This is called only sporadically, for some
   new paths. */

void minimize_bits(afl_state_t *afl, u8 *dst, u8 *src) {

  u32 i = 0;

  while (i < afl->fsrv.map_size) {

    if (*(src++)) { dst[i >> 3] |= 1 << (i & 7); }
    ++i;

  }

}

#ifndef SIMPLE_FILES

/* Construct a file name for a new test case, capturing the operation
   that led to its discovery. Returns a ptr to afl->describe_op_buf_256. */

u8 *describe_op(afl_state_t *afl, u8 new_bits, size_t max_description_len) {

  u8 is_timeout = 0;
  u8 san_crash_only = (afl->san_case_status & SAN_CRASH_ONLY);
  u8 non_cov_incr = (afl->san_case_status & NON_COV_INCREASE_BUG);

  if (new_bits & 0xf0) {

    new_bits -= 0x80;
    is_timeout = 1;

  }

  size_t real_max_len =
      MIN(max_description_len, sizeof(afl->describe_op_buf_256));
  u8 *ret = afl->describe_op_buf_256;

  if (unlikely(afl->syncing_party)) {

    if (unlikely(afl->foreign_file)) {

      sprintf(ret, "sync:%s,src:%.20s", afl->syncing_party, afl->foreign_file);

    } else {

      sprintf(ret, "sync:%s,src:%06u", afl->syncing_party, afl->syncing_case);

    }

  } else {

    sprintf(ret, "src:%06u", afl->current_entry);

    if (afl->splicing_with >= 0) {

      sprintf(ret + strlen(ret), "+%06d", afl->splicing_with);

    }

    sprintf(ret + strlen(ret), ",time:%llu,execs:%llu",
            get_cur_time() + afl->prev_run_time - afl->start_time,
            afl->fsrv.total_execs);

    if (afl->current_custom_fuzz &&
        afl->current_custom_fuzz->afl_custom_describe) {

      /* We are currently in a custom mutator that supports afl_custom_describe,
       * use it! */

      size_t len_current = strlen(ret);
      ret[len_current++] = ',';
      ret[len_current] = '\0';

      // INDIR_CHANGE: ",+icov" is the longest coverage tag
      ssize_t size_left = real_max_len - len_current - strlen(",+icov") - 2;
      if (is_timeout) { size_left -= strlen(",+tout"); }
      if (unlikely(size_left <= 0)) FATAL("filename got too long");

      const char *custom_description =
          afl->current_custom_fuzz->afl_custom_describe(
              afl->current_custom_fuzz->data, size_left);
      if (!custom_description || !custom_description[0]) {

        DEBUGF("Error getting a description from afl_custom_describe");
        /* Take the stage name as description fallback */
        sprintf(ret + len_current, "op:%s", afl->stage_short);

      } else {

        /* We got a proper custom description, use it */
        strncat(ret + len_current, custom_description, size_left);

      }

    } else {

      /* Normal testcase descriptions start here */
      sprintf(ret + strlen(ret), ",op:%s", afl->stage_short);

      if (afl->stage_cur_byte >= 0) {

        sprintf(ret + strlen(ret), ",pos:%d", afl->stage_cur_byte);

        if (afl->stage_val_type != STAGE_VAL_NONE) {

          sprintf(ret + strlen(ret), ",val:%s%+d",
                  (afl->stage_val_type == STAGE_VAL_BE) ? "be:" : "",
                  afl->stage_cur_val);

        }

      } else {

        sprintf(ret + strlen(ret), ",rep:%d", afl->stage_cur_val);

      }

    }

  }

  if (is_timeout) { strcat(ret, ",+tout"); }

  if (new_bits == 2) { strcat(ret, ",+cov"); }

  // INDIR_CHANGE: saved for indirect-only novelty
  if (afl->indir_only_find) { strcat(ret, ",+icov"); }

  if (san_crash_only) { strcat(ret, ",+san"); }

  if (non_cov_incr) { strcat(ret, ",+noncov"); }

  if (unlikely(strlen(ret) >= max_description_len))
    FATAL("describe string is too long");

  return ret;

}

#endif                                                     /* !SIMPLE_FILES */

/* Write a message accompanying the crash directory :-) */

void write_crash_readme(afl_state_t *afl) {

  u8    fn[PATH_MAX];
  s32   fd;
  FILE *f;

  u8 val_buf[STRINGIFY_VAL_SIZE_MAX];

  sprintf(fn, "%s/crashes/README.txt", afl->out_dir);

  fd = open(fn, O_WRONLY | O_CREAT | O_EXCL, afl->perm);

  /* Do not die on errors here - that would be impolite. */

  if (unlikely(fd < 0)) { return; }

  if (afl->chown_needed) {

    if (fchown(fd, -1, afl->fsrv.gid) == -1) { PFATAL("fchown() failed"); }

  }

  f = fdopen(fd, "w");

  if (unlikely(!f)) {

    close(fd);
    return;

  }

  fprintf(
      f,
      "Command line used to find this crash:\n\n"

      "%s\n\n"

      "If you can't reproduce a bug outside of afl-fuzz, be sure to set the "
      "same\n"
      "memory limit. The limit used for this fuzzing session was %s.\n\n"

      "Need a tool to minimize test cases before investigating the crashes or "
      "sending\n"
      "them to a vendor? Check out the afl-tmin that comes with the fuzzer!\n\n"

      "Found any cool bugs in open-source tools using afl-fuzz? If yes, please "
      "post\n"
      "to https://github.com/AFLplusplus/AFLplusplus/issues/286 once the "
      "issues\n"
      " are fixed :)\n\n",

      afl->orig_cmdline,
      stringify_mem_size(val_buf, sizeof(val_buf),
                         afl->fsrv.mem_limit << 20));      /* ignore errors */

  fclose(f);

}

static inline void classify_if_necessary(afl_state_t *afl, bool *classified) {

  if (*classified) return;
  classify_counts(&afl->fsrv);
  *classified = true;

}

static inline void calculate_cksum_if_necessary(afl_state_t *afl, u64 *cksum,
                                                bool *cksumed,
                                                bool *classified) {

  if (*cksumed) return;
  classify_if_necessary(afl, classified);
  *cksum = hash64(afl->fsrv.trace_bits, afl->fsrv.map_size, HASH_CONST);
  *cksumed = true;

}

static inline void calculate_new_bits_if_necessary(afl_state_t *afl,
                                                   u8          *new_bits,
                                                   bool        *bits_counted,
                                                   bool        *classified) {

  if (*bits_counted) return;

  if (*classified) {

    *new_bits = has_new_bits(afl, afl->virgin_bits);

  } else {

    *new_bits = has_new_bits_unclassified(afl, afl->virgin_bits, classified);

  }

  *bits_counted = true;

}

// INDIR_CHANGE: n_fuzz bucket of the current execution, see indir_path_id()
static inline u32 n_fuzz_path(afl_state_t *afl, u64 cksum) {

  return indir_path_id(afl, cksum,
                       afl->shm.indir_mode ? hash_indir_trace(afl) : 0);

}

/* INDIR_CHANGE: q found new edges. Credit its indirect-only ancestors, to
   measure whether keeping indirect-only finds leads to new edge coverage. */

static void indir_credit_ancestors(afl_state_t *afl, struct queue_entry *q) {

  u8 credited = 0;

  for (struct queue_entry *a = q->mother; a; a = a->mother) {

    if (a->indir_only) {

      if (!a->indir_edge_desc++) { ++afl->indir_only_productive; }
      credited = 1;

    }

  }

  afl->indir_edge_desc += credited;

}

/* Check if the result of an execve() during routine fuzzing is interesting,
   save or queue the input test case for further analysis if so. Returns 1 if
   entry is saved, 0 otherwise. */

u8 __attribute__((hot)) save_if_interesting(afl_state_t *afl, void *mem,
                                            u32 len, u8 fault) {

  if (unlikely(len == 0)) { return 0; }

  if (unlikely(fault == FSRV_RUN_TMOUT && afl->afl_env.afl_ignore_timeouts)) {

    if (unlikely(afl->schedule >= FAST && afl->schedule <= RARE)) {

      classify_counts(&afl->fsrv);
      u64 cksum = hash64(afl->fsrv.trace_bits, afl->fsrv.map_size, HASH_CONST);

      // Saturated increment
      u32 path = n_fuzz_path(afl, cksum);  // INDIR_CHANGE
      if (likely(afl->n_fuzz[path] < 0xFFFFFFFF)) afl->n_fuzz[path]++;

    }

    return 0;

  }

  u8  fn[PATH_MAX];
  u8 *queue_fn = "";
  u8  keeping = 0, res, is_timeout = 0;
  u8  san_fault = 0, san_idx = 0, feed_san = 0;
  s32 fd;
  u32 cksum_simplified = 0, cksum_unique = 0;

  bool classified = false, bits_counted = false, cksumed = false;
  u8   new_bits = 0;                       /* valid if bits_counted is true */
  u64  cksum = 0;                               /* valid if cksumed is true */
  // INDIR_CHANGE: indir bit count
  bool indir_bits_counted = false, indir_only = false;
  u8   indir_new_bits = 0;

  afl->san_case_status = 0;

  /* Update path frequency. */

  /* Generating a hash on every input is super expensive. Bad idea and should
     only be used for special schedules */
  if (unlikely(afl->schedule >= FAST && afl->schedule <= RARE)) {

    calculate_cksum_if_necessary(afl, &cksum, &cksumed, &classified);

    /* Saturated increment */
    u32 path = n_fuzz_path(afl, cksum);  // INDIR_CHANGE
    if (likely(afl->n_fuzz[path] < 0xFFFFFFFF)) afl->n_fuzz[path]++;

  }

  /* Only "normal" inputs seem interested to us */
  if (likely(fault == afl->crash_mode)) {

    if (unlikely(afl->san_binary_length) &&
        likely(afl->san_abstraction == SIMPLIFY_TRACE)) {

      memcpy(afl->san_fsrvs[0].trace_bits, afl->fsrv.trace_bits,
             afl->fsrv.map_size);
      simplify_trace(afl, afl->san_fsrvs[0].trace_bits);

      // Note: Original SAND implementation used XXHASH32
      cksum_simplified =
          hash32(afl->san_fsrvs[0].trace_bits, afl->fsrv.map_size, HASH_CONST);

      if (unlikely(!bitmap_read(afl->simplified_n_fuzz, cksum_simplified))) {

        feed_san = 1;
        bitmap_set(afl->simplified_n_fuzz, cksum_simplified);

      }

    }

    if (unlikely(afl->san_binary_length) &&
        unlikely(afl->san_abstraction == COVERAGE_INCREASE)) {

      /* Check if the input increase the coverage */
      calculate_new_bits_if_necessary(afl, &new_bits, &bits_counted,
                                      &classified);
      // INDIR_CHANGE: indirect novelty, see indir_novelty()
      if (afl->shm.indir_mode && !indir_bits_counted) {

        indir_bits_counted = true;
        calculate_cksum_if_necessary(afl, &cksum, &cksumed, &classified);
        indir_new_bits = indir_novelty(afl, new_bits, cksum);

      }

      if (unlikely(new_bits || indir_new_bits)) { feed_san = 1; }

    }

    if (unlikely(afl->san_binary_length) &&
        likely(afl->san_abstraction == UNIQUE_TRACE)) {

      // Note: SAND was evaluated under FAST schedule but should also work
      //       with other scedules.
      classify_if_necessary(afl, &classified);

      cksum_unique =
          hash32(afl->fsrv.trace_bits, afl->fsrv.map_size, HASH_CONST);
      if (unlikely(!bitmap_read(afl->n_fuzz_dup, cksum_unique) &&
                   fault == afl->crash_mode)) {

        feed_san = 1;
        bitmap_set(afl->n_fuzz_dup, cksum_unique);

      }

    }

    if (feed_san) {

      /* The input seems interested to other sanitizers, feed it into extra
       * binaries. */

      for (san_idx = 0; san_idx < afl->san_binary_length; san_idx++) {

        len = write_to_testcase(afl, &mem, len, 0);
        san_fault = fuzz_run_target(afl, &afl->san_fsrvs[san_idx],
                                    afl->san_fsrvs[san_idx].exec_tmout);

        // DEBUGF("ASAN Result: %hhd\n", asan_fault);

        if (unlikely(san_fault && fault == afl->crash_mode)) {

          /* sanitizers discovers distinct bugs! */
          afl->san_case_status |= SAN_CRASH_ONLY;

        }

        if (san_fault == FSRV_RUN_CRASH) {

          /* Treat this execution as fault detected by ASAN */
          // fault = san_fault;

          /* That's pretty enough, break to avoid more overhead. */
          break;

        } else {

          // or keep san_fault as ok
          san_fault = FSRV_RUN_OK;

        }

      }

    }

  }

  /* If there is no crash, everything is fine. */
  if (likely(fault == afl->crash_mode)) {

    /* Keep only if there are new bits in the map, add to queue for
       future fuzzing, etc. */
    calculate_new_bits_if_necessary(afl, &new_bits, &bits_counted, &classified);

    // INDIR_CHANGE: indirect-only novelty ranks like a hit-count change
    // (new_bits = 1), here and in calibrate_case(); see indir_novelty()
    if (afl->shm.indir_mode) {

      if (!indir_bits_counted) {

        indir_bits_counted = true;
        calculate_cksum_if_necessary(afl, &cksum, &cksumed, &classified);
        indir_new_bits = indir_novelty(afl, new_bits, cksum);

      }

      if (indir_new_bits && new_bits == 0) {

        new_bits = 1;
        indir_only = true;

      }

    }

    if (likely(!new_bits)) {

      if (san_fault == FSRV_RUN_OK) {

        if (unlikely(afl->crash_mode)) { ++afl->total_crashes; }
        return 0;

      } else {

        afl->san_case_status |= NON_COV_INCREASE_BUG;
        fault = san_fault;
        goto may_save_fault;

      }

    }

    fault = san_fault;

  save_to_queue:

    /* these calculations are necessary because some code flow may jump here via
       goto */
    calculate_cksum_if_necessary(afl, &cksum, &cksumed, &classified);
    calculate_new_bits_if_necessary(afl, &new_bits, &bits_counted, &classified);

    // INDIR_CHANGE: indirect-only novelty ranks like a hit-count change
    // (new_bits = 1), here and in calibrate_case(); see indir_novelty()
    if (afl->shm.indir_mode) {

      if (!indir_bits_counted) {

        indir_bits_counted = true;
        calculate_cksum_if_necessary(afl, &cksum, &cksumed, &classified);
        indir_new_bits = indir_novelty(afl, new_bits, cksum);

      }

      if (indir_new_bits && new_bits == 0) {

        new_bits = 1;
        indir_only = true;

      }

    }

#ifndef SIMPLE_FILES

    afl->indir_only_find = indir_only;  // INDIR_CHANGE: for describe_op()

    if (!afl->afl_env.afl_sha1_filenames) {

      queue_fn = alloc_printf(
          "%s/queue/id:%06u,%s%s%s", afl->out_dir, afl->queued_items,
          describe_op(afl, new_bits + is_timeout,
                      NAME_MAX - strlen("id:000000,")),
          afl->file_extension ? "." : "",
          afl->file_extension ? (const char *)afl->file_extension : "");

    } else {

      const char *hex = sha1_hex(mem, len);
      queue_fn = alloc_printf(
          "%s/queue/%s%s%s", afl->out_dir, hex, afl->file_extension ? "." : "",
          afl->file_extension ? (const char *)afl->file_extension : "");
      ck_free((char *)hex);

    }

#else

    queue_fn = alloc_printf(
        "%s/queue/id_%06u%s%s", afl->out_dir, afl->queued_items,
        afl->file_extension ? "." : "",
        afl->file_extension ? (const char *)afl->file_extension : "");

#endif                                                    /* ^!SIMPLE_FILES */
    fd = permissive_create(afl, queue_fn);
    if (likely(fd >= 0)) {

      ck_write(fd, mem, len, queue_fn);
      close(fd);

    }

    add_to_queue(afl, queue_fn, len, 0);

    if (unlikely(afl->fuzz_mode) &&
        likely(afl->switch_fuzz_mode && !afl->non_instrumented_mode)) {

      if (afl->afl_env.afl_no_ui) {

        ACTF("New coverage found, switching back to exploration mode.");

      }

      afl->fuzz_mode = 0;

    }

#ifdef INTROSPECTION
    if (afl->custom_mutators_count && afl->current_custom_fuzz) {

      LIST_FOREACH(&afl->custom_mutator_list, struct custom_mutator, {

        if (afl->current_custom_fuzz == el && el->afl_custom_introspection) {

          const char *ptr = el->afl_custom_introspection(el->data);

          if (ptr != NULL && *ptr != 0) {

            fprintf(afl->introspection_file, "QUEUE CUSTOM %s = %s\n", ptr,
                    afl->queue_top->fname);

          }

        }

      });

    } else if (afl->mutation[0] != 0) {

      fprintf(afl->introspection_file, "QUEUE %s = %s\n", afl->mutation,
              afl->queue_top->fname);

    }

#endif

    afl->queue_top->exec_cksum = cksum;

    // INDIR_CHANGE: the indirect checksum must be known before calibration,
    // or every calibration run looks unstable
    if (afl->shm.indir_mode) {

      afl->queue_top->indir_cksum = hash_indir_trace(afl);
      afl->queue_top->indir_only = indir_only;

      if (indir_only) {

        ++afl->queued_indir_only;

      } else if (new_bits == 2) {

        indir_credit_ancestors(afl, afl->queue_top);

      }

    }

    afl->indir_only_find = false;

    if (new_bits == 2) {

      afl->queue_top->has_new_cov = 1;
      ++afl->queued_with_cov;

    }

    /* For AFLFast schedules we update the new queue entry */
    if (unlikely(afl->schedule >= FAST && afl->schedule <= RARE)) {

      // INDIR_CHANGE: the path id includes the indirect trace, so that an
      // indirect-only find does not share (and reset) the counter of the
      // entry whose edge path it has
      afl->queue_top->n_fuzz_entry =
          indir_path_id(afl, cksum, afl->queue_top->indir_cksum);
      if (!afl->n_fuzz[afl->queue_top->n_fuzz_entry] || !afl->shm.indir_mode) {

        afl->n_fuzz[afl->queue_top->n_fuzz_entry] = 1;

      }

    }

    /* Try to calibrate inline; this also calls update_bitmap_score() when
       successful. */
    res = calibrate_case(afl, afl->queue_top, mem, afl->queue_cycle - 1, 0);

    if (unlikely(res == FSRV_RUN_ERROR)) {

      FATAL("Unable to execute target application");

    }

    if (likely(afl->q_testcase_max_cache_size)) {

      queue_testcase_store_mem(afl, afl->queue_top, mem);

    }

    keeping = 1;

  }

may_save_fault:
  switch (fault) {

    case FSRV_RUN_TMOUT:

      /* Timeouts are not very interesting, but we're still obliged to keep
         a handful of samples. We use the presence of new bits in the
         hang-specific bitmap as a signal of uniqueness. In "non-instrumented"
         mode, we just keep everything. */

      ++afl->total_tmouts;

      if (afl->saved_hangs >= KEEP_UNIQUE_HANG) { return keeping; }

      if (likely(!afl->non_instrumented_mode)) {

        simplify_trace(afl, afl->fsrv.trace_bits);
        // INDIR_CHANGE: decouple unique timeout deduplication from indirect
        // novelty
        u8 has_new = has_new_bits(afl, afl->virgin_tmout);
        if (!has_new) { return keeping; }

      }

      is_timeout = 0x80;
#ifdef INTROSPECTION
      if (afl->custom_mutators_count && afl->current_custom_fuzz) {

        LIST_FOREACH(&afl->custom_mutator_list, struct custom_mutator, {

          if (afl->current_custom_fuzz == el && el->afl_custom_introspection) {

            const char *ptr = el->afl_custom_introspection(el->data);

            if (ptr != NULL && *ptr != 0) {

              fprintf(afl->introspection_file,
                      "UNIQUE_TIMEOUT CUSTOM %s = %s\n", ptr,
                      afl->queue_top->fname);

            }

          }

        });

      } else if (afl->mutation[0] != 0) {

        fprintf(afl->introspection_file, "UNIQUE_TIMEOUT %s\n", afl->mutation);

      }

#endif

      /* Before saving, we make sure that it's a genuine hang by re-running
         the target with a more generous timeout (unless the default timeout
         is already generous). */

      if (afl->fsrv.exec_tmout < afl->hang_tmout) {

        u8  new_fault;
        u32 tmp_len = write_to_testcase(afl, &mem, len, 0);

        if (likely(tmp_len)) {

          len = tmp_len;

        } else {

          len = write_to_testcase(afl, &mem, len, 1);

        }

        new_fault = fuzz_run_target(afl, &afl->fsrv, afl->hang_tmout);
        classified = false;
        bits_counted = false;
        cksumed = false;

        /* A corner case that one user reported bumping into: increasing the
           timeout actually uncovers a crash. Make sure we don't discard it if
           so. */

        if (!afl->stop_soon && new_fault == FSRV_RUN_CRASH) {

          goto keep_as_crash;

        }

        if (afl->stop_soon || new_fault != FSRV_RUN_TMOUT) {

          if (afl->afl_env.afl_keep_timeouts) {

            ++afl->saved_tmouts;
            goto save_to_queue;

          } else {

            return keeping;

          }

        }

      }

#ifndef SIMPLE_FILES

      if (!afl->afl_env.afl_sha1_filenames) {

        snprintf(fn, PATH_MAX, "%s/hangs/id:%06llu,%s%s%s", afl->out_dir,
                 afl->saved_hangs,
                 describe_op(afl, 0, NAME_MAX - strlen("id:000000,")),
                 afl->file_extension ? "." : "",
                 afl->file_extension ? (const char *)afl->file_extension : "");

      } else {

        const char *hex = sha1_hex(mem, len);
        snprintf(fn, PATH_MAX, "%s/hangs/%s%s%s", afl->out_dir, hex,
                 afl->file_extension ? "." : "",
                 afl->file_extension ? (const char *)afl->file_extension : "");
        ck_free((char *)hex);

      }

#else

      snprintf(fn, PATH_MAX, "%s/hangs/id_%06llu%s%s", afl->out_dir,
               afl->saved_hangs, afl->file_extension ? "." : "",
               afl->file_extension ? (const char *)afl->file_extension : "");

#endif                                                    /* ^!SIMPLE_FILES */

      ++afl->saved_hangs;

      afl->last_hang_time = get_cur_time();

      break;

    case FSRV_RUN_CRASH:

    keep_as_crash:

      /* This is handled in a manner roughly similar to timeouts,
         except for slightly different limits and no need to re-run test
         cases. */

      ++afl->total_crashes;

      if (afl->saved_crashes >= KEEP_UNIQUE_CRASH) { return keeping; }

      if (likely(!afl->non_instrumented_mode)) {

        simplify_trace(afl, afl->fsrv.trace_bits);
        // INDIR_CHANGE: decouple unique crash deduplication from indirect
        // novelty
        u8 has_new = has_new_bits(afl, afl->virgin_crash);
        if (!has_new) { return keeping; }

      }

      if (unlikely(!afl->saved_crashes) &&
          (afl->afl_env.afl_no_crash_readme != 1)) {

        write_crash_readme(afl);

      }

#ifndef SIMPLE_FILES

      if (!afl->afl_env.afl_sha1_filenames) {

        snprintf(fn, PATH_MAX, "%s/crashes/id:%06llu,sig:%02u,%s%s%s",
                 afl->out_dir, afl->saved_crashes, afl->fsrv.last_kill_signal,
                 describe_op(afl, 0, NAME_MAX - strlen("id:000000,sig:00,")),
                 afl->file_extension ? "." : "",
                 afl->file_extension ? (const char *)afl->file_extension : "");

      } else {

        const char *hex = sha1_hex(mem, len);
        snprintf(fn, PATH_MAX, "%s/crashes/%s%s%s", afl->out_dir, hex,
                 afl->file_extension ? "." : "",
                 afl->file_extension ? (const char *)afl->file_extension : "");
        ck_free((char *)hex);

      }

#else

      snprintf(fn, PATH_MAX, "%s/crashes/id_%06llu_%02u%s%s", afl->out_dir,
               afl->saved_crashes, afl->fsrv.last_kill_signal,
               afl->file_extension ? "." : "",
               afl->file_extension ? (const char *)afl->file_extension : "");

#endif                                                    /* ^!SIMPLE_FILES */

      ++afl->saved_crashes;
#ifdef INTROSPECTION
      if (afl->custom_mutators_count && afl->current_custom_fuzz) {

        LIST_FOREACH(&afl->custom_mutator_list, struct custom_mutator, {

          if (afl->current_custom_fuzz == el && el->afl_custom_introspection) {

            const char *ptr = el->afl_custom_introspection(el->data);

            if (ptr != NULL && *ptr != 0) {

              fprintf(afl->introspection_file, "UNIQUE_CRASH CUSTOM %s = %s\n",
                      ptr, afl->queue_top->fname);

            }

          }

        });

      } else if (afl->mutation[0] != 0) {

        fprintf(afl->introspection_file, "UNIQUE_CRASH %s\n", afl->mutation);

      }

#endif
      if (unlikely(afl->infoexec)) {

        // if the user wants to be informed on new crashes - do that
#if !TARGET_OS_IPHONE
        // we dont care if system errors, but we dont want a
        // compiler warning either
        // See
        // https://stackoverflow.com/questions/11888594/ignoring-return-values-in-c
        (void)(system(afl->infoexec) + 1);
#else
        WARNF("command execution unsupported");
#endif

      }

      afl->last_crash_time = get_cur_time();
      afl->last_crash_execs = afl->fsrv.total_execs;

      break;

    case FSRV_RUN_ERROR:
      FATAL("Unable to execute target application");

    default:
      return keeping;

  }

  /* If we're here, we apparently want to save the crash or hang
     test case, too. */

  fd = permissive_create(afl, fn);
  if (fd >= 0) {

    ck_write(fd, mem, len, fn);
    close(fd);

  }

#ifdef __linux__
  if (afl->fsrv.nyx_mode && fault == FSRV_RUN_CRASH) {

    u8 fn_log[PATH_MAX];

    (void)(snprintf(fn_log, PATH_MAX, "%s.log", fn) + 1);
    fd = open(fn_log, O_WRONLY | O_CREAT | O_EXCL, afl->perm);
    if (unlikely(fd < 0)) { PFATAL("Unable to create '%s'", fn_log); }

    if (afl->chown_needed) {

      if (fchown(fd, -1, afl->fsrv.gid) == -1) { PFATAL("fchown() failed"); }

    }

    u32 nyx_aux_string_len = afl->fsrv.nyx_handlers->nyx_get_aux_string(
        afl->fsrv.nyx_runner, afl->fsrv.nyx_aux_string,
        afl->fsrv.nyx_aux_string_len);

    ck_write(fd, afl->fsrv.nyx_aux_string, nyx_aux_string_len, fn_log);
    close(fd);

  }

#endif

  return keeping;

}

