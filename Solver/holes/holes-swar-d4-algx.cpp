// Solver for the Holes N-Queens problem (N <= 12):
// Unified 64-bit SWAR Bidirectional Bitmask Algorithm X + 8-Way D4-Orbit Search.
// Features 3-word (2-word for N <= 8) 64-bit SWAR row-domain packing, 1-multiply branchless
// column-row gather, portable hardware i32.ctz/i64.ctz (<bit> on C++20), folded rem==1 and
// early rem==2 geometric exit, zero-switch single-loop D4 orbit materialization, pre-table
// root unit propagation with reduced-board Hall check, and active-cell attack table build
// inside a ~35 KB stack frame (safe under Emscripten's default 64 KB stack, 0 B aux heap).
#if __cplusplus >= 202002L
#include <bit>
#endif
#include <cstdint>
#include <string>
#include <vector>

#include "nqueens.h"

namespace {

constexpr int kMaxN = 12;
constexpr uint64_t kOnes = 0x0001000100010001ULL;
constexpr uint64_t k7FFF = 0x7FFF7FFF7FFF7FFFULL;
constexpr uint64_t kHigh = 0x8000800080008000ULL;
constexpr uint64_t kData = 0x0FFF0FFF0FFF0FFFULL;
constexpr uint64_t kSentWord = 0x7000700070007000ULL;
constexpr uint64_t kColPack = 0x0001000200040008ULL;

inline int popcnt32(uint32_t x) {
#if __cplusplus >= 202002L
  return std::popcount(x);
#else
  int c = 0;
  while (x) {
    x &= x - 1u;
    ++c;
  }
  return c;
#endif
}

inline int popcnt64(uint64_t x) {
#if __cplusplus >= 202002L
  return std::popcount(x);
#else
  int c = 0;
  while (x) {
    x &= x - 1ULL;
    ++c;
  }
  return c;
#endif
}

inline int ctzBit32(uint32_t b) {
#if __cplusplus >= 202002L
  return std::countr_zero(b);
#else
  return popcnt32((b & (~b + 1u)) - 1u);
#endif
}

inline int ctz64(uint64_t x) {
#if __cplusplus >= 202002L
  return std::countr_zero(x);
#else
  return popcnt64((x & (~x + 1ULL)) - 1ULL);
#endif
}

inline void applyD4(int k, const uint8_t* src, uint8_t* dst, int n) {
  const int m = n - 1;
  if (k < 4) {
    for (int r = 0; r < n; ++r) {
      dst[(k & 2) ? (m - r) : r] = static_cast<uint8_t>((k & 1) ? (m - src[r]) : src[r]);
    }
  } else {
    for (int r = 0; r < n; ++r) {
      dst[(k & 2) ? (m - src[r]) : src[r]] = static_cast<uint8_t>((k & 1) ? (m - r) : r);
    }
  }
}

inline int cmpBoard(const uint8_t* a, const uint8_t* b, int n) {
  for (int r = 0; r < n; ++r) {
    if (a[r] != b[r]) return a[r] < b[r] ? -1 : 1;
  }
  return 0;
}

inline void emitPacked(uint64_t packed, int n, bool debug, std::vector<std::vector<int>>& solutions) {
  int buf[kMaxN];
  for (int r = 0; r < n; ++r) buf[r] = static_cast<int>((packed >> (r << 2)) & 0xFu);
  solutions.emplace_back(buf, buf + n);
  if (debug) {
    snapshot(nq::queensOf(solutions.back()), "solution " + std::to_string(solutions.size()));
  }
}

inline void emitD4Orbit(uint64_t packed, uint8_t mask, int n, bool debug,
                        std::vector<std::vector<int>>& solutions) {
  const int m = n - 1;
  if (mask == 0xFFu) {
    int b0[kMaxN], b1[kMaxN], b2[kMaxN], b3[kMaxN];
    int b4[kMaxN], b5[kMaxN], b6[kMaxN], b7[kMaxN];
    for (int r = 0; r < n; ++r) {
      const int c = static_cast<int>((packed >> (r << 2)) & 0xFu);
      const int mc = m - c;
      const int mr = m - r;
      b0[r] = c;
      b1[r] = mc;
      b2[mr] = c;
      b3[mr] = mc;
      b4[c] = r;
      b5[c] = mr;
      b6[mc] = r;
      b7[mc] = mr;
    }
    if (!debug) {
      solutions.emplace_back(b0, b0 + n);
      solutions.emplace_back(b1, b1 + n);
      solutions.emplace_back(b2, b2 + n);
      solutions.emplace_back(b3, b3 + n);
      solutions.emplace_back(b4, b4 + n);
      solutions.emplace_back(b5, b5 + n);
      solutions.emplace_back(b6, b6 + n);
      solutions.emplace_back(b7, b7 + n);
    } else {
      const int* bufs[8] = {b0, b1, b2, b3, b4, b5, b6, b7};
      for (int k = 0; k < 8; ++k) {
        solutions.emplace_back(bufs[k], bufs[k] + n);
        snapshot(nq::queensOf(solutions.back()), "solution " + std::to_string(solutions.size()));
      }
    }
    return;
  }

  if ((mask & (mask - 1u)) == 0) {
    int buf[kMaxN];
    const int k = ctzBit32(mask);
    if (k < 4) {
      for (int r = 0; r < n; ++r) {
        const int c = static_cast<int>((packed >> (r << 2)) & 0xFu);
        buf[(k & 2) ? (m - r) : r] = (k & 1) ? (m - c) : c;
      }
    } else {
      for (int r = 0; r < n; ++r) {
        const int c = static_cast<int>((packed >> (r << 2)) & 0xFu);
        buf[(k & 2) ? (m - c) : c] = (k & 1) ? (m - r) : r;
      }
    }
    solutions.emplace_back(buf, buf + n);
    if (debug) {
      snapshot(nq::queensOf(solutions.back()), "solution " + std::to_string(solutions.size()));
    }
    return;
  }

  int b0[kMaxN], b1[kMaxN], b2[kMaxN], b3[kMaxN];
  int b4[kMaxN], b5[kMaxN], b6[kMaxN], b7[kMaxN];
  for (int r = 0; r < n; ++r) {
    const int c = static_cast<int>((packed >> (r << 2)) & 0xFu);
    const int mc = m - c;
    const int mr = m - r;
    b0[r] = c;
    b1[r] = mc;
    b2[mr] = c;
    b3[mr] = mc;
    b4[c] = r;
    b5[c] = mr;
    b6[mc] = r;
    b7[mc] = mr;
  }
  const int* bufs[8] = {b0, b1, b2, b3, b4, b5, b6, b7};
  uint32_t km = mask;
  while (km) {
    const uint32_t kb = km & (~km + 1u);
    km ^= kb;
    const int k = ctzBit32(kb);
    solutions.emplace_back(bufs[k], bufs[k] + n);
    if (debug) {
      snapshot(nq::queensOf(solutions.back()), "solution " + std::to_string(solutions.size()));
    }
  }
}

bool hasPerfectMatchingRem(int n, uint32_t freeRows, const uint32_t* rowAllowed) {
  int colOwner[kMaxN];
  for (int c = 0; c < n; ++c) colOwner[c] = -1;

  auto augment = [&](auto& self, int r, uint32_t& visited) -> bool {
    uint32_t cand = rowAllowed[r] & ~visited;
    while (cand) {
      const uint32_t b = cand & (~cand + 1u);
      cand ^= b;
      const int c = ctzBit32(b);
      visited |= b;
      if (colOwner[c] < 0 || self(self, colOwner[c], visited)) {
        colOwner[c] = r;
        return true;
      }
    }
    return false;
  };

  uint32_t fr = freeRows;
  while (fr) {
    const uint32_t rb = fr & (~fr + 1u);
    fr ^= rb;
    const int r = ctzBit32(rb);
    uint32_t visited = 0;
    if (!augment(augment, r, visited)) return false;
  }
  return true;
}

bool rootUnitProp(int n, uint32_t full, uint32_t* rowAllowed, int& rem,
                  uint32_t& rowMask, uint32_t& colMask, uint64_t& packed) {
  auto placeRoot = [&](int r, int c) -> bool {
    const uint32_t rb = 1u << r;
    const uint32_t cb = 1u << c;
    rowMask |= rb;
    colMask |= cb;
    --rem;
    packed |= static_cast<uint64_t>(c) << (r << 2);
    rowAllowed[r] = 0;
    uint32_t fr = full ^ rowMask;
    while (fr) {
      const uint32_t r2b = fr & (~fr + 1u);
      fr ^= r2b;
      const int r2 = ctzBit32(r2b);
      uint32_t kill = cb;
      const int dr = r2 > r ? (r2 - r) : (r - r2);
      if (c >= dr) kill |= 1u << (c - dr);
      if (c + dr < n) kill |= 1u << (c + dr);
      rowAllowed[r2] &= ~kill;
      if (rowAllowed[r2] == 0) return false;
    }
    return true;
  };

  while (rem > 0) {
    uint32_t once = 0;
    uint32_t twice = 0;
    int forcedR = -1;
    uint32_t forcedCb = 0;
    uint32_t fr = full ^ rowMask;
    while (fr) {
      const uint32_t rb = fr & (~fr + 1u);
      fr ^= rb;
      const int r = ctzBit32(rb);
      const uint32_t av = rowAllowed[r];
      if (av == 0) return false;
      if ((av & (av - 1u)) == 0) {
        forcedR = r;
        forcedCb = av;
        break;
      }
      twice |= once & av;
      once |= av;
    }
    if (forcedR >= 0) {
      if (!placeRoot(forcedR, ctzBit32(forcedCb))) return false;
      continue;
    }
    if ((once | colMask) != full) return false;
    const uint32_t uniqueCols = once & ~twice;
    if (!uniqueCols) break;
    const uint32_t cb = uniqueCols & (~uniqueCols + 1u);
    const int c = ctzBit32(cb);
    int r = -1;
    uint32_t fr2 = full ^ rowMask;
    while (fr2) {
      const uint32_t rb = fr2 & (~fr2 + 1u);
      fr2 ^= rb;
      const int cand = ctzBit32(rb);
      if (rowAllowed[cand] & cb) {
        r = cand;
        break;
      }
    }
    if (r < 0 || !placeRoot(r, c)) return false;
  }
  return true;
}

struct CellAtk {
  uint64_t m0, m1, m2;
};

enum LeafMode {
  kGeneralBuf = 0,
  kGeneralEmit = 1,
  kD4CornerClean = 2,
  kD4CornerHoles = 3,
  kD4IntClean = 4,
  kD4IntHoles = 5,
};

struct SwarD4AlgX {
  int n = 0;
  int m = 0;
  int keyCol = 0;
  uint32_t full = 0;
  uint32_t centralCols = 0;
  uint8_t centerDist[kMaxN]{};
  uint8_t killMask[kMaxN][kMaxN]{};
  uint64_t rowSent[kMaxN][3]{};
  CellAtk atk[kMaxN][kMaxN];

  static constexpr size_t kStackCap = 3584;  // 28 KB on stack (~35 KB total frame)
  uint64_t stackBuf[kStackCap];
  size_t orbitCount = 0;
  size_t totalSolutions = 0;
  std::vector<std::vector<int>>* out = nullptr;
  bool debug = false;

  void buildTables(const uint32_t* activeRows) {
    centralCols = 0;
    for (int i = 0; i < n; ++i) {
      const int d = 2 * i - m;
      const int ad = d < 0 ? -d : d;
      centerDist[i] = static_cast<uint8_t>(ad);
      if (ad <= 3) centralCols |= (1u << i);
      rowSent[i][0] = (i < 4) ? (0x7000ULL << ((i & 3) << 4)) : 0ULL;
      rowSent[i][1] = (i >= 4 && i < 8) ? (0x7000ULL << ((i & 3) << 4)) : 0ULL;
      rowSent[i][2] = (i >= 8) ? (0x7000ULL << ((i & 3) << 4)) : 0ULL;
    }
    for (int r = 0; r < n; ++r) {
      uint32_t cols = activeRows ? activeRows[r] : full;
      const int rWord = r >> 2;
      const uint64_t rClear = ~(0xFFFFULL << ((r & 3) << 4));
      while (cols) {
        const uint32_t cb = cols & (~cols + 1u);
        cols ^= cb;
        const int c = ctzBit32(cb);
        const uint64_t colKeep = ~(static_cast<uint64_t>(cb) * kOnes);
        uint64_t w[3] = {colKeep, colKeep, colKeep};
        w[rWord] &= rClear;
        for (int r2 = r - 1, cl = c - 1, cr = c + 1; r2 >= 0; --r2, --cl, ++cr) {
          const uint32_t diag = (cl >= 0 ? (1u << cl) : 0u) | (cr < n ? (1u << cr) : 0u);
          if (!diag) break;
          w[r2 >> 2] &= ~(static_cast<uint64_t>(diag) << ((r2 & 3) << 4));
        }
        for (int r2 = r + 1, cl = c - 1, cr = c + 1; r2 < n; ++r2, --cl, ++cr) {
          const uint32_t diag = (cl >= 0 ? (1u << cl) : 0u) | (cr < n ? (1u << cr) : 0u);
          if (!diag) break;
          w[r2 >> 2] &= ~(static_cast<uint64_t>(diag) << ((r2 & 3) << 4));
        }
        atk[r][c] = {w[0], w[1], w[2]};
      }
    }
  }

  template <bool TwoWords>
  inline void place(int r, int c, uint64_t& d0, uint64_t& d1, uint64_t& d2) const {
    const CellAtk& a = atk[r][c];
    d0 = (d0 & a.m0) | rowSent[r][0];
    d1 = (d1 & a.m1) | rowSent[r][1];
    if constexpr (!TwoWords) d2 = (d2 & a.m2) | rowSent[r][2];
  }

  template <bool TwoWords>
  inline uint32_t getLane(int r, uint64_t d0, uint64_t d1, uint64_t d2) const {
    const uint64_t w = (r < 4) ? d0 : (TwoWords || r < 8 ? d1 : d2);
    return static_cast<uint32_t>((w >> ((r & 3) << 4)) & 0xFFFu);
  }

  template <bool TwoWords>
  inline uint32_t colRowsMask(int c, uint64_t d0, uint64_t d1, uint64_t d2) const {
    uint64_t v = ((d0 >> c) & kOnes) | (((d1 >> c) & kOnes) << 4);
    if constexpr (!TwoWords) v |= (((d2 >> c) & kOnes) << 8);
    return static_cast<uint32_t>((v * kColPack) >> 48);
  }

  inline void addOrbit(uint64_t packed, uint32_t emitMask) {
    if (!emitMask) return;
    stackBuf[orbitCount++] = packed | (static_cast<uint64_t>(emitMask) << 48);
    totalSolutions += static_cast<size_t>(popcnt32(emitMask));
  }

  template <int Mode>
  inline void onLeaf(uint64_t packed) {
    if constexpr (Mode == kGeneralBuf) {
      if (totalSolutions < kStackCap) stackBuf[totalSolutions] = packed;
      ++totalSolutions;
      return;
    }
    if constexpr (Mode == kGeneralEmit) {
      emitPacked(packed, n, debug, *out);
      return;
    }

    constexpr bool kHasHoles = (Mode == kD4CornerHoles || Mode == kD4IntHoles);
    constexpr bool kCorner = (Mode == kD4CornerClean || Mode == kD4CornerHoles);

    uint32_t alive = 0xFFu;
    if constexpr (kHasHoles) {
      for (int r = 0; r < n; ++r) {
        const int c = static_cast<int>((packed >> (r << 2)) & 0xFu);
        alive &= ~static_cast<uint32_t>(killMask[r][c]);
        if (!alive) return;
      }
    }

    if constexpr (kCorner) {
      if (static_cast<int>((packed >> (keyCol << 2)) & 0xFu) != 1) {
        addOrbit(packed, alive);
        return;
      }
      uint8_t cols[kMaxN];
      uint8_t inv[kMaxN];
      for (int r = 0; r < n; ++r) {
        const uint8_t c = static_cast<uint8_t>((packed >> (r << 2)) & 0xFu);
        cols[r] = c;
        inv[c] = static_cast<uint8_t>(r);
      }
      const int cmp = cmpBoard(cols, inv, n);
      if (cmp > 0) return;
      addOrbit(packed, cmp == 0 ? (alive & 0x69u) : alive);
    } else {
      const int c0 = keyCol;
      const int colM = static_cast<int>((packed >> (m << 2)) & 0xFu);
      const int colC0 = static_cast<int>((packed >> (c0 << 2)) & 0xFu);
      const int colMC0 = static_cast<int>((packed >> ((m - c0) << 2)) & 0xFu);
      const bool tied = (colM == c0 || colM == m - c0 ||
                         colC0 == 0 || colC0 == m ||
                         colMC0 == 0 || colMC0 == m);
      if (!tied) {
        addOrbit(packed, alive);
        return;
      }
      uint8_t imgs[8][kMaxN];
      for (int r = 0; r < n; ++r) imgs[0][r] = static_cast<uint8_t>((packed >> (r << 2)) & 0xFu);
      for (int k = 1; k < 8; ++k) {
        applyD4(k, imgs[0], imgs[k], n);
        if (cmpBoard(imgs[k], imgs[0], n) < 0) return;
      }
      uint32_t canonMask = 1u;
      for (int k = 1; k < 8; ++k) {
        bool dup = false;
        for (int j = 0; j < k; ++j) {
          if (((canonMask >> j) & 1u) && cmpBoard(imgs[k], imgs[j], n) == 0) {
            dup = true;
            break;
          }
        }
        if (!dup) canonMask |= (1u << k);
      }
      addOrbit(packed, alive & canonMask);
    }
  }

  template <int Mode, bool TwoWords>
  void dfs(int rem, uint32_t rowMask, uint32_t colMask, uint64_t d0, uint64_t d1, uint64_t d2,
           uint64_t packed) {
    // Invariant: dfs is always entered with rem >= 2.
    for (;;) {
      // 1. Zero-loop SWAR dead-row check.
      if constexpr (TwoWords) {
        if ((~(d0 + k7FFF) | ~(d1 + k7FFF)) & kHigh) return;
      } else {
        if ((~(d0 + k7FFF) | ~(d1 + k7FFF) | ~(d2 + k7FFF)) & kHigh) return;
      }

      // 2. Zero-loop SWAR forced-row check.
      const uint64_t y0 = d0 & (d0 - kOnes);
      const uint64_t y1 = d1 & (d1 - kOnes);
      const uint64_t y2 = TwoWords ? 0ULL : (d2 & (d2 - kOnes));
      const uint64_t o0 = ~(y0 + k7FFF) & kHigh;
      const uint64_t o1 = ~(y1 + k7FFF) & kHigh;
      const uint64_t o2 = TwoWords ? 0ULL : (~(y2 + k7FFF) & kHigh);
      if (o0 | o1 | o2) {
        int r;
        uint32_t cb;
        if (o1) {
          const int l = ctz64(o1) >> 4;
          r = 4 + l;
          cb = static_cast<uint32_t>((d1 >> (l << 4)) & 0xFFFu);
        } else if (o0) {
          const int l = ctz64(o0) >> 4;
          r = l;
          cb = static_cast<uint32_t>((d0 >> (l << 4)) & 0xFFFu);
        } else {
          const int l = ctz64(o2) >> 4;
          r = 8 + l;
          cb = static_cast<uint32_t>((d2 >> (l << 4)) & 0xFFFu);
        }
        const int c = ctzBit32(cb);
        --rem;
        rowMask |= (1u << r);
        colMask |= cb;
        place<TwoWords>(r, c, d0, d1, d2);
        packed |= static_cast<uint64_t>(c) << (r << 2);
        if (rem == 1) {
          if constexpr (TwoWords) {
            if ((~(d0 + k7FFF) | ~(d1 + k7FFF)) & kHigh) return;
          } else {
            if ((~(d0 + k7FFF) | ~(d1 + k7FFF) | ~(d2 + k7FFF)) & kHigh) return;
          }
          const int r0 = ctzBit32(full ^ rowMask);
          const int c0 = ctzBit32(full ^ colMask);
          onLeaf<Mode>(packed | (static_cast<uint64_t>(c0) << (r0 << 2)));
          return;
        }
        continue;
      }

      // Early rem == 2 exit: both rows passed dead & forced checks, so both have exact freeCols {c0, c1}.
      if (rem == 2) {
        const uint32_t fr = full ^ rowMask;
        const uint32_t rb0 = fr & (~fr + 1u);
        const int r0 = ctzBit32(rb0), r1 = ctzBit32(fr ^ rb0);
        const uint32_t fc = full ^ colMask;
        const uint32_t cb0 = fc & (~fc + 1u);
        const int c0 = ctzBit32(cb0), c1 = ctzBit32(fc ^ cb0);
        if (r1 - r0 != c1 - c0) {
          onLeaf<Mode>(packed | (static_cast<uint64_t>(c0) << (r0 << 2)) |
                       (static_cast<uint64_t>(c1) << (r1 << 2)));
          onLeaf<Mode>(packed | (static_cast<uint64_t>(c1) << (r0 << 2)) |
                       (static_cast<uint64_t>(c0) << (r1 << 2)));
        }
        return;
      }

      // 3. Zero-loop SWAR column cardinality (once, twice, thrice).
      const uint64_t m0 = d0 & kData;
      const uint64_t m1 = d1 & kData;
      uint64_t once4, twice4, thrice4;
      if constexpr (TwoWords) {
        once4 = m0 | m1;
        twice4 = m0 & m1;
        thrice4 = 0ULL;
      } else {
        const uint64_t m2 = d2 & kData;
        const uint64_t o01 = m0 | m1;
        const uint64_t t01 = m0 & m1;
        once4 = o01 | m2;
        twice4 = t01 | (o01 & m2);
        thrice4 = t01 & m2;
      }

      const uint32_t oA = static_cast<uint32_t>(once4), oB = static_cast<uint32_t>(once4 >> 32);
      const uint32_t tA = static_cast<uint32_t>(twice4), tB = static_cast<uint32_t>(twice4 >> 32);
      const uint32_t once2 = oA | oB;
      const uint32_t twice2 = tA | tB | (oA & oB);
      const uint32_t onceLo = once2 & 0xFFFu, onceHi = once2 >> 16;
      const uint32_t once = onceLo | onceHi;
      if ((once | colMask) != full) return;

      const uint32_t twiceLo = twice2 & 0xFFFu, twiceHi = twice2 >> 16;
      const uint32_t twice = twiceLo | twiceHi | (onceLo & onceHi);
      const uint32_t uniqueCols = once & ~twice;
      if (uniqueCols) {
        const uint32_t cb = uniqueCols & (~uniqueCols + 1u);
        const int c = ctzBit32(cb);
        const uint64_t cm = static_cast<uint64_t>(cb) * kOnes;
        int r;
        if (const uint64_t w = d1 & cm) r = 4 + (ctz64(w) >> 4);
        else if constexpr (TwoWords) r = ctz64(d0 & cm) >> 4;
        else if (const uint64_t w = d0 & cm) r = ctz64(w) >> 4;
        else r = 8 + (ctz64(d2 & cm) >> 4);
        --rem;
        rowMask |= (1u << r);
        colMask |= cb;
        place<TwoWords>(r, c, d0, d1, d2);
        packed |= static_cast<uint64_t>(c) << (r << 2);
        continue;
      }

      // 4. SWAR count-2 rows + central count-2 columns Organ-Pipe priority.
      const uint64_t z0 = y0 & (y0 - kOnes);
      const uint64_t z1 = y1 & (y1 - kOnes);
      const uint64_t z2 = TwoWords ? 0ULL : (y2 & (y2 - kOnes));
      const uint64_t tw0 = ~(z0 + k7FFF) & kHigh;
      const uint64_t tw1 = ~(z1 + k7FFF) & kHigh;
      const uint64_t tw2 = TwoWords ? 0ULL : (~(z2 + k7FFF) & kHigh);

      if (!TwoWords && tw1) {
        int r;
        if (tw1 & 0x0000800000000000ULL) r = 6;
        else if (tw1 & 0x0000000080000000ULL) r = 5;
        else if (tw1 & 0x8000000000000000ULL) r = 7;
        else r = 4;
        const uint32_t av = static_cast<uint32_t>((d1 >> ((r & 3) << 4)) & 0xFFFu);
        const uint32_t cb0 = av & (~av + 1u);
        const uint32_t cb1 = av ^ cb0;
        const int c0 = ctzBit32(cb0), c1 = ctzBit32(cb1);
        const uint32_t nRowMask = rowMask | (1u << r);
        uint64_t nd0 = d0, nd1 = d1, nd2 = d2;
        place<TwoWords>(r, c0, nd0, nd1, nd2);
        dfs<Mode, TwoWords>(rem - 1, nRowMask, colMask | cb0, nd0, nd1, nd2,
                            packed | (static_cast<uint64_t>(c0) << (r << 2)));
        --rem;
        rowMask = nRowMask;
        colMask |= cb1;
        place<TwoWords>(r, c1, d0, d1, d2);
        packed |= (static_cast<uint64_t>(c1) << (r << 2));
        continue;
      }

      const uint32_t hA = static_cast<uint32_t>(thrice4), hB = static_cast<uint32_t>(thrice4 >> 32);
      const uint32_t thrice2 = (TwoWords ? 0u : (hA | hB)) | (tA & oB) | (oA & tB);
      const uint32_t thrice = (thrice2 & 0xFFFu) | (thrice2 >> 16) |
                              (twiceLo & onceHi) | (onceLo & twiceHi);
      const uint32_t c2 = twice & ~thrice;

      const uint32_t c2Cent = c2 & centralCols;
      if (c2Cent) {
        int bestC = -1, bestD = 99;
        uint32_t cm = c2Cent;
        while (cm) {
          const uint32_t cb = cm & (~cm + 1u);
          cm ^= cb;
          const int c = ctzBit32(cb);
          if (centerDist[c] < bestD) { bestD = centerDist[c]; bestC = c; }
        }
        const uint32_t cb = 1u << bestC;
        const uint32_t rmask = colRowsMask<TwoWords>(bestC, d0, d1, d2);
        const uint32_t rb0 = rmask & (~rmask + 1u);
        const uint32_t rb1 = rmask ^ rb0;
        const int r0 = ctzBit32(rb0), r1 = ctzBit32(rb1);
        const uint32_t nColMask = colMask | cb;
        uint64_t nd0 = d0, nd1 = d1, nd2 = d2;
        place<TwoWords>(r0, bestC, nd0, nd1, nd2);
        dfs<Mode, TwoWords>(rem - 1, rowMask | rb0, nColMask, nd0, nd1, nd2,
                            packed | (static_cast<uint64_t>(bestC) << (r0 << 2)));
        --rem;
        rowMask |= rb1;
        colMask = nColMask;
        place<TwoWords>(r1, bestC, d0, d1, d2);
        packed |= (static_cast<uint64_t>(bestC) << (r1 << 2));
        continue;
      }

      if (tw0 | tw1 | tw2) {
        int r;
        uint32_t av;
        if (TwoWords && tw1) {
          if (tw1 & 0x0000000000008000ULL) r = 4;
          else if (tw1 & 0x0000000080000000ULL) r = 5;
          else if (tw1 & 0x0000800000000000ULL) r = 6;
          else r = 7;
          av = static_cast<uint32_t>((d1 >> ((r & 3) << 4)) & 0xFFFu);
        } else if (tw0) {
          if (tw0 & 0x8000000000000000ULL) r = 3;
          else if (tw0 & 0x0000800000000000ULL) r = 2;
          else if (tw0 & 0x0000000080000000ULL) r = 1;
          else r = 0;
          av = static_cast<uint32_t>((d0 >> ((r & 3) << 4)) & 0xFFFu);
        } else {
          if (tw2 & 0x0000000000008000ULL) r = 8;
          else if (tw2 & 0x0000000080000000ULL) r = 9;
          else if (tw2 & 0x0000800000000000ULL) r = 10;
          else r = 11;
          av = static_cast<uint32_t>((d2 >> ((r & 3) << 4)) & 0xFFFu);
        }
        const uint32_t cb0 = av & (~av + 1u);
        const uint32_t cb1 = av ^ cb0;
        const int c0 = ctzBit32(cb0), c1 = ctzBit32(cb1);
        const uint32_t nRowMask = rowMask | (1u << r);
        uint64_t nd0 = d0, nd1 = d1, nd2 = d2;
        place<TwoWords>(r, c0, nd0, nd1, nd2);
        dfs<Mode, TwoWords>(rem - 1, nRowMask, colMask | cb0, nd0, nd1, nd2,
                            packed | (static_cast<uint64_t>(c0) << (r << 2)));
        --rem;
        rowMask = nRowMask;
        colMask |= cb1;
        place<TwoWords>(r, c1, d0, d1, d2);
        packed |= (static_cast<uint64_t>(c1) << (r << 2));
        continue;
      }

      if (c2) {
        int bestC = -1, bestD = 99;
        uint32_t cm = c2;
        while (cm) {
          const uint32_t cb = cm & (~cm + 1u);
          cm ^= cb;
          const int c = ctzBit32(cb);
          if (centerDist[c] < bestD) { bestD = centerDist[c]; bestC = c; }
        }
        const uint32_t cb = 1u << bestC;
        const uint32_t rmask = colRowsMask<TwoWords>(bestC, d0, d1, d2);
        const uint32_t rb0 = rmask & (~rmask + 1u);
        const uint32_t rb1 = rmask ^ rb0;
        const int r0 = ctzBit32(rb0), r1 = ctzBit32(rb1);
        const uint32_t nColMask = colMask | cb;
        uint64_t nd0 = d0, nd1 = d1, nd2 = d2;
        place<TwoWords>(r0, bestC, nd0, nd1, nd2);
        dfs<Mode, TwoWords>(rem - 1, rowMask | rb0, nColMask, nd0, nd1, nd2,
                            packed | (static_cast<uint64_t>(bestC) << (r0 << 2)));
        --rem;
        rowMask |= rb1;
        colMask = nColMask;
        place<TwoWords>(r1, bestC, d0, d1, d2);
        packed |= (static_cast<uint64_t>(bestC) << (r1 << 2));
        continue;
      }

      // 5. All remaining rows & columns have >= 3 options: pick tightest central row.
      int bestR = -1, bestKey = 1000;
      uint32_t bestAv = 0;
      uint32_t fr = full ^ rowMask;
      while (fr) {
        const uint32_t rb = fr & (~fr + 1u);
        fr ^= rb;
        const int r = ctzBit32(rb);
        const uint32_t av = getLane<TwoWords>(r, d0, d1, d2);
        const int key = (popcnt32(av) << 4) | centerDist[r];
        if (key < bestKey) {
          bestKey = key;
          bestR = r;
          bestAv = av;
        }
      }

      const uint32_t nRowMask = rowMask | (1u << bestR);
      uint32_t av = bestAv;
      while (av) {
        const uint32_t cb = av & (~av + 1u);
        av ^= cb;
        const int c = ctzBit32(cb);
        if (!av) {
          --rem;
          rowMask = nRowMask;
          colMask |= cb;
          place<TwoWords>(bestR, c, d0, d1, d2);
          packed |= (static_cast<uint64_t>(c) << (bestR << 2));
          break;
        }
        uint64_t nd0 = d0, nd1 = d1, nd2 = d2;
        place<TwoWords>(bestR, c, nd0, nd1, nd2);
        dfs<Mode, TwoWords>(rem - 1, nRowMask, colMask | cb, nd0, nd1, nd2,
                            packed | (static_cast<uint64_t>(c) << (bestR << 2)));
      }
    }
  }

  inline void packRows(const uint32_t* rowAllowed, uint32_t rowMask,
                       uint64_t& d0, uint64_t& d1, uint64_t& d2) const {
    d0 = kSentWord;
    d1 = kSentWord;
    d2 = kSentWord;
    for (int r = 0; r < n; ++r) {
      if (rowMask & (1u << r)) continue;
      const int sh = (r & 3) << 4;
      const uint64_t clearMask = ~(0xFFFFULL << sh);
      const uint64_t val = static_cast<uint64_t>(rowAllowed[r]) << sh;
      if (r < 4) d0 = (d0 & clearMask) | val;
      else if (r < 8) d1 = (d1 & clearMask) | val;
      else d2 = (d2 & clearMask) | val;
    }
  }

  template <bool HasHoles, bool TwoWords>
  void runD4() {
    constexpr int kCornerMode = HasHoles ? kD4CornerHoles : kD4CornerClean;
    constexpr int kIntMode = HasHoles ? kD4IntHoles : kD4IntClean;
    uint32_t rm[kMaxN];

    if (!HasHoles || killMask[0][0] != 0xFFu) {
      for (int c1 = 2; c1 < n; ++c1) {
        if (HasHoles && ((killMask[0][0] | killMask[1][c1]) == 0xFFu)) continue;
        keyCol = c1;
        for (int r = 0; r < n; ++r) rm[r] = (r >= 2 && r < c1) ? (full & ~2u) : full;
        uint64_t d0, d1, d2;
        packRows(rm, 0u, d0, d1, d2);
        place<TwoWords>(0, 0, d0, d1, d2);
        place<TwoWords>(1, c1, d0, d1, d2);
        dfs<kCornerMode, TwoWords>(n - 2, 3u, 1u | (1u << c1), d0, d1, d2, static_cast<uint64_t>(c1) << 4);
      }
    }

    const uint32_t noSides = full & ~(1u | (1u << m));
    for (int c0 = 1; c0 <= (n - 2) / 2; ++c0) {
      if (HasHoles && killMask[0][c0] == 0xFFu) continue;
      keyCol = c0;
      rm[0] = full;
      for (int r = 1; r < m; ++r) rm[r] = (r < c0 || r >= n - c0) ? noSides : full;
      rm[m] = ((1u << (n - 2 * c0)) - 1u) << c0;
      uint64_t d0, d1, d2;
      packRows(rm, 0u, d0, d1, d2);
      place<TwoWords>(0, c0, d0, d1, d2);
      dfs<kIntMode, TwoWords>(n - 1, 1u, 1u << c0, d0, d1, d2, static_cast<uint64_t>(c0));
    }
  }
};

}  // namespace

std::vector<std::vector<int>> solveHoles(int n, const std::vector<std::string>& grid) {
  if (n <= 0 || n > kMaxN || static_cast<int>(grid.size()) != n) return {};
  for (const auto& line : grid) {
    if (static_cast<int>(line.size()) != n) return {};
  }

  uint32_t rowAllowed[kMaxN]{};
  uint32_t colAllowed[kMaxN]{};
  int holeCount = 0;
  int minLineFree = n;
  for (int r = 0; r < n; ++r) {
    const std::string& line = grid[r];
    uint32_t mask = 0;
    for (int c = 0; c < n; ++c) {
      if (line[c] == 'H') {
        ++holeCount;
      } else {
        mask |= (1u << c);
        colAllowed[c] |= (1u << r);
      }
    }
    if (mask == 0) return {};
    rowAllowed[r] = mask;
    const int cnt = popcnt32(mask);
    if (cnt < minLineFree) minLineFree = cnt;
  }
  for (int c = 0; c < n; ++c) {
    if (colAllowed[c] == 0) return {};
    const int cnt = popcnt32(colAllowed[c]);
    if (cnt < minLineFree) minLineFree = cnt;
  }

  if (n == 1) {
    std::vector<std::vector<int>> out = {{0}};
    NQ_SNAPSHOT(nq::queensOf(out[0]), "solution 1");
    return out;
  }
  if (n < 4) return {};

  const uint32_t full = (1u << n) - 1u;
  const bool useD4 = (holeCount == 0 || (minLineFree >= 3 && holeCount * 8 <= n * n));

  int rem = n;
  uint32_t rowMask = 0;
  uint32_t colMask = 0;
  uint64_t packed = 0;
  if (!useD4) {
    if (minLineFree == 1) {
      if (!rootUnitProp(n, full, rowAllowed, rem, rowMask, colMask, packed)) return {};
      if (rem == 0) {
        std::vector<std::vector<int>> solutions;
        solutions.reserve(1);
        emitPacked(packed, n, snapshotsEnabled(), solutions);
        return solutions;
      }
      if (rem == 2) {
        const uint32_t fr = full ^ rowMask;
        const uint32_t rb0 = fr & (~fr + 1u);
        const int r0 = ctzBit32(rb0), r1 = ctzBit32(fr ^ rb0);
        const uint32_t fc = full ^ colMask;
        const uint32_t cb0 = fc & (~fc + 1u);
        const int c0 = ctzBit32(cb0), c1 = ctzBit32(fc ^ cb0);
        if (r1 - r0 == c1 - c0) return {};
        std::vector<std::vector<int>> solutions;
        solutions.reserve(2);
        const bool debug = snapshotsEnabled();
        emitPacked(packed | (static_cast<uint64_t>(c0) << (r0 << 2)) |
                   (static_cast<uint64_t>(c1) << (r1 << 2)), n, debug, solutions);
        emitPacked(packed | (static_cast<uint64_t>(c1) << (r0 << 2)) |
                   (static_cast<uint64_t>(c0) << (r1 << 2)), n, debug, solutions);
        return solutions;
      }
    }

    const uint32_t freeRows = full ^ rowMask;
    if (minLineFree == 1 || minLineFree < (rem + 1) / 2) {
      if (!hasPerfectMatchingRem(n, freeRows, rowAllowed)) return {};
    }
  }

  // Single SwarD4AlgX instance (~35 KB total frame) keeps Emscripten 64 KB stack safe.
  SwarD4AlgX solver;
  solver.n = n;
  solver.m = n - 1;
  solver.full = full;

  if (useD4) {
    solver.buildTables(nullptr);

    if (holeCount == 0) {
      if (n <= 8) solver.runD4<false, true>();
      else solver.runD4<false, false>();
    } else {
      const int m = n - 1;
      for (int hr = 0; hr < n; ++hr) {
        const std::string& row = grid[hr];
        for (int hc = 0; hc < n; ++hc) {
          if (row[hc] != 'H') continue;
          solver.killMask[hr][hc] |= 1u << 0;
          solver.killMask[hr][m - hc] |= 1u << 1;
          solver.killMask[m - hr][hc] |= 1u << 2;
          solver.killMask[m - hr][m - hc] |= 1u << 3;
          solver.killMask[hc][hr] |= 1u << 4;
          solver.killMask[m - hc][hr] |= 1u << 5;
          solver.killMask[hc][m - hr] |= 1u << 6;
          solver.killMask[m - hc][m - hr] |= 1u << 7;
        }
      }
      if (n <= 8) solver.runD4<true, true>();
      else solver.runD4<true, false>();
    }

    std::vector<std::vector<int>> solutions;
    solutions.reserve(solver.totalSolutions);
    const bool debug = snapshotsEnabled();
    for (size_t i = 0; i < solver.orbitCount; ++i) {
      const uint64_t entry = solver.stackBuf[i];
      emitD4Orbit(entry, static_cast<uint8_t>(entry >> 48), n, debug, solutions);
    }
    return solutions;
  }

  solver.buildTables(rowAllowed);
  uint64_t d0, d1, d2;
  solver.packRows(rowAllowed, rowMask, d0, d1, d2);

  if (n <= 8) solver.dfs<kGeneralBuf, true>(rem, rowMask, colMask, d0, d1, d2, packed);
  else solver.dfs<kGeneralBuf, false>(rem, rowMask, colMask, d0, d1, d2, packed);

  std::vector<std::vector<int>> solutions;
  solutions.reserve(solver.totalSolutions);
  const bool debug = snapshotsEnabled();
  if (solver.totalSolutions <= SwarD4AlgX::kStackCap) {
    if (!debug) {
      int buf[kMaxN];
      for (size_t i = 0; i < solver.totalSolutions; ++i) {
        const uint64_t sol = solver.stackBuf[i];
        for (int r = 0; r < n; ++r) buf[r] = static_cast<int>((sol >> (r << 2)) & 0xFu);
        solutions.emplace_back(buf, buf + n);
      }
    } else {
      for (size_t i = 0; i < solver.totalSolutions; ++i) {
        emitPacked(solver.stackBuf[i], n, true, solutions);
      }
    }
  } else {
    solver.out = &solutions;
    solver.debug = debug;
    if (n <= 8) solver.dfs<kGeneralEmit, true>(rem, rowMask, colMask, d0, d1, d2, packed);
    else solver.dfs<kGeneralEmit, false>(rem, rowMask, colMask, d0, d1, d2, packed);
  }
  return solutions;
}
