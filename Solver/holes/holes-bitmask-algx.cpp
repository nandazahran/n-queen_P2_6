// Solver for the Holes case (4A): Unified 64-bit SWAR Bidirectional Bitmask Algorithm X (N <= 12).
// Packs all 12 row domains (12 bits each) into three 64-bit registers (d0, d1, d2, 4 rows/word,
// 0x7000 sentinel for placed/unused rows), running zero-loop SWAR dead-row, forced-row, count-2-row,
// and (once, twice, thrice) column-cardinality checks across all 12 rows simultaneously, unified for
// both D4-Holes (empty & sparse H <= N^2/8) and general Holes with ~28 KB stack and 0 B aux heap.
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

inline int ctzBit32(uint32_t b) {
#if __cplusplus >= 202002L
  return std::countr_zero(b);
#else
  return popcnt32(b - 1u);
#endif
}

inline int ctz64(uint64_t x) {
#if __cplusplus >= 202002L
  return std::countr_zero(x);
#else
  const uint32_t lo = static_cast<uint32_t>(x);
  if (lo) return ctzBit32(lo & (~lo + 1u));
  const uint32_t hi = static_cast<uint32_t>(x >> 32);
  return 32 + ctzBit32(hi & (~hi + 1u));
#endif
}

inline void applyD4(int k, const uint8_t* src, uint8_t* dst, int n) {
  const int m = n - 1;
  switch (k) {
    case 0: for (int r = 0; r < n; ++r) dst[r] = src[r]; break;
    case 1: for (int r = 0; r < n; ++r) dst[r] = static_cast<uint8_t>(m - src[r]); break;
    case 2: for (int r = 0; r < n; ++r) dst[m - r] = src[r]; break;
    case 3: for (int r = 0; r < n; ++r) dst[m - r] = static_cast<uint8_t>(m - src[r]); break;
    case 4: for (int r = 0; r < n; ++r) dst[src[r]] = static_cast<uint8_t>(r); break;
    case 5: for (int r = 0; r < n; ++r) dst[src[r]] = static_cast<uint8_t>(m - r); break;
    case 6: for (int r = 0; r < n; ++r) dst[m - src[r]] = static_cast<uint8_t>(r); break;
    default: for (int r = 0; r < n; ++r) dst[m - src[r]] = static_cast<uint8_t>(m - r); break;
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

  int src[kMaxN];
  int buf[kMaxN];
  for (int r = 0; r < n; ++r) src[r] = static_cast<int>((packed >> (r << 2)) & 0xFu);
  uint32_t km = mask;
  while (km) {
    const uint32_t kb = km & (~km + 1u);
    km ^= kb;
    const int k = ctzBit32(kb);
    switch (k) {
      case 0: for (int r = 0; r < n; ++r) buf[r] = src[r]; break;
      case 1: for (int r = 0; r < n; ++r) buf[r] = m - src[r]; break;
      case 2: for (int r = 0; r < n; ++r) buf[m - r] = src[r]; break;
      case 3: for (int r = 0; r < n; ++r) buf[m - r] = m - src[r]; break;
      case 4: for (int r = 0; r < n; ++r) buf[src[r]] = r; break;
      case 5: for (int r = 0; r < n; ++r) buf[src[r]] = m - r; break;
      case 6: for (int r = 0; r < n; ++r) buf[m - src[r]] = r; break;
      default: for (int r = 0; r < n; ++r) buf[m - src[r]] = m - r; break;
    }
    solutions.emplace_back(buf, buf + n);
    if (debug) {
      snapshot(nq::queensOf(solutions.back()), "solution " + std::to_string(solutions.size()));
    }
  }
}

bool hasPerfectMatching(int n, const uint32_t* rowAllowed) {
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

  for (int r = 0; r < n; ++r) {
    uint32_t visited = 0;
    if (!augment(augment, r, visited)) return false;
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

struct SwarHolesAlgX {
  int n = 0;
  int m = 0;
  int keyCol = 0;
  uint32_t full = 0;
  uint8_t centerDist[kMaxN]{};
  uint8_t killMask[kMaxN][kMaxN]{};
  CellAtk atk[kMaxN][kMaxN];

  static constexpr size_t kStackCap = 3072;  // 24 KB on stack
  uint64_t stackBuf[kStackCap];
  size_t orbitCount = 0;
  size_t totalSolutions = 0;
  std::vector<std::vector<int>>* out = nullptr;
  bool debug = false;

  void buildAtk() {
    for (int r = 0; r < n; ++r) {
      for (int c = 0; c < n; ++c) {
        uint64_t m0 = 0, m1 = 0, m2 = 0;
        for (int r2 = 0; r2 < 12; ++r2) {
          uint16_t lane;
          if (r2 == r) {
            lane = 0x0000u;
          } else if (r2 >= n) {
            lane = 0xFFFFu;
          } else {
            uint32_t kill = 1u << c;
            const int dr = r2 > r ? (r2 - r) : (r - r2);
            if (c >= dr) kill |= 1u << (c - dr);
            if (c + dr < n) kill |= 1u << (c + dr);
            lane = static_cast<uint16_t>(0xFFFFu ^ kill);
          }
          const int sh = (r2 & 3) << 4;
          if (r2 < 4) m0 |= static_cast<uint64_t>(lane) << sh;
          else if (r2 < 8) m1 |= static_cast<uint64_t>(lane) << sh;
          else m2 |= static_cast<uint64_t>(lane) << sh;
        }
        atk[r][c] = {m0, m1, m2};
      }
    }
  }

  inline void place(int r, int c, uint64_t& d0, uint64_t& d1, uint64_t& d2) const {
    const CellAtk& a = atk[r][c];
    d0 &= a.m0;
    d1 &= a.m1;
    d2 &= a.m2;
    const uint64_t sent = 0x7000ULL << ((r & 3) << 4);
    if (r < 4) d0 |= sent;
    else if (r < 8) d1 |= sent;
    else d2 |= sent;
  }

  inline uint32_t getLane(int r, uint64_t d0, uint64_t d1, uint64_t d2) const {
    const uint64_t w = (r < 4) ? d0 : (r < 8 ? d1 : d2);
    return static_cast<uint32_t>((w >> ((r & 3) << 4)) & 0xFFFu);
  }

  inline uint32_t colRowsMask(int c, uint64_t d0, uint64_t d1, uint64_t d2) const {
    const uint64_t cm = (1ULL << c) * kOnes;
    uint32_t res = 0;
    if (const uint64_t w0 = d0 & cm) {
      if (w0 & 0x000000000000FFFFULL) res |= 1u << 0;
      if (w0 & 0x00000000FFFF0000ULL) res |= 1u << 1;
      if (w0 & 0x0000FFFF00000000ULL) res |= 1u << 2;
      if (w0 & 0xFFFF000000000000ULL) res |= 1u << 3;
    }
    if (const uint64_t w1 = d1 & cm) {
      if (w1 & 0x000000000000FFFFULL) res |= 1u << 4;
      if (w1 & 0x00000000FFFF0000ULL) res |= 1u << 5;
      if (w1 & 0x0000FFFF00000000ULL) res |= 1u << 6;
      if (w1 & 0xFFFF000000000000ULL) res |= 1u << 7;
    }
    if (const uint64_t w2 = d2 & cm) {
      if (w2 & 0x000000000000FFFFULL) res |= 1u << 8;
      if (w2 & 0x00000000FFFF0000ULL) res |= 1u << 9;
      if (w2 & 0x0000FFFF00000000ULL) res |= 1u << 10;
      if (w2 & 0xFFFF000000000000ULL) res |= 1u << 11;
    }
    return res;
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

  template <int Mode>
  void dfs(int rem, uint32_t rowMask, uint32_t colMask, uint64_t d0, uint64_t d1, uint64_t d2,
           uint64_t packed) {
    for (;;) {
      // 1. Zero-loop SWAR dead-row check across all 12 rows.
      if ((~(d0 + k7FFF) | ~(d1 + k7FFF) | ~(d2 + k7FFF)) & kHigh) return;

      if (rem == 1) {
        const int r0 = ctzBit32(full ^ rowMask);
        const int c0 = ctzBit32(full ^ colMask);
        onLeaf<Mode>(packed | (static_cast<uint64_t>(c0) << (r0 << 2)));
        return;
      }

      // 2. Zero-loop SWAR forced-row check across all 12 rows.
      const uint64_t y0 = d0 & (d0 - kOnes);
      const uint64_t y1 = d1 & (d1 - kOnes);
      const uint64_t y2 = d2 & (d2 - kOnes);
      const uint64_t o0 = ~(y0 + k7FFF) & kHigh;
      const uint64_t o1 = ~(y1 + k7FFF) & kHigh;
      const uint64_t o2 = ~(y2 + k7FFF) & kHigh;
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
        place(r, c, d0, d1, d2);
        packed |= static_cast<uint64_t>(c) << (r << 2);
        if (rem == 0) {
          onLeaf<Mode>(packed);
          return;
        }
        continue;
      }

      // 3. Zero-loop SWAR column cardinality (once, twice, thrice) across all 12 rows.
      const uint64_t m0 = d0 & kData;
      const uint64_t m1 = d1 & kData;
      const uint64_t m2 = d2 & kData;
      const uint64_t o01 = m0 | m1;
      const uint64_t t01 = m0 & m1;
      const uint64_t once4 = o01 | m2;
      const uint64_t twice4 = t01 | (o01 & m2);
      const uint64_t thrice4 = t01 & m2;

      const uint32_t oA = static_cast<uint32_t>(once4), oB = static_cast<uint32_t>(once4 >> 32);
      const uint32_t tA = static_cast<uint32_t>(twice4), tB = static_cast<uint32_t>(twice4 >> 32);
      const uint32_t hA = static_cast<uint32_t>(thrice4), hB = static_cast<uint32_t>(thrice4 >> 32);
      const uint32_t once2 = oA | oB;
      const uint32_t twice2 = tA | tB | (oA & oB);
      const uint32_t thrice2 = hA | hB | (tA & oB) | (oA & tB);

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
        else if (const uint64_t w = d0 & cm) r = (ctz64(w) >> 4);
        else r = 8 + (ctz64(d2 & cm) >> 4);
        --rem;
        rowMask |= (1u << r);
        colMask |= cb;
        place(r, c, d0, d1, d2);
        packed |= static_cast<uint64_t>(c) << (r << 2);
        if (rem == 0) {
          onLeaf<Mode>(packed);
          return;
        }
        continue;
      }

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

      // 4. Zero-loop SWAR count-2 row check across all 12 rows (preferring central rows in d1).
      const uint64_t z0 = y0 & (y0 - kOnes);
      const uint64_t z1 = y1 & (y1 - kOnes);
      const uint64_t z2 = y2 & (y2 - kOnes);
      const uint64_t tw0 = ~(z0 + k7FFF) & kHigh;
      const uint64_t tw1 = ~(z1 + k7FFF) & kHigh;
      const uint64_t tw2 = ~(z2 + k7FFF) & kHigh;

      if (tw1 | tw0 | tw2) {
        int r;
        uint32_t av;
        if (tw1) {
          if (tw1 & 0x0000800000000000ULL) r = 6;
          else if (tw1 & 0x0000000080000000ULL) r = 5;
          else if (tw1 & 0x8000000000000000ULL) r = 7;
          else r = 4;
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
        place(r, c0, nd0, nd1, nd2);
        dfs<Mode>(rem - 1, nRowMask, colMask | cb0, nd0, nd1, nd2,
                  packed | (static_cast<uint64_t>(c0) << (r << 2)));
        --rem;
        rowMask = nRowMask;
        colMask |= cb1;
        place(r, c1, d0, d1, d2);
        packed |= (static_cast<uint64_t>(c1) << (r << 2));
        continue;
      }

      // 5. Count-2 column check via thrice.
      const uint32_t thrice = (thrice2 & 0xFFFu) | (thrice2 >> 16) |
                              (twiceLo & onceHi) | (onceLo & twiceHi);
      const uint32_t c2 = twice & ~thrice;
      if (c2) {
        int bestC = -1, bestD = 99;
        uint32_t cm = c2;
        while (cm) {
          const uint32_t cb = cm & (~cm + 1u);
          cm ^= cb;
          const int c = ctzBit32(cb);
          if (centerDist[c] < bestD) {
            bestD = centerDist[c];
            bestC = c;
          }
        }
        const uint32_t cb = 1u << bestC;
        const uint32_t rmask = colRowsMask(bestC, d0, d1, d2);
        const uint32_t rb0 = rmask & (~rmask + 1u);
        const uint32_t rb1 = rmask ^ rb0;
        const int r0 = ctzBit32(rb0), r1 = ctzBit32(rb1);
        const uint32_t nColMask = colMask | cb;
        uint64_t nd0 = d0, nd1 = d1, nd2 = d2;
        place(r0, bestC, nd0, nd1, nd2);
        dfs<Mode>(rem - 1, rowMask | rb0, nColMask, nd0, nd1, nd2,
                  packed | (static_cast<uint64_t>(bestC) << (r0 << 2)));
        --rem;
        rowMask |= rb1;
        colMask = nColMask;
        place(r1, bestC, d0, d1, d2);
        packed |= (static_cast<uint64_t>(bestC) << (r1 << 2));
        continue;
      }

      // 6. All remaining rows & columns have >= 3 options: branch on tightest central row.
      int bestR = -1, bestKey = 1000;
      uint32_t bestAv = 0;
      uint32_t fr = full ^ rowMask;
      while (fr) {
        const uint32_t rb = fr & (~fr + 1u);
        fr ^= rb;
        const int r = ctzBit32(rb);
        const uint32_t av = getLane(r, d0, d1, d2);
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
          place(bestR, c, d0, d1, d2);
          packed |= (static_cast<uint64_t>(c) << (bestR << 2));
          break;
        }
        uint64_t nd0 = d0, nd1 = d1, nd2 = d2;
        place(bestR, c, nd0, nd1, nd2);
        dfs<Mode>(rem - 1, nRowMask, colMask | cb, nd0, nd1, nd2,
                  packed | (static_cast<uint64_t>(c) << (bestR << 2)));
      }
    }
  }

  inline void packRows(const uint32_t* rowAllowed, uint64_t& d0, uint64_t& d1, uint64_t& d2) const {
    d0 = kSentWord;
    d1 = kSentWord;
    d2 = kSentWord;
    for (int r = 0; r < n; ++r) {
      const int sh = (r & 3) << 4;
      const uint64_t clearMask = ~(0xFFFFULL << sh);
      const uint64_t val = static_cast<uint64_t>(rowAllowed[r]) << sh;
      if (r < 4) d0 = (d0 & clearMask) | val;
      else if (r < 8) d1 = (d1 & clearMask) | val;
      else d2 = (d2 & clearMask) | val;
    }
  }

  template <bool HasHoles>
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
        packRows(rm, d0, d1, d2);
        place(0, 0, d0, d1, d2);
        place(1, c1, d0, d1, d2);
        dfs<kCornerMode>(n - 2, 3u, 1u | (1u << c1), d0, d1, d2, static_cast<uint64_t>(c1) << 4);
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
      packRows(rm, d0, d1, d2);
      place(0, c0, d0, d1, d2);
      dfs<kIntMode>(n - 1, 1u, 1u << c0, d0, d1, d2, static_cast<uint64_t>(c0));
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

  if (holeCount > 0 && minLineFree < (n + 1) / 2 && !hasPerfectMatching(n, rowAllowed)) return {};

  SwarHolesAlgX solver;
  solver.n = n;
  solver.m = n - 1;
  solver.full = (1u << n) - 1u;
  for (int i = 0; i < n; ++i) {
    const int d = 2 * i - solver.m;
    solver.centerDist[i] = static_cast<uint8_t>(d < 0 ? -d : d);
  }
  solver.buildAtk();

  const bool useD4 = (holeCount == 0 || (minLineFree >= 3 && holeCount * 8 <= n * n));
  if (useD4) {
    if (holeCount == 0) {
      solver.runD4<false>();
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
      solver.runD4<true>();
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

  uint64_t d0, d1, d2;
  solver.packRows(rowAllowed, d0, d1, d2);
  solver.dfs<kGeneralBuf>(n, 0, 0, d0, d1, d2, 0);

  std::vector<std::vector<int>> solutions;
  solutions.reserve(solver.totalSolutions);
  const bool debug = snapshotsEnabled();
  if (solver.totalSolutions <= SwarHolesAlgX::kStackCap) {
    if (!debug) {
      int buf[kMaxN];
      for (size_t i = 0; i < solver.totalSolutions; ++i) {
        const uint64_t packed = solver.stackBuf[i];
        for (int r = 0; r < n; ++r) buf[r] = static_cast<int>((packed >> (r << 2)) & 0xFu);
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
    solver.dfs<kGeneralEmit>(n, 0, 0, d0, d1, d2, 0);
  }
  return solutions;
}
