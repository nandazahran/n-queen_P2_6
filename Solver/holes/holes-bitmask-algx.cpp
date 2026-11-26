// Solver for the Holes case (3C): Unified 25KB-stack D4 + Turbo Bitmask Algorithm X
// with single-scan batch forced-row propagation, specialized unrolled rem==3 -> geometric rem==2,
// and 4-bit (once, twice, thrice, four) bit-parallel column cardinality counters.
#if __cplusplus >= 202002L
#include <bit>
#endif
#include <cstdint>
#include <string>
#include <vector>

#include "nqueens.h"

namespace {

constexpr int kMaxN = 16;

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

inline int ctzBit(uint32_t b) {
#if __cplusplus >= 202002L
  return std::countr_zero(b);
#else
  return popcnt32(b - 1u);
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
    const int k = ctzBit(kb);
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
      const int c = ctzBit(b);
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

enum LeafMode {
  kGeneralBuf = 0,
  kGeneralEmit = 1,
  kD4CornerClean = 2,
  kD4CornerHoles = 3,
  kD4IntClean = 4,
  kD4IntHoles = 5,
};

struct UnifiedHolesAlgX {
  int n = 0;
  int m = 0;
  int keyCol = 0;
  uint32_t full = 0;
  uint32_t rowAllowed[kMaxN]{};
  uint32_t colAllowed[kMaxN]{};
  uint8_t centerDist[kMaxN]{};
  uint8_t killMask[12][12]{};

  static constexpr size_t kStackCap = 3072;  // 24 KB on stack
  uint64_t stackBuf[kStackCap];
  size_t orbitCount = 0;
  size_t totalSolutions = 0;
  std::vector<std::vector<int>>* out = nullptr;
  bool debug = false;

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
      uint8_t cols[12];
      uint8_t inv[12];
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
      uint8_t imgs[8][12];
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

  inline uint32_t availRow(int r, uint32_t colMask, uint32_t diagSum, uint32_t diagDiffRow) const {
    return rowAllowed[r] & ~(colMask | (diagSum >> r) | (diagDiffRow >> (m - r)));
  }

  inline uint32_t availCol(int c, uint32_t rowMask, uint32_t diagSum, uint32_t diagDiffCol) const {
    return colAllowed[c] & ~(rowMask | (diagSum >> c) | (diagDiffCol >> (m - c)));
  }

  template <int Mode>
  void dfs(int rem, uint32_t rowMask, uint32_t colMask, uint32_t diagSum,
           uint32_t diagDiffRow, uint32_t diagDiffCol, uint64_t packed) {
    for (;;) {
      if (rem == 0) {
        onLeaf<Mode>(packed);
        return;
      }
      if (rem == 1) {
        const int r0 = ctzBit(full ^ rowMask);
        const uint32_t a0 = availRow(r0, colMask, diagSum, diagDiffRow);
        if (a0) {
          onLeaf<Mode>(packed | (static_cast<uint64_t>(ctzBit(a0)) << (r0 << 2)));
        }
        return;
      }
      if (rem == 2) {
        const uint32_t fr = full ^ rowMask;
        const uint32_t rb0 = fr & (~fr + 1u);
        const int r0 = ctzBit(rb0);
        const int r1 = ctzBit(fr ^ rb0);
        const uint32_t fc = full ^ colMask;
        const uint32_t cb0 = fc & (~fc + 1u);
        const uint32_t cb1 = fc ^ cb0;
        const int c0 = ctzBit(cb0);
        const int c1 = ctzBit(cb1);
        if (r1 - r0 == c1 - c0) return;
        const uint32_t a0 = availRow(r0, colMask, diagSum, diagDiffRow);
        if (!a0) return;
        const uint32_t a1 = availRow(r1, colMask, diagSum, diagDiffRow);
        if (!a1) return;
        if ((a0 & cb0) && (a1 & cb1)) {
          onLeaf<Mode>(packed | (static_cast<uint64_t>(c0) << (r0 << 2)) |
                       (static_cast<uint64_t>(c1) << (r1 << 2)));
        }
        if ((a0 & cb1) && (a1 & cb0)) {
          onLeaf<Mode>(packed | (static_cast<uint64_t>(c1) << (r0 << 2)) |
                       (static_cast<uint64_t>(c0) << (r1 << 2)));
        }
        return;
      }
      if (rem == 3) {
        uint32_t fr = full ^ rowMask;
        const uint32_t rb0 = fr & (~fr + 1u);
        fr ^= rb0;
        const uint32_t rb1 = fr & (~fr + 1u);
        const uint32_t rb2 = fr ^ rb1;
        const int r0 = ctzBit(rb0);
        const int r1 = ctzBit(rb1);
        const int r2 = ctzBit(rb2);
        uint32_t a0 = availRow(r0, colMask, diagSum, diagDiffRow);
        if (!a0) return;
        const uint32_t a1 = availRow(r1, colMask, diagSum, diagDiffRow);
        if (!a1) return;
        const uint32_t a2 = availRow(r2, colMask, diagSum, diagDiffRow);
        if (!a2) return;
        const uint32_t fc = full ^ colMask;
        if ((a0 | a1 | a2) != fc) return;
        const int dr12 = r2 - r1;
        while (a0) {
          const uint32_t cb = a0 & (~a0 + 1u);
          a0 ^= cb;
          const uint32_t remC = fc ^ cb;
          const uint32_t rcb0 = remC & (~remC + 1u);
          const uint32_t rcb1 = remC ^ rcb0;
          const int rc0 = ctzBit(rcb0);
          const int rc1 = ctzBit(rcb1);
          if (dr12 == rc1 - rc0) continue;
          const int c = ctzBit(cb);
          const uint32_t ds1 = diagSum | (1u << (r0 + c));
          const uint32_t ddr1 = diagDiffRow | (1u << (c - r0 + m));
          const uint32_t b1 = a1 & ~(cb | (ds1 >> r1) | (ddr1 >> (m - r1)));
          if (!b1) continue;
          const uint32_t b2 = a2 & ~(cb | (ds1 >> r2) | (ddr1 >> (m - r2)));
          if (!b2) continue;
          const uint64_t p0 = packed | (static_cast<uint64_t>(c) << (r0 << 2));
          if ((b1 & rcb0) && (b2 & rcb1)) {
            onLeaf<Mode>(p0 | (static_cast<uint64_t>(rc0) << (r1 << 2)) |
                         (static_cast<uint64_t>(rc1) << (r2 << 2)));
          }
          if ((b1 & rcb1) && (b2 & rcb0)) {
            onLeaf<Mode>(p0 | (static_cast<uint64_t>(rc1) << (r1 << 2)) |
                         (static_cast<uint64_t>(rc0) << (r2 << 2)));
          }
        }
        return;
      }

      // Single-scan batch forced-row propagation + 4-bit column cardinality counters.
      uint32_t fr = full ^ rowMask;
      uint32_t once = 0, twice = 0, thrice = 0, four = 0;
      int bestRow = -1;
      int bestRowKey = 1000;
      uint32_t bestRowAvail = 0;
      bool changed = false;

      while (fr) {
        const uint32_t rb = fr & (~fr + 1u);
        fr ^= rb;
        const int r = ctzBit(rb);
        const uint32_t a = availRow(r, colMask, diagSum, diagDiffRow);
        if (!a) return;
        if ((a & (a - 1u)) == 0u) {
          const int c = ctzBit(a);
          --rem;
          rowMask |= rb;
          colMask |= a;
          diagSum |= (1u << (r + c));
          diagDiffRow |= (1u << (c - r + m));
          diagDiffCol |= (1u << (r - c + m));
          packed |= (static_cast<uint64_t>(c) << (r << 2));
          changed = true;
          continue;
        }
        if (!changed) {
          const int key = (popcnt32(a) << 4) | centerDist[r];
          if (key < bestRowKey) {
            bestRowKey = key;
            bestRow = r;
            bestRowAvail = a;
          }
          four |= (thrice & a);
          thrice |= (twice & a);
          twice |= (once & a);
          once |= a;
        }
      }

      if (changed) continue;

      if ((once | colMask) != full) return;

      const uint32_t uniqueCols = once & ~twice;
      if (uniqueCols) {
        const uint32_t cb = uniqueCols & (~uniqueCols + 1u);
        const int c = ctzBit(cb);
        const uint32_t rb = availCol(c, rowMask, diagSum, diagDiffCol);
        const int r = ctzBit(rb);
        --rem;
        rowMask |= rb;
        colMask |= cb;
        diagSum |= (1u << (r + c));
        diagDiffRow |= (1u << (c - r + m));
        diagDiffCol |= (1u << (r - c + m));
        packed |= (static_cast<uint64_t>(c) << (r << 2));
        continue;
      }

      const int bestRowCnt = bestRowKey >> 4;
      int bestCol = -1;
      uint32_t bestColAvail = 0;
      const uint32_t c2 = twice & ~thrice;
      if (c2) {
        int bestKey = bestRowKey;
        uint32_t cm = c2;
        while (cm) {
          const uint32_t cb = cm & (~cm + 1u);
          cm ^= cb;
          const int c = ctzBit(cb);
          const int key = (2 << 4) | centerDist[c];
          if (key < bestKey) {
            bestKey = key;
            bestCol = c;
          }
        }
        if (bestCol >= 0) bestColAvail = availCol(bestCol, rowMask, diagSum, diagDiffCol);
      } else if (bestRowCnt >= 3) {
        const uint32_t c3 = thrice & ~four;
        if (c3) {
          int bestKey = bestRowKey;
          uint32_t cm = c3;
          while (cm) {
            const uint32_t cb = cm & (~cm + 1u);
            cm ^= cb;
            const int c = ctzBit(cb);
            const int key = (3 << 4) | centerDist[c];
            if (key < bestKey) {
              bestKey = key;
              bestCol = c;
            }
          }
          if (bestCol >= 0) bestColAvail = availCol(bestCol, rowMask, diagSum, diagDiffCol);
        } else if (bestRowCnt >= 5) {
          int bestKey = bestRowKey;
          uint32_t cm = full ^ colMask;
          while (cm) {
            const uint32_t cb = cm & (~cm + 1u);
            cm ^= cb;
            const int c = ctzBit(cb);
            const uint32_t ca = availCol(c, rowMask, diagSum, diagDiffCol);
            const int key = (popcnt32(ca) << 4) | centerDist[c];
            if (key < bestKey) {
              bestKey = key;
              bestCol = c;
              bestColAvail = ca;
            }
          }
        }
      }

      if (bestCol >= 0) {
        const int c = bestCol;
        const uint32_t cb = 1u << c;
        uint32_t avail = bestColAvail;
        while (avail) {
          const uint32_t rb = avail & (~avail + 1u);
          avail ^= rb;
          const int r = ctzBit(rb);
          dfs<Mode>(rem - 1, rowMask | rb, colMask | cb,
                    diagSum | (1u << (r + c)),
                    diagDiffRow | (1u << (c - r + m)),
                    diagDiffCol | (1u << (r - c + m)),
                    packed | (static_cast<uint64_t>(c) << (r << 2)));
        }
        return;
      }

      const int r = bestRow;
      const uint32_t rb = 1u << r;
      uint32_t avail = bestRowAvail;
      while (avail) {
        const uint32_t cb = avail & (~avail + 1u);
        avail ^= cb;
        const int c = ctzBit(cb);
        dfs<Mode>(rem - 1, rowMask | rb, colMask | cb,
                  diagSum | (1u << (r + c)),
                  diagDiffRow | (1u << (c - r + m)),
                  diagDiffCol | (1u << (r - c + m)),
                  packed | (static_cast<uint64_t>(c) << (r << 2)));
      }
      return;
    }
  }

  template <bool HasHoles>
  void runD4() {
    constexpr int kCornerMode = HasHoles ? kD4CornerHoles : kD4CornerClean;
    constexpr int kIntMode = HasHoles ? kD4IntHoles : kD4IntClean;

    if (!HasHoles || killMask[0][0] != 0xFFu) {
      for (int c1 = 2; c1 < n; ++c1) {
        if (HasHoles && ((killMask[0][0] | killMask[1][c1]) == 0xFFu)) continue;
        keyCol = c1;
        for (int i = 0; i < n; ++i) {
          rowAllowed[i] = full;
          colAllowed[i] = full;
        }
        for (int r = 2; r < c1; ++r) {
          rowAllowed[r] = full & ~2u;
          colAllowed[1] &= ~(1u << r);
        }
        const uint32_t rm = 3u;
        const uint32_t cm = 1u | (1u << c1);
        const uint32_t ds = 1u | (1u << (1 + c1));
        const uint32_t ddr = (1u << m) | (1u << (c1 - 1 + m));
        const uint32_t ddc = (1u << m) | (1u << (1 - c1 + m));
        dfs<kCornerMode>(n - 2, rm, cm, ds, ddr, ddc, static_cast<uint64_t>(c1) << 4);
      }
    }

    const uint32_t edgeBits = 1u | (1u << m);
    const uint32_t noSides = full & ~edgeBits;
    const uint32_t noBottom = full & ~(1u << m);
    for (int c0 = 1; c0 <= (n - 2) / 2; ++c0) {
      if (HasHoles && killMask[0][c0] == 0xFFu) continue;
      keyCol = c0;
      const uint32_t midMask = ((1u << (n - 2 * c0)) - 1u) << c0;
      rowAllowed[0] = full;
      for (int r = 1; r < m; ++r) {
        rowAllowed[r] = (r < c0 || r >= n - c0) ? noSides : full;
      }
      rowAllowed[m] = midMask;
      colAllowed[0] = midMask;
      colAllowed[m] = midMask;
      for (int c = 1; c < m; ++c) {
        colAllowed[c] = (c < c0 || c >= n - c0) ? noBottom : full;
      }
      const uint32_t rm = 1u;
      const uint32_t cm = 1u << c0;
      const uint32_t ds = 1u << c0;
      const uint32_t ddr = 1u << (c0 + m);
      const uint32_t ddc = 1u << (m - c0);
      dfs<kIntMode>(n - 1, rm, cm, ds, ddr, ddc, static_cast<uint64_t>(c0));
    }
  }
};

}  // namespace

std::vector<std::vector<int>> solveHoles(int n, const std::vector<std::string>& grid) {
  if (n <= 0 || n > kMaxN || static_cast<int>(grid.size()) != n) return {};
  for (const auto& line : grid) {
    if (static_cast<int>(line.size()) != n) return {};
  }

  UnifiedHolesAlgX solver;
  solver.n = n;
  solver.m = n - 1;
  solver.full = (1u << n) - 1u;

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
        solver.colAllowed[c] |= (1u << r);
      }
    }
    if (mask == 0) return {};
    solver.rowAllowed[r] = mask;
    const int cnt = popcnt32(mask);
    if (cnt < minLineFree) minLineFree = cnt;
    const int d = 2 * r - solver.m;
    solver.centerDist[r] = static_cast<uint8_t>(d < 0 ? -d : d);
  }
  for (int c = 0; c < n; ++c) {
    if (solver.colAllowed[c] == 0) return {};
    const int cnt = popcnt32(solver.colAllowed[c]);
    if (cnt < minLineFree) minLineFree = cnt;
  }

  if (n == 1) {
    std::vector<std::vector<int>> out = {{0}};
    NQ_SNAPSHOT(nq::queensOf(out[0]), "solution 1");
    return out;
  }
  if (n < 4) return {};

  const bool useD4 = (n <= 12) && (holeCount == 0 || (minLineFree >= 3 && holeCount * 8 <= n * n));
  if (useD4) {
    if (holeCount == 0) {
      solver.runD4<false>();
    } else {
      if (minLineFree < (n + 1) / 2 && !hasPerfectMatching(n, solver.rowAllowed)) return {};
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

  if (minLineFree < (n + 1) / 2 && !hasPerfectMatching(n, solver.rowAllowed)) return {};

  solver.dfs<kGeneralBuf>(n, 0, 0, 0, 0, 0, 0);

  std::vector<std::vector<int>> solutions;
  solutions.reserve(solver.totalSolutions);
  const bool debug = snapshotsEnabled();
  if (solver.totalSolutions <= UnifiedHolesAlgX::kStackCap) {
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
    solver.dfs<kGeneralEmit>(n, 0, 0, 0, 0, 0, 0);
  }
  return solutions;
}
