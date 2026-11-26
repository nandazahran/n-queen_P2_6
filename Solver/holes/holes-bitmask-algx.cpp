// Solver for the Holes case (1C): Wide 8-way simultaneous D4-Holes (H <= N^2 / 3, N <= 12)
// with single-survivor freeMask specialization (dfsSingle) + 64KB-safe two-pass Bitmask Algorithm X.
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

struct D4Holes {
  int n = 0, m = 0;
  uint32_t full = 0;
  uint32_t rowMask[12]{};
  uint8_t killMask[12][12]{};   // 144 B: bit k set iff T_k(r, c) is a hole
  uint16_t freeMask[8][12]{};   // 192 B: bit c set iff T_k(r, c) is free

  static constexpr int kStackCap = 2048;  // 16 KB on stack
  uint64_t stackBuf[kStackCap];
  int stackCount = 0;
  size_t totalSolutions = 0;

  inline void addFundamental(uint64_t packed, uint32_t emitMask) {
    if (!emitMask) return;
    stackBuf[stackCount++] = packed | (static_cast<uint64_t>(emitMask) << 48);
    totalSolutions += static_cast<size_t>(popcnt32(emitMask));
  }

  void onCornerLeaf(int c1, uint64_t packed, uint32_t alive) {
    if (static_cast<int>((packed >> (c1 << 2)) & 0xFu) != 1) {
      addFundamental(packed, alive);
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
    addFundamental(packed, cmp == 0 ? (alive & 0x69u) : alive);
  }

  void onInteriorLeaf(int c0, uint64_t packed, uint32_t alive) {
    const int colM = static_cast<int>((packed >> (m << 2)) & 0xFu);
    const int colC0 = static_cast<int>((packed >> (c0 << 2)) & 0xFu);
    const int colMC0 = static_cast<int>((packed >> ((m - c0) << 2)) & 0xFu);
    const bool tied = (colM == c0 || colM == m - c0 ||
                       colC0 == 0 || colC0 == m ||
                       colMC0 == 0 || colMC0 == m);
    if (!tied) {
      addFundamental(packed, alive);
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
    addFundamental(packed, alive & canonMask);
  }

  // Fast specialized DFS once only a single D4 symmetry bit remains alive.
  template <bool Corner>
  void dfsSingle(int row, uint32_t col, uint32_t d1, uint32_t d2, int keyCol,
                 uint64_t packed, uint32_t aliveBit, const uint16_t* fm) {
    uint32_t avail = (rowMask[row] & fm[row]) & ~(col | d1 | d2);
    if (row == n - 2) {
      const uint32_t lastMask = rowMask[n - 1] & fm[n - 1];
      while (avail) {
        const uint32_t b = avail & (~avail + 1u);
        avail ^= b;
        const uint32_t col2 = col | b;
        const uint32_t last = lastMask & ~(col2 | ((d1 | b) << 1) | ((d2 | b) >> 1));
        if (last) {
          const uint64_t leafPacked = packed |
                                      (static_cast<uint64_t>(ctzBit(b)) << ((n - 2) << 2)) |
                                      (static_cast<uint64_t>(ctzBit(last)) << ((n - 1) << 2));
          if constexpr (Corner) onCornerLeaf(keyCol, leafPacked, aliveBit);
          else onInteriorLeaf(keyCol, leafPacked, aliveBit);
        }
      }
      return;
    }
    const int shift = row << 2;
    while (avail) {
      const uint32_t b = avail & (~avail + 1u);
      avail ^= b;
      dfsSingle<Corner>(row + 1, col | b, (d1 | b) << 1, (d2 | b) >> 1, keyCol,
                        packed | (static_cast<uint64_t>(ctzBit(b)) << shift), aliveBit, fm);
    }
  }

  template <bool Corner, bool HasHoles>
  void dfs(int row, uint32_t col, uint32_t d1, uint32_t d2, int keyCol, uint64_t packed, uint32_t alive) {
    uint32_t avail = rowMask[row] & ~(col | d1 | d2);
    if (row == n - 2) {
      const uint32_t lastMask = rowMask[n - 1];
      const uint8_t* km2 = killMask[n - 2];
      const uint8_t* km1 = killMask[n - 1];
      while (avail) {
        const uint32_t b = avail & (~avail + 1u);
        avail ^= b;
        const int c2 = ctzBit(b);
        uint32_t a2 = alive;
        if constexpr (HasHoles) {
          a2 &= ~static_cast<uint32_t>(km2[c2]);
          if (!a2) continue;
        }
        const uint32_t col2 = col | b;
        const uint32_t last = lastMask & ~(col2 | ((d1 | b) << 1) | ((d2 | b) >> 1));
        if (last) {
          const int cLast = ctzBit(last);
          uint32_t leafAlive = a2;
          if constexpr (HasHoles) {
            leafAlive &= ~static_cast<uint32_t>(km1[cLast]);
            if (!leafAlive) continue;
          }
          const uint64_t leafPacked = packed |
                                      (static_cast<uint64_t>(c2) << ((n - 2) << 2)) |
                                      (static_cast<uint64_t>(cLast) << ((n - 1) << 2));
          if constexpr (Corner) onCornerLeaf(keyCol, leafPacked, leafAlive);
          else onInteriorLeaf(keyCol, leafPacked, leafAlive);
        }
      }
      return;
    }
    const uint8_t* km = killMask[row];
    const int shift = row << 2;
    while (avail) {
      const uint32_t b = avail & (~avail + 1u);
      avail ^= b;
      const int c = ctzBit(b);
      if constexpr (HasHoles) {
        const uint32_t nextAlive = alive & ~static_cast<uint32_t>(km[c]);
        if (!nextAlive) continue;
        if ((nextAlive & (nextAlive - 1u)) == 0u) {
          dfsSingle<Corner>(row + 1, col | b, (d1 | b) << 1, (d2 | b) >> 1, keyCol,
                            packed | (static_cast<uint64_t>(c) << shift), nextAlive,
                            freeMask[ctzBit(nextAlive)]);
        } else {
          dfs<Corner, true>(row + 1, col | b, (d1 | b) << 1, (d2 | b) >> 1, keyCol,
                            packed | (static_cast<uint64_t>(c) << shift), nextAlive);
        }
      } else {
        dfs<Corner, false>(row + 1, col | b, (d1 | b) << 1, (d2 | b) >> 1, keyCol,
                           packed | (static_cast<uint64_t>(c) << shift), alive);
      }
    }
  }

  template <bool HasHoles>
  void runAll() {
    // Family 1: Corner queen at (0, 0).
    uint32_t a0 = 0xFFu;
    if constexpr (HasHoles) a0 &= ~static_cast<uint32_t>(killMask[0][0]);
    if (a0) {
      for (int c1 = 2; c1 < n; ++c1) {
        uint32_t a1 = a0;
        if constexpr (HasHoles) {
          a1 &= ~static_cast<uint32_t>(killMask[1][c1]);
          if (!a1) continue;
        }
        for (int r = 2; r < n; ++r) rowMask[r] = (r < c1) ? (full & ~2u) : full;
        const uint32_t b0 = 1u, b1 = 1u << c1;
        if constexpr (HasHoles) {
          if ((a1 & (a1 - 1u)) == 0u) {
            dfsSingle<true>(2, b0 | b1, ((b0 << 1) | b1) << 1, ((b0 >> 1) | b1) >> 1, c1,
                            static_cast<uint64_t>(c1) << 4, a1, freeMask[ctzBit(a1)]);
            continue;
          }
        }
        dfs<true, HasHoles>(2, b0 | b1, ((b0 << 1) | b1) << 1, ((b0 >> 1) | b1) >> 1, c1,
                            static_cast<uint64_t>(c1) << 4, a1);
      }
    }

    // Family 2: No corner queen; minimum border distance c0 at (0, c0).
    const uint32_t noSides = full & ~(1u | (1u << m));
    for (int c0 = 1; c0 <= (n - 2) / 2; ++c0) {
      uint32_t ac0 = 0xFFu;
      if constexpr (HasHoles) {
        ac0 &= ~static_cast<uint32_t>(killMask[0][c0]);
        if (!ac0) continue;
      }
      for (int r = 1; r < n - 1; ++r) rowMask[r] = (r < c0 || r >= n - c0) ? noSides : full;
      rowMask[n - 1] = ((1u << (n - 2 * c0)) - 1u) << c0;
      const uint32_t b0 = 1u << c0;
      if constexpr (HasHoles) {
        if ((ac0 & (ac0 - 1u)) == 0u) {
          dfsSingle<false>(1, b0, b0 << 1, b0 >> 1, c0, static_cast<uint64_t>(c0), ac0,
                           freeMask[ctzBit(ac0)]);
          continue;
        }
      }
      dfs<false, HasHoles>(1, b0, b0 << 1, b0 >> 1, c0, static_cast<uint64_t>(c0), ac0);
    }
  }
};

std::vector<std::vector<int>> solveD4Holes(int n, const std::vector<std::string>& grid, int holeCount) {
  if (n == 1) {
    if (holeCount > 0) return {};
    std::vector<std::vector<int>> out = {{0}};
    NQ_SNAPSHOT(nq::queensOf(out[0]), "solution 1");
    return out;
  }
  if (n < 4) return {};

  D4Holes solver;
  solver.n = n;
  solver.m = n - 1;
  solver.full = (1u << n) - 1u;

  if (holeCount == 0) {
    solver.runAll<false>();
  } else {
    const int m = n - 1;
    const uint16_t full16 = static_cast<uint16_t>(solver.full);
    for (int k = 0; k < 8; ++k) {
      for (int r = 0; r < n; ++r) solver.freeMask[k][r] = full16;
    }
    for (int hr = 0; hr < n; ++hr) {
      const std::string& row = grid[hr];
      for (int hc = 0; hc < n; ++hc) {
        if (row[hc] != 'H') continue;
        solver.killMask[hr][hc] |= 1u << 0;
        solver.freeMask[0][hr] &= static_cast<uint16_t>(~(1u << hc));

        solver.killMask[hr][m - hc] |= 1u << 1;
        solver.freeMask[1][hr] &= static_cast<uint16_t>(~(1u << (m - hc)));

        solver.killMask[m - hr][hc] |= 1u << 2;
        solver.freeMask[2][m - hr] &= static_cast<uint16_t>(~(1u << hc));

        solver.killMask[m - hr][m - hc] |= 1u << 3;
        solver.freeMask[3][m - hr] &= static_cast<uint16_t>(~(1u << (m - hc)));

        solver.killMask[hc][hr] |= 1u << 4;
        solver.freeMask[4][hc] &= static_cast<uint16_t>(~(1u << hr));

        solver.killMask[m - hc][hr] |= 1u << 5;
        solver.freeMask[5][m - hc] &= static_cast<uint16_t>(~(1u << hr));

        solver.killMask[hc][m - hr] |= 1u << 6;
        solver.freeMask[6][hc] &= static_cast<uint16_t>(~(1u << (m - hr)));

        solver.killMask[m - hc][m - hr] |= 1u << 7;
        solver.freeMask[7][m - hc] &= static_cast<uint16_t>(~(1u << (m - hr)));
      }
    }
    solver.runAll<true>();
  }

  std::vector<std::vector<int>> solutions;
  solutions.reserve(solver.totalSolutions);
  const bool debug = snapshotsEnabled();
  for (int i = 0; i < solver.stackCount; ++i) {
    const uint64_t entry = solver.stackBuf[i];
    const uint8_t mask = static_cast<uint8_t>(entry >> 48);
    emitD4Orbit(entry, mask, n, debug, solutions);
  }
  return solutions;
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

struct HolesSearch {
  int n = 0;
  int m = 0;
  uint32_t full = 0;
  uint32_t rowAllowed[kMaxN]{};
  uint32_t colAllowed[kMaxN]{};
  int remRows[kMaxN]{};

  static constexpr size_t kStackCap = 3072;
  uint64_t stackSols[kStackCap];
  size_t totalSolutions = 0;
  std::vector<std::vector<int>>* out = nullptr;
  bool debug = false;

  template <bool DirectEmit>
  inline void recordPacked(uint64_t packed) {
    if constexpr (DirectEmit) {
      emitPacked(packed, n, debug, *out);
    } else {
      if (totalSolutions < kStackCap) stackSols[totalSolutions] = packed;
      ++totalSolutions;
    }
  }

  inline uint32_t availRow(int r, uint32_t colMask, uint32_t diagSum, uint32_t diagDiffRow) const {
    return rowAllowed[r] & ~(colMask | (diagSum >> r) | (diagDiffRow >> (m - r)));
  }

  inline uint32_t availCol(int c, uint32_t rowMask, uint32_t diagSum, uint32_t diagDiffCol) const {
    return colAllowed[c] & ~(rowMask | (diagSum >> c) | (diagDiffCol >> (m - c)));
  }

  template <bool DirectEmit>
  void dfs(int rem, uint32_t rowMask, uint32_t colMask, uint32_t diagSum,
           uint32_t diagDiffRow, uint32_t diagDiffCol, uint64_t packed) {
    if (rem == 1) {
      const int r0 = remRows[0];
      const uint32_t a0 = availRow(r0, colMask, diagSum, diagDiffRow);
      if (a0) {
        recordPacked<DirectEmit>(packed | (static_cast<uint64_t>(ctzBit(a0)) << (r0 << 2)));
      }
      return;
    }
    if (rem == 2) {
      const int r0 = remRows[0], r1 = remRows[1];
      uint32_t a0 = availRow(r0, colMask, diagSum, diagDiffRow);
      if (!a0) return;
      const uint32_t a1Base = availRow(r1, colMask, diagSum, diagDiffRow);
      if (!a1Base) return;
      while (a0) {
        const uint32_t b0 = a0 & (~a0 + 1u);
        a0 ^= b0;
        const int c0 = ctzBit(b0);
        const uint32_t ds = diagSum | (1u << (r0 + c0));
        const uint32_t ddr = diagDiffRow | (1u << (c0 - r0 + m));
        const uint32_t a1 = a1Base & ~(b0 | (ds >> r1) | (ddr >> (m - r1)));
        if (a1) {
          recordPacked<DirectEmit>(packed | (static_cast<uint64_t>(c0) << (r0 << 2)) |
                                   (static_cast<uint64_t>(ctzBit(a1)) << (r1 << 2)));
        }
      }
      return;
    }

    uint32_t rowAvail[kMaxN];
    int bestRowIdx = -1;
    int bestCount = 32;
    uint32_t once = 0, twice = 0;

    for (int i = 0; i < rem; ++i) {
      const int r = remRows[i];
      const uint32_t a = availRow(r, colMask, diagSum, diagDiffRow);
      if (!a) return;
      rowAvail[i] = a;
      const int cnt = popcnt32(a);
      if (cnt < bestCount) {
        bestCount = cnt;
        bestRowIdx = i;
        if (cnt == 1) {
          const int c = ctzBit(a);
          remRows[i] = remRows[rem - 1];
          dfs<DirectEmit>(rem - 1, rowMask | (1u << r), colMask | a,
                          diagSum | (1u << (r + c)),
                          diagDiffRow | (1u << (c - r + m)),
                          diagDiffCol | (1u << (r - c + m)),
                          packed | (static_cast<uint64_t>(c) << (r << 2)));
          remRows[i] = r;
          return;
        }
      }
      twice |= (once & a);
      once |= a;
    }

    if ((once | colMask) != full) return;

    const uint32_t uniqueCols = once & ~twice;
    if (uniqueCols) {
      const uint32_t colBit = uniqueCols & (~uniqueCols + 1u);
      const int c = ctzBit(colBit);
      int idx = 0;
      while (!(rowAvail[idx] & colBit)) ++idx;
      const int r = remRows[idx];
      remRows[idx] = remRows[rem - 1];
      dfs<DirectEmit>(rem - 1, rowMask | (1u << r), colMask | colBit,
                      diagSum | (1u << (r + c)),
                      diagDiffRow | (1u << (c - r + m)),
                      diagDiffCol | (1u << (r - c + m)),
                      packed | (static_cast<uint64_t>(c) << (r << 2)));
      remRows[idx] = r;
      return;
    }

    int bestCol = -1;
    uint32_t bestColAvail = 0;
    if (bestCount >= 3) {
      uint32_t freeCols = full & ~colMask;
      while (freeCols) {
        const uint32_t cb = freeCols & (~freeCols + 1u);
        freeCols ^= cb;
        const int c = ctzBit(cb);
        const uint32_t ca = availCol(c, rowMask, diagSum, diagDiffCol);
        const int cnt = popcnt32(ca);
        if (cnt < bestCount) {
          bestCount = cnt;
          bestCol = c;
          bestColAvail = ca;
          if (cnt == 2) break;
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
        int idx = 0;
        while (remRows[idx] != r) ++idx;
        remRows[idx] = remRows[rem - 1];
        dfs<DirectEmit>(rem - 1, rowMask | rb, colMask | cb,
                        diagSum | (1u << (r + c)),
                        diagDiffRow | (1u << (c - r + m)),
                        diagDiffCol | (1u << (r - c + m)),
                        packed | (static_cast<uint64_t>(c) << (r << 2)));
        remRows[idx] = r;
      }
      return;
    }

    const int r = remRows[bestRowIdx];
    const uint32_t rb = 1u << r;
    uint32_t avail = rowAvail[bestRowIdx];
    remRows[bestRowIdx] = remRows[rem - 1];
    while (avail) {
      const uint32_t b = avail & (~avail + 1u);
      avail ^= b;
      const int c = ctzBit(b);
      dfs<DirectEmit>(rem - 1, rowMask | rb, colMask | b,
                      diagSum | (1u << (r + c)),
                      diagDiffRow | (1u << (c - r + m)),
                      diagDiffCol | (1u << (r - c + m)),
                      packed | (static_cast<uint64_t>(c) << (r << 2)));
    }
    remRows[bestRowIdx] = r;
  }
};

std::vector<std::vector<int>> solveHolesAlgX(int n, const uint32_t* rowAllowed,
                                             const uint32_t* colAllowed) {
  HolesSearch search;
  search.n = n;
  search.m = n - 1;
  search.full = (1u << n) - 1u;
  for (int i = 0; i < n; ++i) {
    search.rowAllowed[i] = rowAllowed[i];
    search.colAllowed[i] = colAllowed[i];
    search.remRows[i] = i;
  }
  search.dfs<false>(n, 0, 0, 0, 0, 0, 0);

  std::vector<std::vector<int>> solutions;
  solutions.reserve(search.totalSolutions);
  const bool debug = snapshotsEnabled();
  if (search.totalSolutions <= HolesSearch::kStackCap) {
    if (!debug) {
      int buf[kMaxN];
      for (size_t i = 0; i < search.totalSolutions; ++i) {
        const uint64_t packed = search.stackSols[i];
        for (int r = 0; r < n; ++r) buf[r] = static_cast<int>((packed >> (r << 2)) & 0xFu);
        solutions.emplace_back(buf, buf + n);
      }
    } else {
      for (size_t i = 0; i < search.totalSolutions; ++i) {
        emitPacked(search.stackSols[i], n, true, solutions);
      }
    }
  } else {
    search.out = &solutions;
    search.debug = debug;
    for (int r = 0; r < n; ++r) search.remRows[r] = r;
    search.dfs<true>(n, 0, 0, 0, 0, 0, 0);
  }
  return solutions;
}

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
    uint32_t mask = 0;
    for (int c = 0; c < n; ++c) {
      if (grid[r][c] == 'H') {
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

  if (holeCount == 0 && n <= 12) return solveD4Holes(n, grid, 0);
  if (minLineFree < (n + 1) / 2 && !hasPerfectMatching(n, rowAllowed)) return {};

  if (n <= 12 && minLineFree >= 3 && holeCount * 3 <= n * n) {
    return solveD4Holes(n, grid, holeCount);
  }

  return solveHolesAlgX(n, rowAllowed, colAllowed);
}
