// Solver for the Holes case: 64KB-stack-safe 4-bit packed buffers + zero-aux-heap two-pass spill
// + Hall matching pre-check + adaptive shift bitmask / bidirectional Bitmask Algorithm X.
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

inline int ctz32(uint32_t x) {
#if __cplusplus >= 202002L
  return std::countr_zero(x);
#else
  return popcnt32((x & (~x + 1u)) - 1u);
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

inline uint64_t packCols(const uint8_t* cols, int n) {
  uint64_t p = 0;
  for (int r = 0; r < n; ++r) p |= static_cast<uint64_t>(cols[r]) << (r << 2);
  return p;
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

// Fast 64KB-safe D4 canonical symmetry solver used when H == 0 (~18 KB stack, 0 B aux heap for N <= 12).
struct NormalD4 {
  int n = 0, m = 0;
  uint32_t full = 0;
  uint32_t rowMask[kMaxN]{};
  uint8_t cols[kMaxN]{};
  static constexpr int kStackCap = 2048;
  uint64_t stackCols[kStackCap];
  uint8_t stackMask[kStackCap];
  int stackCount = 0;
  size_t totalSolutions = 0;
  std::vector<std::vector<int>>* out = nullptr;
  bool debug = false;

  template <bool DirectEmit>
  inline void addFundamental(uint8_t mask, int orbitSize) {
    const uint64_t packed = packCols(cols, n);
    if constexpr (DirectEmit) {
      emitD4Orbit(packed, mask, n, debug, *out);
    } else {
      if (stackCount < kStackCap) {
        stackCols[stackCount] = packed;
        stackMask[stackCount] = mask;
        ++stackCount;
      } else {
        ++stackCount;
      }
      totalSolutions += static_cast<size_t>(orbitSize);
    }
  }

  template <bool DirectEmit>
  void onCornerLeaf(int c1) {
    if (cols[c1] != 1) { addFundamental<DirectEmit>(0xFFu, 8); return; }
    uint8_t inv[kMaxN];
    for (int r = 0; r < n; ++r) inv[cols[r]] = static_cast<uint8_t>(r);
    const int c = cmpBoard(cols, inv, n);
    if (c > 0) return;
    addFundamental<DirectEmit>(c == 0 ? 0x69u : 0xFFu, c == 0 ? 4 : 8);
  }

  template <bool DirectEmit>
  void onInteriorLeaf(int c0) {
    const bool tied = (cols[m] == c0 || cols[m] == m - c0 ||
                       cols[c0] == 0 || cols[c0] == m ||
                       cols[m - c0] == 0 || cols[m - c0] == m);
    if (!tied) { addFundamental<DirectEmit>(0xFFu, 8); return; }
    uint8_t imgs[8][kMaxN];
    for (int r = 0; r < n; ++r) imgs[0][r] = cols[r];
    for (int k = 1; k < 8; ++k) {
      applyD4(k, cols, imgs[k], n);
      if (cmpBoard(imgs[k], imgs[0], n) < 0) return;
    }
    uint8_t mask = 1u;
    int orbitSize = 1;
    for (int k = 1; k < 8; ++k) {
      bool dup = false;
      for (int j = 0; j < k; ++j) {
        if (((mask >> j) & 1u) && cmpBoard(imgs[k], imgs[j], n) == 0) { dup = true; break; }
      }
      if (!dup) { mask |= static_cast<uint8_t>(1u << k); ++orbitSize; }
    }
    addFundamental<DirectEmit>(mask, orbitSize);
  }

  template <bool Corner, bool DirectEmit>
  void dfs(int row, uint32_t col, uint32_t d1, uint32_t d2, int keyCol) {
    uint32_t avail = rowMask[row] & ~(col | d1 | d2);
    if (row == n - 2) {
      const uint32_t lastMask = rowMask[n - 1];
      while (avail) {
        const uint32_t b = avail & (~avail + 1u);
        avail ^= b;
        const uint32_t c2 = col | b;
        const uint32_t last = lastMask & ~(c2 | ((d1 | b) << 1) | ((d2 | b) >> 1));
        if (last) {
          cols[n - 2] = static_cast<uint8_t>(ctzBit(b));
          cols[n - 1] = static_cast<uint8_t>(ctzBit(last));
          if constexpr (Corner) onCornerLeaf<DirectEmit>(keyCol);
          else onInteriorLeaf<DirectEmit>(keyCol);
        }
      }
      return;
    }
    while (avail) {
      const uint32_t b = avail & (~avail + 1u);
      avail ^= b;
      cols[row] = static_cast<uint8_t>(ctzBit(b));
      dfs<Corner, DirectEmit>(row + 1, col | b, (d1 | b) << 1, (d2 | b) >> 1, keyCol);
    }
  }

  template <bool DirectEmit>
  void runAll() {
    cols[0] = 0;
    for (int c1 = 2; c1 < n; ++c1) {
      cols[1] = static_cast<uint8_t>(c1);
      for (int r = 2; r < n; ++r) rowMask[r] = (r < c1) ? (full & ~2u) : full;
      const uint32_t b0 = 1u, b1 = 1u << c1;
      dfs<true, DirectEmit>(2, b0 | b1, ((b0 << 1) | b1) << 1, ((b0 >> 1) | b1) >> 1, c1);
    }

    const uint32_t noSides = full & ~(1u | (1u << m));
    for (int c0 = 1; c0 <= (n - 2) / 2; ++c0) {
      cols[0] = static_cast<uint8_t>(c0);
      for (int r = 1; r < n - 1; ++r) rowMask[r] = (r < c0 || r >= n - c0) ? noSides : full;
      rowMask[n - 1] = ((1u << (n - 2 * c0)) - 1u) << c0;
      const uint32_t b0 = 1u << c0;
      dfs<false, DirectEmit>(1, b0, b0 << 1, b0 >> 1, c0);
    }
  }
};

std::vector<std::vector<int>> solveNormalD4(int size) {
  if (size == 1) {
    std::vector<std::vector<int>> out = {{0}};
    NQ_SNAPSHOT(nq::queensOf(out[0]), "solution 1");
    return out;
  }
  if (size < 4) return {};
  NormalD4 normal;
  normal.n = size;
  normal.m = size - 1;
  normal.full = (1u << size) - 1u;
  normal.runAll<false>();

  std::vector<std::vector<int>> solutions;
  solutions.reserve(normal.totalSolutions);
  const bool debug = snapshotsEnabled();
  if (normal.stackCount <= NormalD4::kStackCap) {
    for (int i = 0; i < normal.stackCount; ++i) {
      emitD4Orbit(normal.stackCols[i], normal.stackMask[i], size, debug, solutions);
    }
  } else {
    normal.out = &solutions;
    normal.debug = debug;
    normal.runAll<true>();
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

// 64KB-safe HolesSearch: 24 KB 4-bit packed stack buffer + zero-aux-heap two-pass direct-emit on spill.
struct HolesSearch {
  int n = 0;
  int m = 0;
  uint32_t full = 0;
  uint32_t rowAllowed[kMaxN]{};
  uint32_t colAllowed[kMaxN]{};
  uint32_t shiftAllowed[kMaxN]{};
  int remRows[kMaxN]{};

  static constexpr size_t kStackCap = 3072;  // 24 KB on stack (covers 100% of N <= 11)
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
        const uint64_t c0 = static_cast<uint64_t>(ctzBit(a0));
        recordPacked<DirectEmit>(packed | (c0 << (r0 << 2)));
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
          const uint64_t p = packed | (static_cast<uint64_t>(c0) << (r0 << 2)) |
                             (static_cast<uint64_t>(ctzBit(a1)) << (r1 << 2));
          recordPacked<DirectEmit>(p);
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

  template <int Orient, bool DirectEmit>
  void dfsShift(int step, uint32_t used, uint32_t d1, uint32_t d2, uint64_t packed) {
    uint32_t avail = shiftAllowed[step] & ~(used | d1 | d2);
    if (step == n - 2) {
      const uint32_t lastAllowed = shiftAllowed[n - 1];
      while (avail) {
        const uint32_t b = avail & (~avail + 1u);
        avail ^= b;
        const uint32_t last = lastAllowed & ~((used | b) | ((d1 | b) << 1) | ((d2 | b) >> 1));
        if (last) {
          const int v0 = ctzBit(b);
          const int v1 = ctzBit(last);
          uint64_t p = packed;
          if constexpr (Orient == 0) {
            p |= (static_cast<uint64_t>(v0) << ((n - 2) << 2)) | (static_cast<uint64_t>(v1) << ((n - 1) << 2));
          } else if constexpr (Orient == 1) {
            p |= (static_cast<uint64_t>(v0) << 4) | static_cast<uint64_t>(v1);
          } else if constexpr (Orient == 2) {
            p |= (static_cast<uint64_t>(n - 2) << (v0 << 2)) | (static_cast<uint64_t>(n - 1) << (v1 << 2));
          } else {
            p |= (static_cast<uint64_t>(1) << (v0 << 2));
          }
          recordPacked<DirectEmit>(p);
        }
      }
      return;
    }
    while (avail) {
      const uint32_t b = avail & (~avail + 1u);
      avail ^= b;
      const int v = ctzBit(b);
      uint64_t nextPacked = packed;
      if constexpr (Orient == 0) {
        nextPacked |= static_cast<uint64_t>(v) << (step << 2);
      } else if constexpr (Orient == 1) {
        nextPacked |= static_cast<uint64_t>(v) << ((m - step) << 2);
      } else if constexpr (Orient == 2) {
        nextPacked |= static_cast<uint64_t>(step) << (v << 2);
      } else {
        nextPacked |= static_cast<uint64_t>(m - step) << (v << 2);
      }
      dfsShift<Orient, DirectEmit>(step + 1, used | b, (d1 | b) << 1, (d2 | b) >> 1, nextPacked);
    }
  }

  template <bool DirectEmit>
  void runShift(int bestOrient) {
    if (bestOrient == 0) dfsShift<0, DirectEmit>(0, 0, 0, 0, 0);
    else if (bestOrient == 1) dfsShift<1, DirectEmit>(0, 0, 0, 0, 0);
    else if (bestOrient == 2) dfsShift<2, DirectEmit>(0, 0, 0, 0, 0);
    else dfsShift<3, DirectEmit>(0, 0, 0, 0, 0);
  }
};

std::vector<std::vector<int>> solveHolesGeneral(int n, const uint32_t* rowAllowed,
                                                const uint32_t* colAllowed, int holeCount,
                                                int minLineFree) {
  HolesSearch search;
  search.n = n;
  search.m = n - 1;
  search.full = (1u << n) - 1u;
  for (int i = 0; i < n; ++i) {
    search.rowAllowed[i] = rowAllowed[i];
    search.colAllowed[i] = colAllowed[i];
  }

  const bool useShift = (n >= 4 && holeCount * 5 < n * n && minLineFree >= n - 3);
  int bestOrient = 0;
  if (useShift) {
    const int m = n - 1;
    auto score = [&](int orient) -> int {
      auto lineAt = [&](int s) -> uint32_t {
        if (orient == 0) return search.rowAllowed[s];
        if (orient == 1) return search.rowAllowed[m - s];
        if (orient == 2) return search.colAllowed[s];
        return search.colAllowed[m - s];
      };
      return 4 * popcnt32(lineAt(0)) + 2 * popcnt32(lineAt(1)) + popcnt32(lineAt(2));
    };
    int bestScore = score(0);
    for (int o = 1; o < 4; ++o) {
      const int sc = score(o);
      if (sc < bestScore) { bestScore = sc; bestOrient = o; }
    }
    for (int s = 0; s < n; ++s) {
      if (bestOrient == 0) search.shiftAllowed[s] = search.rowAllowed[s];
      else if (bestOrient == 1) search.shiftAllowed[s] = search.rowAllowed[m - s];
      else if (bestOrient == 2) search.shiftAllowed[s] = search.colAllowed[s];
      else search.shiftAllowed[s] = search.colAllowed[m - s];
    }
    search.runShift<false>(bestOrient);
  } else {
    for (int r = 0; r < n; ++r) search.remRows[r] = r;
    search.dfs<false>(n, 0, 0, 0, 0, 0, 0);
  }

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
    if (useShift) {
      search.runShift<true>(bestOrient);
    } else {
      for (int r = 0; r < n; ++r) search.remRows[r] = r;
      search.dfs<true>(n, 0, 0, 0, 0, 0, 0);
    }
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

  if (holeCount == 0) return solveNormalD4(n);
  if (n == 1) return {};
  if (n < 4) return {};
  if (minLineFree < (n + 1) / 2 && !hasPerfectMatching(n, rowAllowed)) return {};

  return solveHolesGeneral(n, rowAllowed, colAllowed, holeCount, minLineFree);
}
