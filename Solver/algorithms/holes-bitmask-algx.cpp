// Solver for the Holes case: Hall matching pre-check + adaptive shift bitmask / bidirectional Bitmask Algorithm X.
//
// ---- Mode & entry point --------------------------------------------------------------------------------------------
//   solveHoles(n, grid)    Holes case: grid[r][c] is '.' (free) or 'H' (hole). Queens cannot stand on a hole,
//                          but attacks pass straight through it. Every row must hold one queen.
//
// ---- The idea ------------------------------------------------------------------------------------------------------
// A board with holes is solved with three fast regimes depending on hole density:
//
//   H == 0   No holes at all: 8-fold D4 canonical border-symmetry bitmask search solves the Normal board directly.
//   Feasibility check (H > 0): Every row and column needs a distinct free cell, so an O(N^2) bitmask Kuhn bipartite
//            matching test immediately rejects unsolvable boards that fail Hall's marriage condition.
//   Sparse   When holes are few and every row/column remains wide open, pure shift-bitmask DFS (choosing the tightest
//            of the 4 board orientations: top-down, bottom-up, left-right, right-left) avoids MRV scan overhead.
//   General  Bidirectional Bitmask Algorithm X tracks both row and column availability in O(1) via three diagonal
//            bitmasks, combining row/column forward checking, forced-row and hidden-single-column unit propagation,
//            bidirectional MRV branching (picking the tightest row OR column), and last-two-rows unrolling.
#include <cstdint>
#include <string>
#include <vector>

#include "nqueens.h"

namespace {  // names in here belong to this file only

constexpr int kMaxN = 16;

struct Fundamental {
  uint8_t cols[kMaxN];
  uint8_t mask;
};

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

// Fast D4 canonical symmetry solver used when H == 0.
struct NormalD4 {
  int n = 0, m = 0;
  uint32_t full = 0;
  uint32_t rowMask[kMaxN]{};
  uint8_t cols[kMaxN]{};
  static constexpr int kStackCap = 2048;
  Fundamental stackBuf[kStackCap];
  int stackCount = 0;
  std::vector<Fundamental> heapBuf;
  size_t totalSolutions = 0;

  void addFundamental(uint8_t mask, int orbitSize) {
    Fundamental f;
    for (int r = 0; r < n; ++r) f.cols[r] = cols[r];
    f.mask = mask;
    if (stackCount < kStackCap) stackBuf[stackCount++] = f;
    else heapBuf.push_back(f);
    totalSolutions += static_cast<size_t>(orbitSize);
  }

  void onCornerLeaf(int c1) {
    if (cols[c1] != 1) { addFundamental(0xFFu, 8); return; }
    uint8_t inv[kMaxN];
    for (int r = 0; r < n; ++r) inv[cols[r]] = static_cast<uint8_t>(r);
    const int c = cmpBoard(cols, inv, n);
    if (c > 0) return;
    addFundamental(c == 0 ? 0x69u : 0xFFu, c == 0 ? 4 : 8);
  }

  void onInteriorLeaf(int c0) {
    const bool tied = (cols[m] == c0 || cols[m] == m - c0 ||
                       cols[c0] == 0 || cols[c0] == m ||
                       cols[m - c0] == 0 || cols[m - c0] == m);
    if (!tied) { addFundamental(0xFFu, 8); return; }
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
    addFundamental(mask, orbitSize);
  }

  template <bool Corner>
  void dfs(int row, uint32_t col, uint32_t d1, uint32_t d2, int keyCol) {
    uint32_t avail = rowMask[row] & ~(col | d1 | d2);
    if (row == n - 2) {
      const uint32_t lastMask = rowMask[n - 1];
      while (avail) {
        const uint32_t b = avail & -avail;
        avail ^= b;
        const uint32_t c2 = col | b;
        const uint32_t last = lastMask & ~(c2 | ((d1 | b) << 1) | ((d2 | b) >> 1));
        if (last) {
          cols[n - 2] = static_cast<uint8_t>(__builtin_ctz(b));
          cols[n - 1] = static_cast<uint8_t>(__builtin_ctz(last));
          if constexpr (Corner) onCornerLeaf(keyCol);
          else onInteriorLeaf(keyCol);
        }
      }
      return;
    }
    while (avail) {
      const uint32_t b = avail & -avail;
      avail ^= b;
      cols[row] = static_cast<uint8_t>(__builtin_ctz(b));
      dfs<Corner>(row + 1, col | b, (d1 | b) << 1, (d2 | b) >> 1, keyCol);
    }
  }

  std::vector<std::vector<int>> solve(int size) {
    if (size == 1) {
      std::vector<std::vector<int>> out = {{0}};
      NQ_SNAPSHOT(nq::queensOf(out[0]), "solution 1");
      return out;
    }
    if (size < 4) return {};
    n = size; m = size - 1; full = (1u << n) - 1u;

    cols[0] = 0;
    for (int c1 = 2; c1 < n; ++c1) {
      cols[1] = static_cast<uint8_t>(c1);
      for (int r = 2; r < n; ++r) rowMask[r] = (r < c1) ? (full & ~2u) : full;
      const uint32_t b0 = 1u, b1 = 1u << c1;
      dfs<true>(2, b0 | b1, ((b0 << 1) | b1) << 1, ((b0 >> 1) | b1) >> 1, c1);
    }

    const uint32_t noSides = full & ~(1u | (1u << m));
    for (int c0 = 1; c0 <= (n - 2) / 2; ++c0) {
      cols[0] = static_cast<uint8_t>(c0);
      for (int r = 1; r < n - 1; ++r) rowMask[r] = (r < c0 || r >= n - c0) ? noSides : full;
      rowMask[n - 1] = ((1u << (n - 2 * c0)) - 1u) << c0;
      const uint32_t b0 = 1u << c0;
      dfs<false>(1, b0, b0 << 1, b0 >> 1, c0);
    }

    std::vector<std::vector<int>> solutions;
    solutions.reserve(totalSolutions);
    const bool debug = snapshotsEnabled();
    auto emit = [&](const Fundamental& f) {
      uint8_t tmp[kMaxN];
      int buf[kMaxN];
      for (int k = 0; k < 8; ++k) {
        if (!((f.mask >> k) & 1u)) continue;
        applyD4(k, f.cols, tmp, n);
        for (int r = 0; r < n; ++r) buf[r] = tmp[r];
        solutions.emplace_back(buf, buf + n);
        if (__builtin_expect(debug, 0)) {
          snapshot(nq::queensOf(solutions.back()), "solution " + std::to_string(solutions.size()));
        }
      }
    };
    for (int i = 0; i < stackCount; ++i) emit(stackBuf[i]);
    for (const auto& f : heapBuf) emit(f);
    return solutions;
  }
};

// O(N^2) Kuhn's algorithm using bitmasks to test whether rows and columns admit a perfect matching.
bool hasPerfectMatching(int n, const uint32_t* rowAllowed) {
  int colOwner[kMaxN];
  for (int c = 0; c < n; ++c) colOwner[c] = -1;

  auto augment = [&](auto& self, int r, uint32_t& visited) -> bool {
    uint32_t cand = rowAllowed[r] & ~visited;
    while (cand) {
      const uint32_t b = cand & -cand;
      cand ^= b;
      const int c = __builtin_ctz(b);
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

struct CompactSol {
  uint8_t cols[kMaxN];
};

struct HolesSearch {
  int n = 0;
  int m = 0;
  uint32_t full = 0;
  uint32_t rowAllowed[kMaxN]{};
  uint32_t colAllowed[kMaxN]{};
  uint8_t cols[kMaxN]{};
  int remRows[kMaxN]{};

  static constexpr int kStackCap = 2048;
  CompactSol stackSols[kStackCap];
  int stackCount = 0;
  std::vector<CompactSol> heapSols;

  inline void record() {
    CompactSol s;
    for (int r = 0; r < n; ++r) s.cols[r] = cols[r];
    if (stackCount < kStackCap) stackSols[stackCount++] = s;
    else heapSols.push_back(s);
  }

  inline uint32_t availRow(int r, uint32_t colMask, uint32_t diagSum, uint32_t diagDiffRow) const {
    return rowAllowed[r] & ~(colMask | (diagSum >> r) | (diagDiffRow >> (m - r)));
  }

  inline uint32_t availCol(int c, uint32_t rowMask, uint32_t diagSum, uint32_t diagDiffCol) const {
    return colAllowed[c] & ~(rowMask | (diagSum >> c) | (diagDiffCol >> (m - c)));
  }

  // Bidirectional Bitmask Algorithm X:
  //   diagSum     bit (r + c)
  //   diagDiffRow bit (c - r + n - 1) -> row r attacked columns = diagDiffRow >> (n - 1 - r)
  //   diagDiffCol bit (r - c + n - 1) -> col c attacked rows    = diagDiffCol >> (n - 1 - c)
  void dfs(int rem, uint32_t rowMask, uint32_t colMask, uint32_t diagSum,
           uint32_t diagDiffRow, uint32_t diagDiffCol) {
    if (rem == 1) {
      const int r0 = remRows[0];
      const uint32_t a0 = availRow(r0, colMask, diagSum, diagDiffRow);
      if (a0) {
        cols[r0] = static_cast<uint8_t>(__builtin_ctz(a0));
        record();
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
        const uint32_t b0 = a0 & -a0;
        a0 ^= b0;
        const int c0 = __builtin_ctz(b0);
        const uint32_t ds = diagSum | (1u << (r0 + c0));
        const uint32_t ddr = diagDiffRow | (1u << (c0 - r0 + m));
        const uint32_t a1 = a1Base & ~(b0 | (ds >> r1) | (ddr >> (m - r1)));
        if (a1) {
          cols[r0] = static_cast<uint8_t>(c0);
          cols[r1] = static_cast<uint8_t>(__builtin_ctz(a1));
          record();
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
      const int cnt = __builtin_popcount(a);
      if (cnt < bestCount) {
        bestCount = cnt;
        bestRowIdx = i;
        if (cnt == 1) {
          const int c = __builtin_ctz(a);
          cols[r] = static_cast<uint8_t>(c);
          remRows[i] = remRows[rem - 1];
          dfs(rem - 1, rowMask | (1u << r), colMask | a,
              diagSum | (1u << (r + c)),
              diagDiffRow | (1u << (c - r + m)),
              diagDiffCol | (1u << (r - c + m)));
          remRows[i] = r;
          return;
        }
      }
      twice |= (once & a);
      once |= a;
    }

    // Column forward checking: every free column must remain reachable.
    if ((once | colMask) != full) return;

    // Hidden single column: a free column reachable by only one row forces that placement.
    const uint32_t uniqueCols = once & ~twice;
    if (uniqueCols) {
      const uint32_t colBit = uniqueCols & -uniqueCols;
      const int c = __builtin_ctz(colBit);
      int idx = 0;
      while (!(rowAvail[idx] & colBit)) ++idx;
      const int r = remRows[idx];
      cols[r] = static_cast<uint8_t>(c);
      remRows[idx] = remRows[rem - 1];
      dfs(rem - 1, rowMask | (1u << r), colMask | colBit,
          diagSum | (1u << (r + c)),
          diagDiffRow | (1u << (c - r + m)),
          diagDiffCol | (1u << (r - c + m)));
      remRows[idx] = r;
      return;
    }

    // If the tightest row has >= 3 candidates, check columns for a tighter MRV branch.
    int bestCol = -1;
    uint32_t bestColAvail = 0;
    if (bestCount >= 3) {
      uint32_t freeCols = full & ~colMask;
      while (freeCols) {
        const uint32_t cb = freeCols & -freeCols;
        freeCols ^= cb;
        const int c = __builtin_ctz(cb);
        const uint32_t ca = availCol(c, rowMask, diagSum, diagDiffCol);
        const int cnt = __builtin_popcount(ca);
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
        const uint32_t rb = avail & -avail;
        avail ^= rb;
        const int r = __builtin_ctz(rb);
        int idx = 0;
        while (remRows[idx] != r) ++idx;
        cols[r] = static_cast<uint8_t>(c);
        remRows[idx] = remRows[rem - 1];
        dfs(rem - 1, rowMask | rb, colMask | cb,
            diagSum | (1u << (r + c)),
            diagDiffRow | (1u << (c - r + m)),
            diagDiffCol | (1u << (r - c + m)));
        remRows[idx] = r;
      }
      return;
    }

    const int r = remRows[bestRowIdx];
    const uint32_t rb = 1u << r;
    uint32_t avail = rowAvail[bestRowIdx];
    remRows[bestRowIdx] = remRows[rem - 1];
    while (avail) {
      const uint32_t b = avail & -avail;
      avail ^= b;
      const int c = __builtin_ctz(b);
      cols[r] = static_cast<uint8_t>(c);
      dfs(rem - 1, rowMask | rb, colMask | b,
          diagSum | (1u << (r + c)),
          diagDiffRow | (1u << (c - r + m)),
          diagDiffCol | (1u << (r - c + m)));
    }
    remRows[bestRowIdx] = r;
  }

  uint32_t shiftAllowed[kMaxN]{};

  // Pure shift bitmask search for sparse boards.
  // Orientations: 0 = rows top-down, 1 = rows bottom-up, 2 = cols left-to-right, 3 = cols right-to-left.
  template <int Orient>
  void dfsShift(int step, uint32_t used, uint32_t d1, uint32_t d2) {
    uint32_t avail = shiftAllowed[step] & ~(used | d1 | d2);
    if (step == n - 2) {
      const uint32_t lastAllowed = shiftAllowed[n - 1];
      while (avail) {
        const uint32_t b = avail & -avail;
        avail ^= b;
        const uint32_t last = lastAllowed & ~((used | b) | ((d1 | b) << 1) | ((d2 | b) >> 1));
        if (last) {
          const uint8_t v0 = static_cast<uint8_t>(__builtin_ctz(b));
          const uint8_t v1 = static_cast<uint8_t>(__builtin_ctz(last));
          if constexpr (Orient == 0) {
            cols[n - 2] = v0;
            cols[n - 1] = v1;
          } else if constexpr (Orient == 1) {
            cols[1] = v0;
            cols[0] = v1;
          } else if constexpr (Orient == 2) {
            cols[v0] = static_cast<uint8_t>(n - 2);
            cols[v1] = static_cast<uint8_t>(n - 1);
          } else {
            cols[v0] = 1;
            cols[v1] = 0;
          }
          record();
        }
      }
      return;
    }
    while (avail) {
      const uint32_t b = avail & -avail;
      avail ^= b;
      const uint8_t v = static_cast<uint8_t>(__builtin_ctz(b));
      if constexpr (Orient == 0) {
        cols[step] = v;
      } else if constexpr (Orient == 1) {
        cols[m - step] = v;
      } else if constexpr (Orient == 2) {
        cols[v] = static_cast<uint8_t>(step);
      } else {
        cols[v] = static_cast<uint8_t>(m - step);
      }
      dfsShift<Orient>(step + 1, used | b, (d1 | b) << 1, (d2 | b) >> 1);
    }
  }

  std::vector<std::vector<int>> materialize() const {
    const size_t total = static_cast<size_t>(stackCount) + heapSols.size();
    std::vector<std::vector<int>> solutions;
    solutions.reserve(total);
    const bool debug = snapshotsEnabled();
    int buf[kMaxN];
    auto emit = [&](const CompactSol& s) {
      for (int r = 0; r < n; ++r) buf[r] = s.cols[r];
      solutions.emplace_back(buf, buf + n);
      if (__builtin_expect(debug, 0)) {
        snapshot(nq::queensOf(solutions.back()), "solution " + std::to_string(solutions.size()));
      }
    };
    for (int i = 0; i < stackCount; ++i) emit(stackSols[i]);
    for (const auto& s : heapSols) emit(s);
    return solutions;
  }
};

}  // namespace

std::vector<std::vector<int>> solveHoles(int n, const std::vector<std::string>& grid) {
  if (n <= 0 || n > kMaxN || static_cast<int>(grid.size()) != n) return {};
  for (const auto& line : grid) {
    if (static_cast<int>(line.size()) != n) return {};
  }

  HolesSearch search;
  search.n = n;
  search.m = n - 1;
  search.full = (1u << n) - 1u;

  int holeCount = 0;
  int minLineFree = n;
  for (int r = 0; r < n; ++r) {
    uint32_t mask = 0;
    for (int c = 0; c < n; ++c) {
      if (grid[r][c] == 'H') {
        ++holeCount;
      } else {
        mask |= (1u << c);
        search.colAllowed[c] |= (1u << r);
      }
    }
    if (mask == 0) return {};
    search.rowAllowed[r] = mask;
    const int cnt = __builtin_popcount(mask);
    if (cnt < minLineFree) minLineFree = cnt;
  }
  for (int c = 0; c < n; ++c) {
    if (search.colAllowed[c] == 0) return {};
    const int cnt = __builtin_popcount(search.colAllowed[c]);
    if (cnt < minLineFree) minLineFree = cnt;
  }

  if (holeCount == 0) {
    NormalD4 normal;
    return normal.solve(n);
  }

  if (!hasPerfectMatching(n, search.rowAllowed)) return {};

  // Sparse boards with wide-open lines use pure shift bitmask in the most constrained orientation.
  if (n >= 4 && holeCount * 5 < n * n && minLineFree >= n - 3) {
    const int m = n - 1;
    auto score = [&](int orient) -> int {
      auto lineAt = [&](int s) -> uint32_t {
        if (orient == 0) return search.rowAllowed[s];
        if (orient == 1) return search.rowAllowed[m - s];
        if (orient == 2) return search.colAllowed[s];
        return search.colAllowed[m - s];
      };
      return 4 * __builtin_popcount(lineAt(0)) + 2 * __builtin_popcount(lineAt(1)) + __builtin_popcount(lineAt(2));
    };
    int bestOrient = 0, bestScore = score(0);
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
    if (bestOrient == 0) search.dfsShift<0>(0, 0, 0, 0);
    else if (bestOrient == 1) search.dfsShift<1>(0, 0, 0, 0);
    else if (bestOrient == 2) search.dfsShift<2>(0, 0, 0, 0);
    else search.dfsShift<3>(0, 0, 0, 0);
    return search.materialize();
  }

  for (int r = 0; r < n; ++r) search.remRows[r] = r;
  search.dfs(n, 0, 0, 0, 0, 0);
  return search.materialize();
}
