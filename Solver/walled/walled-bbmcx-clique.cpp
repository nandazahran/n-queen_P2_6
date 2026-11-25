// Solver for the Walled case: component-decomposed bitset Maximum Independent Set enumeration (BBMCX +
// geometric segment clique-cover bounds).
//
// ---- Mode & entry point --------------------------------------------------------------------------------------------
//   solveWalled(n, grid)    Walled case: grid[r][c] is '.' (free) or 'W' (wall). Queens cannot stand on a wall,
//                           and attacks stop at any wall between them. Returns every board that holds the
//                           largest possible number of queens, as lists of (row, column).
//
// ---- The idea ------------------------------------------------------------------------------------------------------
// Two queens may stand together iff they do not attack each other, so every valid board is an independent set of the
// walled attack graph (equivalently, a clique of its complement). This solver enumerates all maximum independent sets:
//
//   1. Zero-wall fast path: when there are no walls (N >= 4), the answer is exactly the Normal N-Queens solutions,
//      computed with 8-fold D4 canonical border-symmetry bitmask search.
//   2. O(N^2) graph construction: walls split each row, column, and diagonal into independent line segments, building
//      the conflict bitsets in linear time per cell.
//   3. Connected-component decomposition: isolated cells are mandatory in every optimal board; clique components
//      contribute one queen per vertex in O(1); remaining components are solved independently and combined via
//      Cartesian product.
//   4. Exact BBMCX search per component: uses template-specialized fixed-width bitsets (1..4 uint64_t words), a
//      multi-start min-conflict-degree greedy + 1-2 swap local search for an instant lower bound, and a hybrid
//      upper bound combining row-segment cover, column-segment cover, and bitset greedy clique cover with 1-vertex
//      recoloring (Tomita/Segundo) and minimum-branching-set pigeonhole branching.
#include <algorithm>
#include <array>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "nqueens.h"

namespace {  // names in here belong to this file only

using Cell = std::pair<int, int>;
using Board = std::vector<Cell>;

// ---- Fast path for W == 0, N >= 4 (8-fold D4 Normal N-Queens) ------------------------------------------------------

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

std::vector<Board> solveNoWalls(int size) {
  int n = size, m = size - 1;
  uint32_t full = (1u << n) - 1u;
  uint32_t rowMask[kMaxN]{};
  uint8_t cols[kMaxN]{};
  static constexpr int kStackCap = 2048;
  Fundamental stackBuf[kStackCap];
  int stackCount = 0;
  std::vector<Fundamental> heapBuf;
  size_t totalSolutions = 0;

  auto addFund = [&](uint8_t mask, int orbitSize) {
    Fundamental f;
    for (int r = 0; r < n; ++r) f.cols[r] = cols[r];
    f.mask = mask;
    if (stackCount < kStackCap) stackBuf[stackCount++] = f;
    else heapBuf.push_back(f);
    totalSolutions += static_cast<size_t>(orbitSize);
  };

  auto onCorner = [&](int c1) {
    if (cols[c1] != 1) { addFund(0xFFu, 8); return; }
    uint8_t inv[kMaxN];
    for (int r = 0; r < n; ++r) inv[cols[r]] = static_cast<uint8_t>(r);
    const int c = cmpBoard(cols, inv, n);
    if (c > 0) return;
    addFund(c == 0 ? 0x69u : 0xFFu, c == 0 ? 4 : 8);
  };

  auto onInterior = [&](int c0) {
    const bool tied = (cols[m] == c0 || cols[m] == m - c0 ||
                       cols[c0] == 0 || cols[c0] == m ||
                       cols[m - c0] == 0 || cols[m - c0] == m);
    if (!tied) { addFund(0xFFu, 8); return; }
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
    addFund(mask, orbitSize);
  };

  auto dfsCorner = [&](auto& self, int row, uint32_t col, uint32_t d1, uint32_t d2, int c1) -> void {
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
          onCorner(c1);
        }
      }
      return;
    }
    while (avail) {
      const uint32_t b = avail & -avail;
      avail ^= b;
      cols[row] = static_cast<uint8_t>(__builtin_ctz(b));
      self(self, row + 1, col | b, (d1 | b) << 1, (d2 | b) >> 1, c1);
    }
  };

  auto dfsInterior = [&](auto& self, int row, uint32_t col, uint32_t d1, uint32_t d2, int c0) -> void {
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
          onInterior(c0);
        }
      }
      return;
    }
    while (avail) {
      const uint32_t b = avail & -avail;
      avail ^= b;
      cols[row] = static_cast<uint8_t>(__builtin_ctz(b));
      self(self, row + 1, col | b, (d1 | b) << 1, (d2 | b) >> 1, c0);
    }
  };

  cols[0] = 0;
  for (int c1 = 2; c1 < n; ++c1) {
    cols[1] = static_cast<uint8_t>(c1);
    for (int r = 2; r < n; ++r) rowMask[r] = (r < c1) ? (full & ~2u) : full;
    const uint32_t b0 = 1u, b1 = 1u << c1;
    dfsCorner(dfsCorner, 2, b0 | b1, ((b0 << 1) | b1) << 1, ((b0 >> 1) | b1) >> 1, c1);
  }

  const uint32_t noSides = full & ~(1u | (1u << m));
  for (int c0 = 1; c0 <= (n - 2) / 2; ++c0) {
    cols[0] = static_cast<uint8_t>(c0);
    for (int r = 1; r < n - 1; ++r) rowMask[r] = (r < c0 || r >= n - c0) ? noSides : full;
    rowMask[n - 1] = ((1u << (n - 2 * c0)) - 1u) << c0;
    const uint32_t b0 = 1u << c0;
    dfsInterior(dfsInterior, 1, b0, b0 << 1, b0 >> 1, c0);
  }

  std::vector<Board> boards;
  boards.reserve(totalSolutions);
  const bool debug = snapshotsEnabled();
  auto emit = [&](const Fundamental& f) {
    uint8_t tmp[kMaxN];
    Cell buf[kMaxN];
    for (int k = 0; k < 8; ++k) {
      if (!((f.mask >> k) & 1u)) continue;
      applyD4(k, f.cols, tmp, n);
      for (int r = 0; r < n; ++r) buf[r] = {r, static_cast<int>(tmp[r])};
      boards.emplace_back(buf, buf + n);
      if (__builtin_expect(debug, 0)) {
        snapshot(boards.back(), "board with " + std::to_string(n) + " queens");
      }
    }
  };
  for (int i = 0; i < stackCount; ++i) emit(stackBuf[i]);
  for (const auto& f : heapBuf) emit(f);
  return boards;
}

// ---- Fixed-width bitset for W = 1, 2, 3, 4 64-bit words ------------------------------------------------------------

template <int W>
struct Bits {
  uint64_t w[W]{};

  inline bool any() const {
    uint64_t x = 0;
    for (int i = 0; i < W; ++i) x |= w[i];
    return x != 0;
  }

  inline bool empty() const { return !any(); }

  inline void set(int idx) { w[idx >> 6] |= (1ull << (idx & 63)); }
  inline void clear(int idx) { w[idx >> 6] &= ~(1ull << (idx & 63)); }

  inline int lsb() const {
    for (int i = 0; i < W; ++i) {
      if (w[i]) return (i << 6) + __builtin_ctzll(w[i]);
    }
    return -1;
  }

  inline int popcount() const {
    int c = 0;
    for (int i = 0; i < W; ++i) c += __builtin_popcountll(w[i]);
    return c;
  }

  inline bool hasSingleBit() const {
    int seen = 0;
    for (int i = 0; i < W; ++i) {
      if (w[i]) {
        if (seen || (w[i] & (w[i] - 1ull))) return false;
        seen = 1;
      }
    }
    return seen == 1;
  }

  inline Bits operator&(const Bits& o) const {
    Bits r;
    for (int i = 0; i < W; ++i) r.w[i] = w[i] & o.w[i];
    return r;
  }

  inline Bits& operator&=(const Bits& o) {
    for (int i = 0; i < W; ++i) w[i] &= o.w[i];
    return *this;
  }

  inline Bits& operator|=(const Bits& o) {
    for (int i = 0; i < W; ++i) w[i] |= o.w[i];
    return *this;
  }

  inline bool intersects(const Bits& o) const {
    uint64_t x = 0;
    for (int i = 0; i < W; ++i) x |= (w[i] & o.w[i]);
    return x != 0;
  }
};

// ---- Exact MIS enumerator on a single connected component ----------------------------------------------------------

struct ComponentResult {
  int optSize = 0;
  size_t boardCount = 0;
  std::vector<Cell> vertexCells;    // local vertex -> (row, col)
  std::vector<uint8_t> flatBoards;  // boardCount * optSize local vertex indices
};

template <int W>
struct ComponentSolver {
  static constexpr int kMaxV = W * 64;

  int m = 0;
  std::vector<Cell> cells;
  Bits<W> conflict[kMaxV];  // vertices conflicting with v (excluding v)
  Bits<W> compat[kMaxV];    // vertices compatible with v (excluding v)
  std::vector<Bits<W>> rowSegs;
  std::vector<Bits<W>> colSegs;

  uint8_t cur[kMaxV]{};
  int bestSize = 0;
  size_t bestCount = 0;
  std::vector<uint8_t> flatBest;

  // Deterministic multi-start min-conflict-degree greedy + 1-2 swap local search for a tight initial lower bound.
  int findLowerBound() const {
    Bits<W> all{};
    for (int i = 0; i < m; ++i) all.set(i);

    auto runGreedy = [&](int forcedFirst) -> int {
      Bits<W> P = all;
      Bits<W> sol{};
      int sz = 0;
      if (forcedFirst >= 0) {
        sol.set(forcedFirst);
        P &= compat[forcedFirst];
        ++sz;
      }
      while (P.any()) {
        int pick = -1;
        int bestDeg = 1000000;
        Bits<W> scan = P;
        while (scan.any()) {
          const int v = scan.lsb();
          scan.clear(v);
          const int deg = (P & conflict[v]).popcount();
          if (deg < bestDeg) {
            bestDeg = deg;
            pick = v;
            if (deg == 0) break;
          }
        }
        sol.set(pick);
        P &= compat[pick];
        ++sz;
      }

      // 1-2 swap improvement: replace one queen by two mutually compatible cells if possible.
      bool improved = true;
      while (improved) {
        improved = false;
        Bits<W> inSol = sol;
        while (inSol.any()) {
          const int q = inSol.lsb();
          inSol.clear(q);
          Bits<W> reduced = sol;
          reduced.clear(q);
          Bits<W> pool = all;
          Bits<W> tmp = reduced;
          while (tmp.any()) {
            const int u = tmp.lsb();
            tmp.clear(u);
            pool &= compat[u];
          }
          pool.clear(q);
          Bits<W> scan = pool;
          while (scan.any()) {
            const int a = scan.lsb();
            scan.clear(a);
            const Bits<W> partners = scan & compat[a];
            if (partners.any()) {
              const int b = partners.lsb();
              sol = reduced;
              sol.set(a);
              sol.set(b);
              ++sz;
              Bits<W> ext = pool & compat[a] & compat[b];
              while (ext.any()) {
                const int e = ext.lsb();
                sol.set(e);
                ext &= compat[e];
                ++sz;
              }
              improved = true;
              break;
            }
          }
          if (improved) break;
        }
      }
      return sz;
    };

    int bestLB = runGreedy(-1);
    const int starts = std::min(m, 12);
    for (int s = 0; s < starts; ++s) {
      const int lb = runGreedy(s);
      if (lb > bestLB) bestLB = lb;
    }
    return bestLB;
  }

  inline void recordBoard(int size) {
    if (size > bestSize) {
      bestSize = size;
      bestCount = 0;
      flatBest.clear();
    }
    flatBest.insert(flatBest.end(), cur, cur + size);
    ++bestCount;
  }

  // Evaluates a geometric segment clique cover on P.
  // Returns false when activeCount < need (prune), or outputs the union of the (activeCount - need + 1)
  // smallest active segments as a guaranteed branching cover.
  static bool evalSegCover(const std::vector<Bits<W>>& segs, const Bits<W>& P, int need,
                           int& outActive, Bits<W>& outU, int& outUSize, int capSize) {
    Bits<W> activeInter[kMaxV];
    int activeSize[kMaxV];
    int cnt = 0;
    const int totalSegs = static_cast<int>(segs.size());
    for (int i = 0; i < totalSegs; ++i) {
      const Bits<W> inter = P & segs[i];
      if (inter.any()) {
        activeInter[cnt] = inter;
        activeSize[cnt] = inter.popcount();
        ++cnt;
      }
    }
    outActive = cnt;
    if (cnt < need) return false;

    const int take = cnt - need + 1;
    if (take == 1) {
      int bestIdx = 0;
      for (int i = 1; i < cnt; ++i) {
        if (activeSize[i] < activeSize[bestIdx]) bestIdx = i;
      }
      outU = activeInter[bestIdx];
      outUSize = activeSize[bestIdx];
      return true;
    }

    int order[kMaxV];
    for (int i = 0; i < cnt; ++i) order[i] = i;
    Bits<W> u{};
    int uSize = 0;
    for (int t = 0; t < take; ++t) {
      int minPos = t;
      for (int j = t + 1; j < cnt; ++j) {
        if (activeSize[order[j]] < activeSize[order[minPos]]) minPos = j;
      }
      std::swap(order[t], order[minPos]);
      uSize += activeSize[order[t]];
      if (uSize >= capSize) {
        outUSize = capSize;
        return true;
      }
      u |= activeInter[order[t]];
    }
    outU = u;
    outUSize = uSize;
    return true;
  }

  void expand(Bits<W> P, int curSize) {
    if (P.empty()) {
      if (curSize >= bestSize) recordBoard(curSize);
      return;
    }

    if (curSize >= bestSize) {
      bestSize = curSize + 1;
      bestCount = 0;
      flatBest.clear();
    }

    int need = bestSize - curSize;
    const int pCount = P.popcount();
    if (pCount < need) return;

    // Fast path for need == 1: either P is a clique (emit every single vertex) or P contains a compatible pair.
    if (need == 1) {
      Bits<W> scan = P;
      while (scan.any()) {
        const int v = scan.lsb();
        scan.clear(v);
        if ((scan & compat[v]).any()) {
          bestSize = curSize + 2;
          bestCount = 0;
          flatBest.clear();
          need = 2;
          break;
        }
      }
      if (need == 1) {
        Bits<W> emit = P;
        while (emit.any()) {
          const int v = emit.lsb();
          emit.clear(v);
          cur[curSize] = static_cast<uint8_t>(v);
          recordBoard(curSize + 1);
        }
        return;
      }
      if (pCount < 2) return;
    }

    Bits<W> bestU = P;
    int bestUSize = pCount;

    // 1. Row-segment clique cover bound.
    int activeRows = 0;
    Bits<W> uRow{};
    int uRowSize = bestUSize;
    if (!evalSegCover(rowSegs, P, need, activeRows, uRow, uRowSize, bestUSize)) return;
    if (uRowSize < bestUSize) {
      bestU = uRow;
      bestUSize = uRowSize;
    }
    if (bestUSize == 1) {
      const int v = bestU.lsb();
      cur[curSize] = static_cast<uint8_t>(v);
      expand(P & compat[v], curSize + 1);
      return;
    }

    // 2. Column-segment clique cover bound.
    int activeCols = 0;
    Bits<W> uCol{};
    int uColSize = bestUSize;
    if (!evalSegCover(colSegs, P, need, activeCols, uCol, uColSize, bestUSize)) return;
    if (uColSize < bestUSize) {
      bestU = uCol;
      bestUSize = uColSize;
    }
    if (bestUSize == 1) {
      const int v = bestU.lsb();
      cur[curSize] = static_cast<uint8_t>(v);
      expand(P & compat[v], curSize + 1);
      return;
    }

    // 3. BBMCX bitset greedy clique cover with 1-vertex recoloring (target kMin = need - 1 cliques).
    const int kMin = need - 1;
    Bits<W> U = P;
    Bits<W> C[kMaxV];
    int numColors = 0;
    while (numColors < kMin && U.any()) {
      Bits<W> Q = U;
      Bits<W> cls{};
      while (Q.any()) {
        const int v = Q.lsb();
        cls.set(v);
        U.clear(v);
        Q &= conflict[v];
      }
      C[numColors++] = cls;
    }
    if (U.empty()) return;

    Bits<W> unabsorbed{};
    int unabsorbedCnt = 0;
    Bits<W> remU = U;
    while (remU.any()) {
      const int v = remU.lsb();
      remU.clear(v);
      bool absorbed = false;
      for (int k1 = 0; k1 < numColors; ++k1) {
        const Bits<W> bad = C[k1] & compat[v];
        if (bad.empty()) {
          C[k1].set(v);
          absorbed = true;
          break;
        }
        if (bad.hasSingleBit()) {
          const int w = bad.lsb();
          for (int k2 = 0; k2 < numColors; ++k2) {
            if (k2 == k1) continue;
            if (!C[k2].intersects(compat[w])) {
              C[k1].clear(w);
              C[k1].set(v);
              C[k2].set(w);
              absorbed = true;
              break;
            }
          }
          if (absorbed) break;
        }
      }
      if (!absorbed) {
        unabsorbed.set(v);
        ++unabsorbedCnt;
        if (unabsorbedCnt >= bestUSize) break;
      }
    }
    if (unabsorbedCnt == 0) return;

    if (unabsorbedCnt < bestUSize) {
      bestU = unabsorbed;
      bestUSize = unabsorbedCnt;
    }

    // Branch on every vertex in the tightest pigeonhole cover bestU.
    Bits<W> remP = P;
    int remPCount = pCount;
    while (bestU.any()) {
      if (curSize + remPCount < bestSize) break;
      const int v = bestU.lsb();
      bestU.clear(v);
      remP.clear(v);
      --remPCount;
      const Bits<W> nextP = remP & compat[v];
      if (curSize + 1 + nextP.popcount() < bestSize) continue;
      cur[curSize] = static_cast<uint8_t>(v);
      expand(nextP, curSize + 1);
    }
  }

  ComponentResult solve() {
    bestSize = findLowerBound();
    bestCount = 0;
    flatBest.clear();
    Bits<W> all{};
    for (int i = 0; i < m; ++i) all.set(i);
    expand(all, 0);
    return {bestSize, bestCount, std::move(cells), std::move(flatBest)};
  }
};

// Dispatches a connected component to the tightest fixed-width bitset solver W in {1, 2, 3, 4}.
template <int W>
ComponentResult runComponentWithWidth(
    const std::vector<int>& compGlobal,
    const std::vector<Cell>& allCells,
    const std::vector<std::array<uint64_t, 4>>& globalConflict,
    const std::vector<int>& rowSegId,
    const std::vector<int>& colSegId,
    int totalRowSegs,
    int totalColSegs) {
  const int m = static_cast<int>(compGlobal.size());

  // Sort vertices by non-decreasing conflict degree (non-increasing degree in the complement graph).
  std::vector<std::pair<int, int>> degOrder;
  degOrder.reserve(static_cast<size_t>(m));
  for (int i = 0; i < m; ++i) {
    const int g = compGlobal[i];
    int deg = 0;
    for (int j = 0; j < m; ++j) {
      const int h = compGlobal[j];
      if ((globalConflict[g][h >> 6] >> (h & 63)) & 1ull) ++deg;
    }
    degOrder.emplace_back(deg, g);
  }
  std::sort(degOrder.begin(), degOrder.end());

  ComponentSolver<W> solver;
  solver.m = m;
  solver.cells.resize(static_cast<size_t>(m));
  std::vector<int> orderedGlobal(static_cast<size_t>(m));
  for (int i = 0; i < m; ++i) {
    orderedGlobal[i] = degOrder[i].second;
    solver.cells[i] = allCells[orderedGlobal[i]];
  }

  Bits<W> allMask{};
  for (int i = 0; i < m; ++i) allMask.set(i);

  for (int i = 0; i < m; ++i) {
    const int g = orderedGlobal[i];
    Bits<W> cMask{};
    for (int j = 0; j < m; ++j) {
      if (i == j) continue;
      const int h = orderedGlobal[j];
      if ((globalConflict[g][h >> 6] >> (h & 63)) & 1ull) cMask.set(j);
    }
    solver.conflict[i] = cMask;
    Bits<W> comp = allMask;
    for (int k = 0; k < W; ++k) comp.w[k] &= ~cMask.w[k];
    comp.clear(i);
    solver.compat[i] = comp;
  }

  std::vector<int> rowMap(static_cast<size_t>(totalRowSegs), -1);
  std::vector<int> colMap(static_cast<size_t>(totalColSegs), -1);
  for (int i = 0; i < m; ++i) {
    const int g = orderedGlobal[i];
    const int rs = rowSegId[g];
    if (rowMap[rs] < 0) {
      rowMap[rs] = static_cast<int>(solver.rowSegs.size());
      solver.rowSegs.push_back(Bits<W>{});
    }
    solver.rowSegs[rowMap[rs]].set(i);

    const int cs = colSegId[g];
    if (colMap[cs] < 0) {
      colMap[cs] = static_cast<int>(solver.colSegs.size());
      solver.colSegs.push_back(Bits<W>{});
    }
    solver.colSegs[colMap[cs]].set(i);
  }

  return solver.solve();
}

}  // namespace

std::vector<Board> solveWalled(int n, const std::vector<std::string>& grid) {
  if (n <= 0 || n > kMaxN || static_cast<int>(grid.size()) != n) return {};
  for (const auto& line : grid) {
    if (static_cast<int>(line.size()) != n) return {};
  }

  std::vector<Cell> cells;
  cells.reserve(static_cast<size_t>(n * n));
  int cellIdx[kMaxN][kMaxN];
  for (int r = 0; r < n; ++r) {
    for (int c = 0; c < n; ++c) {
      if (grid[r][c] == 'W') {
        cellIdx[r][c] = -1;
      } else {
        cellIdx[r][c] = static_cast<int>(cells.size());
        cells.emplace_back(r, c);
      }
    }
  }

  const int V = static_cast<int>(cells.size());
  if (V == 0) return {{}};
  if (V == 1) {
    std::vector<Board> out = {{cells[0]}};
    NQ_SNAPSHOT(out[0], "board with 1 queens");
    return out;
  }
  if (V == n * n && n >= 4) {
    return solveNoWalls(n);
  }

  // O(N^2) construction of row, column, and both diagonal wall-split segments.
  std::vector<int> rowSegId(static_cast<size_t>(V), -1);
  std::vector<int> colSegId(static_cast<size_t>(V), -1);
  std::vector<int> d1SegId(static_cast<size_t>(V), -1);
  std::vector<int> d2SegId(static_cast<size_t>(V), -1);

  std::vector<std::array<uint64_t, 4>> rowMasks, colMasks, d1Masks, d2Masks;

  auto assignLine = [&](int r0, int c0, int dr, int dc,
                        std::vector<int>& segId,
                        std::vector<std::array<uint64_t, 4>>& masks) {
    int curSeg = -1;
    for (int r = r0, c = c0; r >= 0 && r < n && c >= 0 && c < n; r += dr, c += dc) {
      const int v = cellIdx[r][c];
      if (v < 0) {
        curSeg = -1;
      } else {
        if (curSeg < 0) {
          curSeg = static_cast<int>(masks.size());
          masks.push_back({0, 0, 0, 0});
        }
        segId[v] = curSeg;
        masks[curSeg][v >> 6] |= (1ull << (v & 63));
      }
    }
  };

  for (int r = 0; r < n; ++r) assignLine(r, 0, 0, 1, rowSegId, rowMasks);
  for (int c = 0; c < n; ++c) assignLine(0, c, 1, 0, colSegId, colMasks);
  for (int c = 0; c < n; ++c) assignLine(0, c, 1, 1, d1SegId, d1Masks);
  for (int r = 1; r < n; ++r) assignLine(r, 0, 1, 1, d1SegId, d1Masks);
  for (int c = 0; c < n; ++c) assignLine(0, c, 1, -1, d2SegId, d2Masks);
  for (int r = 1; r < n; ++r) assignLine(r, n - 1, 1, -1, d2SegId, d2Masks);

  std::vector<std::array<uint64_t, 4>> globalConflict(static_cast<size_t>(V), {0, 0, 0, 0});
  for (int v = 0; v < V; ++v) {
    const auto& rm = rowMasks[rowSegId[v]];
    const auto& cm = colMasks[colSegId[v]];
    const auto& m1 = d1Masks[d1SegId[v]];
    const auto& m2 = d2Masks[d2SegId[v]];
    for (int w = 0; w < 4; ++w) {
      globalConflict[v][w] = rm[w] | cm[w] | m1[w] | m2[w];
    }
    globalConflict[v][v >> 6] &= ~(1ull << (v & 63));
  }

  // Decompose conflict graph into connected components.
  std::vector<char> visited(static_cast<size_t>(V), 0);
  Board forced;
  std::vector<ComponentResult> compResults;
  int totalOptQueens = 0;

  std::vector<int> bfs;
  bfs.reserve(static_cast<size_t>(V));

  for (int start = 0; start < V; ++start) {
    if (visited[start]) continue;
    bfs.clear();
    bfs.push_back(start);
    visited[start] = 1;
    for (size_t head = 0; head < bfs.size(); ++head) {
      const int u = bfs[head];
      for (int w = 0; w < 4; ++w) {
        uint64_t bits = globalConflict[u][w];
        while (bits) {
          const int v = (w << 6) + __builtin_ctzll(bits);
          bits &= bits - 1ull;
          if (!visited[v]) {
            visited[v] = 1;
            bfs.push_back(v);
          }
        }
      }
    }

    const int sz = static_cast<int>(bfs.size());
    if (sz == 1) {
      forced.push_back(cells[bfs[0]]);
      ++totalOptQueens;
      continue;
    }

    bool isClique = true;
    for (int u : bfs) {
      int deg = 0;
      for (int w = 0; w < 4; ++w) deg += __builtin_popcountll(globalConflict[u][w]);
      if (deg != sz - 1) {
        isClique = false;
        break;
      }
    }
    if (isClique) {
      ComponentResult res;
      res.optSize = 1;
      res.boardCount = static_cast<size_t>(sz);
      res.vertexCells.reserve(static_cast<size_t>(sz));
      res.flatBoards.reserve(static_cast<size_t>(sz));
      for (int i = 0; i < sz; ++i) {
        res.vertexCells.push_back(cells[bfs[i]]);
        res.flatBoards.push_back(static_cast<uint8_t>(i));
      }
      totalOptQueens += 1;
      compResults.push_back(std::move(res));
      continue;
    }

    ComponentResult res;
    if (sz <= 64) {
      res = runComponentWithWidth<1>(bfs, cells, globalConflict, rowSegId, colSegId,
                                     static_cast<int>(rowMasks.size()), static_cast<int>(colMasks.size()));
    } else if (sz <= 128) {
      res = runComponentWithWidth<2>(bfs, cells, globalConflict, rowSegId, colSegId,
                                     static_cast<int>(rowMasks.size()), static_cast<int>(colMasks.size()));
    } else if (sz <= 192) {
      res = runComponentWithWidth<3>(bfs, cells, globalConflict, rowSegId, colSegId,
                                     static_cast<int>(rowMasks.size()), static_cast<int>(colMasks.size()));
    } else {
      res = runComponentWithWidth<4>(bfs, cells, globalConflict, rowSegId, colSegId,
                                     static_cast<int>(rowMasks.size()), static_cast<int>(colMasks.size()));
    }
    totalOptQueens += res.optSize;
    compResults.push_back(std::move(res));
  }

  // Combine independent component solutions via Cartesian product with exact capacity reservation.
  size_t totalBoards = 1;
  for (const auto& cr : compResults) totalBoards *= cr.boardCount;

  std::vector<Board> result;
  result.reserve(totalBoards);
  const bool debug = snapshotsEnabled();

  if (compResults.empty()) {
    result.push_back(forced);
    if (__builtin_expect(debug, 0)) {
      snapshot(result.back(), "board with " + std::to_string(totalOptQueens) + " queens");
    }
    return result;
  }

  if (compResults.size() == 1 && forced.empty()) {
    const auto& cr = compResults[0];
    const int k = cr.optSize;
    Cell buf[kMaxN * kMaxN];
    const uint8_t* ptr = cr.flatBoards.data();
    for (size_t b = 0; b < cr.boardCount; ++b, ptr += k) {
      for (int i = 0; i < k; ++i) buf[i] = cr.vertexCells[ptr[i]];
      result.emplace_back(buf, buf + k);
      if (__builtin_expect(debug, 0)) {
        snapshot(result.back(), "board with " + std::to_string(totalOptQueens) + " queens");
      }
    }
    return result;
  }

  Cell acc[kMaxN * kMaxN];
  int accLen = 0;
  for (const auto& q : forced) acc[accLen++] = q;

  auto combine = [&](auto& self, size_t idx, int len) -> void {
    if (idx == compResults.size()) {
      result.emplace_back(acc, acc + len);
      if (__builtin_expect(debug, 0)) {
        snapshot(result.back(), "board with " + std::to_string(totalOptQueens) + " queens");
      }
      return;
    }
    const auto& cr = compResults[idx];
    const int k = cr.optSize;
    const uint8_t* ptr = cr.flatBoards.data();
    for (size_t b = 0; b < cr.boardCount; ++b, ptr += k) {
      for (int i = 0; i < k; ++i) acc[len + i] = cr.vertexCells[ptr[i]];
      self(self, idx + 1, len + k);
    }
  };
  combine(combine, 0, accLen);
  return result;
}
