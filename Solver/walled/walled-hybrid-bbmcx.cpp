// Solver for the Walled case: ultra-fast component-decomposed bitset Maximum Independent Set enumeration.
// Combines:
// 1. Fixed-width bitset (1, 2, or 3 x 64-bit words) for zero heap allocation during search.
// 2. Component decomposition and clique component fast-path (alpha == 1).
// 3. Segment Bound Filtering + Exact-Cover Unit Propagation.
// 4. Bit-parallel cutoff coloring (limit = need - 1) with Re-NUMBER repair.
// 5. Minimum-width branching set selection (Dynamic coloring vs Row-MRV vs Col-MRV).
// 6. 1-2 swap local search for an immediate tight lower bound.
// 7. Fast-path for W == 0 (Normal board) via compile-time specialized D4 symmetry bitmask.
#include <cstdint>
#include <memory>
#include <string>
#include <utility>
#include <vector>
#include "nqueens.h"

namespace {

// ============================================================================
// 1. Fixed-Size Stack/Register Bitset (1, 2, or 3 x 64-bit words = up to 192 bits)
//    Zero heap allocations, compiles directly to WASM i64 bitwise/popcnt/ctz/clz.
// ============================================================================
template <int W>
struct Bitset {
  uint64_t w[W]{};

  __attribute__((always_inline)) inline void clear() {
    for (int i = 0; i < W; ++i) w[i] = 0ULL;
  }

  __attribute__((always_inline)) inline bool any() const {
    if constexpr (W == 1) {
      return w[0] != 0ULL;
    } else if constexpr (W == 2) {
      return (w[0] | w[1]) != 0ULL;
    } else {
      return (w[0] | w[1] | w[2]) != 0ULL;
    }
  }

  __attribute__((always_inline)) inline bool none() const { return !any(); }

  __attribute__((always_inline)) inline void set(int idx) {
    if constexpr (W == 1) {
      w[0] |= (1ULL << idx);
    } else {
      w[idx >> 6] |= (1ULL << (idx & 63));
    }
  }

  __attribute__((always_inline)) inline void reset(int idx) {
    if constexpr (W == 1) {
      w[0] &= ~(1ULL << idx);
    } else {
      w[idx >> 6] &= ~(1ULL << (idx & 63));
    }
  }

  __attribute__((always_inline)) inline bool test(int idx) const {
    if constexpr (W == 1) {
      return (w[0] >> idx) & 1ULL;
    } else {
      return (w[idx >> 6] >> (idx & 63)) & 1ULL;
    }
  }

  __attribute__((always_inline)) inline int popcount() const {
    if constexpr (W == 1) {
      return __builtin_popcountll(w[0]);
    } else if constexpr (W == 2) {
      return __builtin_popcountll(w[0]) + __builtin_popcountll(w[1]);
    } else {
      return __builtin_popcountll(w[0]) + __builtin_popcountll(w[1]) +
             __builtin_popcountll(w[2]);
    }
  }

  __attribute__((always_inline)) inline bool isSingle() const {
    if constexpr (W == 1) {
      return w[0] != 0ULL && (w[0] & (w[0] - 1ULL)) == 0ULL;
    } else {
      return popcount() == 1;
    }
  }

  __attribute__((always_inline)) inline int lsb() const {
    if constexpr (W == 1) {
      return __builtin_ctzll(w[0]);
    } else if constexpr (W == 2) {
      return w[0] ? __builtin_ctzll(w[0]) : 64 + __builtin_ctzll(w[1]);
    } else {
      if (w[0]) return __builtin_ctzll(w[0]);
      if (w[1]) return 64 + __builtin_ctzll(w[1]);
      return 128 + __builtin_ctzll(w[2]);
    }
  }

  __attribute__((always_inline)) inline int msb() const {
    if constexpr (W == 1) {
      return 63 - __builtin_clzll(w[0]);
    } else if constexpr (W == 2) {
      return w[1] ? 127 - __builtin_clzll(w[1]) : 63 - __builtin_clzll(w[0]);
    } else {
      if (w[2]) return 191 - __builtin_clzll(w[2]);
      if (w[1]) return 127 - __builtin_clzll(w[1]);
      return 63 - __builtin_clzll(w[0]);
    }
  }

  __attribute__((always_inline)) inline Bitset operator&(const Bitset& o) const {
    Bitset r;
    for (int i = 0; i < W; ++i) r.w[i] = w[i] & o.w[i];
    return r;
  }

  __attribute__((always_inline)) inline Bitset operator|(const Bitset& o) const {
    Bitset r;
    for (int i = 0; i < W; ++i) r.w[i] = w[i] | o.w[i];
    return r;
  }

  __attribute__((always_inline)) inline Bitset& operator&=(const Bitset& o) {
    for (int i = 0; i < W; ++i) w[i] &= o.w[i];
    return *this;
  }

  __attribute__((always_inline)) inline Bitset& operator|=(const Bitset& o) {
    for (int i = 0; i < W; ++i) w[i] |= o.w[i];
    return *this;
  }
};

// ============================================================================
// 2. Fast-Path No-Walls Solver: Compile-Time Specialized D4 Symmetry Bitmask
//    Handles W == 0 for 4 <= N <= 12 in < 2 ms.
// ============================================================================
template <int N>
struct UltraNoWallSolver {
  static constexpr int M = N - 1;
  static constexpr uint32_t FULL = (1u << N) - 1u;
  static constexpr uint32_t HIGH_BIT = 1u << M;
  static constexpr int kOrb8Cap = (N <= 10) ? 128 : (N == 11 ? 512 : 2048);
  static constexpr int kSymCap = 64;

  uint32_t rowMask[N]{};
  uint32_t rowBit[N]{};

  int c0 = 0;
  int mc0 = 0;
  int deadlineM = 0;
  int deadline0 = 0;
  uint32_t bitMC0 = 0;

  uint64_t orb8Buf[kOrb8Cap];
  int orb8Count = 0;
  std::vector<uint64_t> orb8Overflow;

  uint64_t symBuf[kSymCap];
  int symCount = 0;
  std::vector<uint64_t> symOverflow;

  size_t totalSolutions = 0;

  __attribute__((always_inline)) inline uint64_t packFromBits() const {
    uint64_t p = 0;
    for (int r = N - 1; r >= 0; --r) {
      p = (p << 4) | static_cast<uint64_t>(__builtin_ctz(rowBit[r]));
    }
    return p;
  }

  __attribute__((always_inline)) inline uint64_t packFromCols(
      const uint8_t* cols) const {
    uint64_t p = 0;
    for (int r = N - 1; r >= 0; --r) {
      p = (p << 4) | static_cast<uint64_t>(cols[r]);
    }
    return p;
  }

  __attribute__((always_inline)) inline void pushOrbit8(uint64_t packed) {
    if (orb8Count < kOrb8Cap) {
      orb8Buf[orb8Count++] = packed;
    } else {
      orb8Overflow.push_back(packed);
    }
    totalSolutions += 8;
  }

  __attribute__((always_inline)) inline void pushOrbit8Bits() {
    pushOrbit8(packFromBits());
  }

  __attribute__((always_inline)) inline void pushSym(uint64_t packed,
                                                     bool isOrb2) {
    const uint64_t entry = packed | (isOrb2 ? (1ULL << 63) : 0ULL);
    if (symCount < kSymCap) {
      symBuf[symCount++] = entry;
    } else {
      symOverflow.push_back(entry);
    }
    totalSolutions += isOrb2 ? 2 : 4;
  }

  inline void onInteriorLeaf(uint32_t colM1) {
    const bool tie180 = (colM1 == bitMC0);
    const bool tie90 = (rowBit[mc0] == 1u);
    const bool tie270 = (rowBit[c0] == HIGH_BIT);

    if (!(tie180 | tie90 | tie270)) {
      pushOrbit8Bits();
      return;
    }

    uint8_t cols[N];
    for (int r = 0; r < N; ++r) {
      cols[r] = static_cast<uint8_t>(__builtin_ctz(rowBit[r]));
    }

    bool sym180 = tie180;
    if (tie180) {
      for (int r = 1; r <= M / 2; ++r) {
        const int v = M - cols[M - r];
        if (v != cols[r]) {
          if (v < cols[r]) return;
          sym180 = false;
          break;
        }
      }
    }

    bool sym90 = false;
    if (tie90 | tie270) {
      uint8_t inv[N];
      for (int r = 0; r < N; ++r) {
        inv[cols[r]] = static_cast<uint8_t>(r);
      }

      if (tie90) {
        bool eq = true;
        for (int r = 1; r < N; ++r) {
          const int v = M - inv[r];
          if (v != cols[r]) {
            if (v < cols[r]) return;
            eq = false;
            break;
          }
        }
        if (eq) sym90 = true;
      }

      if (tie270 && !sym90) {
        bool eq = true;
        for (int r = 1; r < N; ++r) {
          const int v = inv[M - r];
          if (v != cols[r]) {
            if (v < cols[r]) return;
            eq = false;
            break;
          }
        }
        if (eq) sym90 = true;
      }
    }

    const uint64_t packed = packFromCols(cols);
    if (sym90) {
      pushSym(packed, true);
    } else if (sym180) {
      pushSym(packed, false);
    } else {
      pushOrbit8(packed);
    }
  }

  template <int Row, bool Corner>
  void dfs(uint32_t freeCol, uint32_t d1, uint32_t d2) {
    if constexpr (Row == N - 3) {
      if constexpr (!Corner) {
        if ((freeCol & rowMask[N - 1]) == 0) return;
      }
      uint32_t avail = freeCol & rowMask[N - 3] & ~(d1 | d2);
      if constexpr (!Corner) {
        if (N - 3 == deadlineM && (freeCol & HIGH_BIT)) {
          avail &= HIGH_BIT;
        } else if (N - 3 == deadline0 && (freeCol & 1u)) {
          avail &= 1u;
        }
      }
      const uint32_t maskM2 = rowMask[N - 2];
      const uint32_t maskM1 = rowMask[N - 1];
      while (avail) {
        const uint32_t b = avail & (0u - avail);
        avail ^= b;
        const uint32_t rem2 = freeCol ^ b;
        const uint32_t a = rem2 & (0u - rem2);
        const uint32_t c = rem2 ^ a;
        if (c == (a << 1)) continue;

        const uint32_t nd1 = (d1 | b) << 1;
        const uint32_t nd2 = (d2 | b) >> 1;
        const uint32_t okM2 = maskM2 & ~(nd1 | nd2);
        const uint32_t okM1 = maskM1 & ~((nd1 << 1) | (nd2 >> 1));

        if ((a & okM2) && (c & okM1)) {
          rowBit[N - 3] = b;
          rowBit[N - 2] = a;
          rowBit[N - 1] = c;
          if constexpr (Corner) pushOrbit8Bits();
          else onInteriorLeaf(c);
        }
        if ((c & okM2) && (a & okM1)) {
          rowBit[N - 3] = b;
          rowBit[N - 2] = c;
          rowBit[N - 1] = a;
          if constexpr (Corner) pushOrbit8Bits();
          else onInteriorLeaf(a);
        }
      }
      return;
    } else if constexpr (Row == N - 2) {
      const uint32_t a = freeCol & (0u - freeCol);
      const uint32_t c = freeCol ^ a;
      if (c == (a << 1)) return;
      const uint32_t okM2 = rowMask[N - 2] & ~(d1 | d2);
      const uint32_t okM1 = rowMask[N - 1] & ~((d1 << 1) | (d2 >> 1));
      if ((a & okM2) && (c & okM1)) {
        rowBit[N - 2] = a;
        rowBit[N - 1] = c;
        if constexpr (Corner) pushOrbit8Bits();
        else onInteriorLeaf(c);
      }
      if ((c & okM2) && (a & okM1)) {
        rowBit[N - 2] = c;
        rowBit[N - 1] = a;
        if constexpr (Corner) pushOrbit8Bits();
        else onInteriorLeaf(a);
      }
      return;
    } else {
      uint32_t avail = freeCol & rowMask[Row] & ~(d1 | d2);
      if constexpr (!Corner) {
        if (Row == deadlineM && (freeCol & HIGH_BIT)) {
          avail &= HIGH_BIT;
        } else if (Row == deadline0 && (freeCol & 1u)) {
          avail &= 1u;
        }
      }
      while (avail) {
        const uint32_t b = avail & (0u - avail);
        avail ^= b;
        rowBit[Row] = b;
        dfs<Row + 1, Corner>(freeCol ^ b, (d1 | b) << 1, (d2 | b) >> 1);
      }
    }
  }

  void run() {
    rowBit[0] = 1u;
    for (int c1 = 2; c1 < M; ++c1) {
      const uint32_t b1 = 1u << c1;
      rowBit[1] = b1;
      if (c1 == M - 1) {
        for (int r = 2; r < M; ++r) {
          uint32_t mask = FULL & ~2u;
          const int diagCol = 1 + M - r;
          if (diagCol < N) mask &= ~(1u << diagCol);
          rowMask[r] = mask;
        }
        rowMask[M] = 2u;
      } else {
        for (int r = 2; r < N; ++r) {
          rowMask[r] = (r < c1) ? (FULL & ~2u) : FULL;
        }
      }
      dfs<2, true>(FULL ^ (1u | b1), (2u | b1) << 1, b1 >> 1);
    }

    const uint32_t noSides = FULL & ~(1u | HIGH_BIT);
    constexpr int kMaxC0 = (N - 2) / 2;
    for (int c = 1; c <= kMaxC0; ++c) {
      c0 = c;
      mc0 = M - c;
      deadlineM = mc0 - 1;
      deadline0 = mc0;
      bitMC0 = 1u << mc0;

      const uint32_t b0 = 1u << c;
      rowBit[0] = b0;

      for (int r = 1; r < M; ++r) {
        rowMask[r] = (r < c || r > mc0) ? noSides : FULL;
      }
      rowMask[c] &= ~1u;
      rowMask[mc0] &= ~HIGH_BIT;
      rowMask[M] = (((1u << (N - 2 * c)) - 1u) << c) & ~b0;

      if constexpr ((N & 1) == 0) {
        if (c == kMaxC0) {
          const uint32_t forcedCols = HIGH_BIT | 1u | (1u << (c + 1));
          bool dead = false;
          for (int r = 1; r < M; ++r) {
            if (r == c) {
              rowMask[r] = HIGH_BIT;
            } else if (r == c + 1) {
              rowMask[r] = 1u;
            } else {
              uint32_t mask = rowMask[r] & ~forcedCols;
              const int dA = (r > c) ? (r - c) : (c - r);
              const int colA = M - dA;
              if (colA >= 0) mask &= ~(1u << colA);
              const int colB = (r > c + 1) ? (r - (c + 1)) : ((c + 1) - r);
              if (colB < N) mask &= ~(1u << colB);
              const int dC = M - r;
              if (c + 1 + dC < N) mask &= ~(1u << (c + 1 + dC));
              if (c + 1 - dC >= 0) mask &= ~(1u << (c + 1 - dC));
              rowMask[r] = mask;
              if (mask == 0) dead = true;
            }
          }
          if (dead) continue;
          rowMask[M] = 1u << (c + 1);
        }
      }

      dfs<1, false>(FULL ^ b0, b0 << 1, b0 >> 1);
    }
  }

  std::vector<std::vector<std::pair<int, int>>> materialize() const {
    std::vector<std::vector<std::pair<int, int>>> solutions;
    solutions.reserve(totalSolutions);

    auto emitOrb8 = [&](uint64_t p) {
      std::pair<int, int> b0[N], b1[N], b2[N], b3[N], b4[N], b5[N], b6[N], b7[N];
      for (int r = 0; r < N; ++r) {
        const int c = static_cast<int>(p & 0xFu);
        p >>= 4;
        const int mc = M - c;
        const int mr = M - r;
        b0[r] = {r, c};
        b1[r] = {r, mc};
        b2[mr] = {mr, c};
        b3[mr] = {mr, mc};
        b4[c] = {c, r};
        b5[c] = {c, mr};
        b6[mc] = {mc, r};
        b7[mc] = {mc, mr};
      }
      solutions.emplace_back(b0, b0 + N);
      solutions.emplace_back(b1, b1 + N);
      solutions.emplace_back(b2, b2 + N);
      solutions.emplace_back(b3, b3 + N);
      solutions.emplace_back(b4, b4 + N);
      solutions.emplace_back(b5, b5 + N);
      solutions.emplace_back(b6, b6 + N);
      solutions.emplace_back(b7, b7 + N);
    };

    auto emitSym = [&](uint64_t entry) {
      const bool isOrb2 = (entry >> 63) != 0;
      uint64_t p = entry;
      if (isOrb2) {
        std::pair<int, int> b0[N], b1[N];
        for (int r = 0; r < N; ++r) {
          const int c = static_cast<int>(p & 0xFu);
          p >>= 4;
          b0[r] = {r, c};
          b1[r] = {r, M - c};
        }
        solutions.emplace_back(b0, b0 + N);
        solutions.emplace_back(b1, b1 + N);
      } else {
        std::pair<int, int> b0[N], b1[N], b4[N], b5[N];
        for (int r = 0; r < N; ++r) {
          const int c = static_cast<int>(p & 0xFu);
          p >>= 4;
          b0[r] = {r, c};
          b1[r] = {r, M - c};
          b4[c] = {c, r};
          b5[c] = {c, M - r};
        }
        solutions.emplace_back(b0, b0 + N);
        solutions.emplace_back(b1, b1 + N);
        solutions.emplace_back(b4, b4 + N);
        solutions.emplace_back(b5, b5 + N);
      }
    };

    for (int i = 0; i < orb8Count; ++i) emitOrb8(orb8Buf[i]);
    for (uint64_t p : orb8Overflow) emitOrb8(p);
    for (int i = 0; i < symCount; ++i) emitSym(symBuf[i]);
    for (uint64_t e : symOverflow) emitSym(e);

    return solutions;
  }
};

template <int N>
std::vector<std::vector<std::pair<int, int>>> solveNoWallsFixed() {
  auto solver = std::make_unique<UltraNoWallSolver<N>>();
  solver->run();
  return solver->materialize();
}

// ============================================================================
// 3. Exact Walled Component Solver (Hybrid Segment-MRV + Unit Propagation +
//    Bit-Parallel Cutoff Coloring + Re-NUMBER Repair + 1-2 Swap Local Search)
//    Templated by word count W in {1, 2, 3} for optimal WASM register usage.
// ============================================================================
constexpr int kMaxCells = 144;
constexpr int kMaxSegs = 72;
constexpr int kMaxDepth = 76;

inline void insertionSortCoords(std::pair<int, int>* arr, int len) {
  for (int i = 1; i < len; ++i) {
    const auto key = arr[i];
    int j = i - 1;
    while (j >= 0 && arr[j] > key) {
      arr[j + 1] = arr[j];
      --j;
    }
    arr[j + 1] = key;
  }
}

template <int W>
struct CompSolver {
  int V = 0;
  int numRowSegs = 0;
  int numColSegs = 0;

  std::pair<int, int> coords[kMaxCells];
  Bitset<W> allVerts;
  Bitset<W> adjG[kMaxCells];
  Bitset<W> nonAdj[kMaxCells];
  Bitset<W> rowSegMask[kMaxSegs];
  Bitset<W> colSegMask[kMaxSegs];

  Bitset<W> colorScratch[kMaxCells];
  uint8_t rowPool[kMaxDepth][kMaxSegs];
  uint8_t rowSzPool[kMaxDepth][kMaxSegs];
  uint8_t colPool[kMaxDepth][kMaxSegs];
  uint8_t colSzPool[kMaxDepth][kMaxSegs];
  uint8_t chosenPool[kMaxDepth][kMaxSegs];

  int bestSize = 0;
  std::vector<Bitset<W>> solutions;

  int improveLocalSearch(Bitset<W> I, int sz) const {
    bool improved = true;
    while (improved) {
      improved = false;
      Bitset<W> scanI = I;
      while (scanI.any()) {
        const int u = scanI.lsb();
        scanI.reset(u);

        Bitset<W> avail = allVerts;
        Bitset<W> others = I;
        others.reset(u);
        while (others.any()) {
          const int x = others.lsb();
          others.reset(x);
          avail &= nonAdj[x];
        }

        Bitset<W> scan = avail;
        int foundA = -1, foundB = -1;
        while (scan.any()) {
          const int a = scan.lsb();
          scan.reset(a);
          Bitset<W> partners = avail & nonAdj[a];
          if (partners.any()) {
            foundA = a;
            foundB = partners.lsb();
            break;
          }
        }

        if (foundA != -1) {
          I.reset(u);
          I.set(foundA);
          I.set(foundB);
          ++sz;

          Bitset<W> ext = avail & nonAdj[foundA] & nonAdj[foundB];
          while (ext.any()) {
            int bestV = -1;
            int bestDeg = 1000;
            Bitset<W> s = ext;
            while (s.any()) {
              const int c = s.lsb();
              s.reset(c);
              const int d = (ext & adjG[c]).popcount();
              if (d < bestDeg) {
                bestDeg = d;
                bestV = c;
              }
            }
            I.set(bestV);
            ++sz;
            ext &= nonAdj[bestV];
          }
          improved = true;
          break;
        }
      }
    }
    return sz;
  }

  int runHeuristics() const {
    int bestLB = 1;

    {
      Bitset<W> rem = allVerts;
      Bitset<W> I;
      int sz = 0;
      while (rem.any()) {
        int bestV = -1, bestDeg = 1000;
        Bitset<W> s = rem;
        while (s.any()) {
          const int v = s.lsb();
          s.reset(v);
          const int d = (rem & adjG[v]).popcount();
          if (d < bestDeg) {
            bestDeg = d;
            bestV = v;
            if (d == 0) break;
          }
        }
        I.set(bestV);
        ++sz;
        rem &= nonAdj[bestV];
      }
      const int imp = improveLocalSearch(I, sz);
      if (imp > bestLB) bestLB = imp;
    }

    {
      Bitset<W> rem = allVerts;
      Bitset<W> I;
      int sz = 0;
      while (rem.any()) {
        int bestSegSz = 1000;
        Bitset<W> bestSeg;
        for (int s = 0; s < numRowSegs; ++s) {
          Bitset<W> inter = rem & rowSegMask[s];
          if (inter.any()) {
            const int c = inter.popcount();
            if (c < bestSegSz) {
              bestSegSz = c;
              bestSeg = inter;
              if (c == 1) break;
            }
          }
        }
        int bestV = -1, bestDeg = 1000;
        while (bestSeg.any()) {
          const int v = bestSeg.lsb();
          bestSeg.reset(v);
          const int d = (rem & adjG[v]).popcount();
          if (d < bestDeg) {
            bestDeg = d;
            bestV = v;
          }
        }
        I.set(bestV);
        ++sz;
        rem &= nonAdj[bestV];
      }
      const int imp = improveLocalSearch(I, sz);
      if (imp > bestLB) bestLB = imp;
    }

    {
      Bitset<W> rem = allVerts;
      Bitset<W> I;
      int sz = 0;
      while (rem.any()) {
        int bestSegSz = 1000;
        Bitset<W> bestSeg;
        for (int s = 0; s < numColSegs; ++s) {
          Bitset<W> inter = rem & colSegMask[s];
          if (inter.any()) {
            const int c = inter.popcount();
            if (c < bestSegSz) {
              bestSegSz = c;
              bestSeg = inter;
              if (c == 1) break;
            }
          }
        }
        int bestV = -1, bestDeg = 1000;
        while (bestSeg.any()) {
          const int v = bestSeg.lsb();
          bestSeg.reset(v);
          const int d = (rem & adjG[v]).popcount();
          if (d < bestDeg) {
            bestDeg = d;
            bestV = v;
          }
        }
        I.set(bestV);
        ++sz;
        rem &= nonAdj[bestV];
      }
      const int imp = improveLocalSearch(I, sz);
      if (imp > bestLB) bestLB = imp;
    }

    return bestLB;
  }

  void search(Bitset<W> P, Bitset<W> curSet, int curSize,
              const uint8_t* parentRowIds, int parentRowCnt,
              const uint8_t* parentColIds, int parentColCnt, int depth) {
    uint8_t* rowIds = rowPool[depth];
    uint8_t* rowSzs = rowSzPool[depth];
    uint8_t* colIds = colPool[depth];
    uint8_t* colSzs = colSzPool[depth];

    const uint8_t* srcRow = parentRowIds;
    int srcRowCnt = parentRowCnt;
    const uint8_t* srcCol = parentColIds;
    int srcColCnt = parentColCnt;

    int rCnt = 0;
    int cCnt = 0;
    int rowHist[13];
    int colHist[13];

    int need = 0;
    while (true) {
      if (P.none()) {
        if (curSize > bestSize) {
          bestSize = curSize;
          solutions.clear();
          solutions.push_back(curSet);
        } else if (curSize == bestSize) {
          solutions.push_back(curSet);
        }
        return;
      }

      if (curSize >= bestSize) {
        bestSize = curSize + 1;
        solutions.clear();
      }
      need = bestSize - curSize;

      const int pSize = P.popcount();
      if (pSize < need) return;

      if (pSize == 1) {
        curSet |= P;
        solutions.push_back(curSet);
        return;
      }

      for (int s = 1; s <= 12; ++s) rowHist[s] = 0;
      rCnt = 0;
      int rowMinSz = 1000;
      int rowMinId = -1;
      for (int i = 0; i < srcRowCnt; ++i) {
        const uint8_t id = srcRow[i];
        const Bitset<W> inter = P & rowSegMask[id];
        if (inter.any()) {
          const int sz = inter.popcount();
          rowIds[rCnt] = id;
          rowSzs[rCnt] = static_cast<uint8_t>(sz);
          ++rCnt;
          ++rowHist[sz];
          if (sz < rowMinSz) {
            rowMinSz = sz;
            rowMinId = id;
          }
        }
      }
      if (rCnt < need) return;

      if (rCnt == need && rowMinSz == 1) {
        const int v = (P & rowSegMask[rowMinId]).lsb();
        curSet.set(v);
        ++curSize;
        P &= nonAdj[v];
        srcRow = rowIds;
        srcRowCnt = rCnt;
        continue;
      }

      for (int s = 1; s <= 12; ++s) colHist[s] = 0;
      cCnt = 0;
      int colMinSz = 1000;
      int colMinId = -1;
      for (int i = 0; i < srcColCnt; ++i) {
        const uint8_t id = srcCol[i];
        const Bitset<W> inter = P & colSegMask[id];
        if (inter.any()) {
          const int sz = inter.popcount();
          colIds[cCnt] = id;
          colSzs[cCnt] = static_cast<uint8_t>(sz);
          ++cCnt;
          ++colHist[sz];
          if (sz < colMinSz) {
            colMinSz = sz;
            colMinId = id;
          }
        }
      }
      if (cCnt < need) return;

      if (cCnt == need && colMinSz == 1) {
        const int v = (P & colSegMask[colMinId]).lsb();
        curSet.set(v);
        ++curSize;
        P &= nonAdj[v];
        srcRow = rowIds;
        srcRowCnt = rCnt;
        srcCol = colIds;
        srcColCnt = cCnt;
        continue;
      }

      if (need == 1) {
        if (rCnt == 1 || cCnt == 1) {
          Bitset<W> rem = P;
          while (rem.any()) {
            const int v = rem.lsb();
            rem.reset(v);
            Bitset<W> sol = curSet;
            sol.set(v);
            solutions.push_back(sol);
          }
          return;
        }
        bool hasPair = false;
        Bitset<W> scan = P;
        while (scan.any()) {
          const int v = scan.lsb();
          scan.reset(v);
          if ((P & nonAdj[v]).any()) {
            hasPair = true;
            break;
          }
        }
        if (!hasPair) {
          Bitset<W> rem = P;
          while (rem.any()) {
            const int v = rem.lsb();
            rem.reset(v);
            Bitset<W> sol = curSet;
            sol.set(v);
            solutions.push_back(sol);
          }
          return;
        }
        bestSize = curSize + 2;
        solutions.clear();
        srcRow = rowIds;
        srcRowCnt = rCnt;
        srcCol = colIds;
        srcColCnt = cCnt;
        continue;
      }

      break;
    }

    const int limit = need - 1;
    Bitset<W> U = P;
    int numColors = 0;
    while (numColors < limit && U.any()) {
      Bitset<W> q = U;
      Bitset<W> col;
      while (q.any()) {
        const int v = q.lsb();
        col.set(v);
        U.reset(v);
        q.reset(v);
        q &= adjG[v];
      }
      colorScratch[numColors++] = col;
    }
    if (U.none()) return;

    if (limit >= 2) {
      Bitset<W> toTry = U;
      while (toTry.any()) {
        const int v = toTry.lsb();
        toTry.reset(v);
        bool repaired = false;
        for (int k1 = 0; k1 < limit; ++k1) {
          const Bitset<W> conflict = colorScratch[k1] & nonAdj[v];
          if (conflict.none()) {
            colorScratch[k1].set(v);
            U.reset(v);
            repaired = true;
            break;
          }
          if (conflict.isSingle()) {
            const int w = conflict.lsb();
            for (int k2 = 0; k2 < limit; ++k2) {
              if (k2 == k1) continue;
              if ((colorScratch[k2] & nonAdj[w]).none()) {
                colorScratch[k1].reset(w);
                colorScratch[k2].set(w);
                colorScratch[k1].set(v);
                U.reset(v);
                repaired = true;
                break;
              }
            }
            if (repaired) break;
          }
        }
      }
      if (U.none()) return;
    }

    const int colorBranchSize = U.popcount();

    int rowBranchSize = 0;
    {
      int needSegs = rCnt - need + 1;
      for (int s = 1; s <= 12 && needSegs > 0; ++s) {
        const int take = rowHist[s] < needSegs ? rowHist[s] : needSegs;
        rowBranchSize += take * s;
        needSegs -= take;
      }
    }

    int colBranchSize = 0;
    {
      int needSegs = cCnt - need + 1;
      for (int s = 1; s <= 12 && needSegs > 0; ++s) {
        const int take = colHist[s] < needSegs ? colHist[s] : needSegs;
        colBranchSize += take * s;
        needSegs -= take;
      }
    }

    if (colorBranchSize < rowBranchSize && colorBranchSize < colBranchSize) {
      while (U.any()) {
        if (limit + U.popcount() < bestSize - curSize) break;
        const int v = U.msb();
        U.reset(v);
        P.reset(v);
        Bitset<W> nextP = P & nonAdj[v];
        Bitset<W> nextCur = curSet;
        nextCur.set(v);
        search(nextP, nextCur, curSize + 1, rowIds, rCnt, colIds, cCnt,
               depth + 1);
      }
    } else if (rowBranchSize <= colBranchSize) {
      uint8_t* chosenSegs = chosenPool[depth];
      const int needSegs = rCnt - need + 1;
      int taken = 0;
      for (int s = 1; s <= 12 && taken < needSegs; ++s) {
        if (rowHist[s] == 0) continue;
        for (int i = 0; i < rCnt && taken < needSegs; ++i) {
          if (rowSzs[i] == s) chosenSegs[taken++] = rowIds[i];
        }
      }
      int remCliques = rCnt;
      for (int idx = 0; idx < taken; ++idx) {
        if (remCliques < bestSize - curSize) break;
        Bitset<W> seg = P & rowSegMask[chosenSegs[idx]];
        while (seg.any()) {
          const int v = seg.msb();
          seg.reset(v);
          P.reset(v);
          Bitset<W> nextP = P & nonAdj[v];
          Bitset<W> nextCur = curSet;
          nextCur.set(v);
          search(nextP, nextCur, curSize + 1, rowIds, rCnt, colIds, cCnt,
                 depth + 1);
        }
        --remCliques;
      }
    } else {
      uint8_t* chosenSegs = chosenPool[depth];
      const int needSegs = cCnt - need + 1;
      int taken = 0;
      for (int s = 1; s <= 12 && taken < needSegs; ++s) {
        if (colHist[s] == 0) continue;
        for (int i = 0; i < cCnt && taken < needSegs; ++i) {
          if (colSzs[i] == s) chosenSegs[taken++] = colIds[i];
        }
      }
      int remCliques = cCnt;
      for (int idx = 0; idx < taken; ++idx) {
        if (remCliques < bestSize - curSize) break;
        Bitset<W> seg = P & colSegMask[chosenSegs[idx]];
        while (seg.any()) {
          const int v = seg.msb();
          seg.reset(v);
          P.reset(v);
          Bitset<W> nextP = P & nonAdj[v];
          Bitset<W> nextCur = curSet;
          nextCur.set(v);
          search(nextP, nextCur, curSize + 1, rowIds, rCnt, colIds, cCnt,
                 depth + 1);
        }
        --remCliques;
      }
    }
  }

  std::vector<std::vector<std::pair<int, int>>> solve(
      const std::vector<int>& compVerts,
      const std::pair<int, int>* globalCoords,
      const Bitset<3>* globalAdj,
      const int* globalRowSeg,
      const int* globalColSeg) {
    V = static_cast<int>(compVerts.size());

    Bitset<W> rawAdj[kMaxCells];
    int globalToRaw[kMaxCells];
    for (int i = 0; i < kMaxCells; ++i) globalToRaw[i] = -1;
    for (int i = 0; i < V; ++i) globalToRaw[compVerts[i]] = i;

    for (int i = 0; i < V; ++i) {
      Bitset<3> ga = globalAdj[compVerts[i]];
      while (ga.any()) {
        const int g = ga.lsb();
        ga.reset(g);
        const int r = globalToRaw[g];
        if (r >= 0) rawAdj[i].set(r);
      }
    }

    Bitset<W> active;
    for (int i = 0; i < V; ++i) active.set(i);

    int order[kMaxCells];
    int rawToNew[kMaxCells];
    for (int pos = V - 1; pos >= 0; --pos) {
      int bestRaw = -1;
      int maxConf = -1;
      Bitset<W> s = active;
      while (s.any()) {
        const int r = s.lsb();
        s.reset(r);
        const int deg = (active & rawAdj[r]).popcount();
        if (deg > maxConf) {
          maxConf = deg;
          bestRaw = r;
        }
      }
      order[pos] = bestRaw;
      rawToNew[bestRaw] = pos;
      active.reset(bestRaw);
    }

    allVerts.clear();
    for (int i = 0; i < V; ++i) {
      allVerts.set(i);
      coords[i] = globalCoords[compVerts[order[i]]];
    }

    for (int i = 0; i < V; ++i) {
      adjG[i].clear();
      Bitset<W> ra = rawAdj[order[i]];
      while (ra.any()) {
        const int r = ra.lsb();
        ra.reset(r);
        adjG[i].set(rawToNew[r]);
      }
      for (int k = 0; k < W; ++k) {
        nonAdj[i].w[k] = allVerts.w[k] & ~adjG[i].w[k];
      }
      nonAdj[i].reset(i);
    }

    int rowMap[kMaxCells];
    int colMap[kMaxCells];
    for (int i = 0; i < kMaxCells; ++i) {
      rowMap[i] = -1;
      colMap[i] = -1;
    }
    numRowSegs = 0;
    numColSegs = 0;
    for (int i = 0; i < V; ++i) {
      const int g = compVerts[order[i]];
      const int rs = globalRowSeg[g];
      if (rowMap[rs] < 0) {
        rowMap[rs] = numRowSegs;
        rowSegMask[numRowSegs].clear();
        ++numRowSegs;
      }
      rowSegMask[rowMap[rs]].set(i);

      const int cs = globalColSeg[g];
      if (colMap[cs] < 0) {
        colMap[cs] = numColSegs;
        colSegMask[numColSegs].clear();
        ++numColSegs;
      }
      colSegMask[colMap[cs]].set(i);
    }

    bestSize = runHeuristics();
    solutions.clear();
    solutions.reserve(64);

    uint8_t initRowIds[kMaxSegs];
    uint8_t initColIds[kMaxSegs];
    for (int i = 0; i < numRowSegs; ++i) initRowIds[i] = static_cast<uint8_t>(i);
    for (int i = 0; i < numColSegs; ++i) initColIds[i] = static_cast<uint8_t>(i);

    Bitset<W> emptySet;
    search(allVerts, emptySet, 0, initRowIds, numRowSegs, initColIds,
           numColSegs, 0);

    std::vector<std::vector<std::pair<int, int>>> result;
    result.reserve(solutions.size());
    std::pair<int, int> buf[kMaxSegs];
    for (const Bitset<W>& sol : solutions) {
      int len = 0;
      Bitset<W> s = sol;
      while (s.any()) {
        const int v = s.lsb();
        s.reset(v);
        buf[len++] = coords[v];
      }
      insertionSortCoords(buf, len);
      result.emplace_back(buf, buf + len);
    }
    return result;
  }
};

template <int W>
std::vector<std::vector<std::pair<int, int>>> solveComponentWords(
    const std::vector<int>& compVerts,
    const std::pair<int, int>* globalCoords,
    const Bitset<3>* globalAdj,
    const int* globalRowSeg,
    const int* globalColSeg) {
  auto solver = std::make_unique<CompSolver<W>>();
  return solver->solve(compVerts, globalCoords, globalAdj, globalRowSeg,
                       globalColSeg);
}

}  // namespace

std::vector<std::vector<std::pair<int, int>>> solveWalled(
    int n, const std::vector<std::string>& grid) {
  if (n <= 0 || static_cast<int>(grid.size()) < n) return {};

  bool hasWall = false;
  int cellId[16][16];
  std::pair<int, int> globalCoords[kMaxCells];
  int numCells = 0;

  for (int r = 0; r < n; ++r) {
    const std::string& row = grid[r];
    for (int c = 0; c < n; ++c) {
      if (row[c] == 'W') {
        hasWall = true;
        cellId[r][c] = -1;
      } else {
        cellId[r][c] = numCells;
        globalCoords[numCells] = {r, c};
        ++numCells;
      }
    }
  }

  if (numCells == 0) return {};

  if (!hasWall && n >= 4 && n <= 12) {
    switch (n) {
      case 4:  return solveNoWallsFixed<4>();
      case 5:  return solveNoWallsFixed<5>();
      case 6:  return solveNoWallsFixed<6>();
      case 7:  return solveNoWallsFixed<7>();
      case 8:  return solveNoWallsFixed<8>();
      case 9:  return solveNoWallsFixed<9>();
      case 10: return solveNoWallsFixed<10>();
      case 11: return solveNoWallsFixed<11>();
      case 12: return solveNoWallsFixed<12>();
      default: break;
    }
  }

  Bitset<3> globalAdj[kMaxCells];
  int globalRowSeg[kMaxCells];
  int globalColSeg[kMaxCells];

  auto linkSegment = [&](const int* ids, int cnt) {
    if (cnt <= 1) return;
    Bitset<3> segMask;
    for (int i = 0; i < cnt; ++i) segMask.set(ids[i]);
    for (int i = 0; i < cnt; ++i) {
      const int u = ids[i];
      globalAdj[u] |= segMask;
      globalAdj[u].reset(u);
    }
  };

  int segBuf[16];

  int rowSegCount = 0;
  for (int r = 0; r < n; ++r) {
    int c = 0;
    while (c < n) {
      while (c < n && cellId[r][c] < 0) ++c;
      if (c >= n) break;
      int cnt = 0;
      while (c < n && cellId[r][c] >= 0) {
        const int u = cellId[r][c++];
        globalRowSeg[u] = rowSegCount;
        segBuf[cnt++] = u;
      }
      linkSegment(segBuf, cnt);
      ++rowSegCount;
    }
  }

  int colSegCount = 0;
  for (int c = 0; c < n; ++c) {
    int r = 0;
    while (r < n) {
      while (r < n && cellId[r][c] < 0) ++r;
      if (r >= n) break;
      int cnt = 0;
      while (r < n && cellId[r][c] >= 0) {
        const int u = cellId[r++][c];
        globalColSeg[u] = colSegCount;
        segBuf[cnt++] = u;
      }
      linkSegment(segBuf, cnt);
      ++colSegCount;
    }
  }

  for (int d = -(n - 1); d <= n - 1; ++d) {
    int r = (d >= 0) ? d : 0;
    int c = (d >= 0) ? 0 : -d;
    while (r < n && c < n) {
      while (r < n && c < n && cellId[r][c] < 0) {
        ++r;
        ++c;
      }
      if (r >= n || c >= n) break;
      int cnt = 0;
      while (r < n && c < n && cellId[r][c] >= 0) {
        segBuf[cnt++] = cellId[r++][c++];
      }
      linkSegment(segBuf, cnt);
    }
  }

  for (int s = 0; s <= 2 * (n - 1); ++s) {
    int r = (s < n) ? 0 : (s - (n - 1));
    int c = s - r;
    while (r < n && c >= 0) {
      while (r < n && c >= 0 && cellId[r][c] < 0) {
        ++r;
        --c;
      }
      if (r >= n || c < 0) break;
      int cnt = 0;
      while (r < n && c >= 0 && cellId[r][c] >= 0) {
        segBuf[cnt++] = cellId[r++][c--];
      }
      linkSegment(segBuf, cnt);
    }
  }

  std::vector<std::pair<int, int>> forcedCoords;
  std::vector<std::vector<std::vector<std::pair<int, int>>>> compSols;

  Bitset<3> unvisited;
  for (int i = 0; i < numCells; ++i) unvisited.set(i);

  int queue[kMaxCells];
  while (unvisited.any()) {
    const int start = unvisited.lsb();
    unvisited.reset(start);

    if (globalAdj[start].none()) {
      forcedCoords.push_back(globalCoords[start]);
      continue;
    }

    int qHead = 0, qTail = 0;
    queue[qTail++] = start;
    while (qHead < qTail) {
      const int u = queue[qHead++];
      Bitset<3> nbrs = globalAdj[u] & unvisited;
      while (nbrs.any()) {
        const int v = nbrs.lsb();
        nbrs.reset(v);
        unvisited.reset(v);
        queue[qTail++] = v;
      }
    }

    const int compSize = qTail;

    bool isClique = true;
    for (int i = 0; i < compSize; ++i) {
      if (globalAdj[queue[i]].popcount() != compSize - 1) {
        isClique = false;
        break;
      }
    }
    if (isClique) {
      std::vector<std::vector<std::pair<int, int>>> sols;
      sols.reserve(compSize);
      for (int i = 0; i < compSize; ++i) {
        sols.push_back({globalCoords[queue[i]]});
      }
      compSols.push_back(std::move(sols));
      continue;
    }

    std::vector<int> compVerts(queue, queue + compSize);
    if (compSize <= 64) {
      compSols.push_back(solveComponentWords<1>(
          compVerts, globalCoords, globalAdj, globalRowSeg, globalColSeg));
    } else if (compSize <= 128) {
      compSols.push_back(solveComponentWords<2>(
          compVerts, globalCoords, globalAdj, globalRowSeg, globalColSeg));
    } else {
      compSols.push_back(solveComponentWords<3>(
          compVerts, globalCoords, globalAdj, globalRowSeg, globalColSeg));
    }
  }

  if (compSols.empty()) {
    insertionSortCoords(forcedCoords.data(),
                        static_cast<int>(forcedCoords.size()));
    return {std::move(forcedCoords)};
  }

  if (compSols.size() == 1 && forcedCoords.empty()) {
    return std::move(compSols[0]);
  }

  size_t totalSols = 1;
  int totalQueens = static_cast<int>(forcedCoords.size());
  for (const auto& cs : compSols) {
    totalSols *= cs.size();
    totalQueens += static_cast<int>(cs[0].size());
  }

  std::vector<std::vector<std::pair<int, int>>> finalSolutions;
  finalSolutions.reserve(totalSols);

  std::pair<int, int> curBuf[kMaxCells];
  std::pair<int, int> sortedBuf[kMaxCells];
  const int baseLen = static_cast<int>(forcedCoords.size());
  for (int i = 0; i < baseLen; ++i) curBuf[i] = forcedCoords[i];

  const int numComps = static_cast<int>(compSols.size());
  auto combine = [&](auto&& self, int idx, int offset) -> void {
    if (idx == numComps) {
      for (int i = 0; i < totalQueens; ++i) sortedBuf[i] = curBuf[i];
      insertionSortCoords(sortedBuf, totalQueens);
      finalSolutions.emplace_back(sortedBuf, sortedBuf + totalQueens);
      return;
    }
    for (const auto& sub : compSols[idx]) {
      const int len = static_cast<int>(sub.size());
      for (int i = 0; i < len; ++i) curBuf[offset + i] = sub[i];
      self(self, idx + 1, offset + len);
    }
  };

  combine(combine, 0, baseLen);
  return finalSolutions;
}
