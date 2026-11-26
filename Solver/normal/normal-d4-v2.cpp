// Ultra-optimized D4 canonical border-symmetry bitmask solver.
// Combines:
// 1. Compact GenericD4 for N = 4..9 (keeps WASM binary small for fast JIT
// warmup in fresh workers).
// 2. Compile-time N specialization for N = 10..12 with 4-row terminal fusion
// (inlines N-3..N-1 into N-4).
// 3. 1-step forward lookahead (passes precomputed `avail` to avoid dead-end
// calls) + early last-row check.
// 4. Compile-time guarded deadline checks (Row + 1 >= N / 2 - 1) and zero heap
// allocations during search.
#include "nqueens.h"
#include <cstdint>
#include <vector>

namespace {

constexpr int kMaxN = 16;

// ============================================================================
// Compact Generic D4 Solver (N = 4..9) - minimizes WASM code bloat
// ============================================================================
struct GenericD4 {

  int n = 0;
  int m = 0;
  uint32_t full = 0;
  uint32_t highBit = 0;
  uint32_t rowMask[kMaxN]{};
  uint32_t rowBit[kMaxN]{};
  int c0 = 0;
  int mc0 = 0;
  int deadlineM = 0;
  int deadline0 = 0;
  uint32_t bitMC0 = 0;

  uint64_t orb8Buf[256];
  int orb8Count = 0;
  uint64_t symBuf[64];
  int symCount = 0;
  size_t totalSolutions = 0;

  inline uint64_t packBits() const {
    uint64_t p = 0;
    for (int r = n - 1; r >= 0; --r) {
      p = (p << 4) | static_cast<uint64_t>(__builtin_ctz(rowBit[r]));
    }
    return p;
  }

  inline void pushOrb8(uint64_t p) {
    orb8Buf[orb8Count++] = p;
    totalSolutions += 8;
  }

  inline void pushSym(uint64_t p, bool orb2) {
    symBuf[symCount++] = p | (orb2 ? (1ULL << 63) : 0ULL);
    totalSolutions += orb2 ? 2 : 4;
  }

  void onInteriorLeaf(uint32_t colM1) {
    const bool tie180 = (colM1 == bitMC0);
    const bool tie90 = (rowBit[mc0] == 1u);
    const bool tie270 = (rowBit[c0] == highBit);
    if (!(tie180 | tie90 | tie270)) {
      pushOrb8(packBits());
      return;
    }

    uint8_t cols[kMaxN];
    for (int r = 0; r < n; ++r) {
      cols[r] = static_cast<uint8_t>(__builtin_ctz(rowBit[r]));
    }

    bool sym180 = tie180;
    if (tie180) {
      for (int r = 1; r <= m / 2; ++r) {
        const int v = m - cols[m - r];
        if (v != cols[r]) {
          if (v < cols[r])
            return;
          sym180 = false;
          break;
        }
      }
    }

    bool sym90 = false;
    if (tie90 | tie270) {
      uint8_t inv[kMaxN];
      for (int r = 0; r < n; ++r)
        inv[cols[r]] = static_cast<uint8_t>(r);
      if (tie90) {
        bool eq = true;
        for (int r = 1; r < n; ++r) {
          const int v = m - inv[r];
          if (v != cols[r]) {
            if (v < cols[r])
              return;
            eq = false;
            break;
          }
        }
        if (eq)
          sym90 = true;
      }
      if (tie270 && !sym90) {
        bool eq = true;
        for (int r = 1; r < n; ++r) {
          const int v = inv[m - r];
          if (v != cols[r]) {
            if (v < cols[r])
              return;
            eq = false;
            break;
          }
        }
        if (eq)
          sym90 = true;
      }
    }

    uint64_t p = 0;
    for (int r = n - 1; r >= 0; --r)
      p = (p << 4) | cols[r];
    if (sym90)
      pushSym(p, true);
    else if (sym180)
      pushSym(p, false);
    else
      pushOrb8(p);
  }

  template <bool Corner>
  void dfs(int row, uint32_t freeCol, uint32_t d1, uint32_t d2) {
    if (row == n - 2) {
      const uint32_t a = freeCol & (0u - freeCol);
      const uint32_t c = freeCol ^ a;
      if (c == (a << 1))
        return;
      const uint32_t okM2 = rowMask[n - 2] & ~(d1 | d2);
      const uint32_t okM1 = rowMask[n - 1] & ~((d1 << 1) | (d2 >> 1));
      if ((a & okM2) && (c & okM1)) {
        rowBit[n - 2] = a;
        rowBit[n - 1] = c;
        if constexpr (Corner)
          pushOrb8(packBits());
        else
          onInteriorLeaf(c);
      }
      if ((c & okM2) && (a & okM1)) {
        rowBit[n - 2] = c;
        rowBit[n - 1] = a;
        if constexpr (Corner)
          pushOrb8(packBits());
        else
          onInteriorLeaf(a);
      }
      return;
    }
    uint32_t avail = freeCol & rowMask[row] & ~(d1 | d2);
    if constexpr (!Corner) {
      if (row == deadlineM && (freeCol & highBit))
        avail &= highBit;
      else if (row == deadline0 && (freeCol & 1u))
        avail &= 1u;
    }
    while (avail) {
      const uint32_t b = avail & (0u - avail);
      avail ^= b;
      rowBit[row] = b;
      dfs<Corner>(row + 1, freeCol ^ b, (d1 | b) << 1, (d2 | b) >> 1);
    }
  }

  std::vector<std::vector<int>> solve(int size) {
    n = size;
    m = size - 1;
    full = (1u << n) - 1u;
    highBit = 1u << m;

    rowBit[0] = 1u;
    for (int c1 = 2; c1 < m; ++c1) {
      const uint32_t b1 = 1u << c1;
      rowBit[1] = b1;
      if (c1 == m - 1) {
        for (int r = 2; r < m; ++r) {
          uint32_t mask = full & ~2u;
          const int diagCol = 1 + m - r;
          if (diagCol < n)
            mask &= ~(1u << diagCol);
          rowMask[r] = mask;
        }
        rowMask[m] = 2u;
      } else {
        for (int r = 2; r < n; ++r) {
          rowMask[r] = (r < c1) ? (full & ~2u) : full;
        }
      }
      dfs<true>(2, full ^ (1u | b1), (2u | b1) << 1, b1 >> 1);
    }

    const uint32_t noSides = full & ~(1u | highBit);
    const int maxC0 = (n - 2) / 2;
    for (int c = 1; c <= maxC0; ++c) {
      c0 = c;
      mc0 = m - c;
      deadlineM = mc0 - 1;
      deadline0 = mc0;
      bitMC0 = 1u << mc0;

      const uint32_t b0 = 1u << c;
      rowBit[0] = b0;
      for (int r = 1; r < m; ++r) {
        rowMask[r] = (r < c || r > mc0) ? noSides : full;
      }
      rowMask[c] &= ~1u;
      rowMask[mc0] &= ~highBit;
      rowMask[m] = (((1u << (n - 2 * c)) - 1u) << c) & ~b0;
      dfs<false>(1, full ^ b0, b0 << 1, b0 >> 1);
    }

    std::vector<std::vector<int>> solutions;
    solutions.reserve(totalSolutions);
    int b0[kMaxN], b1[kMaxN], b2[kMaxN], b3[kMaxN];
    int b4[kMaxN], b5[kMaxN], b6[kMaxN], b7[kMaxN];
    for (int i = 0; i < orb8Count; ++i) {
      uint64_t p = orb8Buf[i];
      for (int r = 0; r < n; ++r) {
        const int c = static_cast<int>(p & 0xFu);
        p >>= 4;
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
      solutions.emplace_back(b0, b0 + n);
      solutions.emplace_back(b1, b1 + n);
      solutions.emplace_back(b2, b2 + n);
      solutions.emplace_back(b3, b3 + n);
      solutions.emplace_back(b4, b4 + n);
      solutions.emplace_back(b5, b5 + n);
      solutions.emplace_back(b6, b6 + n);
      solutions.emplace_back(b7, b7 + n);
    }
    for (int i = 0; i < symCount; ++i) {
      const uint64_t entry = symBuf[i];
      const bool orb2 = (entry >> 63) != 0;
      uint64_t p = entry;
      if (orb2) {
        for (int r = 0; r < n; ++r) {
          const int c = static_cast<int>(p & 0xFu);
          p >>= 4;
          b0[r] = c;
          b1[r] = m - c;
        }
        solutions.emplace_back(b0, b0 + n);
        solutions.emplace_back(b1, b1 + n);
      } else {
        for (int r = 0; r < n; ++r) {
          const int c = static_cast<int>(p & 0xFu);
          p >>= 4;
          b0[r] = c;
          b1[r] = m - c;
          b4[c] = r;
          b5[c] = m - r;
        }
        solutions.emplace_back(b0, b0 + n);
        solutions.emplace_back(b1, b1 + n);
        solutions.emplace_back(b4, b4 + n);
        solutions.emplace_back(b5, b5 + n);
      }
    }
    return solutions;
  }
};

// ============================================================================
// Compile-Time Specialized Ultra-Fast D4 Bitmask Solver (N = 10, 11, 12)
// ============================================================================
template <int N> struct UltraSolver {
  static constexpr int M = N - 1;
  static constexpr uint32_t FULL = (1u << N) - 1u;
  static constexpr uint32_t HIGH_BIT = 1u << M;
  static constexpr int kOrb8Cap = (N == 10) ? 128 : (N == 11 ? 512 : 2048);
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

  uint64_t symBuf[kSymCap];
  int symCount = 0;

  size_t totalSolutions = 0;

  __attribute__((always_inline)) inline uint64_t packFromBits() const {
    uint64_t p = 0;
    for (int r = N - 1; r >= 0; --r) {
      p = (p << 4) | static_cast<uint64_t>(__builtin_ctz(rowBit[r]));
    }
    return p;
  }

  __attribute__((always_inline)) inline void pushOrbit8(uint64_t packed) {
    orb8Buf[orb8Count++] = packed;
    totalSolutions += 8;
  }

  __attribute__((always_inline)) inline void pushSym(uint64_t packed,
                                                     bool isOrb2) {
    symBuf[symCount++] = packed | (isOrb2 ? (1ULL << 63) : 0ULL);
    totalSolutions += isOrb2 ? 2 : 4;
  }

  inline void onInteriorLeaf(uint32_t colM1) {
    const bool tie180 = (colM1 == bitMC0);
    const bool tie90 = (rowBit[mc0] == 1u);
    const bool tie270 = (rowBit[c0] == HIGH_BIT);

    if (!(tie180 | tie90 | tie270)) {
      pushOrbit8(packFromBits());
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
          if (v < cols[r])
            return;
          sym180 = false;
          break;
        }
      }
    }

    bool sym90 = false;
    if (tie90 | tie270) {
      uint8_t inv[N];
      for (int r = 0; r < N; ++r)
        inv[cols[r]] = static_cast<uint8_t>(r);

      if (tie90) {
        bool eq = true;
        for (int r = 1; r < N; ++r) {
          const int v = M - inv[r];
          if (v != cols[r]) {
            if (v < cols[r])
              return;
            eq = false;
            break;
          }
        }
        if (eq)
          sym90 = true;
      }

      if (tie270 && !sym90) {
        bool eq = true;
        for (int r = 1; r < N; ++r) {
          const int v = inv[M - r];
          if (v != cols[r]) {
            if (v < cols[r])
              return;
            eq = false;
            break;
          }
        }
        if (eq)
          sym90 = true;
      }
    }

    uint64_t p = 0;
    for (int r = N - 1; r >= 0; --r) {
      p = (p << 4) | static_cast<uint64_t>(cols[r]);
    }
    if (sym90)
      pushSym(p, true);
    else if (sym180)
      pushSym(p, false);
    else
      pushOrbit8(p);
  }

  template <bool Corner>
  __attribute__((always_inline)) inline void
  resolveLast3(uint32_t avail3, uint32_t free3, uint32_t d1_3, uint32_t d2_3,
               uint32_t maskM2, uint32_t maskM1) {
    do {
      const uint32_t b = avail3 & (0u - avail3);
      avail3 ^= b;
      const uint32_t rem2 = free3 ^ b;
      const uint32_t a = rem2 & (0u - rem2);
      const uint32_t c = rem2 ^ a;
      if (c == (a << 1))
        continue;

      const uint32_t nd1 = (d1_3 | b) << 1;
      const uint32_t nd2 = (d2_3 | b) >> 1;
      const uint32_t okM2 = maskM2 & ~(nd1 | nd2);
      const uint32_t okM1 = maskM1 & ~((nd1 << 1) | (nd2 >> 1));

      if ((a & okM2) && (c & okM1)) {
        rowBit[N - 3] = b;
        rowBit[N - 2] = a;
        rowBit[N - 1] = c;
        if constexpr (Corner)
          pushOrbit8(packFromBits());
        else
          onInteriorLeaf(c);
      }
      if ((c & okM2) && (a & okM1)) {
        rowBit[N - 3] = b;
        rowBit[N - 2] = c;
        rowBit[N - 1] = a;
        if constexpr (Corner)
          pushOrbit8(packFromBits());
        else
          onInteriorLeaf(a);
      }
    } while (avail3);
  }

  // `avail` is precomputed by the parent and guaranteed non-zero.
  template <int Row, bool Corner>
  void dfs(uint32_t avail, uint32_t freeCol, uint32_t d1, uint32_t d2) {
    if constexpr (Row == N - 4) {
      // Inline N-3..N-1 directly inside N-4 to eliminate ~31k recursive calls
      // at N=12.
      const uint32_t maskM3 = rowMask[N - 3];
      const uint32_t maskM2 = rowMask[N - 2];
      const uint32_t maskM1 = rowMask[N - 1];
      do {
        const uint32_t b = avail & (0u - avail);
        avail ^= b;
        const uint32_t nextFree = freeCol ^ b;
        if constexpr (!Corner) {
          if ((nextFree & maskM1) == 0)
            continue;
        }
        const uint32_t nd1 = (d1 | b) << 1;
        const uint32_t nd2 = (d2 | b) >> 1;
        uint32_t avail3 = nextFree & maskM3 & ~(nd1 | nd2);
        if constexpr (!Corner) {
          if (N - 3 == deadlineM && (nextFree & HIGH_BIT))
            avail3 &= HIGH_BIT;
          else if (N - 3 == deadline0 && (nextFree & 1u))
            avail3 &= 1u;
        }
        if (avail3) {
          rowBit[N - 4] = b;
          resolveLast3<Corner>(avail3, nextFree, nd1, nd2, maskM2, maskM1);
        }
      } while (avail);
    } else {
      const uint32_t nextMask = rowMask[Row + 1];
      const uint32_t lastMask = rowMask[N - 1];
      do {
        const uint32_t b = avail & (0u - avail);
        avail ^= b;
        const uint32_t nextFree = freeCol ^ b;
        if constexpr (!Corner) {
          if ((nextFree & lastMask) == 0)
            continue;
        }
        const uint32_t nd1 = (d1 | b) << 1;
        const uint32_t nd2 = (d2 | b) >> 1;
        uint32_t nav = nextFree & nextMask & ~(nd1 | nd2);
        if constexpr (!Corner && (Row + 1) >= (N / 2 - 1)) {
          if (Row + 1 == deadlineM && (nextFree & HIGH_BIT))
            nav &= HIGH_BIT;
          else if (Row + 1 == deadline0 && (nextFree & 1u))
            nav &= 1u;
        }
        if (nav) {
          rowBit[Row] = b;
          dfs<Row + 1, Corner>(nav, nextFree, nd1, nd2);
        }
      } while (avail);
    }
  }

  void run() {
    // 1. Corner Class: cols[0] = 0, cols[1] = c1 (2 <= c1 <= M - 1)
    rowBit[0] = 1u;
    for (int c1 = 2; c1 < M; ++c1) {
      const uint32_t b1 = 1u << c1;
      rowBit[1] = b1;
      if (c1 == M - 1) {
        for (int r = 2; r < M; ++r) {
          uint32_t mask = FULL & ~2u;
          const int diagCol = 1 + M - r;
          if (diagCol < N)
            mask &= ~(1u << diagCol);
          rowMask[r] = mask;
        }
        rowMask[M] = 2u;
      } else {
        for (int r = 2; r < N; ++r) {
          rowMask[r] = (r < c1) ? (FULL & ~2u) : FULL;
        }
      }
      const uint32_t f2 = FULL ^ (1u | b1);
      const uint32_t d1_2 = (2u | b1) << 1;
      const uint32_t d2_2 = b1 >> 1;
      const uint32_t av2 = f2 & rowMask[2] & ~(d1_2 | d2_2);
      if (av2)
        dfs<2, true>(av2, f2, d1_2, d2_2);
    }

    // 2. Interior Class: 1 <= c0 <= (N - 2) / 2
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
              if (colA >= 0)
                mask &= ~(1u << colA);
              const int colB = (r > c + 1) ? (r - (c + 1)) : ((c + 1) - r);
              if (colB < N)
                mask &= ~(1u << colB);
              const int dC = M - r;
              if (c + 1 + dC < N)
                mask &= ~(1u << (c + 1 + dC));
              if (c + 1 - dC >= 0)
                mask &= ~(1u << (c + 1 - dC));
              rowMask[r] = mask;
              if (mask == 0)
                dead = true;
            }
          }
          if (dead)
            continue;
          rowMask[M] = 1u << (c + 1);
        }
      }

      const uint32_t f1 = FULL ^ b0;
      const uint32_t d1_1 = b0 << 1;
      const uint32_t d2_1 = b0 >> 1;
      const uint32_t av1 = f1 & rowMask[1] & ~(d1_1 | d2_1);
      if (av1)
        dfs<1, false>(av1, f1, d1_1, d2_1);
    }
  }

  std::vector<std::vector<int>> materialize() const {
    std::vector<std::vector<int>> solutions;
    solutions.reserve(totalSolutions);

    int b0[N], b1[N], b2[N], b3[N], b4[N], b5[N], b6[N], b7[N];
    for (int i = 0; i < orb8Count; ++i) {
      uint64_t p = orb8Buf[i];
      for (int r = 0; r < N; ++r) {
        const int c = static_cast<int>(p & 0xFu);
        p >>= 4;
        const int mc = M - c;
        const int mr = M - r;
        b0[r] = c;
        b1[r] = mc;
        b2[mr] = c;
        b3[mr] = mc;
        b4[c] = r;
        b5[c] = mr;
        b6[mc] = r;
        b7[mc] = mr;
      }
      solutions.emplace_back(b0, b0 + N);
      solutions.emplace_back(b1, b1 + N);
      solutions.emplace_back(b2, b2 + N);
      solutions.emplace_back(b3, b3 + N);
      solutions.emplace_back(b4, b4 + N);
      solutions.emplace_back(b5, b5 + N);
      solutions.emplace_back(b6, b6 + N);
      solutions.emplace_back(b7, b7 + N);
    }

    for (int i = 0; i < symCount; ++i) {
      const uint64_t entry = symBuf[i];
      const bool isOrb2 = (entry >> 63) != 0;
      uint64_t p = entry;
      if (isOrb2) {
        for (int r = 0; r < N; ++r) {
          const int c = static_cast<int>(p & 0xFu);
          p >>= 4;
          b0[r] = c;
          b1[r] = M - c;
        }
        solutions.emplace_back(b0, b0 + N);
        solutions.emplace_back(b1, b1 + N);
      } else {
        for (int r = 0; r < N; ++r) {
          const int c = static_cast<int>(p & 0xFu);
          p >>= 4;
          b0[r] = c;
          b1[r] = M - c;
          b4[c] = r;
          b5[c] = M - r;
        }
        solutions.emplace_back(b0, b0 + N);
        solutions.emplace_back(b1, b1 + N);
        solutions.emplace_back(b4, b4 + N);
        solutions.emplace_back(b5, b5 + N);
      }
    }

    return solutions;
  }
};

template <int N> std::vector<std::vector<int>> solveFixed() {
  UltraSolver<N> solver;
  solver.run();
  return solver.materialize();
}

std::vector<std::vector<int>> solveFallback(int n) {
  std::vector<std::vector<int>> solutions;
  const uint32_t full = (1u << n) - 1u;
  int cur[16];
  auto dfs = [&](auto &&self, int row, uint32_t freeCol, uint32_t d1,
                 uint32_t d2) -> void {
    uint32_t avail = freeCol & ~(d1 | d2);
    if (row == n - 1) {
      if (avail) {
        cur[row] = __builtin_ctz(avail);
        solutions.emplace_back(cur, cur + n);
      }
      return;
    }
    while (avail) {
      const uint32_t b = avail & (0u - avail);
      avail ^= b;
      cur[row] = __builtin_ctz(b);
      self(self, row + 1, freeCol ^ b, (d1 | b) << 1, (d2 | b) >> 1);
    }
  };
  dfs(dfs, 0, full, 0u, 0u);
  return solutions;
}

} // namespace

std::vector<std::vector<int>> solveNQueens(int n) {
  switch (n) {
  case 1:
    return {{0}};
  case 4:
  case 5:
  case 6:
  case 7:
  case 8:
  case 9: {
    GenericD4 solver;
    return solver.solve(n);
  }
  case 10:
    return solveFixed<10>();
  case 11:
    return solveFixed<11>();
  case 12:
    return solveFixed<12>();
  default:
    if (n >= 13 && n <= 16)
      return solveFallback(n);
    return {};
  }
}
