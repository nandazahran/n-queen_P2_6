// Solver for the Normal, Pre-placed and Holes cases: backtracking that fills the most constrained row next (MRV).
//
// ---- The idea ------------------------------------------------------------------------------------------------------
// The plain backtracking solvers fill the rows in order. This one picks, at every step, the row with the fewest columns
// still open (the "minimum remaining values" heuristic): that is the row closest to a dead end, so a failing branch is
// cut as early as possible and the tree stays narrow. A row down to zero columns ends the branch immediately.
//
// Rows are therefore filled out of order, so `cols[r]` is -1 for every row not filled yet. The taken cells are kept as
// one column bitmask plus two per-cell tables indexed by the absolute diagonal numbers `row + column` and
// `row - column + N - 1`. A hole clears one bit of its own row.
//
//   Normal      no pre-placed queens, no holes.
//   Pre-placed  the pre-placed queens are placed up front, so their rows never take part in the choice.
//   Holes       the hole bits are the only difference.
#include <cstdlib>  // std::abs
#include <string>
#include <utility>
#include <vector>

#include "nqueens.h"

namespace {  // names in here belong to this file only

// A Debug run keeps only the first and the last snapshots, so a dead end is shown the first time and then every
// DEAD_END_EVERY-th time. Lower it to see more of them.
const long long DEAD_END_EVERY = 1000;

// Checks that the pre-placed queens fit an N x N board and do not attack each other.
// On success `fixed[r]` is the column of the pre-placed queen in row r, or -1 when row r is still free.
bool readPreplaced(int n, const std::vector<std::pair<int, int>>& preplaced, std::vector<int>& fixed) {
  fixed.assign(n, -1);
  for (const auto& queen : preplaced) {
    const int r = queen.first, c = queen.second;
    if (r < 0 || r >= n || c < 0 || c >= n) return false;  // off the board
    if (fixed[r] != -1) return false;                      // two queens in one row
    fixed[r] = c;
  }
  for (size_t i = 0; i < preplaced.size(); ++i) {
    for (size_t j = i + 1; j < preplaced.size(); ++j) {
      const int r1 = preplaced[i].first, c1 = preplaced[i].second;
      const int r2 = preplaced[j].first, c2 = preplaced[j].second;
      if (c1 == c2 || std::abs(c1 - c2) == std::abs(r1 - r2)) return false;  // share a column or a diagonal
    }
  }
  return true;
}

struct MrvSearch {
  int n = 0;
  int full = 0;                    // n columns set
  std::vector<int> cols;           // cols[r] = column of row r, -1 = not placed
  int colUsedMask = 0;             // columns that are taken
  std::vector<char> d1, d2;        // diagonal r + c, and diagonal r - c + n - 1, are taken
  std::vector<int> holeMask;       // bit c set when the cell (r, c) is a hole
  std::vector<std::vector<int>> solutions;
  long long deadEnds = 0;          // only counted in a Debug run

  // The columns that are still open in `row`, as a bitmask.
  int available(int row) const {
    int avail = full & ~colUsedMask;
    for (int c = 0; c < n; ++c)
      if (d1[row + c] || d2[row - c + n - 1]) avail &= ~(1 << c);
    return avail & ~holeMask[row];
  }

  void place(int row, int c) {
    cols[row] = c;
    colUsedMask |= 1 << c;
    d1[row + c] = 1;
    d2[row - c + n - 1] = 1;
  }

  void unplace(int row, int c) {
    cols[row] = -1;
    colUsedMask &= ~(1 << c);
    d1[row + c] = 0;
    d2[row - c + n - 1] = 0;
  }

  void run(const std::vector<int>& preplacedColumns, const std::vector<std::string>& grid) {
    cols.assign(static_cast<size_t>(n), -1);
    colUsedMask = 0;
    d1.assign(2 * static_cast<size_t>(n), 0);
    d2.assign(2 * static_cast<size_t>(n), 0);
    holeMask.assign(static_cast<size_t>(n), 0);
    if (static_cast<int>(grid.size()) == n) {
      for (int r = 0; r < n; ++r)
        for (int c = 0; c < n; ++c)
          if (grid[r][c] == 'H') holeMask[r] |= 1 << c;
    }
    for (int r = 0; r < n; ++r)
      if (preplacedColumns[r] >= 0) place(r, preplacedColumns[r]);
    search();
  }

  void search() {
    // Pick the unfilled row with the fewest open columns. Ties go to the lowest row, so the answer is deterministic.
    int bestRow = -1, bestAvail = 0, bestCount = 0;
    for (int r = 0; r < n; ++r) {
      if (cols[r] != -1) continue;
      const int avail = available(r);
      const int count = __builtin_popcount(static_cast<unsigned>(avail));
      if (bestRow == -1 || count < bestCount) {
        bestRow = r;
        bestAvail = avail;
        bestCount = count;
        if (count == 0) break;  // nothing can beat a dead end
      }
    }
    if (bestRow == -1) {
      solutions.push_back(cols);
      NQ_SNAPSHOT(nq::queensOf(cols), "solution " + std::to_string(solutions.size()));
      return;
    }
    if (bestCount == 0) {
      // Written out as a plain snapshot() call so that a normal run does not even count the dead ends.
      if (snapshotsEnabled() && (++deadEnds == 1 || deadEnds % DEAD_END_EVERY == 0))
        snapshot(nq::queensOf(cols), "dead end at row " + std::to_string(bestRow));
      return;
    }
    while (bestAvail) {
      const int bit = bestAvail & -bestAvail;
      const int c = __builtin_ctz(static_cast<unsigned>(bit));
      place(bestRow, c);
      search();
      unplace(bestRow, c);
      bestAvail -= bit;
    }
  }
};

}  // namespace

std::vector<std::vector<int>> solveNQueens(int n) {
  MrvSearch search;
  search.n = n;
  search.full = (1 << n) - 1;
  search.run(std::vector<int>(static_cast<size_t>(n), -1), std::vector<std::string>());
  return search.solutions;
}

std::vector<std::vector<int>> solvePreplaced(int n, const std::vector<std::pair<int, int>>& preplaced) {
  std::vector<int> fixed;
  if (!readPreplaced(n, preplaced, fixed)) return {};

  MrvSearch search;
  search.n = n;
  search.full = (1 << n) - 1;
  search.run(fixed, std::vector<std::string>());
  return search.solutions;
}

std::vector<std::vector<int>> solveHoles(int n, const std::vector<std::string>& grid) {
  if (static_cast<int>(grid.size()) != n) return {};
  for (const std::string& line : grid)
    if (static_cast<int>(line.size()) != n) return {};

  MrvSearch search;
  search.n = n;
  search.full = (1 << n) - 1;
  search.run(std::vector<int>(static_cast<size_t>(n), -1), grid);
  return search.solutions;
}
