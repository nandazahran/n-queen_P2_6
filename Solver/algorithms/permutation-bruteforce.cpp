// Solver for the Normal, Pre-placed and Holes cases: brute force over the orderings of the columns.
//
// ---- The idea ------------------------------------------------------------------------------------------------------
// N queens on N rows need exactly one queen per row and no two in one column, so every candidate is an ordering (a
// permutation) of the columns 0..N-1: cols[r] is the column of the queen in row r. Rows and columns are then fine by
// construction and only the diagonals need checking.
//
// This is the slow baseline. It builds all N! orderings one after the other and filters them, with no pruning at all: no
// partial board is ever thrown away early, so the work is N! and nothing less. A big board therefore runs past the
// cutoff and ends as Failed, which is the point of having it next to the backtracking solvers.
//
// The diagonal test itself is cheap on purpose: one pass over the rows with a 32-bit mask per diagonal direction, so
// each ordering costs O(N) instead of the O(N^2) pairwise scan of the example solver. The ordering is not checked for
// holes or pre-placed queens first; those cases only restrict which orderings count as a solution.
//
//   Normal      every ordering without a shared diagonal.
//   Pre-placed  the pre-placed columns stay on their rows, and the free columns are permuted over the free rows.
//   Holes       every ordering whose queens all land off the holes.
#include <algorithm>  // std::next_permutation, std::sort
#include <cstdlib>    // std::abs
#include <numeric>    // std::iota
#include <string>
#include <utility>
#include <vector>

#include "nqueens.h"

namespace {  // names in here belong to this file only

// A Debug run keeps only the first and the last snapshots, so a rejected ordering is shown the first time and then
// every REJECT_EVERY-th time. Lower it to see more of them.
const long long REJECT_EVERY = 1000;

// Looks for two queens on one diagonal in a single pass. Returns true as soon as one is found.
// The two bitsets say which diagonals of each direction are already used.
bool sharedDiagonal(const std::vector<int>& cols) {
  const int n = static_cast<int>(cols.size());
  unsigned d1 = 0, d2 = 0;  // n <= 12 in the tester, so 2 * n - 1 <= 23 bits fit
  for (int r = 0; r < n; ++r) {
    const unsigned b1 = 1u << (r + cols[r]);
    const unsigned b2 = 1u << (r - cols[r] + n - 1);
    if ((d1 & b1) || (d2 & b2)) return true;
    d1 |= b1;
    d2 |= b2;
  }
  return false;
}

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

}  // namespace

std::vector<std::vector<int>> solveNQueens(int n) {
  std::vector<std::vector<int>> solutions;

  std::vector<int> cols(static_cast<size_t>(n));
  std::iota(cols.begin(), cols.end(), 0);  // 0, 1, 2, ... n-1: the first ordering

  long long rejected = 0;  // orderings turned down, only counted in a Debug run
  do {
    if (!sharedDiagonal(cols)) {
      solutions.push_back(cols);
      NQ_SNAPSHOT(nq::queensOf(cols), "solution " + std::to_string(solutions.size()));
    } else if (snapshotsEnabled() && (++rejected == 1 || rejected % REJECT_EVERY == 0)) {
      // Written out as a plain snapshot() call so that a normal run does not even count the rejected orderings.
      snapshot(nq::queensOf(cols), "rejected: two queens share a diagonal");
    }
  } while (std::next_permutation(cols.begin(), cols.end()));  // false after the last ordering

  return solutions;
}

std::vector<std::vector<int>> solvePreplaced(int n, const std::vector<std::pair<int, int>>& preplaced) {
  std::vector<int> fixed;
  if (!readPreplaced(n, preplaced, fixed)) return {};

  // The pre-placed queens keep their rows and columns; only the rest is permuted.
  std::vector<int> freeRows, freeCols;
  std::vector<char> columnTaken(static_cast<size_t>(n), 0);
  std::vector<int> cols(static_cast<size_t>(n), -1);
  for (int r = 0; r < n; ++r) {
    if (fixed[r] == -1) {
      freeRows.push_back(r);
    } else {
      cols[r] = fixed[r];
      columnTaken[fixed[r]] = 1;
    }
  }
  for (int c = 0; c < n; ++c)
    if (!columnTaken[c]) freeCols.push_back(c);
  if (freeRows.size() != freeCols.size()) return {};  // cannot happen once the pre-placed queens are checked

  std::vector<std::vector<int>> solutions;
  do {
    for (size_t i = 0; i < freeRows.size(); ++i) cols[freeRows[i]] = freeCols[i];
    if (!sharedDiagonal(cols)) {
      solutions.push_back(cols);
      NQ_SNAPSHOT(nq::queensOf(cols), "solution " + std::to_string(solutions.size()));
    }
  } while (std::next_permutation(freeCols.begin(), freeCols.end()));

  return solutions;
}

std::vector<std::vector<int>> solveHoles(int n, const std::vector<std::string>& grid) {
  if (static_cast<int>(grid.size()) != n) return {};
  for (const std::string& line : grid)
    if (static_cast<int>(line.size()) != n) return {};

  std::vector<std::vector<int>> solutions;

  std::vector<int> cols(static_cast<size_t>(n));
  std::iota(cols.begin(), cols.end(), 0);

  long long rejected = 0;  // orderings turned down, only counted in a Debug run
  do {
    // The lowest row whose queen sits on a hole stops the check: the queens above it are still worth showing.
    int holeRow = -1;
    for (int r = 0; r < n; ++r) {
      if (grid[r][cols[r]] == 'H') {
        holeRow = r;
        break;
      }
    }
    if (holeRow >= 0) {
      if (snapshotsEnabled() && (++rejected == 1 || rejected % REJECT_EVERY == 0)) {
        std::vector<int> above(cols.begin(), cols.begin() + holeRow);
        above.resize(static_cast<size_t>(n), -1);  // the rows not reached yet are drawn empty
        snapshot(nq::queensOf(above), "rejected: (" + std::to_string(holeRow) + "," +
                                          std::to_string(cols[holeRow]) + ") is a hole");
      }
      continue;
    }
    if (!sharedDiagonal(cols)) {
      solutions.push_back(cols);
      NQ_SNAPSHOT(nq::queensOf(cols), "solution " + std::to_string(solutions.size()));
    }
  } while (std::next_permutation(cols.begin(), cols.end()));

  return solutions;
}
