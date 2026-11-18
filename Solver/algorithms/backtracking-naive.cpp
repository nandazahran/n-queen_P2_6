// Solver for the Normal, Pre-placed and Holes cases: recursive backtracking, one row at a time.
//
// ---- The idea ------------------------------------------------------------------------------------------------------
// A board holds one queen per row, so the rows are filled in order. Three tables remember what is already taken: the
// columns, the diagonals going down-right (row + column) and the diagonals going down-left (row - column + N - 1). The
// current row then only tries the columns that all three tables leave free.
//
// The three cases differ in one thing only: the list of rows still to fill.
//   Normal      every row is free.
//   Pre-placed  the rows holding a pre-placed queen are marked as taken up front, so the search never revisits them.
//   Holes       every row is free, but a hole removes one candidate column of its own row. Attacks pass through a hole,
//               so the tables are not changed by it.
//
// A row with no free column is a dead end, and the search steps back to the row above.
#include <cstdlib>  // std::abs
#include <numeric>  // std::iota
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

struct Search {
  int n = 0;
  std::vector<int> rows;           // rows still to fill, in the order the search fills them
  std::vector<int> cols;           // cols[r] = column of row r, -1 = not placed
  std::vector<char> colUsed;       // column c is taken
  std::vector<char> d1, d2;        // diagonal r + c, and diagonal r - c + n - 1, are taken
  std::vector<int> holeMask;       // bit c set when the cell (r, c) is a hole
  std::vector<std::vector<int>> solutions;
  long long deadEnds = 0;          // only counted in a Debug run

  void place(int row, int c) {
    cols[row] = c;
    colUsed[c] = 1;
    d1[row + c] = 1;
    d2[row - c + n - 1] = 1;
  }

  void unplace(int row) {
    const int c = cols[row];
    colUsed[c] = 0;
    d1[row + c] = 0;
    d2[row - c + n - 1] = 0;
    cols[row] = -1;
  }

  bool available(int row, int c) const {
    return !colUsed[c] && !d1[row + c] && !d2[row - c + n - 1] && !(holeMask[row] & (1 << c));
  }

  // The rows of `grid` that hold a 'H'.
  void readHoles(const std::vector<std::string>& grid) {
    holeMask.assign(n, 0);
    for (int r = 0; r < n; ++r)
      for (int c = 0; c < n; ++c)
        if (grid[r][c] == 'H') holeMask[r] |= 1 << c;
  }

  void run(int size, const std::vector<int>& fillRows) {
    n = size;
    rows = fillRows;
    cols.assign(n, -1);
    colUsed.assign(n, 0);
    d1.assign(2 * static_cast<size_t>(n), 0);
    d2.assign(2 * static_cast<size_t>(n), 0);
    holeMask.assign(n, 0);
    search(0);
  }

  void search(int idx) {
    if (idx == static_cast<int>(rows.size())) {
      solutions.push_back(cols);
      NQ_SNAPSHOT(nq::queensOf(cols), "solution " + std::to_string(solutions.size()));
      return;
    }
    const int row = rows[idx];
    bool tried = false;
    for (int c = 0; c < n; ++c) {
      if (!available(row, c)) continue;
      tried = true;
      place(row, c);
      search(idx + 1);
      unplace(row);
    }
    if (tried || !snapshotsEnabled()) return;
    // No column was free for this row: show the board so far. It is written out as a plain snapshot() call so that a
    // normal run does not even count the dead ends.
    if (++deadEnds == 1 || deadEnds % DEAD_END_EVERY == 0)
      snapshot(nq::queensOf(cols), "dead end at row " + std::to_string(row));
  }
};

}  // namespace

std::vector<std::vector<int>> solveNQueens(int n) {
  Search search;
  std::vector<int> rows(static_cast<size_t>(n));
  std::iota(rows.begin(), rows.end(), 0);
  search.run(n, rows);
  return search.solutions;
}

std::vector<std::vector<int>> solvePreplaced(int n, const std::vector<std::pair<int, int>>& preplaced) {
  std::vector<int> fixed;
  if (!readPreplaced(n, preplaced, fixed)) return {};

  Search search;
  std::vector<int> rows;
  search.n = n;
  search.cols.assign(fixed.begin(), fixed.end());
  search.colUsed.assign(n, 0);
  search.d1.assign(2 * static_cast<size_t>(n), 0);
  search.d2.assign(2 * static_cast<size_t>(n), 0);
  search.holeMask.assign(n, 0);
  for (int r = 0; r < n; ++r) {
    if (fixed[r] == -1) {
      rows.push_back(r);
      continue;
    }
    search.colUsed[fixed[r]] = 1;
    search.d1[r + fixed[r]] = 1;
    search.d2[r - fixed[r] + n - 1] = 1;
  }
  search.rows = rows;
  search.search(0);
  return search.solutions;
}

std::vector<std::vector<int>> solveHoles(int n, const std::vector<std::string>& grid) {
  if (static_cast<int>(grid.size()) != n) return {};
  for (const std::string& line : grid)
    if (static_cast<int>(line.size()) != n) return {};

  Search search;
  std::vector<int> rows(static_cast<size_t>(n));
  std::iota(rows.begin(), rows.end(), 0);
  search.n = n;
  search.cols.assign(n, -1);
  search.colUsed.assign(n, 0);
  search.d1.assign(2 * static_cast<size_t>(n), 0);
  search.d2.assign(2 * static_cast<size_t>(n), 0);
  search.readHoles(grid);
  search.rows = rows;
  search.search(0);
  return search.solutions;
}
