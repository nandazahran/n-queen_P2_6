// Solver for the Walled case: the board as a graph, and the answer as its largest independent set.
//
// ---- The idea ------------------------------------------------------------------------------------------------------
// Two queens may stand on the board together exactly when they do not attack each other, and a wall between them stops
// the attack. So build a graph whose vertices are the free cells and whose edges join two cells that attack each other.
// A board is then an independent set of that graph, and the largest board is a maximum independent set.
//
// A maximum independent set of a graph is a maximum clique of its complement, and maximum clique has a strong exact
// algorithm: Bron-Kerbosch with a greedy colouring bound (Tomita's MCQ). The colouring splits the candidates into
// classes of mutually non-adjacent vertices, and a clique takes at most one vertex per class, so the class number of a
// candidate is an upper bound on how many more vertices a clique through it can hold. A branch is dropped as soon as
// that bound cannot beat the best board found so far; equal is still explored, because the answer is every board of the
// maximum size.
//
// This is a different bound from the one in walled-branch-bound.cpp, which counts the row and column runs a wall leaves
// behind. Counting runs is tight when there are no walls and loose when there are many; the colouring bound adapts to
// the actual attack graph.
#include <algorithm>  // std::find
#include <cstdint>
#include <cstdlib>  // std::abs
#include <string>
#include <utility>
#include <vector>

#include "nqueens.h"

namespace {  // names in here belong to this file only

// True when a wall stands strictly between the two cells. They must share a row, a column or a diagonal.
bool wallBetween(const std::vector<std::string>& grid, int r1, int c1, int r2, int c2) {
  const int dr = (r2 > r1) - (r2 < r1);
  const int dc = (c2 > c1) - (c2 < c1);
  for (int r = r1 + dr, c = c1 + dc; r != r2 || c != c2; r += dr, c += dc)
    if (grid[r][c] == 'W') return true;
  return false;
}

struct WalledClique {
  int n = 0;
  std::vector<std::pair<int, int>> cellOf;      // vertex -> (row, column)
  std::vector<std::vector<uint64_t>> adj;       // complement graph: 1 = the two cells can hold queens together
  std::vector<int> clique;                      // vertices of the board being built
  std::vector<std::vector<std::pair<int, int>>> best;
  int bestSize = 0;

  WalledClique(int size, const std::vector<std::string>& grid) : n(size) { build(grid); }

  std::vector<std::vector<std::pair<int, int>>> run() {
    std::vector<int> all(static_cast<size_t>(cellOf.size()));
    for (size_t i = 0; i < all.size(); ++i) all[i] = static_cast<int>(i);
    expand(std::move(all));
    return std::move(best);
  }

 private:
  bool adjacent(int a, int b) const { return (adj[a][b >> 6] >> (b & 63)) & 1ull; }

  void build(const std::vector<std::string>& grid) {
    for (int r = 0; r < n; ++r)
      for (int c = 0; c < n; ++c)
        if (grid[r][c] != 'W') cellOf.emplace_back(r, c);

    const int cells = static_cast<int>(cellOf.size());
    const int words = (cells + 63) / 64;
    adj.assign(static_cast<size_t>(cells), std::vector<uint64_t>(static_cast<size_t>(words), 0));
    for (int a = 0; a < cells; ++a) {
      const auto [r1, c1] = cellOf[a];
      for (int b = a + 1; b < cells; ++b) {
        const auto [r2, c2] = cellOf[b];
        const bool sharesLine = r1 == r2 || c1 == c2 || std::abs(r1 - r2) == std::abs(c1 - c2);
        if (sharesLine && !wallBetween(grid, r1, c1, r2, c2)) continue;  // they attack: no edge
        adj[a][b >> 6] |= 1ull << (b & 63);
        adj[b][a >> 6] |= 1ull << (a & 63);
      }
    }
  }

  void record() {
    const int size = static_cast<int>(clique.size());
    if (size > bestSize) {
      bestSize = size;
      best.clear();
    }
    std::vector<std::pair<int, int>> board;
    board.reserve(clique.size());
    for (int v : clique) board.push_back(cellOf[v]);
    best.push_back(std::move(board));
    NQ_SNAPSHOT(best.back(), "board with " + std::to_string(size) + " queens");
  }

  // Greedy colouring of the candidates. `order` lists them class by class and `bound[i]` is the class of `order[i]`,
  // which is an upper bound on the size of a clique taken from `order[0..i]`.
  void colourSort(const std::vector<int>& candidates, std::vector<int>& order, std::vector<int>& bound) const {
    order.clear();
    bound.clear();
    std::vector<int> rest = candidates;
    int colour = 0;
    while (!rest.empty()) {
      ++colour;
      std::vector<int> next, cls;
      for (int v : rest) {
        bool fits = true;
        for (int u : cls) {
          if (adjacent(v, u)) {
            fits = false;
            break;
          }
        }
        if (fits) {
          cls.push_back(v);
          order.push_back(v);
          bound.push_back(colour);
        } else {
          next.push_back(v);
        }
      }
      rest.swap(next);
    }
  }

  void expand(std::vector<int> candidates) {
    if (static_cast<int>(clique.size()) >= bestSize) record();
    std::vector<int> order, bound;
    colourSort(candidates, order, bound);
    for (int i = static_cast<int>(order.size()) - 1; i >= 0; --i) {
      if (static_cast<int>(clique.size()) + bound[i] < bestSize) return;  // cannot catch up
      const int v = order[i];
      clique.push_back(v);
      std::vector<int> next;
      for (int u : candidates)
        if (adjacent(v, u)) next.push_back(u);
      expand(std::move(next));
      clique.pop_back();
      // The candidates left are exactly order[0..i-1], so a clique is built in one order only.
      candidates.erase(std::find(candidates.begin(), candidates.end(), v));
    }
  }
};

}  // namespace

std::vector<std::vector<std::pair<int, int>>> solveWalled(int n, const std::vector<std::string>& grid) {
  if (n <= 0 || static_cast<int>(grid.size()) != n) return {};
  for (const std::string& line : grid)
    if (static_cast<int>(line.size()) != n) return {};
  return WalledClique(n, grid).run();
}
