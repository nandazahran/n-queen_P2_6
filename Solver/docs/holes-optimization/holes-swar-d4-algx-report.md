# Optimizing the Holes N-Queens Solver (`holes-swar-d4-algx.cpp`)

**Champion Solver:** [`Solver/holes/holes-swar-d4-algx.cpp`](../../holes/holes-swar-d4-algx.cpp) — **Unified 64-bit SWAR Bidirectional Bitmask Algorithm X + 8-Way $D_4$-Orbit Search** (superseding the original `holes-bitmask-algx.cpp`).

---

## Executive Summary

Across **5 iterative optimization rounds (16 benchmarked builds)** grounded in [`Solver/docs/literature_review.md`](../literature_review.md), we redesigned `solveHoles(int n, const std::vector<std::string>& grid)` ($N \le 12$) to optimize WebAssembly (`em++ -O2 -std=c++17`) execution speed, dynamic heap peak (`sbrk(0)` delta), static `.data`/`.bss` overhead, and Emscripten default **64 KB stack safety**, while strictly adhering to Competition Rules 1–5 and 100% solution parity.

| Metric | Baseline (`Bitmask AlgX`) | Champion (`SWAR D4-AlgX`) | Improvement |
|---|---:|---:|---:|
| **36-case total CPU (`total_min_ms`)** | `20.890 ms` | **`5.940 ms`** | **`3.52x` faster (`-71.6%`)** |
| **36-case median CPU (`total_median_ms`)** | `24.504 ms` | **`6.268 ms`** | **`3.91x` faster (`-74.4%`)** |
| **Official 27-case mirror (`official27_ms`)** | `2.630 ms` | **`1.245 ms`** | **`2.11x` faster (`-52.6%`)** |
| **$N=12$ sparse/empty sum (`n12_sparse_ms`)** | `19.094 ms` | **`4.926 ms`** | **`3.88x` faster (`-74.2%`)** |
| **$N=12$ transition/dense/UNSAT (`n12_search_ms`)** | `1.231 ms` | **`0.703 ms`** | **`1.75x` faster (`-42.9%`)** |
| **36-case dynamic heap (`total_heap_kb`)** | `3,580 KB` | **`3,100 KB`** | **`-480 KB` (`-13.4%`, `0 B` aux heap floor)** |
| **Max single-case heap (`max_heap_kb`)** | `1,088 KB` | **`940 KB`** | **`-148 KB` (`-13.6%`)** |
| **64 KB stack safety (`-sSTACK_SIZE=65536`)** | **FAIL (`42/42`)** | **PASS (`0/42`)** | **Fixed (`~35 KB` frame, `~29 KB` margin)** |
| **Static `.data`/`.bss` delta** | `272 B` (`.rodata`) | **`272 B` (`.rodata`)** | **`0 B` mutable static RAM** |
| **Rules 1–5 & Correctness** | `rules_ok=1, valid=1` | **`rules_ok=1, valid=1`** | **223+ stress boards (`124,978+` sols) verified** |

Interactive chart: [`optimization-progress.html`](optimization-progress.html) (offline self-contained HTML; open in any browser).
Raw measurements and reproducible plotting script: [`benchmark-results.json`](benchmark-results.json), [`render_charts.py`](render_charts.py).

---

## Root Causes Diagnosed in Baseline (`holes-bitmask-algx.cpp`)

1. **64 KB Stack Overflow (`42/42` fails):** `solveHoles()` declared both `HolesSearch` (`~33 KB`) and `NormalD4` (`~35 KB`) in disjoint `if/else` scopes, causing LLVM to reserve `~68 KB` in the function prologue and overflow Emscripten's default 64 KB stack on every single call.
2. **Sparse Heap Spill (`+480 KB` excess `sbrk` heap):** Whenever `H > 0` produced `> 2,048` solutions (`n12_h1_ultra`, `n12_h4_ultra`, `n12_h12_sparse`, `n12_sparse`), `HolesSearch` spilled from `stackSols[2048]` into a geometrically growing `std::vector<Board> heapSols`, raising `n12_h1_ultra` from the `832 KB` output floor to `1,088 KB` (`+256 KB`).
3. **Asymmetric Sparse Search Overhead:** Even a single hole (`H = 1`) disabled $D_4$ symmetry completely, forcing row-by-row backtracking over `~750k` nodes (`6.803 ms` on `n12_h1_ultra` vs `2.171 ms` on `n12_h0`).
4. **Slow General-Holes Inner Loop:** `HolesSearch::dfsAlgX()` scanned all $N$ rows and $N$ columns via loops and recomputed `rowAvail` arrays per node.

---

## Key Algorithmic & Systems Breakthroughs

### 1. 8-Way Simultaneous $D_4$-Orbit Holes Search (`8-Way D4-Holes`)
Every valid Holes solution is a valid Normal $N$-Queens solution avoiding holes. For sparse boards ($H \le N^2/8$ and $\text{minLineFree} \ge 3$), computing a 144-byte runtime `killMask[12][12]` (bit $k$ set iff $D_4$ transform $T_k(r, c)$ lands on a hole) allows running full 8-fold $D_4$ canonical search on arbitrary asymmetric boards and filtering `alive` masks at the `2,106` leaves. Because $N \le 12$ has at most `1,787` fundamental orbits (`14 KB` packed as `uint64_t`: 48-bit columns + 8-bit `emitMask`), sparse boards **never spill to heap** (`0 B` auxiliary heap). This cut `total_min_ms` from `20.890 ms` to `11.624 ms` and reached the exact `3,100 KB` heap floor.

### 2. Unified $D_4$ + Turbo Bidirectional Bitmask Algorithm X (`Unified D4 + Turbo AlgX`)
Because $D_4$ canonical border restrictions are simply initial per-row column bitmasks, running Bidirectional Bitmask Algorithm X (bit-parallel `(once, twice, thrice)` column cardinality counters, iterative unit-propagation fixpoint, Knuth Organ-Pipe central tie-breaking, and geometric `rem == 2` square pruning `r1 - r0 != c1 - c0`) inside $D_4$ cut $N=12$ $D_4$ search nodes **`3.5x`** (from `194,792` down to `55,928`), beating shift-bitmask $D_4$ even on `H = 0` (`1.389 ms` vs `1.590 ms`) and reaching `8.157 ms`.

### 3. Unified 64-Bit SWAR Bidirectional Algorithm X (`SWAR-AlgX`)
Packing all 12 row domains (12 bits/row, 4 rows/word, `0x7000` sentinel for placed/unused rows) into **three 64-bit registers `(d0, d1, d2)`** (`two` registers for $N \le 8$ via `template <bool TwoWords>`) with a runtime `3.45 KB` `CellAtk atk[12][12]` table performs:
- **Zero-loop dead-row check:** `~(d + 0x7FFF7FFF7FFF7FFFULL) & 0x8000800080008000ULL`
- **Zero-loop forced-row check:** `y = d & (d - kOnes)`, `~(y + k7FFF) & kHigh`
- **Zero-loop count-2 row check:** `z = y & (y - kOnes)`, `~(z + k7FFF) & kHigh`
- **Zero-loop `(once, twice, thrice)` column cardinality** via bitwise word folding across `(d0, d1, d2)`
- **Early `rem == 2` theorem:** Once dead-row and forced-row checks pass at `rem == 2`, both remaining rows must equal the exact 2 remaining columns `{c0, c1}`, so both placements are valid iff `r1 - r0 != c1 - c0`.
- **Single stack frame:** One `SwarD4AlgX` object (`~35 KB` total stack frame, `~29 KB` headroom below 64 KB).

This architecture cut total runtime from `8.157 ms` to `6.218 ms`.

### 4. Final Synthesis (`SWAR D4-AlgX` — `holes-swar-d4-algx.cpp`)
Isolated WASM ablations identified and stacked five clean gains on top of the 64-bit SWAR core:
1. **1-Multiply Branchless SWAR Column-Row Gather (`colRowsMask`):** Packs all 12 rows of column `c` into a 12-bit mask via `((v * 0x0001000200040008ULL) >> 48)` (exhaustively verified over all `49,152` column/mask pairs; replaces out-of-line 12-branch helper).
2. **True Hardware `i32.ctz` / `i64.ctz` in Pure ISO C++17:** `popcnt32((b & (~b + 1u)) - 1u)` lowers directly to a single `i32.ctz` (with `#if __cplusplus >= 202002L` `<bit>` path), while keeping `cb = x & (~x + 1u)` in parallel with `colMask |= cb`.
3. **Folded `rem == 1` Inside Forced-Row Loop:** Because `dfs` enters with `rem >= 2` and exits at `rem == 2` before branching, `rem == 1` can only arise after a forced-row decrement, removing `if (rem == 1)` from all `~58k` loop headers and eliminating dead `if (rem == 0)` checks.
4. **Zero-Switch Single-Loop `emitD4Orbit`:** Eliminates per-survivor `switch` loops on partial hole masks (`H = 1, 4, 12, 17`), cutting `n12_h1_ultra` to `1.037 ms` and `n12_h4_ultra` to `1.009 ms`.
5. **Pre-Table `rootUnitProp` + Reduced-Board Hall Check + Active-Cell `buildTables`:** Solves forced dense boards (`n9_dense = 0.001 ms`, `n12_dense = 0.004 ms`) before constructing `atk[r][c]`, and mathematically skips Hall's check on the `useD4` path (guaranteed whenever `minLineFree >= 3 && H <= N^2/8` for $N \le 12$). Dropping root SAC-1 eliminated its `2–5 µs` overhead on medium boards.

---

## Complete Evolution Across All 16 Benchmarked Designs

All builds were benchmarked sequentially with [`scripts/bench-holes.mjs`](../../../scripts/bench-holes.mjs) (1 warmup + 15 timed runs in fresh WASM instances per case across 36 boards spanning $N = 4 \dots 12$).

| Stage | Algorithm Variant | `total_min_ms` | `official27_ms` | `n12_sparse_ms` | `n12_search_ms` | `total_heap_kb` | `stack64k_ok` |
|---|---|---:|---:|---:|---:|---:|---:|
| Baseline | **Baseline (Bitmask AlgX)** | `20.890` | `2.630` | `19.094` | `1.231` | `3,580` | **0 (42 fails)** |
| R1-A | Two-Pass 4-Bit Shift | `27.839` | `3.491` | `26.221` | `1.160` | `3,100` | 1 |
| R1-B ★ | **8-Way D4-Holes** (`H <= N^2/8`) | `11.624` | `2.320` | `9.152` | `2.000` | `3,100` | 1 |
| R1-C | Wide D4-Holes (`H <= N^2/3`) | `14.157` | `2.544` | `9.918` | `3.725` | `3,100` | 1 |
| R2-A | D4 Leaf-Filter Zero-CTZ | `11.622` | `2.461` | `9.952` | `1.157` | `3,100` | 1 |
| R2-B | D4 3-Row Unroll | `10.110` | `2.066` | `8.435` | `1.218` | `3,100` | 1 |
| R2-C ★ | **D4 Yao-Li Iterative** | `9.706` | `1.988` | `8.113` | `1.165` | `3,100` | 1 |
| R3-A | D4 + Turbo AlgX (General Only) | `9.482` | `2.006` | `8.142` | `0.899` | `3,100` | 1 |
| R3-B ★ | **Unified D4 + Turbo AlgX** | `8.157` | `1.715` | `6.845` | `0.905` | `3,100` | 1 |
| R3-C | Turbo AlgX + Batch / 4-Bit | `9.178` | `1.901` | `7.676` | `1.051` | `3,100` | 1 |
| R4-A | SWAR-AlgX Core | `6.971` | `1.444` | `5.761` | `0.839` | `3,100` | 1 |
| R4-B | SWAR-AlgX + 2-Word / Early `rem==2` | `6.225` | `1.308` | `5.157` | `0.728` | `3,100` | 1 |
| R4-C ★ | **SWAR-AlgX + Root Prop / SAC-1** | `6.218` | `1.322` | `5.169` | `0.711` | `3,100` | 1 |
| **Champion** 🏆 | **SWAR D4-AlgX (`holes-swar-d4-algx.cpp`)** | **`5.940`** | **`1.245`** | **`4.926`** | **`0.703`** | **`3,100`** | **1** |
| R5-B | SWAR D4-AlgX (`H <= N^2/9`, 4096 buf) | `6.030` | `1.323` | `4.984` | `0.706` | `3,100` | 1 |
| R5-C | SWAR D4-AlgX + Split Emit / Dense SAC-1 | `6.083` | `1.288` | `5.048` | `0.705` | `3,100` | 1 |

---

## Per-Case $N = 12$ Comparison (Baseline vs `SWAR D4-AlgX`)

| Case | Category | $H$ | Solutions | Baseline CPU / Heap | `SWAR D4-AlgX` CPU / Heap | Speedup / Heap Saved |
|---|---|---:|---:|---:|---:|---:|
| `n12_h0` | empty | 0 | 14,200 | `2.171 ms` / `940 KB` | **`1.019 ms` / `940 KB`** | **`2.13x`** / `0 KB` |
| `n12_h1_ultra` | ultra_sparse | 1 | 12,561 | `6.803 ms` / `1,088 KB` | **`1.037 ms` / `832 KB`** | **`6.56x`** / **`-256 KB`** |
| `n12_h4_ultra` | ultra_sparse | 4 | 9,463 | `4.774 ms` / `752 KB` | **`1.009 ms` / `624 KB`** | **`4.73x`** / **`-128 KB`** |
| `n12_h12_sparse` | sparse | 12 | 4,970 | `3.313 ms` / `392 KB` | **`0.944 ms` / `328 KB`** | **`3.51x`** / **`-64 KB`** |
| `n12_sparse` | sparse | 17 | 3,154 | `2.033 ms` / `240 KB` | **`0.917 ms` / `208 KB`** | **`2.22x`** / **`-32 KB`** |
| `n12_h24_trans` | transition | 24 | 1,309 | `0.790 ms` / `84 KB` | **`0.463 ms` / `84 KB`** | **`1.71x`** / `0 KB` |
| `n12_h36_trans` | transition | 36 | 589 | `0.283 ms` / `36 KB` | **`0.159 ms` / `36 KB`** | **`1.78x`** / `0 KB` |
| `n12_asym_clust` | asymmetric | 36 | 108 | `0.112 ms` / `4 KB` | **`0.049 ms` / `4 KB`** | **`2.29x`** / `0 KB` |
| `n12_medium` | medium | 60 | 11 | `0.027 ms` / `0 KB` | **`0.013 ms` / `0 KB`** | **`2.08x`** / `0 KB` |
| `n12_h62_unsat` | unsat | 62 | 0 | `0.007 ms` / `0 KB` | **`0.007 ms` / `0 KB`** | `1.00x` / `0 KB` |
| `n12_h70_unsat` | unsat | 70 | 0 | `0.008 ms` / `0 KB` | **`0.006 ms` / `0 KB`** | **`1.33x`** / `0 KB` |
| `n12_dense` | dense | 95 | 1 | `0.005 ms` / `0 KB` | **`0.004 ms` / `0 KB`** | **`1.25x`** / `0 KB` |

---

## Falsified Hypotheses (Documented Dead Ends)

- **Two-pass shift-DFS on sparse spill:** Doubled sparse CPU (`27.839 ms`); superseded by single-pass $D_4$-orbit buffering.
- **Wide $D_4$ dispatch (`H <= N^2/3`) & tighter (`H <= N^2/9`):** Measured crossover is strictly `H <= N^2/8` (`H <= 18` at $N=12$); tightening to `H <= N^2/9` regressed `n10_sparse`, `n11_sparse`, and `n12_sparse`.
- **Linear-memory `colBits` in $D_4$, explicit linear-memory stack for 48-byte SWAR state, and bidirectional column scan at `min >= 3`:** Each increased WASM memory traffic or scan cost more than the nodes saved.
- **4-bit `four` counter + naive `rem == 3` and medium-board root SAC-1:** Added branch/scan overhead on fast paths (`n12_medium` already solves in `0.013 ms`).
- **Split `0x0F`/`0xF0` partial `emitD4Orbit`:** Ran two loops whenever an orbit retained both direct and transposed survivors (`>90%` of partial orbits).

---

## Final Verification

- **42-case verification & 36-case WASM benchmark (`node scripts/bench-holes.mjs`):** `valid=1`, `rules_ok=1`, `stack64k_ok=1 (0/42 fails)`, `static_delta_b=272 B`.
- **Extended 223-board stress suite:** `124,978` total solutions across $N = 1 \dots 12$ (empty, single-hole symmetries, Hall-fail, forced chains, adversarial clusters, and 200 seeded random boards) passed with 100% sorted solution-hash parity against `Solver/normal/backtracking-bitmask.cpp` under both `-std=c++17` and `-std=c++20` with `-sSTACK_SIZE=65536 -sSTACK_OVERFLOW_CHECK=2` and debug `NQ_SNAPSHOT` verification.
- **Official project build:** `npm run build:solvers -- --native` compiles `holes/holes-swar-d4-algx` cleanly (`17 ok, 0 failed`).
