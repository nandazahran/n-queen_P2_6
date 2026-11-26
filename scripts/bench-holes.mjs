#!/usr/bin/env node
// Fixed Holes solver benchmark & verification harness for OpenResearch experiments.
// Measures CPU (WASM -O2 min/median/MAD over fresh instances), dynamic heap (sbrk delta),
// static memory overhead (.data/.bss/.rodata delta vs stub), 64 KB stack safety,
// C++20 portability, Rules 1-5 compliance, and exact solution-set parity vs reference.
import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { performance } from "node:perf_hooks";
import { fileURLToPath, pathToFileURL } from "node:url";

const repo = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const CANDIDATE_SRC = path.join(repo, "Solver/holes/holes-bitmask-algx.cpp");
const REFERENCE_SRC = path.join(repo, "Solver/normal/backtracking-bitmask.cpp");
const RUNTIME_SRC = path.join(repo, "Tester/Harness/nqueen_runtime.cpp");
const TIMED_RUNS = 15;
const WARMUP_RUNS = 1;
const CASE_HOLES = 2;

function orxReport(obj) {
  process.stdout.write(`::orx:: ${JSON.stringify(obj)}\n`);
}

// ---- Exact PRNG and board generation from Tester/Board/{rng,preplaced,positions}.ts ----

function mulberry32(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

const randInt = (rng, n) => Math.floor(rng() * n);

function randomSolution(n, rng) {
  for (let attempt = 0; attempt < 1000; attempt++) {
    const q = Array.from({ length: n }, (_, r) => r);
    for (let i = n - 1; i > 0; i--) {
      const j = randInt(rng, i + 1);
      [q[i], q[j]] = [q[j], q[i]];
    }
    const colC = new Int32Array(n);
    const d1 = new Int32Array(2 * n - 1);
    const d2 = new Int32Array(2 * n - 1);
    const add = (r, c, s) => {
      colC[c] += s;
      d1[r - c + n - 1] += s;
      d2[r + c] += s;
    };
    q.forEach((c, r) => add(r, c, 1));
    const conflicts = (r, c) => colC[c] + d1[r - c + n - 1] + d2[r + c];
    for (let step = 0; step < 50 * n; step++) {
      const bad = [];
      for (let r = 0; r < n; r++) if (conflicts(r, q[r]) - 3 > 0) bad.push(r);
      if (bad.length === 0) return q;
      const r = bad[randInt(rng, bad.length)];
      add(r, q[r], -1);
      let best = Infinity;
      let cands = [];
      for (let c = 0; c < n; c++) {
        const k = conflicts(r, c);
        if (k < best) {
          best = k;
          cands = [c];
        } else if (k === best) {
          cands.push(c);
        }
      }
      q[r] = cands[randInt(rng, cands.length)];
      add(r, q[r], 1);
    }
  }
  throw new Error(`randomSolution failed for n=${n}`);
}

function generateHolesGrid(n, count, seed, solvable = true) {
  const rng = mulberry32(seed);
  const reserved = new Set();
  if (solvable) randomSolution(n, rng).forEach((c, r) => reserved.add(r * n + c));
  const cells = [];
  for (let i = 0; i < n * n; i++) if (!reserved.has(i)) cells.push(i);
  for (let i = cells.length - 1; i > 0; i--) {
    const j = randInt(rng, i + 1);
    [cells[i], cells[j]] = [cells[j], cells[i]];
  }
  const rows = Array.from({ length: n }, () => new Array(n).fill("."));
  for (const idx of cells.slice(0, count)) {
    rows[Math.floor(idx / n)][idx % n] = "H";
  }
  return rows.map((r) => r.join(""));
}

function passesHall(grid) {
  const n = grid.length;
  for (let r = 0; r < n; r++) if (!grid[r].includes(".")) return false;
  for (let c = 0; c < n; c++) {
    let ok = false;
    for (let r = 0; r < n; r++) if (grid[r][c] === ".") { ok = true; break; }
    if (!ok) return false;
  }
  const colOwner = new Int32Array(n).fill(-1);
  const assign = (r, visited) => {
    for (let c = 0; c < n; c++) {
      if (grid[r][c] === "H" || visited[c]) continue;
      visited[c] = 1;
      if (colOwner[c] === -1 || assign(colOwner[c], visited)) {
        colOwner[c] = r;
        return true;
      }
    }
    return false;
  };
  for (let r = 0; r < n; r++) {
    if (!assign(r, new Uint8Array(n))) return false;
  }
  return true;
}

// ---- Encoding & Exact Validation (matches Tester/Board/solution-check.ts) ----

function encodeHolesInput(n, grid) {
  const out = new Uint8Array(3 + n * n);
  out[0] = n;
  out[1] = 0;
  out[2] = 0;
  for (let r = 0; r < n; r++) {
    for (let c = 0; c < n; c++) {
      out[3 + r * n + c] = grid[r].charCodeAt(c);
    }
  }
  return out;
}

function hashSolution(data, start, n) {
  let h1 = 0x811c9dc5 | 0;
  let h2 = 0x9e3779b9 | 0;
  for (let i = 0; i < n; i++) {
    const b = data[start + i];
    h1 = Math.imul(h1 ^ b, 0x01000193);
    h2 = Math.imul(h2 + b + 1, 0x85ebca6b);
    h2 ^= h2 >>> 13;
  }
  return (h1 >>> 0) * 2097152 + ((h2 >>> 0) & 0x1fffff);
}

function validateHolesSolutions(n, grid, count, data) {
  if (data.length !== count * n) return `packed byte length mismatch (${data.length} vs ${count * n})`;
  const hole = new Uint8Array(n * n);
  for (let r = 0; r < n; r++) {
    for (let c = 0; c < n; c++) if (grid[r][c] === "H") hole[r * n + c] = 1;
  }
  const col = new Int32Array(n);
  const down = new Int32Array(2 * n);
  const up = new Int32Array(2 * n);
  const hashes = new Float64Array(count);

  for (let i = 0; i < count; i++) {
    const stamp = i + 1;
    const base = i * n;
    for (let r = 0; r < n; r++) {
      const c = data[base + r];
      if (c >= n) return `sol ${i} row ${r} col ${c} out of range`;
      const d = r - c + n - 1;
      const u = r + c;
      if (col[c] === stamp || down[d] === stamp || up[u] === stamp) {
        return `sol ${i} has attacking queens at (${r},${c})`;
      }
      col[c] = down[d] = up[u] = stamp;
      if (hole[r * n + c]) return `sol ${i} places queen on hole (${r},${c})`;
    }
    hashes[i] = hashSolution(data, base, n);
  }

  hashes.sort();
  for (let i = 1; i < count; i++) {
    if (hashes[i] === hashes[i - 1]) {
      // Exact byte check among colliding hashes
      const target = hashes[i];
      const matches = [];
      for (let j = 0; j < count; j++) {
        if (hashSolution(data, j * n, n) === target) matches.push(j);
      }
      for (let a = 0; a < matches.length; a++) {
        for (let b = a + 1; b < matches.length; b++) {
          let same = true;
          for (let r = 0; r < n; r++) {
            if (data[matches[a] * n + r] !== data[matches[b] * n + r]) {
              same = false;
              break;
            }
          }
          if (same) return `duplicate solution at indices ${matches[a]} and ${matches[b]}`;
        }
      }
    }
  }
  return { ok: true, sortedHashes: hashes };
}

// ---- Rules 1-5 Static Compliance Audit ----

const ALLOWED_STD_HEADERS = new Set([
  "algorithm", "array", "bit", "bitset", "cassert", "cmath", "cstddef", "cstdint",
  "cstdlib", "cstring", "functional", "limits", "numeric", "string", "tuple",
  "type_traits", "utility", "vector",
]);

function auditCompliance(sourcePath) {
  const raw = readFileSync(sourcePath, "utf8");
  const issues = [];

  // Rule 2: No #line directives
  if (/^\s*#\s*line\b/m.test(raw)) issues.push("Rule 2: #line directive found");

  // Rule 4: Standard C++ headers + "nqueens.h" only
  for (const m of raw.matchAll(/^\s*#\s*include\s*([<"])([^>"]+)[>"]/gm)) {
    const [, delim, hdr] = m;
    if (delim === '"') {
      if (hdr !== "nqueens.h") issues.push(`Rule 4: non-allowed local header "${hdr}"`);
    } else if (!ALLOWED_STD_HEADERS.has(hdr)) {
      issues.push(`Rule 4: non-allowed system header <${hdr}>`);
    }
  }

  // Strip comments and strings for code inspection
  const stripped = raw.replace(/\/\*[\s\S]*?\*\/|\/\/[^\n]*|"(?:\\.|[^"\\\n])*"|'(?:\\.|[^'\\\n])*'/g, " ");

  // Rule 1: No custom allocator overrides or raw malloc/free
  if (/\boperator\s+(?:new|delete)\b/.test(stripped)) issues.push("Rule 1: operator new/delete override");
  if (/\b(?:malloc|calloc|realloc|free)\s*\(/.test(stripped)) issues.push("Rule 1: raw C allocator call");

  // Rule 3: No mutable static variables
  for (const m of stripped.matchAll(/\bstatic\s+(?!constexpr\b|const\b|inline\b|assert\b)([A-Za-z_][\w:<>]*)\s+([A-Za-z_]\w*)/g)) {
    issues.push(`Rule 3: mutable static variable '${m[1]} ${m[2]}'`);
  }

  // Rule 5: Flag suspiciously large const/constexpr arrays (> 64 entries)
  for (const m of stripped.matchAll(/\b(?:constexpr|const)\b[^;{}]*\[(\d+)\]\s*=\s*\{/g)) {
    if (Number(m[1]) > 64) issues.push(`Rule 5: large constant lookup array [${m[1]}]`);
  }

  return issues;
}

// ---- Emscripten Compiler & Fresh-Instance WASM Runner ----

function compileWasm(srcPath, outJs, extraFlags = []) {
  const args = [
    srcPath,
    RUNTIME_SRC,
    `-I${path.join(repo, "Tester/Harness")}`,
    "-O2",
    "-std=c++17",
    "-sMODULARIZE=1",
    "-sEXPORT_ES6=1",
    "-sEXPORT_NAME=createSolver",
    "-sENVIRONMENT=worker,node",
    "-sALLOW_MEMORY_GROWTH=1",
    "-sMAXIMUM_MEMORY=536870912",
    "-sSTACK_SIZE=1048576",
    "-sFILESYSTEM=0",
    "-sEXPORTED_FUNCTIONS=_nq_alloc_input,_nq_prepare,_nq_solve,_nq_pack,_nq_result,_nq_count,_nq_bad,_nq_heap_top",
    "-sEXPORTED_RUNTIME_METHODS=HEAPU8",
    "--profiling-funcs",
    ...extraFlags,
    "-o",
    outJs,
  ];
  const r = spawnSync("em++", args, { cwd: repo, encoding: "utf8" });
  if (r.error || r.status !== 0) {
    throw new Error(`em++ failed for ${path.basename(srcPath)}:\n${r.error?.message ?? ""}${r.stdout ?? ""}${r.stderr ?? ""}`);
  }
}

async function loadCompiledModule(mjsPath) {
  const factory = (await import(pathToFileURL(mjsPath).href)).default;
  const wasmBytes = readFileSync(mjsPath.replace(/\.mjs$/, ".wasm"));
  const compiled = await WebAssembly.compile(wasmBytes);
  return {
    wasmSizeBytes: wasmBytes.length,
    async instantiate() {
      return factory({
        instantiateWasm(imports, receiveInstance) {
          WebAssembly.instantiate(compiled, imports).then((inst) => receiveInstance(inst, compiled));
          return {};
        },
      });
    },
  };
}

async function runOnce(bundle, n, grid, packResult) {
  const mod = await bundle.instantiate();
  const initHeapTop = mod._nq_heap_top();
  const bytes = encodeHolesInput(n, grid);
  const at = mod._nq_alloc_input(bytes.length);
  mod.HEAPU8.set(bytes, at);
  if (mod._nq_prepare(CASE_HOLES, 0) !== 0) throw new Error("nq_prepare failed");
  const heapBefore = mod._nq_heap_top();
  const t0 = performance.now();
  const code = mod._nq_solve();
  const computeMs = performance.now() - t0;
  if (code !== 0) throw new Error(`nq_solve returned code ${code}`);
  const heapAfter = mod._nq_heap_top();
  const heapPeakBytes = Math.max(0, heapAfter - heapBefore);

  if (!packResult) return { computeMs, heapPeakBytes, initHeapTop };

  const packed = mod._nq_pack();
  if (packed < 0) {
    throw new Error(`nq_pack failed (${packed}): bad=[${mod._nq_bad(0)},${mod._nq_bad(1)},${mod._nq_bad(2)}]`);
  }
  const ptr = mod._nq_result();
  const count = mod._nq_count();
  const data = mod.HEAPU8.slice(ptr, ptr + packed);
  return { computeMs, heapPeakBytes, initHeapTop, count, data };
}

function median(arr) {
  const s = [...arr].sort((a, b) => a - b);
  const m = s.length >> 1;
  return s.length % 2 ? s[m] : (s[m - 1] + s[m]) / 2;
}

function mad(arr) {
  const m = median(arr);
  return median(arr.map((v) => Math.abs(v - m)));
}

// ---- Build Deterministic 36-Case Suite + 6 Edge Cases ----

async function buildSuite(refBundle) {
  const cases = [];

  // Group A: 27 official-mirror solvable cases (N = 4..12, sparse / medium / dense)
  for (let n = 4; n <= 12; n++) {
    const hSparse = Math.max(1, Math.floor(0.12 * n * n));
    const hMedium = Math.floor(0.42 * n * n);
    const hDense = Math.min(n * n - n, Math.floor(0.72 * (n * n - n)));
    cases.push({
      id: `n${n}_sparse`,
      regime: "sparse",
      official: true,
      n,
      h: hSparse,
      grid: generateHolesGrid(n, hSparse, 100 + n * 10 + 1, true),
    });
    cases.push({
      id: `n${n}_medium`,
      regime: "medium",
      official: true,
      n,
      h: hMedium,
      grid: generateHolesGrid(n, hMedium, 100 + n * 10 + 2, true),
    });
    cases.push({
      id: `n${n}_dense`,
      regime: "dense",
      official: true,
      n,
      h: hDense,
      grid: generateHolesGrid(n, hDense, 100 + n * 10 + 3, true),
    });
  }

  // Group B: 9 N=12 critical stress, boundary, spill, asymmetric, and Hall-passing UNSAT cases
  const empty12 = Array.from({ length: 12 }, () => ".".repeat(12));
  cases.push({ id: "n12_h0", regime: "empty", official: false, n: 12, h: 0, grid: empty12 });
  cases.push({ id: "n12_h1_ultra", regime: "ultra_sparse", official: false, n: 12, h: 1, grid: generateHolesGrid(12, 1, 701, true) });
  cases.push({ id: "n12_h4_ultra", regime: "ultra_sparse", official: false, n: 12, h: 4, grid: generateHolesGrid(12, 4, 704, true) });
  cases.push({ id: "n12_h12_sparse", regime: "sparse", official: false, n: 12, h: 12, grid: generateHolesGrid(12, 12, 712, true) });
  cases.push({ id: "n12_h24_trans", regime: "transition", official: false, n: 12, h: 24, grid: generateHolesGrid(12, 24, 724, true) });
  cases.push({ id: "n12_h36_trans", regime: "transition", official: false, n: 12, h: 36, grid: generateHolesGrid(12, 36, 736, true) });

  // Deterministic Hall-passing diagonal-UNSAT boards at N=12 (verified via independent reference)
  async function findHardUnsat(hTarget, startSeed) {
    for (let s = startSeed; s < startSeed + 500; s++) {
      const g = generateHolesGrid(12, hTarget, s, false);
      if (!passesHall(g)) continue;
      const res = await runOnce(refBundle, 12, g, true);
      if (res.count === 0) return { grid: g, seed: s };
    }
    throw new Error(`Could not find Hall-passing UNSAT board at H=${hTarget}`);
  }
  const unsat1 = await findHardUnsat(62, 2000);
  const unsat2 = await findHardUnsat(70, 3000);
  cases.push({ id: "n12_h62_unsat", regime: "unsat", official: false, n: 12, h: 62, seed: unsat1.seed, grid: unsat1.grid });
  cases.push({ id: "n12_h70_unsat", regime: "unsat", official: false, n: 12, h: 70, seed: unsat2.seed, grid: unsat2.grid });

  // Asymmetric clustered holes (N=12, solvable): holes concentrated in bottom 4 rows & right 3 cols
  {
    const rng = mulberry32(9001);
    const planted = randomSolution(12, rng);
    const keep = new Set(planted.map((c, r) => r * 12 + c));
    const rows = Array.from({ length: 12 }, () => new Array(12).fill("."));
    let placed = 0;
    for (let r = 8; r < 12; r++) {
      for (let c = 0; c < 12; c++) {
        if (!keep.has(r * 12 + c) && (r + c) % 2 === 0) {
          rows[r][c] = "H";
          placed++;
        }
      }
    }
    for (let r = 0; r < 8; r++) {
      for (let c = 9; c < 12; c++) {
        if (!keep.has(r * 12 + c) && (r + c) % 3 !== 0) {
          rows[r][c] = "H";
          placed++;
        }
      }
    }
    cases.push({
      id: "n12_asym_clust",
      regime: "asymmetric",
      official: false,
      n: 12,
      h: placed,
      grid: rows.map((r) => r.join("")),
    });
  }

  // Edge cases (verified for correctness & 64 KB stack safety, not included in timed score)
  // Hall-failing N=12 board: rows 0,1,2 only allow cols 0,1 (every row/col has >=2 free cells, yet no matching!)
  const hallFail = Array.from({ length: 12 }, () => new Array(12).fill("."));
  for (let r = 0; r < 3; r++) for (let c = 2; c < 12; c++) hallFail[r][c] = "H";
  const edgeCases = [
    { id: "edge_n1_free", n: 1, grid: ["."] },
    { id: "edge_n1_hole", n: 1, grid: ["H"] },
    { id: "edge_n2_empty", n: 2, grid: ["..", ".."] },
    { id: "edge_n3_empty", n: 3, grid: ["...", "...", "..."] },
    { id: "edge_n4_empty", n: 4, grid: ["....", "....", "....", "...."] },
    { id: "edge_n12_hall_fail", n: 12, grid: hallFail.map((r) => r.join("")) },
  ];

  return { cases, edgeCases };
}

async function main() {
  const tmpDir = mkdtempSync(path.join(os.tmpdir(), "nq-holes-bench-"));
  try {
    orxReport({
      plan: [
        { phase: "build", of: 4, unit: "targets" },
        { phase: "verify", of: 42, unit: "cases" },
        { phase: "bench", of: 36, unit: "cases" },
      ],
    });

    // ---- Phase 1: Build ----
    orxReport({ phase: "build", step: 0, of: 4, unit: "targets" });

    const prodJs = path.join(tmpDir, "cand_prod.mjs");
    compileWasm(CANDIDATE_SRC, prodJs);
    const prodBundle = await loadCompiledModule(prodJs);
    orxReport({ step: 1 });

    const stack64Js = path.join(tmpDir, "cand_64k.mjs");
    compileWasm(CANDIDATE_SRC, stack64Js, ["-sSTACK_SIZE=65536", "-sSTACK_OVERFLOW_CHECK=2"]);
    const stack64Bundle = await loadCompiledModule(stack64Js);
    orxReport({ step: 2 });

    // C++20 portability compile check + empty stub for .data/.bss baseline
    let cpp20Ok = true;
    try {
      const cpp20Js = path.join(tmpDir, "cand_cpp20.mjs");
      compileWasm(CANDIDATE_SRC, cpp20Js, ["-std=c++20"]);
    } catch (e) {
      cpp20Ok = false;
      console.error("C++20 compile failed:", e.message);
    }
    const stubSrc = path.join(tmpDir, "stub.cpp");
    writeFileSync(
      stubSrc,
      `#include "nqueens.h"\nstd::vector<std::vector<int>> solveHoles(int, const std::vector<std::string>&) { return {}; }\n`,
    );
    const stubJs = path.join(tmpDir, "stub.mjs");
    compileWasm(stubSrc, stubJs);
    const stubBundle = await loadCompiledModule(stubJs);
    orxReport({ step: 3 });

    const refJs = path.join(tmpDir, "ref.mjs");
    compileWasm(REFERENCE_SRC, refJs);
    const refBundle = await loadCompiledModule(refJs);
    orxReport({ step: 4 });

    // Static compliance + .data/.bss/.rodata overhead vs empty stub
    const complianceIssues = auditCompliance(CANDIDATE_SRC);
    const candInit = (await prodBundle.instantiate())._nq_heap_top();
    const stubInit = (await stubBundle.instantiate())._nq_heap_top();
    const staticDeltaBytes = Math.max(0, candInit - stubInit);

    console.log(`=== Holes Benchmark ===`);
    console.log(`Candidate: ${path.relative(repo, CANDIDATE_SRC)} (${prodBundle.wasmSizeBytes} B wasm)`);
    console.log(`Static memory delta vs stub (.data/.bss/.rodata): ${staticDeltaBytes} B (cand=${candInit}, stub=${stubInit})`);
    console.log(`C++20 compile: ${cpp20Ok ? "PASS" : "FAIL"}`);
    console.log(`Rules 1-5 static audit: ${complianceIssues.length === 0 ? "PASS" : "FAIL (" + complianceIssues.join("; ") + ")"}`);

    // ---- Phase 2: Verify (correctness + 64 KB stack safety across 6 edge + 36 bench cases) ----
    const { cases, edgeCases } = await buildSuite(refBundle);
    const allVerify = [...edgeCases, ...cases];
    orxReport({ phase: "verify", step: 0, of: allVerify.length, unit: "cases" });

    let validOk = 1;
    let stack64Ok = 1;
    let stack64Fails = 0;
    const expectedCounts = new Map();

    for (let i = 0; i < allVerify.length; i++) {
      const tc = allVerify[i];
      const refRes = await runOnce(refBundle, tc.n, tc.grid, true);
      const refVal = validateHolesSolutions(tc.n, tc.grid, refRes.count, refRes.data);
      if (typeof refVal === "string") throw new Error(`Reference failed on ${tc.id}: ${refVal}`);
      expectedCounts.set(tc.id, refRes.count);

      // Production correctness & exact solution-set parity
      const candRes = await runOnce(prodBundle, tc.n, tc.grid, true);
      const candVal = validateHolesSolutions(tc.n, tc.grid, candRes.count, candRes.data);
      if (typeof candVal === "string") {
        validOk = 0;
        console.error(`INVALID [${tc.id}]: ${candVal}`);
      } else if (candRes.count !== refRes.count) {
        validOk = 0;
        console.error(`COUNT MISMATCH [${tc.id}]: got ${candRes.count}, expected ${refRes.count}`);
      } else {
        for (let k = 0; k < refRes.count; k++) {
          if (candVal.sortedHashes[k] !== refVal.sortedHashes[k]) {
            validOk = 0;
            console.error(`SOLUTION SET MISMATCH [${tc.id}] at sorted hash ${k}`);
            break;
          }
        }
      }

      // 64 KB stack overflow safety check
      try {
        const s64 = await runOnce(stack64Bundle, tc.n, tc.grid, true);
        if (s64.count !== refRes.count) {
          stack64Ok = 0;
          stack64Fails++;
          console.error(`64KB STACK COUNT MISMATCH [${tc.id}]: got ${s64.count}, expected ${refRes.count}`);
        }
      } catch (e) {
        stack64Ok = 0;
        stack64Fails++;
        console.error(`64KB STACK FAIL [${tc.id}]: ${e.message.split("\n")[0]}`);
      }
      orxReport({ step: i + 1 });
    }

    const rulesOk = complianceIssues.length === 0 && cpp20Ok ? 1 : 0;
    console.log(`Verification: valid=${validOk} stack64k_ok=${stack64Ok} (fails=${stack64Fails}) rules_ok=${rulesOk}`);
    if (!validOk) {
      orxReport({
        m: {
          valid: 0,
          stack64k_ok: stack64Ok,
          rules_ok: rulesOk,
          static_delta_b: staticDeltaBytes,
        },
      });
      process.exit(1);
    }

    // ---- Phase 3: Benchmark (1 warmup + TIMED_RUNS fresh WASM runs per case) ----
    orxReport({ phase: "bench", step: 0, of: cases.length, unit: "cases" });

    let totalMinMs = 0;
    let totalMedianMs = 0;
    let official27Ms = 0;
    let n12TotalMs = 0;
    let n12SearchMs = 0;
    let n12SparseMs = 0;
    let totalHeapBytes = 0;
    let maxHeapBytes = 0;
    let n12SpillHeapBytes = 0;

    const searchHeavyIds = new Set([
      "n12_medium", "n12_dense", "n12_h24_trans", "n12_h36_trans",
      "n12_h62_unsat", "n12_h70_unsat", "n12_asym_clust",
    ]);
    const sparse12Ids = new Set(["n12_h0", "n12_h1_ultra", "n12_h4_ultra", "n12_h12_sparse", "n12_sparse"]);
    const spill12Ids = new Set(["n12_h1_ultra", "n12_h4_ultra", "n12_h12_sparse", "n12_sparse"]);

    console.log(
      `\n${"CASE".padEnd(16)} ${"REGIME".padEnd(12)} ${"N".padStart(2)} ${"H".padStart(3)} ${"SOLS".padStart(6)} ${"MIN_MS".padStart(8)} ${"MED_MS".padStart(8)} ${"MAD_MS".padStart(8)} ${"HEAP_KB".padStart(9)}`,
    );

    for (let i = 0; i < cases.length; i++) {
      const tc = cases[i];
      const sols = expectedCounts.get(tc.id);
      const times = [];
      let peakHeap = 0;

      for (let w = 0; w < WARMUP_RUNS; w++) {
        const r = await runOnce(prodBundle, tc.n, tc.grid, false);
        if (r.heapPeakBytes > peakHeap) peakHeap = r.heapPeakBytes;
      }
      for (let t = 0; t < TIMED_RUNS; t++) {
        const r = await runOnce(prodBundle, tc.n, tc.grid, false);
        times.push(r.computeMs);
        if (r.heapPeakBytes > peakHeap) peakHeap = r.heapPeakBytes;
      }

      const minMs = Math.min(...times);
      const medMs = median(times);
      const madMs = mad(times);
      const heapKb = peakHeap / 1024;

      totalMinMs += minMs;
      totalMedianMs += medMs;
      if (tc.official) official27Ms += minMs;
      if (tc.n === 12) n12TotalMs += minMs;
      if (searchHeavyIds.has(tc.id)) n12SearchMs += minMs;
      if (sparse12Ids.has(tc.id)) n12SparseMs += minMs;
      totalHeapBytes += peakHeap;
      if (peakHeap > maxHeapBytes) maxHeapBytes = peakHeap;
      if (spill12Ids.has(tc.id)) n12SpillHeapBytes += peakHeap;

      console.log(
        `${tc.id.padEnd(16)} ${tc.regime.padEnd(12)} ${String(tc.n).padStart(2)} ${String(tc.h).padStart(3)} ${String(sols).padStart(6)} ${minMs.toFixed(3).padStart(8)} ${medMs.toFixed(3).padStart(8)} ${madMs.toFixed(3).padStart(8)} ${heapKb.toFixed(1).padStart(9)}`,
      );

      orxReport({
        row: "cases",
        m: {
          case_id: tc.id,
          regime: tc.regime,
          n: tc.n,
          h: tc.h,
          sols,
          min_ms: Number(minMs.toFixed(4)),
          median_ms: Number(medMs.toFixed(4)),
          heap_kb: Number(heapKb.toFixed(2)),
        },
      });
      orxReport({ step: i + 1 });
    }

    const totalHeapKb = totalHeapBytes / 1024;
    const maxHeapKb = maxHeapBytes / 1024;
    const n12SpillHeapKb = n12SpillHeapBytes / 1024;

    console.log(`\n=== SUMMARY ===`);
    console.log(`total_min_ms      = ${totalMinMs.toFixed(4)} ms`);
    console.log(`total_median_ms   = ${totalMedianMs.toFixed(4)} ms`);
    console.log(`official27_ms     = ${official27Ms.toFixed(4)} ms`);
    console.log(`n12_total_ms      = ${n12TotalMs.toFixed(4)} ms`);
    console.log(`n12_search_ms     = ${n12SearchMs.toFixed(4)} ms`);
    console.log(`n12_sparse_ms     = ${n12SparseMs.toFixed(4)} ms`);
    console.log(`total_heap_kb     = ${totalHeapKb.toFixed(2)} KB`);
    console.log(`n12_spill_heap_kb = ${n12SpillHeapKb.toFixed(2)} KB`);
    console.log(`max_heap_kb       = ${maxHeapKb.toFixed(2)} KB`);
    console.log(`static_delta_b    = ${staticDeltaBytes} B`);
    console.log(`stack64k_ok       = ${stack64Ok} (fails=${stack64Fails})`);
    console.log(`rules_ok          = ${rulesOk}`);
    console.log(`valid             = ${validOk}`);

    orxReport({
      m: {
        total_min_ms: Number(totalMinMs.toFixed(4)),
        total_median_ms: Number(totalMedianMs.toFixed(4)),
        official27_ms: Number(official27Ms.toFixed(4)),
        n12_total_ms: Number(n12TotalMs.toFixed(4)),
        n12_search_ms: Number(n12SearchMs.toFixed(4)),
        n12_sparse_ms: Number(n12SparseMs.toFixed(4)),
        total_heap_kb: Number(totalHeapKb.toFixed(2)),
        n12_spill_heap_kb: Number(n12SpillHeapKb.toFixed(2)),
        max_heap_kb: Number(maxHeapKb.toFixed(2)),
        static_delta_b: staticDeltaBytes,
        stack64k_ok: stack64Ok,
        rules_ok: rulesOk,
        valid: validOk,
      },
    });
  } finally {
    rmSync(tmpDir, { recursive: true, force: true });
  }
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
