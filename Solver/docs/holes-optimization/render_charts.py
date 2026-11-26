"""Generate offline interactive HTML charts for the Holes N-Queens optimization study."""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from chart_renderer import render_chart

data = json.loads((HERE / "benchmark-results.json").read_text(encoding="utf-8"))
summary = data["summary"]
per_case = data["perCase"]

exp_points = []
for idx, r in enumerate(summary):
    exp_points.append({
        "step": idx,
        "label": r["shortName"],
        "total_min_ms": r["total_min_ms"],
        "official27_ms": r["official27_ms"],
        "n12_sparse_ms": r["n12_sparse_ms"],
        "n12_search_ms": r["n12_search_ms"],
        "total_heap_kb": r["total_heap_kb"],
    })

n12_order = [
    ("n12_h0", "H=0"),
    ("n12_h1_ultra", "H=1"),
    ("n12_h4_ultra", "H=4"),
    ("n12_h12_sparse", "H=12"),
    ("n12_sparse", "H=17"),
    ("n12_h24_trans", "H=24"),
    ("n12_h36_trans", "H=36"),
    ("n12_asym_clust", "Asym36"),
    ("n12_medium", "H=60"),
    ("n12_h62_unsat", "U62"),
    ("n12_h70_unsat", "U70"),
    ("n12_dense", "H=95"),
]

milestone_names = [
    "Baseline (Bitmask AlgX)",
    "8-Way D4-Holes",
    "Unified D4 + Turbo AlgX",
    "SWAR D4-AlgX",
]

round_series_cpu = []
round_series_heap = []
for name in milestone_names:
    pts_cpu = []
    pts_heap = []
    for idx, (cid, short) in enumerate(n12_order):
        c = per_case[name][cid]
        pts_cpu.append({"step": idx, "label": short, "case_min_ms": c["min"]})
        pts_heap.append({"step": idx, "label": short, "case_heap_kb": c["heap"]})
    round_series_cpu.append({"name": name, "points": pts_cpu})
    round_series_heap.append({"name": name, "points": pts_heap})

pareto_pass = []
pareto_fail = []
for r in summary:
    pt = {"step": r["total_heap_kb"], "pareto_ms": r["total_min_ms"], "label": r["algorithm"]}
    if r["stack64k_ok"]:
        pareto_pass.append(pt)
    else:
        pareto_fail.append(pt)

render_chart(
    HERE / "optimization-progress.html",
    title="Holes N-Queens WASM Optimization (Baseline to SWAR D4-AlgX)",
    subtitle="36 benchmark cases (N=4..12) · Emscripten -O2 -std=c++17 · min of 15 fresh WASM instances per case",
    x_label="Algorithm Variant",
    metrics=[
        {
            "key": "total_min_ms",
            "label": "Total 36-case CPU (ms)",
            "type": "bar",
            "unit": "ms",
            "xLabel": "Algorithm Variant",
            "yLabel": "Total min time (ms)",
            "series": [{"name": "36-case total_min_ms", "points": exp_points}],
        },
        {
            "key": "official27_ms",
            "label": "Official 27-case CPU (ms)",
            "type": "bar",
            "unit": "ms",
            "xLabel": "Algorithm Variant",
            "yLabel": "Official 27-case min time (ms)",
            "series": [{"name": "official27_ms", "points": exp_points}],
        },
        {
            "key": "case_min_ms",
            "label": "N=12 per-case CPU (Key Milestones)",
            "type": "bar",
            "unit": "ms",
            "xLabel": "N=12 Board",
            "yLabel": "Case min time (ms)",
            "series": round_series_cpu,
        },
        {
            "key": "case_heap_kb",
            "label": "N=12 per-case Heap Peak (Baseline vs SWAR D4-AlgX)",
            "type": "bar",
            "unit": "KB",
            "xLabel": "N=12 Board",
            "yLabel": "Dynamic sbrk heap delta (KB)",
            "series": [round_series_heap[0], round_series_heap[3]],
        },
        {
            "key": "pareto_ms",
            "label": "CPU vs Heap Pareto (minimize both; guide frontier)",
            "type": "pareto",
            "unit": "ms",
            "xLabel": "Total 36-case sbrk heap delta (KB)",
            "yLabel": "Total 36-case min time (ms)",
            "minimizeX": True,
            "maximizeY": False,
            "series": [
                {"name": "64 KB stack safe", "points": pareto_pass},
                {"name": "64 KB stack overflow (Baseline)", "points": pareto_fail},
            ],
        },
    ],
)
print("Rendered Solver/docs/holes-optimization/optimization-progress.html cleanly.")
