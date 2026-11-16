#!/usr/bin/env python3
"""Build holes-graph.json and HOLES.md for the Lyasoff 2016 proof-hole board.

Scans Lyasoff2016/**/*.lean for paper-facing theorems/lemmas, marks those whose
proof body contains a bare `sorry` tactic as open, and wires hard dependency
edges from the paper/plan order.
"""
from __future__ import annotations

import json
import re
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "Lyasoff2016"
OUT_JSON = ROOT / "holes-graph.json"
OUT_MD = ROOT / "HOLES.md"
OUT_EDGES = ROOT / "holes-edges.txt"

# Bare tactic `sorry`, not the substring of "sorry-free".
SORRY_RE = re.compile(r"(?<![\w-])sorry(?![\w-])")
DECL_RE = re.compile(r"^(theorem|lemma)\s+([A-Za-z0-9_']+)")

# Paper-facing nodes shown on the board (id → metadata).
# status is overwritten from the Lean scan when the declaration is found.
NODES: dict[str, dict] = {
    # §1
    "time_reversal": {
        "label": "§1 time rev",
        "section": 1,
        "file": "Lyasoff2016/Setting.lean",
        "detail": "Identity in law for integral functionals of BM (1.3).",
    },
    # §2
    "lemma_2_1": {
        "label": "Lem 2.1",
        "section": 2,
        "file": "Lyasoff2016/Auxiliary.lean",
        "detail": "Positive and negative integer moments of ∫ e^{σW} are finite.",
    },
    "prop_2_2": {
        "label": "Prop 2.2",
        "section": 2,
        "file": "Lyasoff2016/Auxiliary.lean",
        "detail": "Conditional density φ(x|y) exists, C^∞ on x>0, with decay/moment bounds.",
    },
    "scaling_relations": {
        "label": "Scaling",
        "section": 2,
        "file": "Lyasoff2016/Auxiliary.lean",
        "detail": "Brownian scaling of joint/cond/∞ densities (nonneg continuous versions).",
    },
    "girsanov_density": {
        "label": "Girsanov (2.2)",
        "section": 2,
        "file": "Lyasoff2016/Auxiliary.lean",
        "detail": "Cameron–Martin–Girsanov shift of the joint density.",
    },
    # §3
    "infinite_integral_finite": {
        "label": "∫₀^∞ finite",
        "section": 3,
        "file": "Lyasoff2016/FokkerPlanck.lean",
        "detail": "Footnote 2: a.s. finiteness of the perpetuity for ν<0.",
    },
    "Z_stationary": {
        "label": "Z stationary",
        "section": 3,
        "file": "Lyasoff2016/FokkerPlanck.lean",
        "detail": "Stationarity of Z_t vs the infinite-horizon integral.",
    },
    "dufresne_zero_flux": {
        "label": "Zero-flux ODE",
        "section": 3,
        "file": "Lyasoff2016/FokkerPlanck.lean",
        "detail": "Dufresne density satisfies the stationary zero-flux ODE.",
    },
    "perpetuity_inv_moment": {
        "label": "E[A⁻¹]=−ν",
        "section": 3,
        "file": "Lyasoff2016/FokkerPlanck.lean",
        "detail": "First reciprocal moment via Dynkin/stationarity of Z and L(log).",
    },
    "perpetuity_neg_moments": {
        "label": "E[A⁻ⁿ]",
        "section": 3,
        "file": "Lyasoff2016/FokkerPlanck.lean",
        "detail": "All reciprocal moments match the inverse-Gamma moments.",
    },
    "dufresne_theorem_sigma_one": {
        "label": "Dufresne σ=1",
        "section": 3,
        "file": "Lyasoff2016/FokkerPlanck.lean",
        "detail": "Unit-volatility law of A is igMeasure(−2ν, 2).",
    },
    "dufresne_theorem": {
        "label": "Dufresne thm",
        "section": 3,
        "file": "Lyasoff2016/FokkerPlanck.lean",
        "detail": "General σ via Brownian scaling from σ=1.",
    },
    "fokker_planck_joint": {
        "label": "FP (3.6b)",
        "section": 3,
        "file": "Lyasoff2016/FokkerPlanck.lean",
        "detail": "Joint density satisfies the divergence-form Fokker–Planck PDE.",
    },
    "remark_3_2": {
        "label": "Rem 3.2",
        "section": 3,
        "file": "Lyasoff2016/FokkerPlanck.lean",
        "detail": "Reflection / running-max identity in law.",
    },
    # §4
    "theorem_4_1_pde": {
        "label": "Thm 4.1 PDE",
        "section": 4,
        "file": "Lyasoff2016/Foliation.lean",
        "detail": "Foliation PDE for the conditional density.",
    },
    "theorem_4_1_striking": {
        "label": "Thm 4.1 (4.4)",
        "section": 4,
        "file": "Lyasoff2016/Foliation.lean",
        "detail": "Striking reciprocal-moment identity.",
    },
    "formula_4_6": {
        "label": "(4.6)",
        "section": 4,
        "file": "Lyasoff2016/Foliation.lean",
        "detail": "Conditional density via T_{t,y} from the y=0 slice.",
    },
    "prop_4_4": {
        "label": "Prop 4.4",
        "section": 4,
        "file": "Lyasoff2016/Foliation.lean",
        "detail": "Uniqueness of φ(·|0) from the Laplace normalisation.",
    },
    "theorem_4_5": {
        "label": "Thm 4.5",
        "section": 4,
        "file": "Lyasoff2016/Foliation.lean",
        "detail": "Closed form of the reciprocal Laplace transform L_{t,y}.",
    },
    # §5
    "g_solves_contour_equation": {
        "label": "g contour eq",
        "section": 5,
        "file": "Lyasoff2016/IntegralReps.lean",
        "detail": "g_{t,p} solves the contour equation for a ∈ [π/2, 3π/2].",
    },
    "yor_formula_classical": {
        "label": "Yor classical",
        "section": 5,
        "file": "Lyasoff2016/IntegralReps.lean",
        "detail": "Yor's joint density (1.1) as an independent classical input.",
    },
    "remark_5_1": {
        "label": "Rem 5.1",
        "section": 5,
        "file": "Lyasoff2016/IntegralReps.lean",
        "detail": "π-formula p=2, σ=2 recovers Yor.",
    },
    "pi_formula": {
        "label": "π / π/2",
        "section": 5,
        "file": "Lyasoff2016/IntegralReps.lean",
        "detail": "Joint density via π and π/2 formulae for p=2,3,4.",
    },
    "yor_formula": {
        "label": "Yor via Rem 5.1",
        "section": 5,
        "file": "Lyasoff2016/IntegralReps.lean",
        "detail": "yor_formula := yor_formula_classical (or Rem 5.1 route).",
    },
    # §6
    "S_zero": {
        "label": "S_{0,p}",
        "section": 6,
        "file": "Lyasoff2016/Asian.lean",
        "detail": "Closed form of S at k=0 via Gamma.",
    },
    "S_closed_form": {
        "label": "S_{k,p}",
        "section": 6,
        "file": "Lyasoff2016/Asian.lean",
        "detail": "Incomplete-Gamma closed form of S_{k,p}.",
    },
    "benchmark_k_zero": {
        "label": "k=0 benchmark",
        "section": 6,
        "file": "Lyasoff2016/Asian.lean",
        "detail": "E[∫ e^{σW+νs}] closed form.",
    },
    "asian_price_formula": {
        "label": "Asian price",
        "section": 6,
        "file": "Lyasoff2016/Asian.lean",
        "detail": "Call = ∬ Re F from π/2-formula p=4.",
    },
    "asian_delta": {
        "label": "Asian delta",
        "section": 6,
        "file": "Lyasoff2016/Asian.lean",
        "detail": "Strike derivative = ∬ Re F′.",
    },
    "table1_asian_enclosure": {
        "label": "Table 1",
        "section": 6,
        "file": "Lyasoff2016/Tables.lean",
        "detail": "Interval certificate for Table 1 (T=1/2, σ=0.22).",
    },
    "table2_asian_enclosure": {
        "label": "Table 2",
        "section": 6,
        "file": "Lyasoff2016/Tables.lean",
        "detail": "Interval certificate for Table 2 (T=1/2, σ=1/3).",
    },
    "table3_asian_enclosure": {
        "label": "Table 3",
        "section": 6,
        "file": "Lyasoff2016/Tables.lean",
        "detail": "Interval certificate for Table 3 (T=1, σ=0.22).",
    },
    "table4_asian_enclosure": {
        "label": "Table 4",
        "section": 6,
        "file": "Lyasoff2016/Tables.lean",
        "detail": "Interval certificate for Table 4 (T=1, σ=1/3).",
    },
}

# Hard edges: from → to means the current Lean proof of `to` still needs `from`
# (so `to` cannot be marked done while `from` is unfinished). Keep these honest:
# paper-order aspirations that the Lean proof already bypassed belong in SOFT_EDGES.
HARD_EDGES: list[tuple[str, str]] = [
    # §2
    ("lemma_2_1", "prop_2_2"),
    # §3 Dufresne moment chain (wrappers still call the σ=1 tip)
    ("infinite_integral_finite", "Z_stationary"),
    ("Z_stationary", "perpetuity_inv_moment"),
    ("dufresne_zero_flux", "perpetuity_inv_moment"),
    ("perpetuity_inv_moment", "perpetuity_neg_moments"),
    ("perpetuity_neg_moments", "dufresne_theorem_sigma_one"),
    ("dufresne_theorem_sigma_one", "dufresne_theorem"),
    ("time_reversal", "fokker_planck_joint"),
    ("time_reversal", "remark_3_2"),
    # §4 internal (already sorry-free; keep for structure)
    ("theorem_4_1_pde", "theorem_4_1_striking"),
    ("theorem_4_1_pde", "formula_4_6"),
    ("formula_4_6", "prop_4_4"),
    ("prop_4_4", "theorem_4_5"),
    ("theorem_4_5", "theorem_4_1_striking"),
    # §5
    ("g_solves_contour_equation", "pi_formula"),
    ("yor_formula_classical", "pi_formula"),
    ("yor_formula_classical", "yor_formula"),
    # §6
    ("S_zero", "S_closed_form"),
    ("pi_formula", "asian_price_formula"),
    ("girsanov_density", "asian_price_formula"),
    ("S_closed_form", "asian_price_formula"),
    ("asian_price_formula", "asian_delta"),
    ("asian_price_formula", "table1_asian_enclosure"),
    ("asian_price_formula", "table2_asian_enclosure"),
    ("asian_price_formula", "table3_asian_enclosure"),
    ("asian_price_formula", "table4_asian_enclosure"),
    ("benchmark_k_zero", "table1_asian_enclosure"),
]

# Soft edges: paper/logical order only. Drawn on the board but do NOT force
# status (Lean already discharged the target without that prerequisite).
SOFT_EDGES: list[tuple[str, str]] = [
    ("prop_2_2", "scaling_relations"),
    ("prop_2_2", "fokker_planck_joint"),
    ("fokker_planck_joint", "theorem_4_1_pde"),
    ("theorem_4_5", "g_solves_contour_equation"),
    ("pi_formula", "remark_5_1"),
    ("remark_5_1", "yor_formula"),
]

def scan_lean() -> dict[str, dict]:
    """Return map decl_name → {file, line, has_sorry}."""
    found: dict[str, dict] = {}
    for path in sorted(LEAN_ROOT.rglob("*.lean")):
        lines = path.read_text(encoding="utf-8").splitlines()
        decls: list[tuple[int, str]] = []
        for i, line in enumerate(lines):
            m = DECL_RE.match(line)
            if m:
                decls.append((i, m.group(2)))
        for idx, (lineno, name) in enumerate(decls):
            end = decls[idx + 1][0] if idx + 1 < len(decls) else len(lines)
            body = "\n".join(lines[lineno:end])
            # Ignore sorry mentions inside comments/docstrings of the form sorry-free
            # by stripping block/line comments first.
            stripped = re.sub(r"/-.*?-/", "", body, flags=re.S)
            stripped = re.sub(r"--.*?$", "", stripped, flags=re.M)
            has = bool(SORRY_RE.search(stripped))
            rel = str(path.relative_to(ROOT))
            # Prefer first occurrence (paper module over Lib duplicates).
            if name not in found:
                found[name] = {"file": rel, "line": lineno + 1, "has_sorry": has}
            elif has and not found[name]["has_sorry"]:
                found[name] = {"file": rel, "line": lineno + 1, "has_sorry": has}
    return found


def build() -> dict:
    scanned = scan_lean()
    # Local sorry (missing decl counts as a hole).
    raw_sorry = {
        nid: True if nid not in scanned else scanned[nid]["has_sorry"]
        for nid in NODES
    }
    hard_preds: dict[str, list[str]] = {nid: [] for nid in NODES}
    for frm, to in HARD_EDGES:
        if frm in NODES and to in NODES:
            hard_preds[to].append(frm)

    status: dict[str, str] = {}
    # Fixpoint: a node is done only if it has no local sorry AND every hard
    # predecessor is done. Otherwise open (all hard preds done) or blocked.
    for _ in range(len(NODES) + 2):
        changed = False
        for nid in NODES:
            preds_done = all(status.get(p) == "done" for p in hard_preds[nid])
            if not raw_sorry[nid] and preds_done:
                st = "done"
            elif preds_done:
                st = "open"
            else:
                st = "blocked"
            if status.get(nid) != st:
                status[nid] = st
                changed = True
        if not changed:
            break

    nodes = []
    for nid, meta in NODES.items():
        info = scanned.get(nid, {})
        file_ = info.get("file", meta["file"])
        nodes.append({
            "id": nid,
            "label": meta["label"],
            "section": meta["section"],
            "file": file_ + (f":{info['line']}" if "line" in info else ""),
            "status": status[nid],
            "blocker": None,
            "detail": meta.get("detail"),
        })

    # Annotate blockers for blocked nodes (hard preds only).
    by_id = {n["id"]: n for n in nodes}
    for n in nodes:
        if n["status"] != "blocked":
            continue
        unfinished = [
            p for p in hard_preds[n["id"]]
            if by_id.get(p, {}).get("status") != "done"
        ]
        if unfinished:
            n["blocker"] = "needs " + ", ".join(unfinished)

    edges = [
        {"from": frm, "to": to, "kind": "hard"}
        for frm, to in HARD_EDGES
        if frm in NODES and to in NODES
    ] + [
        {"from": frm, "to": to, "kind": "soft"}
        for frm, to in SOFT_EDGES
        if frm in NODES and to in NODES
    ]
    sorry_count = sum(1 for n in nodes if n["status"] in ("open", "blocked"))
    open_ids = [n["id"] for n in nodes if n["status"] == "open"]

    data = {
        "updated": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "sorryCount": sorry_count,
        "legend": {
            "open": "No unfinished required proof-deps — try next",
            "blocked": "Waiting on incomplete required proof-deps",
            "done": "Proved (no sorry)",
        },
        "notes": [
            "Hard edge B→A: Lean proof of A still needs B — A cannot be done while B is unfinished.",
            "Soft edge B→A: paper-order aspiration only (drawn dashed); does not affect status.",
            "Done = no local sorry and every hard predecessor is done (no unproven→proven).",
            "Blue = done. Green = open. Grey = blocked.",
            "Regenerate with: python3 scripts/build_holes.py",
            f"Open tips: {', '.join(open_ids) if open_ids else '(none)'}.",
        ],
        "nodes": nodes,
        "edges": edges,
    }
    return data


def write_md(data: dict) -> None:
    by_sec: dict[int, list] = {}
    for n in data["nodes"]:
        by_sec.setdefault(n["section"], []).append(n)
    open_n = [n for n in data["nodes"] if n["status"] == "open"]
    blocked_n = [n for n in data["nodes"] if n["status"] == "blocked"]
    done_n = [n for n in data["nodes"] if n["status"] == "done"]

    lines = [
        "# Proof holes (Lyasoff 2016)",
        "",
        "Inventory of paper-facing Lean holes, ordered **prove-first**.",
        "",
        f"**Updated:** {data['updated']}",
        f"**Holes:** {data['sorryCount']} open+blocked · "
        f"{len(open_n)} open · {len(blocked_n)} blocked · {len(done_n)} done.",
        "",
        "**Live board:** [`holes.html`](holes.html) + [`holes-graph.json`](holes-graph.json).",
        "",
        "```bash",
        "python3 scripts/build_holes.py",
        "python3 -m http.server 8765   # then open http://localhost:8765/holes.html",
        "```",
        "",
        "## Open now (Layer 0)",
        "",
    ]
    if not open_n:
        lines.append("_None — every remaining hole is blocked or done._")
    else:
        lines.append("| Id | Label | File |")
        lines.append("|---|---|---|")
        for n in open_n:
            lines.append(f"| `{n['id']}` | {n['label']} | `{n['file']}` |")
    lines += ["", "## By section", ""]
    for sec in sorted(by_sec):
        rows = by_sec[sec]
        holes = sum(1 for n in rows if n["status"] != "done")
        lines.append(f"### §{sec} — {holes} hole(s)")
        lines.append("")
        lines.append("| Status | Id | Label | File |")
        lines.append("|---|---|---|---|")
        for n in rows:
            lines.append(
                f"| {n['status']} | `{n['id']}` | {n['label']} | `{n['file']}` |"
            )
        lines.append("")
    lines += [
        "## Dependency sketch",
        "",
        "```mermaid",
        "flowchart TD",
        "  L2[lemma_2_1] --> P22[prop_2_2]",
        "  P22 --> Scale[scaling_relations]",
        "  Scale --> Gir[girsanov_density]",
        "  Inf[infinite_integral_finite] --> Z[Z_stationary]",
        "  Z --> Inv[perpetuity_inv_moment]",
        "  ZF[dufresne_zero_flux] --> Inv",
        "  Inv --> Neg[perpetuity_neg_moments]",
        "  Neg --> D1[dufresne_theorem_sigma_one]",
        "  D1 --> D[dufresne_theorem]",
        "  TR[time_reversal] --> FP[fokker_planck_joint]",
        "  P22 --> FP",
        "  FP --> T41[theorem_4_1_pde]",
        "  T41 --> F46[formula_4_6]",
        "  F46 --> P44[prop_4_4]",
        "  P44 --> T45[theorem_4_5]",
        "  T45 --> G[g_solves_contour_equation]",
        "  G --> Pi[pi_formula]",
        "  YorC[yor_formula_classical] --> Pi",
        "  Pi --> Asian[asian_price_formula]",
        "  Gir --> Asian",
        "  Asian --> Delta[asian_delta]",
        "  Asian --> T1[tables 1-4]",
        "```",
        "",
    ]
    OUT_MD.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    data = build()
    OUT_JSON.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    write_md(data)
    OUT_EDGES.write_text(
        "\n".join(f"{e['from']} -{e['kind']}-> {e['to']}" for e in data["edges"]) + "\n",
        encoding="utf-8",
    )
    open_n = sum(1 for n in data["nodes"] if n["status"] == "open")
    blocked_n = sum(1 for n in data["nodes"] if n["status"] == "blocked")
    done_n = sum(1 for n in data["nodes"] if n["status"] == "done")
    print(
        f"Wrote {OUT_JSON.name}, {OUT_MD.name}: "
        f"{open_n} open, {blocked_n} blocked, {done_n} done "
        f"(sorryCount={data['sorryCount']})"
    )


if __name__ == "__main__":
    main()
