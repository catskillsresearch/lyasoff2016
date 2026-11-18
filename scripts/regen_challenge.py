#!/usr/bin/env python3
"""Regenerate Mathlib-only Challenge.lean from holes-graph.json + library defs."""
from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

# No chart theorem is excluded for extra axioms. Numerical tables are data only.
CLASSICAL_AXIOM_THMS = set()

# Formulae whose Challenge bodies would pull non-Mathlib helpers; Comparator supplies values.
DEF_NAMES = [
    "Lyasoff2016.yorDensity",
    "Lyasoff2016.piFormula",
    "Lyasoff2016.piHalfFormula",
    "Lyasoff2016.contourIntegrand",
    "Lyasoff2016.Ffun",
    "Lyasoff2016.FfunDeriv",
    "Lyasoff2016.dufresne",
    # Single-file Challenge shares `OfNat` `_proof_N` auxes across decls; Solution
    # (multi-file) does not. Treat these as type-only holes so Comparator matches.
    "Lyasoff2016.jointFokkerPlanckAdjoint",
    "Lyasoff2016.SatisfiesTheorem41PDE",
    "Lyasoff2016.SatisfiesFoliationODE",
    "Lyasoff2016.TransformedMassIdentity",
    "Lyasoff2016.HasLaplaceReduction",
    "Lyasoff2016.contourEq",
]


def extract_header(path: Path, line: int) -> str:
    lines = path.read_text().splitlines()
    start = None
    for i in range(max(0, line - 4), min(len(lines), line + 6)):
        if re.match(r"^(?:noncomputable\s+)?(?:theorem|lemma)\s+", lines[i]):
            start = i
            break
    if start is None:
        raise SystemExit(f"no theorem at {path}:{line}")
    hdr: list[str] = []
    for k in range(start, len(lines)):
        L = lines[k]
        # Bindings inside the statement use `let x := …`; ignore those.
        if re.search(r"\blet\b.+:=", L):
            hdr.append(L)
            continue
        if re.search(r":=\s*by\b", L):
            hdr.append(re.split(r":=\s*by\b", L, maxsplit=1)[0].rstrip())
            break
        if ":=" in L:
            # Proof-term style: `theorem … : Type := proof`
            hdr.append(L.split(":=", 1)[0].rstrip())
            break
        if L.rstrip().endswith(" where"):
            hdr.append(L.rstrip()[:-6])
            break
        hdr.append(L)
    else:
        raise SystemExit(f"no := for theorem at {path}:{line}")
    return "\n".join(hdr).rstrip() + " := by\n  sorry"


def extract_decl_block(path: Path, name: str) -> str:
    """Return def/abbrev/structure block for `name` (header through end of decl)."""
    lines = path.read_text().splitlines()
    for i, L in enumerate(lines):
        if not re.match(
            rf"^(?:noncomputable\s+|abbrev\s+)*(?:def|abbrev|structure)\s+{re.escape(name)}\b",
            L,
        ):
            continue
        j = i + 1
        while j < len(lines):
            N = lines[j]
            if re.match(
                r"^(?:noncomputable\s+|protected\s+|private\s+|abbrev\s+)*"
                r"(?:def|abbrev|structure|theorem|lemma|axiom|namespace|end)\b",
                N,
            ):
                break
            if (
                N.startswith("/- Paper")
                or N.startswith("/-!")
                or N.startswith("/--")
                or N.startswith("/-")
            ):
                break
            j += 1
        return "\n".join(lines[i:j]).rstrip()
    raise SystemExit(f"missing decl {name} in {path}")


def sorry_def(path: Path, name: str) -> str:
    """Keep type signature; replace body with `sorry`."""
    block = extract_decl_block(path, name)
    lines = block.splitlines()
    hdr: list[str] = []
    for L in lines:
        if ":=" in L:
            hdr.append(L.split(":=")[0].rstrip())
            break
        if L.rstrip().endswith(" where"):
            # inductive-style: keep until where, then sorry is wrong — use opaque-style
            hdr.append(L.rstrip()[:-6].rstrip())
            break
        hdr.append(L)
    else:
        # gammaMoment-style with `|` matchers: take through type line only
        for L in lines:
            hdr.append(L)
            if L.rstrip().endswith(":") or "→" in L:
                break
        text = "\n".join(hdr).rstrip()
        if text.endswith(":"):
            text = text[:-1].rstrip()
        return text + " := sorry"
    return "\n".join(hdr).rstrip() + " := sorry"


def main() -> None:
    g = json.load(open(ROOT / "holes-graph.json"))
    nodes = g["nodes"]
    assert len(nodes) == 38, len(nodes)

    thm_names: list[str] = []
    thm_blocks: list[str] = []
    for n in nodes:
        fqn = f"Lyasoff2016.{n['id']}"
        if fqn in CLASSICAL_AXIOM_THMS:
            continue  # classical axioms: disclosed, not Comparator
        path_s, line_s = n["file"].split(":")
        thm_names.append(fqn)
        thm_blocks.append(extract_header(ROOT / path_s, int(line_s)))

    # Supporting defs with full Mathlib-auditable bodies
    keep_full = [
        ("Lyasoff2016/Setting.lean", "IsBM"),
        ("Lyasoff2016/Setting.lean", "expInt"),
        ("Lyasoff2016/Setting.lean", "jointLaw"),
        ("Lyasoff2016/Setting.lean", "IsJointDensity"),
        ("Lyasoff2016/Setting.lean", "IsCondDensity"),
        ("Lyasoff2016/Setting.lean", "pd"),
        ("Lyasoff2016/Setting.lean", "invGammaDensity"),
        ("Lyasoff2016/Auxiliary.lean", "IsInftyDensity"),
        ("Lyasoff2016/Zproc.lean", "Zproc"),
        ("Lyasoff2016/GammaMoment.lean", "gammaMoment"),
        ("Lyasoff2016/JointA.lean", "jointA"),
        ("Lyasoff2016/JointFokkerPlanckHelpers.lean", "jointDomain"),
        ("Lyasoff2016/Foliation.lean", "SatisfiesStrikingIdentity"),
        ("Lyasoff2016/Foliation.lean", "laplaceCond"),
        ("Lyasoff2016/Sfun.lean", "Sfun"),
        ("Lyasoff2016/UpperGamma.lean", "upperGamma"),
        ("Lyasoff2016/Asian.lean", "asianCall"),
        ("Lyasoff2016/Asian.lean", "asianMarketPrice"),
    ]
    # Formula / OfNat-proof holes (types only in Comparator).
    keep_sorry = [
        ("Lyasoff2016/YorDensity.lean", "yorDensity"),
        ("Lyasoff2016/PiFormula.lean", "piFormula"),
        ("Lyasoff2016/PiHalfFormula.lean", "piHalfFormula"),
        ("Lyasoff2016/ContourIntegrand.lean", "contourIntegrand"),
        ("Lyasoff2016/Ffun.lean", "Ffun"),
        ("Lyasoff2016/FfunDeriv.lean", "FfunDeriv"),
        ("Lyasoff2016/Dufresne.lean", "dufresne"),
        ("Lyasoff2016/JointFokkerPlanckAdjoint.lean", "jointFokkerPlanckAdjoint"),
        ("Lyasoff2016/Foliation.lean", "SatisfiesTheorem41PDE"),
        ("Lyasoff2016/Foliation.lean", "SatisfiesFoliationODE"),
        ("Lyasoff2016/Foliation.lean", "TransformedMassIdentity"),
        ("Lyasoff2016/Foliation.lean", "HasLaplaceReduction"),
        ("Lyasoff2016/ContourEq.lean", "contourEq"),
    ]
    after_sorry: list[tuple[str, str]] = []

    def_blocks: list[str] = []
    for rel, name in keep_full:
        def_blocks.append(extract_decl_block(ROOT / rel, name))
    for rel, name in keep_sorry:
        def_blocks.append(sorry_def(ROOT / rel, name))
    for rel, name in after_sorry:
        def_blocks.append(extract_decl_block(ROOT / rel, name))

    body = "\n\n".join(def_blocks + thm_blocks)
    body = re.sub(r"\n{3,}", "\n\n", body)
    # Without `open scoped ContDiff`, bare `∞` is ℝ≥0∞; use the ℕ∞ top form.
    body = body.replace(
        "ContDiff ℝ ∞",
        "ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)",
    )

    header = """/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import Mathlib.Probability.BrownianMotion.Basic

/-!
# Palomar Challenge (statement of record)

Mathlib-only statement file for the Lyasoff 2016 proof-chart family. Compared
declarations match `Solution.lean` via the `Lyasoff2016/` library. Framing:
reconstruction/verification of Lyasoff, *Another look at the integral of
exponential Brownian motion and the pricing of Asian options*, Finance Stoch.
20 (2016) 1061–1096. Andrew Lyasoff did not participate in or endorse this
formalization. Comparator covers every proof-chart theorem whose Solution proof
uses only `propext` / `Quot.sound` / `Classical.choice`. Four numerical
certificates from the chart are disclosed outside Comparator
(see `PROVENANCE.md` / `formalization.yaml`).
-/
@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real
-- Do not `open scoped ContDiff`: it reserves `ω` as an infinity notation.

namespace Lyasoff2016

-- Force the same level-parameter name Comparator sees on Solution (`u_1`).
-- Mathlib-only Challenge otherwise elaborates `Type*` as `u_2`.
universe u_1

noncomputable section

variable {Ω : Type u_1} [MeasurableSpace Ω]

"""
    # Library decls use `Type*`; rewrite so Challenge levelParams match Solution.
    body = body.replace("{Ω : Type*}", "{Ω : Type u_1}")
    footer = "\n\nend\nend Lyasoff2016\n"
    text = header + body.strip() + footer
    (ROOT / "Challenge.lean").write_text(text)
    print(f"theorems={len(thm_names)} def_names={len(DEF_NAMES)}")
    print(f"lines={text.count(chr(10))+1} bytes={len(text.encode())}")
    missing_classical = sorted(CLASSICAL_AXIOM_THMS)
    print("excluded_classical:", ", ".join(missing_classical))

    cfg = {
        "challenge_module": "Challenge",
        "solution_module": "Solution",
        "theorem_names": thm_names,
        "definition_names": DEF_NAMES,
        "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
    }
    (ROOT / "comparator.json").write_text(json.dumps(cfg, indent=2) + "\n")
    print("wrote Challenge.lean and comparator.json")


if __name__ == "__main__":
    main()
