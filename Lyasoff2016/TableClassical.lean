/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
# §6 Tables 1–4 — classical numerical certificates

Lyasoff (2016) reports high-precision mpmath/spline quadratures of `∬ Re F` for the
market Asian call. These axioms record those printed absolute-error claims; they are
not interval-arithmetic re-derivations. Density identities remain axioms-clean.
-/
module

public import Lyasoff2016.Asian
public import Lyasoff2016.TableParams


@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal Real

noncomputable section
namespace Lyasoff2016

/-- Risk-free rate used in Tables 1–4 (paper: r = 2.5% = 5/200). -/
def tableRate : ℝ := (5 : ℝ) / 200

/-! Printed digit strings (vision OCR Tables 1–4). -/

def table1 : Fin 6 → ℚ
  | 0 => 302471713826246 / 1000000000000000
  | 1 => 203823272652937 / 1000000000000000
  | 2 => 109134667336200 / 1000000000000000
  | 3 => 38694821814008 / 1000000000000000
  | 4 => 8127776133751 / 1000000000000000
  | 5 => 1028464610034 / 1000000000000000

def table2 : Fin 6 → ℚ
  | 0 => 30256324113 / 100000000000
  | 1 => 20574087443 / 100000000000
  | 2 => 11939786084 / 100000000000
  | 3 => 5691875027 / 100000000000
  | 4 => 2222765943 / 100000000000
  | 5 => 727337085 / 100000000000

def table3 : Fin 6 → ℚ
  | 0 => 304923087645 / 1000000000000
  | 1 => 208572293433 / 1000000000000
  | 2 => 120806302805 / 1000000000000
  | 3 => 56156816264 / 1000000000000
  | 4 => 20689114929 / 1000000000000
  | 5 => 6174095598 / 1000000000000

def table4 : Fin 6 → ℚ
  | 0 => 30620859092 / 100000000000
  | 1 => 21565075810 / 100000000000
  | 2 => 13878233268 / 100000000000
  | 3 => 8160208509 / 100000000000
  | 4 => 4425815874 / 100000000000
  | 5 => 2244768617 / 100000000000

/-- Classical numerical certificate (Lyasoff p. 1094, Table 1): market price within
`err0` of the printed digit string (mp.dps = 120; K = 0 error ≤ 1e-15). -/
axiom table1_asian_enclosure_classical {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (_hW : IsBM P W) (i : Fin 6) :
    |asianMarketPrice P W table1Params.σ tableRate table1Params.T.toNNReal
        (tableStrikes i) - (table1 i : ℝ)| ≤ table1Params.err0

/-- Classical numerical certificate (Lyasoff p. 1094, Table 2): market price within
`err0` of the printed digit string (mp.dps = 60; K = 0 error ≤ 1e-11). -/
axiom table2_asian_enclosure_classical {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (_hW : IsBM P W) (i : Fin 6) :
    |asianMarketPrice P W table2Params.σ tableRate table2Params.T.toNNReal
        (tableStrikes i) - (table2 i : ℝ)| ≤ table2Params.err0

/-- Classical numerical certificate (Lyasoff p. 1095, Table 3): market price within
`err0` of the printed digit string (mp.dps = 60; K = 0 error ≤ 1e-12). -/
axiom table3_asian_enclosure_classical {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (_hW : IsBM P W) (i : Fin 6) :
    |asianMarketPrice P W table3Params.σ tableRate table3Params.T.toNNReal
        (tableStrikes i) - (table3 i : ℝ)| ≤ table3Params.err0

/-- Classical numerical certificate (Lyasoff p. 1095, Table 4): market price within
`err0` of the printed digit string (mp.dps = 45; K = 0 error ≤ 1e-11). -/
axiom table4_asian_enclosure_classical {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (_hW : IsBM P W) (i : Fin 6) :
    |asianMarketPrice P W table4Params.σ tableRate table4Params.T.toNNReal
        (tableStrikes i) - (table4 i : ℝ)| ≤ table4Params.err0

end Lyasoff2016
