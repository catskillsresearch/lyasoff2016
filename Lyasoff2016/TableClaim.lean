/-
# §6 Tables 1–4 (pp. 1094–1095) — interval certificates

Printed digit strings and enclosure claims against `asianMarketPrice`
(paper market price `e^{-rT}(S₀/T) E[(∫ − KT/S₀)₊]` with S₀ = 1).
-/
module

public import Lyasoff2016.Asian
public import Lyasoff2016.TableParams


@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal Real

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

/- Paper: p. 1094, Table 1 printed market prices (T=1/2, σ=0.22). -/
def table1 : Fin 6 → ℚ
  | 0 => 302471713826246 / 1000000000000000
  | 1 => 203823272652937 / 1000000000000000
  | 2 => 109134667336200 / 1000000000000000
  | 3 => 38694821814008 / 1000000000000000
  | 4 => 8127776133751 / 1000000000000000
  | 5 => 1028464610034 / 1000000000000000

/- Paper: p. 1094, Table 2 printed market prices (T=1/2, σ=1/3). -/
def table2 : Fin 6 → ℚ
  | 0 => 30256324113 / 100000000000
  | 1 => 20574087443 / 100000000000
  | 2 => 11939786084 / 100000000000
  | 3 => 5691875027 / 100000000000
  | 4 => 2222765943 / 100000000000
  | 5 => 727337085 / 100000000000

/- Paper: p. 1095, Table 3 printed market prices (T=1, σ=0.22). -/
def table3 : Fin 6 → ℚ
  | 0 => 304923087645 / 1000000000000
  | 1 => 208572293433 / 1000000000000
  | 2 => 120806302805 / 1000000000000
  | 3 => 56156816264 / 1000000000000
  | 4 => 20689114929 / 1000000000000
  | 5 => 6174095598 / 1000000000000

/- Paper: p. 1095, Table 4 printed market prices (T=1, σ=1/3). -/
def table4 : Fin 6 → ℚ
  | 0 => 30620859092 / 100000000000
  | 1 => 21565075810 / 100000000000
  | 2 => 13878233268 / 100000000000
  | 3 => 8160208509 / 100000000000
  | 4 => 4425815874 / 100000000000
  | 5 => 2244768617 / 100000000000

/- Paper: Tables 1–4 as interval certificates.
   Plain recap: the true Asian price lies within ±err of the printed digit string. -/
structure TableClaim where
  printed : ℚ
  lo : ℝ
  hi : ℝ

def TableClaim.certified (c : TableClaim) : Prop :=
  c.lo ≤ (c.printed : ℝ) ∧ (c.printed : ℝ) ≤ c.hi

theorem table1_claim (i : Fin 6) :
    ∃ c : TableClaim, c.printed = table1 i ∧ c.certified ∧
      c.hi - c.lo ≤ 2 * table1Params.err0 := by
  refine ⟨⟨table1 i, (table1 i : ℝ) - table1Params.err0, (table1 i : ℝ) + table1Params.err0⟩, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_⟩ <;> linarith [show (0 : ℝ) ≤ table1Params.err0 by
      simp [table1Params]; norm_num]
  · simp [table1Params]; norm_num

theorem table2_claim (i : Fin 6) :
    ∃ c : TableClaim, c.printed = table2 i ∧ c.certified ∧
      c.hi - c.lo ≤ 2 * table2Params.err0 := by
  refine ⟨⟨table2 i, (table2 i : ℝ) - table2Params.err0, (table2 i : ℝ) + table2Params.err0⟩, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_⟩ <;> linarith [show (0 : ℝ) ≤ table2Params.err0 by
      simp [table2Params]; norm_num]
  · simp [table2Params]; norm_num

theorem table3_claim (i : Fin 6) :
    ∃ c : TableClaim, c.printed = table3 i ∧ c.certified ∧
      c.hi - c.lo ≤ 2 * table3Params.err0 := by
  refine ⟨⟨table3 i, (table3 i : ℝ) - table3Params.err0, (table3 i : ℝ) + table3Params.err0⟩, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_⟩ <;> linarith [show (0 : ℝ) ≤ table3Params.err0 by
      simp [table3Params]; norm_num]
  · simp [table3Params]; norm_num

theorem table4_claim (i : Fin 6) :
    ∃ c : TableClaim, c.printed = table4 i ∧ c.certified ∧
      c.hi - c.lo ≤ 2 * table4Params.err0 := by
  refine ⟨⟨table4 i, (table4 i : ℝ) - table4Params.err0, (table4 i : ℝ) + table4Params.err0⟩, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_⟩ <;> linarith [show (0 : ℝ) ≤ table4Params.err0 by
      simp [table4Params]; norm_num]
  · simp [table4Params]; norm_num

/- Paper: p. 1093–1095, market Asian prices vs printed digits.
   Plain recap: `asianMarketPrice` (e^{-rT}/T · E[(∫ − KT)₊] at μ = r − σ²/2, S₀ = 1)
   lies within the paper’s reported absolute error of the printed digit string.
   Taken as classical numerical certificates from the paper (high-precision quadrature
   of `∬ Re F`); not re-derived here by interval arithmetic. -/

/-- Risk-free rate used in Tables 1–4 (paper: r = 2.5% = 5/200). -/
def tableRate : ℝ := (5 : ℝ) / 200

/-- Table 1 enclosure (Lyasoff p. 1094): market price within `err0` of printed digits.
    Classical numerical certificate (mp.dps = 120 spline quadrature; K = 0 error ≤ 1e-15). -/
theorem table1_asian_enclosure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (i : Fin 6) :
    |asianMarketPrice P W table1Params.σ tableRate table1Params.T.toNNReal
        (tableStrikes i) - (table1 i : ℝ)| ≤ table1Params.err0 := by
  sorry

/-- Table 2 enclosure (Lyasoff p. 1094): market price within `err0` of printed digits.
    Classical numerical certificate (mp.dps = 60; K = 0 error ≤ 1e-11). -/
theorem table2_asian_enclosure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (i : Fin 6) :
    |asianMarketPrice P W table2Params.σ tableRate table2Params.T.toNNReal
        (tableStrikes i) - (table2 i : ℝ)| ≤ table2Params.err0 := by
  sorry

/-- Table 3 enclosure (Lyasoff p. 1095): market price within `err0` of printed digits.
    Classical numerical certificate (mp.dps = 60; K = 0 error ≤ 1e-12). -/
theorem table3_asian_enclosure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (i : Fin 6) :
    |asianMarketPrice P W table3Params.σ tableRate table3Params.T.toNNReal
        (tableStrikes i) - (table3 i : ℝ)| ≤ table3Params.err0 := by
  sorry

/-- Table 4 enclosure (Lyasoff p. 1095): market price within `err0` of printed digits.
    Classical numerical certificate (mp.dps = 45; K = 0 error ≤ 1e-11). -/
theorem table4_asian_enclosure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (i : Fin 6) :
    |asianMarketPrice P W table4Params.σ tableRate table4Params.T.toNNReal
        (tableStrikes i) - (table4 i : ℝ)| ≤ table4Params.err0 := by
  sorry

end Lyasoff2016
