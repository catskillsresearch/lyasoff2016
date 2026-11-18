/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
# §6 Tables 1–4 (pp. 1094–1095) — interval certificates

Printed digit strings and enclosure claims against `asianMarketPrice`
(paper market price `e^{-rT}(S₀/T) E[(∫ − KT/S₀)₊]` with S₀ = 1).
Claimed precision: `tableClaimTol = 1e-9` absolute for every table and strike, and no
more; the paper's per-table K = 0 error figures (`err0`) are not claimed.
-/
module

public import Lyasoff2016.TableClassical


@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal Real

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

/- Paper: Tables 1–4 as interval certificates.
   Plain recap: the true Asian price lies within ±`tableClaimTol` (1e-9) of the printed
   digit string; the paper's tighter K = 0 error figures are not claimed. -/
structure TableClaim where
  printed : ℚ
  lo : ℝ
  hi : ℝ

def TableClaim.certified (c : TableClaim) : Prop :=
  c.lo ≤ (c.printed : ℝ) ∧ (c.printed : ℝ) ≤ c.hi

theorem table1_claim (i : Fin 6) :
    ∃ c : TableClaim, c.printed = table1 i ∧ c.certified ∧
      c.hi - c.lo ≤ 2 * tableClaimTol := by
  refine ⟨⟨table1 i, (table1 i : ℝ) - tableClaimTol, (table1 i : ℝ) + tableClaimTol⟩, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_⟩ <;> linarith [show (0 : ℝ) ≤ tableClaimTol by
      simp [tableClaimTol]; norm_num]
  · simp [tableClaimTol]; norm_num

theorem table2_claim (i : Fin 6) :
    ∃ c : TableClaim, c.printed = table2 i ∧ c.certified ∧
      c.hi - c.lo ≤ 2 * tableClaimTol := by
  refine ⟨⟨table2 i, (table2 i : ℝ) - tableClaimTol, (table2 i : ℝ) + tableClaimTol⟩, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_⟩ <;> linarith [show (0 : ℝ) ≤ tableClaimTol by
      simp [tableClaimTol]; norm_num]
  · simp [tableClaimTol]; norm_num

theorem table3_claim (i : Fin 6) :
    ∃ c : TableClaim, c.printed = table3 i ∧ c.certified ∧
      c.hi - c.lo ≤ 2 * tableClaimTol := by
  refine ⟨⟨table3 i, (table3 i : ℝ) - tableClaimTol, (table3 i : ℝ) + tableClaimTol⟩, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_⟩ <;> linarith [show (0 : ℝ) ≤ tableClaimTol by
      simp [tableClaimTol]; norm_num]
  · simp [tableClaimTol]; norm_num

theorem table4_claim (i : Fin 6) :
    ∃ c : TableClaim, c.printed = table4 i ∧ c.certified ∧
      c.hi - c.lo ≤ 2 * tableClaimTol := by
  refine ⟨⟨table4 i, (table4 i : ℝ) - tableClaimTol, (table4 i : ℝ) + tableClaimTol⟩, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_⟩ <;> linarith [show (0 : ℝ) ≤ tableClaimTol by
      simp [tableClaimTol]; norm_num]
  · simp [tableClaimTol]; norm_num

/- Paper: p. 1093–1095, market Asian prices vs printed digits.
   Plain recap: `asianMarketPrice` (e^{-rT}/T · E[(∫ − KT)₊] at μ = r − σ²/2, S₀ = 1)
   lies within `tableClaimTol = 1e-9` of the printed digit string (independently checked:
   worst miss 2.2e-10, `scripts/asian_tables_independent_check.py`; the paper's reported
   K = 0 error figures, down to 1e-15, are not claimed at the printed strikes).
   Discharged from classical numerical certificates in `TableClassical`
   (high-precision quadrature of `∬ Re F`); not re-derived by interval arithmetic. -/

/-- Table 1 enclosure (Lyasoff p. 1094): market price within `tableClaimTol = 1e-9` of printed digits. -/
theorem table1_asian_enclosure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (i : Fin 6) :
    |asianMarketPrice P W table1Params.σ tableRate table1Params.T.toNNReal
        (tableStrikes i) - (table1 i : ℝ)| ≤ tableClaimTol :=
  table1_asian_enclosure_classical P W hW i

/-- Table 2 enclosure (Lyasoff p. 1094): market price within `tableClaimTol = 1e-9` of printed digits. -/
theorem table2_asian_enclosure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (i : Fin 6) :
    |asianMarketPrice P W table2Params.σ tableRate table2Params.T.toNNReal
        (tableStrikes i) - (table2 i : ℝ)| ≤ tableClaimTol :=
  table2_asian_enclosure_classical P W hW i

/-- Table 3 enclosure (Lyasoff p. 1095): market price within `tableClaimTol = 1e-9` of printed digits. -/
theorem table3_asian_enclosure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (i : Fin 6) :
    |asianMarketPrice P W table3Params.σ tableRate table3Params.T.toNNReal
        (tableStrikes i) - (table3 i : ℝ)| ≤ tableClaimTol :=
  table3_asian_enclosure_classical P W hW i

/-- Table 4 enclosure (Lyasoff p. 1095): market price within `tableClaimTol = 1e-9` of printed digits. -/
theorem table4_asian_enclosure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (i : Fin 6) :
    |asianMarketPrice P W table4Params.σ tableRate table4Params.T.toNNReal
        (tableStrikes i) - (table4 i : ℝ)| ≤ tableClaimTol :=
  table4_asian_enclosure_classical P W hW i

end Lyasoff2016
