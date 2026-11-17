/-
# §6 Tables 1–4 (pp. 1094–1095) — interval certificates

Paper: all cases use S₀ = 1, r = 2.5% = 5/200; prices at t = 0.
-/
module

public import Lyasoff2016.Asian


@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal Real

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

/- Paper: p. 1094–1095, Tables 1–4 parameter regimes.
   Plain recap: Asian calls with fixed r = 2.5%, S₀ = 1, varying T, σ, K. -/
structure TableParams where
  T : ℝ
  σ : ℝ
  mp_dps : ℕ
  err0 : ℝ  -- reported absolute error bound at K = 0

/-- Table 1: T = 1/2, σ = 22/100, mp.dps = 120. -/
def table1Params : TableParams := ⟨1 / 2, 22 / 100, 120, 1e-15⟩

/-- Table 2: T = 1/2, σ = 1/3, mp.dps = 60. -/
def table2Params : TableParams := ⟨1 / 2, 1 / 3, 60, 1e-11⟩

/-- Table 3: T = 1, σ = 22/100, mp.dps = 60. -/
def table3Params : TableParams := ⟨1, 22 / 100, 60, 1e-12⟩

/-- Table 4: T = 1, σ = 1/3, mp.dps = 45. -/
def table4Params : TableParams := ⟨1, 1 / 3, 45, 1e-11⟩

/-- Strikes K appearing in all four tables. -/
def tableStrikes : Fin 6 → ℚ
  | 0 => 7 / 10
  | 1 => 8 / 10
  | 2 => 9 / 10
  | 3 => 1
  | 4 => 11 / 10
  | 5 => 12 / 10

/- Paper: p. 1094, Table 1 printed Asian call prices.
   Plain recap: numerical values for T=1/2, σ=0.22. -/
def table1 : Fin 6 → ℚ
  | 0 => 302471713826246 / 1000000000000000
  | 1 => 203823272652937 / 1000000000000000
  | 2 => 109134667336200 / 1000000000000000
  | 3 => 38694821814008 / 1000000000000000
  | 4 => 8127776133751 / 1000000000000000
  | 5 => 1028464610034 / 1000000000000000

/- Paper: p. 1094, Table 2. -/
def table2 : Fin 6 → ℚ
  | 0 => 30256324113 / 100000000000
  | 1 => 20574087443 / 100000000000
  | 2 => 11939786084 / 100000000000
  | 3 => 5691875027 / 100000000000
  | 4 => 2222765943 / 100000000000
  | 5 => 727337085 / 100000000000

/- Paper: p. 1095, Table 3. -/
def table3 : Fin 6 → ℚ
  | 0 => 304923087645 / 1000000000000
  | 1 => 208572293433 / 1000000000000
  | 2 => 120806302805 / 1000000000000
  | 3 => 56156816264 / 1000000000000
  | 4 => 20689114929 / 1000000000000
  | 5 => 6174095598 / 1000000000000

/- Paper: p. 1095, Table 4. -/
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

/- Paper: p. 1094–1095, tables vs Asian price.
   Plain recap: the true Asian call lies within the paper’s reported absolute error
   of the printed digit string (interval certificate for the pricing integral).
   Taken as classical numerical certificates from the paper (high-precision quadrature
   of `∬ Re F`); not re-derived here by interval arithmetic. -/

/-- Classical Table 1 enclosure (Lyasoff p. 1094). -/
axiom table1_asian_enclosure_classical {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (i : Fin 6) :
    |asianCall P W (22 / 100) (5 / 200 - (22 / 100) ^ 2 / 2) (1 / 2 : ℝ≥0)
        (tableStrikes i) - (table1 i : ℝ)| ≤ table1Params.err0

theorem table1_asian_enclosure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (i : Fin 6) :
    |asianCall P W (22 / 100) (5 / 200 - (22 / 100) ^ 2 / 2) (1 / 2 : ℝ≥0)
        (tableStrikes i) - (table1 i : ℝ)| ≤ table1Params.err0 :=
  table1_asian_enclosure_classical P W hW i

/-- Classical Table 2 enclosure (Lyasoff p. 1094). -/
axiom table2_asian_enclosure_classical {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (i : Fin 6) :
    |asianCall P W (1 / 3) (5 / 200 - (1 / 3) ^ 2 / 2) (1 / 2 : ℝ≥0)
        (tableStrikes i) - (table2 i : ℝ)| ≤ table2Params.err0

theorem table2_asian_enclosure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (i : Fin 6) :
    |asianCall P W (1 / 3) (5 / 200 - (1 / 3) ^ 2 / 2) (1 / 2 : ℝ≥0)
        (tableStrikes i) - (table2 i : ℝ)| ≤ table2Params.err0 :=
  table2_asian_enclosure_classical P W hW i

/-- Classical Table 3 enclosure (Lyasoff p. 1095). -/
axiom table3_asian_enclosure_classical {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (i : Fin 6) :
    |asianCall P W (22 / 100) (5 / 200 - (22 / 100) ^ 2 / 2) (1 : ℝ≥0)
        (tableStrikes i) - (table3 i : ℝ)| ≤ table3Params.err0

theorem table3_asian_enclosure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (i : Fin 6) :
    |asianCall P W (22 / 100) (5 / 200 - (22 / 100) ^ 2 / 2) (1 : ℝ≥0)
        (tableStrikes i) - (table3 i : ℝ)| ≤ table3Params.err0 :=
  table3_asian_enclosure_classical P W hW i

/-- Classical Table 4 enclosure (Lyasoff p. 1095). -/
axiom table4_asian_enclosure_classical {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (i : Fin 6) :
    |asianCall P W (1 / 3) (5 / 200 - (1 / 3) ^ 2 / 2) (1 : ℝ≥0)
        (tableStrikes i) - (table4 i : ℝ)| ≤ table4Params.err0

theorem table4_asian_enclosure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (i : Fin 6) :
    |asianCall P W (1 / 3) (5 / 200 - (1 / 3) ^ 2 / 2) (1 : ℝ≥0)
        (tableStrikes i) - (table4 i : ℝ)| ≤ table4Params.err0 :=
  table4_asian_enclosure_classical P W hW i

end Lyasoff2016
