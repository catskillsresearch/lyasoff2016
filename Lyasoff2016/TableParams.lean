/-
# §6 Tables 1–4 (pp. 1094–1095) — parameter regimes

Paper: all cases use S₀ = 1, r = 2.5% = 5/200; prices at t = 0.
-/
module

public import Mathlib


@[expose] public section

open scoped Real

noncomputable section
namespace Lyasoff2016

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

end Lyasoff2016
