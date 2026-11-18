/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Complex Asian inner integral `S_{k,p}(A)` for complex rate `A` (p. 1091).
-/
module

public import Lyasoff2016.Sfun


@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/- Paper: p. 1091, first display, S_{k,p} for complex A with ℜ(A) > 0:
     S_{k,p}(A) := ∫_k^∞ e^{−A/x} (x − k) / x^p dx. -/
def SfunC (k : ℝ) (p : ℕ) (A : ℂ) : ℂ :=
  ∫ x in Ioi k, (((x - k) * x ^ (-(p : ℤ)) : ℝ) : ℂ) * Complex.exp (-A / x)

namespace SfunC

/-- On real arguments (and integer strikes) the complex `SfunC` is the real `Sfun`, so
`Sfun.zero` and `Sfun.closed_form` evaluate it there. -/
theorem ofReal (k p : ℕ) (α : ℝ) :
    SfunC (k : ℝ) p (α : ℂ) = ((Sfun k p α : ℝ) : ℂ) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hset : (∫ v in Ioi (0 : ℝ), max (v - (k : ℝ)) 0 * v ^ (-(p : ℤ)) * Real.exp (-α / v)) =
      ∫ v in Ioi (k : ℝ), (v - (k : ℝ)) * v ^ (-(p : ℤ)) * Real.exp (-α / v) := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (Ioi_subset_Ioi hk)]
    · refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
      rw [max_eq_left (sub_nonneg.mpr (le_of_lt hv))]
    · intro v hv
      have hvk : v ≤ (k : ℝ) := by simpa using hv.2
      rw [max_eq_right (sub_nonpos.mpr hvk)]
      ring
  simp only [SfunC, Sfun]
  rw [hset, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  push_cast
  ring_nf

end SfunC

end Lyasoff2016