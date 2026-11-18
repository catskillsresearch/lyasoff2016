/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Modified Bessel function K₁ (whole-line integral representation, DLMF 10.32.9).
-/
module

public import Lyasoff2016.Setting


@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/- The standard whole-line integral representation from DLMF 10.32.9,
   specialized to order one.  Mathlib does not currently define `Kν`. -/
def modifiedBesselK1 (z : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ u : ℝ, Real.exp (-z * Real.cosh u + u)

namespace modifiedBesselK1

/- Paper: p. 1075, link of the foliation constant to modified Bessel K₁.
   The printed calculation is
   `∫ exp (-u/2 - (4/x) cosh (u/2)) du = 4 K₁(4/x)`. -/
theorem identity (x : ℝ) :
    ∫ u : ℝ, Real.exp (-u / 2 - (4 / x) * Real.cosh (u / 2)) =
      4 * modifiedBesselK1 (4 / x) := by
  let g : ℝ → ℝ := fun u => Real.exp (-u - (4 / x) * Real.cosh u)
  have hscale : (∫ u : ℝ, g (u / 2)) = 2 * ∫ u : ℝ, g u := by
    simpa using (Measure.integral_comp_div g (2 : ℝ))
  have hneg : (∫ u : ℝ, g u) =
      ∫ u : ℝ, Real.exp (-(4 / x) * Real.cosh u + u) := by
    rw [← MeasureTheory.integral_neg_eq_self]
    congr 1
    funext u
    simp only [g, neg_neg, Real.cosh_neg]
    ring_nf
  rw [show (fun u : ℝ => Real.exp (-u / 2 - (4 / x) * Real.cosh (u / 2))) =
      fun u => g (u / 2) by funext u; simp [g]; ring_nf]
  rw [hscale, hneg]
  simp only [modifiedBesselK1]
  ring

end modifiedBesselK1
end Lyasoff2016