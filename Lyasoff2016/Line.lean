/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Integral lines of the foliation vector field V = (σ²x/2)∂ₓ + σ∂ᵧ.
-/
module

public import Lyasoff2016.Setting


@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/- Paper: p. 1071, integral lines of V = (σ²x/2)∂ₓ + σ∂ᵧ.
   Plain recap: the flow is u ↦ (x e^{σ²u/2}, y + σ u).
   PAPER NOTE: printed second coordinate (y+u)σ is wrong; flow of σ∂ᵧ is y+σu. -/
def line (σ x y u : ℝ) : ℝ × ℝ := (x * Real.exp (σ ^ 2 * u / 2), y + σ * u)

namespace line

/- Paper: p. 1071.
   Plain recap: that curve is an integral curve of the vector field V. -/
theorem is_integral_curve (σ x y u : ℝ) :
    HasDerivAt (fun u => (line σ x y u).1) (σ ^ 2 / 2 * (line σ x y u).1) u ∧
    HasDerivAt (fun u => (line σ x y u).2) σ u := by
  constructor
  · have h : HasDerivAt (fun u : ℝ => σ ^ 2 * u / 2) (σ ^ 2 / 2) u := by
      simpa using ((hasDerivAt_id u).const_mul (σ ^ 2)).div_const 2
    have := (h.exp).const_mul x
    simp only [line]
    convert this using 1
    ring
  · simp only [line]
    simpa using ((hasDerivAt_id u).const_mul σ).const_add y

/- Paper: p. 1073, foliation.
   Plain recap: every point (x,y) in ℝ₊₊×ℝ lies on the line through (x e^{-σy/2}, 0). -/
theorem foliation (σ : ℝ) (hσ : σ ≠ 0) (x y : ℝ) :
    line σ (x * Real.exp (-(σ * y) / 2)) 0 (y / σ) = (x, y) := by
  simp only [line]
  refine Prod.ext ?_ ?_
  · show x * Real.exp (-(σ * y) / 2) * Real.exp (σ ^ 2 * (y / σ) / 2) = x
    have : σ ^ 2 * (y / σ) / 2 = σ * y / 2 := by field_simp
    rw [this, mul_assoc, ← Real.exp_add]
    have : -(σ * y) / 2 + σ * y / 2 = 0 := by ring
    rw [this]; simp
  · show 0 + σ * (y / σ) = y
    field_simp; ring

end line
end Lyasoff2016