/-
Complex error function `cerf` used in integral representations (p. 1082–1083).
-/
module

public import Lyasoff2016.Setting


@[expose] public section

open MeasureTheory Set Filter Topology Metric Complex
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/- Paper: p. 1082–1083, complex error function used to build g_{t,p} for p = 3,4.
   Plain recap: entire function erf on ℂ, defined via the Gaussian integral
   `erf z = (2/√π) ∫₀¹ z e^{-(zs)²} ds` (the substitution `u = zs` in `(2/√π) ∫₀ᶻ e^{-u²} du`). -/
def cerf (z : ℂ) : ℂ :=
  (2 / Real.sqrt Real.pi : ℂ) * ∫ s in (0 : ℝ)..1, z * cexp (-(z * (s : ℂ)) ^ 2)

namespace cerf

/-- `cerf` is odd. -/
theorem neg (z : ℂ) : cerf (-z) = -cerf z := by
  simp only [cerf]
  have h : ∀ s : ℝ, -z * cexp (-(-z * (s : ℂ)) ^ 2) = -(z * cexp (-(z * (s : ℂ)) ^ 2)) := by
    intro s
    rw [show (-z * (s : ℂ)) ^ 2 = (z * (s : ℂ)) ^ 2 by ring]
    ring
  simp only [h, intervalIntegral.integral_neg, mul_neg]

/-- The complex error function commutes with complex conjugation. -/
theorem conj (z : ℂ) : cerf (starRingEnd ℂ z) = starRingEnd ℂ (cerf z) := by
  rw [cerf, cerf, map_mul]
  have hc : (starRingEnd ℂ) ((2 / Real.sqrt Real.pi : ℂ)) =
      (2 / Real.sqrt Real.pi : ℂ) := by
    rw [map_div₀, map_ofNat, conj_ofReal]
  rw [hc]
  congr 1
  have hi : (∫ s in (0 : ℝ)..1,
      starRingEnd ℂ (z * cexp (-(z * (s : ℂ)) ^ 2))) =
      starRingEnd ℂ (∫ s in (0 : ℝ)..1, z * cexp (-(z * (s : ℂ)) ^ 2)) :=
    (RCLike.conjLIE (K := ℂ)).toLinearIsometry.intervalIntegral_comp_comm _
  rw [← hi]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [map_mul, ← exp_conj]
  congr 2
  simp only [map_neg, map_pow, map_mul, conj_ofReal]

/-- The `z`-derivative of the integrand `z ↦ z e^{-(zs)²}` is `e^{-(zs)²} (1 - 2 (zs)²)`. -/
private theorem hasDerivAt_integrand (s : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => w * cexp (-(w * (s : ℂ)) ^ 2))
      (cexp (-(z * (s : ℂ)) ^ 2) * (1 - 2 * (z * (s : ℂ)) ^ 2)) z := by
  have h1 : HasDerivAt (fun w : ℂ => -(w * (s : ℂ)) ^ 2) (-(2 * (z * (s : ℂ)) * (s : ℂ))) z := by
    have h := (((hasDerivAt_id' z).mul_const (s : ℂ)).fun_pow 2).fun_neg
    convert h using 1
    simp
  have h2 := (hasDerivAt_id' z).fun_mul h1.cexp
  convert h2 using 1
  ring

/-- The same expression `e^{-(zs)²} (1 - 2 (zs)²)` is the `s`-derivative of `s ↦ s e^{-(zs)²}`. -/
private theorem hasDerivAt_primitive (z : ℂ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => (t : ℂ) * cexp (-(z * (t : ℂ)) ^ 2))
      (cexp (-(z * (s : ℂ)) ^ 2) * (1 - 2 * (z * (s : ℂ)) ^ 2)) s := by
  have h1 : HasDerivAt (fun w : ℂ => -(z * w) ^ 2) (-(2 * (z * (s : ℂ)) * z)) (s : ℂ) := by
    have h := (((hasDerivAt_id' (s : ℂ)).const_mul z).fun_pow 2).fun_neg
    convert h using 1
    simp
  have h2 := (hasDerivAt_id' (s : ℂ)).fun_mul h1.cexp
  have h3 : HasDerivAt (fun w : ℂ => w * cexp (-(z * w) ^ 2))
      (cexp (-(z * (s : ℂ)) ^ 2) * (1 - 2 * (z * (s : ℂ)) ^ 2)) (s : ℂ) := by
    convert h2 using 1
    ring
  exact h3.comp_ofReal

/-- `∫₀¹ e^{-(zs)²} (1 - 2 (zs)²) ds = e^{-z²}` by the fundamental theorem of calculus. -/
private theorem integral_deriv_integrand (z : ℂ) :
    ∫ s in (0 : ℝ)..1, cexp (-(z * (s : ℂ)) ^ 2) * (1 - 2 * (z * (s : ℂ)) ^ 2) =
      cexp (-z ^ 2) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_primitive z s)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp

/-- `cerf' z = (2/√π) e^{-z²}`, by differentiating under the integral sign. -/
theorem hasDerivAt (z : ℂ) :
    HasDerivAt cerf ((2 / Real.sqrt Real.pi : ℂ) * cexp (-z ^ 2)) z := by
  -- The derivative of the integrand is jointly continuous, hence bounded on the compact set
  -- `closedBall z 1 ×ˢ [0, 1]`.
  have hcont : Continuous fun p : ℂ × ℝ =>
      cexp (-(p.1 * (p.2 : ℂ)) ^ 2) * (1 - 2 * (p.1 * (p.2 : ℂ)) ^ 2) := by fun_prop
  obtain ⟨C, hC⟩ := ((isCompact_closedBall z 1).prod
    (isCompact_Icc (a := (0 : ℝ)) (b := 1))).exists_bound_of_continuousOn hcont.continuousOn
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := 1) (x₀ := z) (s := closedBall z 1) (bound := fun _ => C)
    (F := fun (w : ℂ) (s : ℝ) => w * cexp (-(w * (s : ℂ)) ^ 2))
    (F' := fun (w : ℂ) (s : ℝ) => cexp (-(w * (s : ℂ)) ^ 2) * (1 - 2 * (w * (s : ℂ)) ^ 2))
    (closedBall_mem_nhds z one_pos)
    (Eventually.of_forall fun w => Continuous.aestronglyMeasurable (by fun_prop))
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.aestronglyMeasurable (by fun_prop))
    (Eventually.of_forall fun t ht w hw => hC (w, t)
      ⟨hw, by rw [uIoc_of_le zero_le_one] at ht; exact Ioc_subset_Icc_self ht⟩)
    intervalIntegrable_const
    (Eventually.of_forall fun t _ w _ => hasDerivAt_integrand t w)
  have h := key.2.const_mul (2 / Real.sqrt Real.pi : ℂ)
  rw [integral_deriv_integrand] at h
  exact h

/-- `cerf` is entire. -/
theorem differentiable : Differentiable ℂ cerf :=
  fun z => (hasDerivAt z).differentiableAt

/-- `cerf` is smooth (indeed analytic) on `ℂ`. -/
theorem contDiff : ContDiff ℂ ⊤ cerf :=
  differentiable.contDiff

theorem deriv_apply (z : ℂ) :
    deriv cerf z = (2 / Real.sqrt Real.pi : ℂ) * cexp (-z ^ 2) :=
  (hasDerivAt z).deriv

end cerf

end Lyasoff2016
