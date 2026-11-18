/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
# §4 Reciprocal moments from the transformed mass identity (4.7)

If a nonnegative integrable `φ0` on `(0, ∞)` satisfies the transformed mass identity
`∫ φ0(x) exp(-a(z)/x) dx = exp(-z²/(2t))` with `a(z) = 4/σ² (cosh(σz/2) - 1)`, then
differentiating in `a` (dominated convergence) gives the weighted reciprocal moments
`∫ x⁻¹ φ0(x) exp(-a(z)/x) dx`, and monotone convergence as `z → 0` gives
`∫ x⁻¹ φ0(x) dx = 1/t`.  These are the analytic inputs for the striking identity (4.4).
-/
module

public import Mathlib

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal Real

noncomputable section
namespace Lyasoff2016

/-- The exponent `a(z) = 4/σ² (cosh(σz/2) − 1)` of the transformed mass identity. -/
def massExponent (σ z : ℝ) : ℝ := 4 / σ ^ 2 * (Real.cosh (σ * z / 2) - 1)

lemma massExponent_pos {σ : ℝ} (hσ : 0 < σ) {z : ℝ} (hz : z ≠ 0) : 0 < massExponent σ z := by
  unfold massExponent
  have : 1 < Real.cosh (σ * z / 2) := Real.one_lt_cosh.2 (by
    have := mul_ne_zero hσ.ne' hz; intro h; apply this; linarith)
  have : (0 : ℝ) < 4 / σ ^ 2 := by positivity
  nlinarith

lemma massExponent_hasDerivAt (σ z : ℝ) :
    HasDerivAt (massExponent σ) (2 / σ * Real.sinh (σ * z / 2)) z := by
  have hlin : HasDerivAt (fun z : ℝ => σ * z / 2) (σ / 2) z := by
    simpa using ((hasDerivAt_id z).const_mul σ).div_const 2
  have h := (((Real.hasDerivAt_cosh (σ * z / 2)).comp z hlin).sub_const 1).const_mul (4 / σ ^ 2)
  unfold massExponent
  refine h.congr_deriv ?_
  rcases eq_or_ne σ 0 with h0 | h0
  · subst h0; simp
  · field_simp
    ring

section MassToMoments

variable {σ t : ℝ} {φ0 : ℝ → ℝ}

/-- Domination: `x⁻¹ e^{-a/x} ≤ 1/a` for `a, x > 0`. -/
lemma inv_mul_exp_neg_div_le {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    x⁻¹ * Real.exp (-a / x) ≤ a⁻¹ := by
  have h1 : a / x + 1 ≤ Real.exp (a / x) := Real.add_one_le_exp _
  have hpos : 0 < Real.exp (a / x) := Real.exp_pos _
  rw [neg_div, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hpos]
  have hxa : x⁻¹ = a⁻¹ * (a / x) := by field_simp
  rw [hxa]
  gcongr
  linarith

variable (hσ : 0 < σ) (ht : 0 < t)
  (hint : IntegrableOn φ0 (Ioi 0)) (hnn : ∀ x, 0 < x → 0 ≤ φ0 x)
  (hmass : ∀ z : ℝ, ∫ x in Ioi (0 : ℝ),
      φ0 x * Real.exp (-4 / (σ ^ 2 * x) * (Real.cosh (σ * z / 2) - 1)) =
        Real.exp (-z ^ 2 / (2 * t)))
include hint

/-- Laplace transform in `1/x` of `φ0` on `(0, ∞)`. -/
def laplaceInv (φ0 : ℝ → ℝ) (a : ℝ) : ℝ := ∫ x in Ioi (0 : ℝ), φ0 x * Real.exp (-a / x)

omit hint in
lemma laplaceInv_massExponent (z : ℝ) :
    laplaceInv φ0 (massExponent σ z) =
      ∫ x in Ioi (0 : ℝ), φ0 x * Real.exp (-4 / (σ ^ 2 * x) * (Real.cosh (σ * z / 2) - 1)) := by
  unfold laplaceInv massExponent
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  congr 2
  have hx : x ≠ 0 := (ne_of_gt hx)
  by_cases hσ0 : σ = 0
  · subst hσ0; simp
  field_simp

lemma aestronglyMeasurable_mul_exp (f : ℝ → ℝ) (hf : Measurable f) :
    AEStronglyMeasurable (fun x => φ0 x * f x) (volume.restrict (Ioi 0)) :=
  hint.aestronglyMeasurable.mul hf.aestronglyMeasurable

/-- Differentiation under the integral sign for `a > 0`. -/
lemma laplaceInv_hasDerivAt {a₀ : ℝ} (ha₀ : 0 < a₀) :
    IntegrableOn (fun x => x⁻¹ * φ0 x * Real.exp (-a₀ / x)) (Ioi 0) ∧
    HasDerivAt (laplaceInv φ0)
      (-∫ x in Ioi (0 : ℝ), x⁻¹ * φ0 x * Real.exp (-a₀ / x)) a₀ := by
  have hmeasE : ∀ a : ℝ, Measurable fun x : ℝ => Real.exp (-a / x) := fun a => by fun_prop
  have hmeasE' : ∀ a : ℝ, Measurable fun x : ℝ => Real.exp (-a / x) * -x⁻¹ := fun a => by
    fun_prop
  have hs : Ioi (a₀ / 2) ∈ 𝓝 a₀ := Ioi_mem_nhds (by linarith)
  have hF_int : Integrable (fun x => φ0 x * Real.exp (-a₀ / x)) (volume.restrict (Ioi 0)) := by
    refine hint.bdd_mul (c := 1) (hmeasE a₀).aestronglyMeasurable ?_ |>.congr ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 (by
        have : 0 ≤ a₀ / x := div_nonneg ha₀.le (le_of_lt hx)
        rw [neg_div]; linarith)
    · exact ae_of_all _ fun x => by simp [mul_comm]
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun a x => φ0 x * Real.exp (-a / x))
    (F' := fun a x => φ0 x * (Real.exp (-a / x) * -x⁻¹))
    (bound := fun x => (a₀ / 2)⁻¹ * ‖φ0 x‖) (μ := volume.restrict (Ioi 0)) hs
    (Eventually.of_forall fun a => hint.aestronglyMeasurable.mul (hmeasE a).aestronglyMeasurable)
    hF_int (hint.aestronglyMeasurable.mul (hmeasE' a₀).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx a ha
      have hx : 0 < x := hx
      have ha : a₀ / 2 < a := ha
      have hapos : 0 < a := by linarith
      rw [norm_mul, norm_mul, norm_neg, Real.norm_eq_abs (Real.exp _),
        abs_of_pos (Real.exp_pos _), norm_inv, Real.norm_eq_abs x, abs_of_pos hx]
      rw [mul_comm ((a₀ / 2)⁻¹)]
      gcongr
      calc Real.exp (-a / x) * x⁻¹ = x⁻¹ * Real.exp (-a / x) := mul_comm _ _
        _ ≤ a⁻¹ := inv_mul_exp_neg_div_le hapos hx
        _ ≤ (a₀ / 2)⁻¹ := by gcongr)
    (hint.norm.const_mul _)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx a _
      have hx : x ≠ 0 := ne_of_gt hx
      have h1 : HasDerivAt (fun a : ℝ => -a / x) (-x⁻¹) a := by
        have := ((hasDerivAt_id a).neg).div_const x
        exact this.congr_deriv (by simp [div_eq_mul_inv])
      exact (h1.exp).const_mul (φ0 x))
  obtain ⟨hint', hderiv⟩ := h
  refine ⟨?_, ?_⟩
  · refine (hint'.neg).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.neg_apply]; ring
  · unfold laplaceInv
    refine hderiv.congr_deriv ?_
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    ring_nf

include hσ ht hmass

/-- Weighted reciprocal moments from the mass identity, for `z ≠ 0`. -/
lemma integral_inv_mul_exp_massExponent {z : ℝ} (hz : z ≠ 0) :
    ∫ x in Ioi (0 : ℝ), x⁻¹ * φ0 x * Real.exp (-massExponent σ z / x) =
      z / t * Real.exp (-z ^ 2 / (2 * t)) / (2 / σ * Real.sinh (σ * z / 2)) := by
  have ha := massExponent_pos hσ hz
  obtain ⟨-, hD⟩ := laplaceInv_hasDerivAt hint ha
  have hcomp := hD.comp z (massExponent_hasDerivAt σ z)
  have hfun : laplaceInv φ0 ∘ massExponent σ = fun z => Real.exp (-z ^ 2 / (2 * t)) := by
    funext z; simp only [Function.comp_apply, laplaceInv_massExponent, hmass]
  rw [hfun] at hcomp
  have hG : HasDerivAt (fun z : ℝ => Real.exp (-z ^ 2 / (2 * t)))
      (Real.exp (-z ^ 2 / (2 * t)) * (-(2 * z) / (2 * t))) z := by
    have := (((hasDerivAt_pow 2 z).neg).div_const (2 * t)).exp
    refine this.congr_deriv ?_
    simp only [Pi.neg_apply]; push_cast; ring
  have huniq := hcomp.unique hG
  have hsinh : Real.sinh (σ * z / 2) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]
    have := mul_ne_zero hσ.ne' hz; intro h; apply this; linarith
  have hσ0 : σ ≠ 0 := hσ.ne'
  have ht0 : t ≠ 0 := ht.ne'
  rw [eq_div_iff (mul_ne_zero (div_ne_zero two_ne_zero hσ0) hsinh)]
  linear_combination (-1 : ℝ) * huniq

include hnn

/-- The reciprocal moment at the zero endpoint: `∫ x⁻¹ φ0 = 1/t`, by monotone convergence
from the weighted moments as `z → 0⁺`. -/
lemma integral_inv_mul_of_mass :
    ∫ x in Ioi (0 : ℝ), x⁻¹ * φ0 x = 1 / t := by
  set μ : Measure ℝ := volume.restrict (Ioi 0) with hμ
  let z : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hzpos : ∀ n, 0 < z n := fun n => by positivity
  have hz0 : ∀ n, z n ≠ 0 := fun n => (hzpos n).ne'
  let a : ℕ → ℝ := fun n => massExponent σ (z n)
  let f : ℕ → ℝ → ℝ := fun n x => x⁻¹ * φ0 x * Real.exp (-a n / x)
  let formula : ℝ → ℝ := fun z =>
    z / t * Real.exp (-z ^ 2 / (2 * t)) / (2 / σ * Real.sinh (σ * z / 2))
  have hfint : ∀ n, Integrable (f n) μ := fun n =>
    (laplaceInv_hasDerivAt hint (massExponent_pos hσ (hz0 n))).1
  have hval : ∀ n, ∫ x, f n x ∂μ = formula (z n) := fun n =>
    integral_inv_mul_exp_massExponent hσ ht hint hmass (hz0 n)
  have hfnn : ∀ n, 0 ≤ᵐ[μ] f n := fun n => by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx : 0 < x := hx
    exact mul_nonneg (mul_nonneg (inv_nonneg.2 hx.le) (hnn x hx)) (Real.exp_pos _).le
  -- limit of the closed form
  have hzt : Tendsto z atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hw : Tendsto (fun n => σ * z n / 2) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · simpa using (hzt.const_mul σ).div_const 2
    · exact (by have := hzpos n; positivity : (0 : ℝ) < σ * z n / 2).ne'
  have hslope := (hasDerivAt_iff_tendsto_slope_zero.1 (Real.hasDerivAt_sinh 0)).comp hw
  simp only [Real.cosh_zero, zero_add, Real.sinh_zero, sub_zero, smul_eq_mul] at hslope
  have hinv := hslope.inv₀ one_ne_zero
  have hE : Tendsto (fun n => Real.exp (-z n ^ 2 / (2 * t))) atTop (𝓝 1) := by
    have : Continuous fun z : ℝ => Real.exp (-z ^ 2 / (2 * t)) := by fun_prop
    have h : Tendsto (fun n => Real.exp (-z n ^ 2 / (2 * t))) atTop
        (𝓝 (Real.exp (-(0 : ℝ) ^ 2 / (2 * t)))) := (this.tendsto 0).comp hzt
    rwa [show Real.exp (-(0 : ℝ) ^ 2 / (2 * t)) = 1 by simp] at h
  have hlim : Tendsto (fun n => formula (z n)) atTop (𝓝 (1 / t)) := by
    have h := (hE.const_mul (1 / t)).mul hinv
    simp only [mul_one, inv_one] at h
    refine h.congr fun n => ?_
    have hsinh : Real.sinh (σ * z n / 2) ≠ 0 := by
      rw [Ne, Real.sinh_eq_zero]; have := hzpos n; positivity
    have hσ0 : σ ≠ 0 := hσ.ne'
    simp only [Function.comp_apply, formula]
    field_simp
  -- monotone convergence in `ℝ≥0∞`
  have ha_tend : Tendsto a atTop (𝓝 0) := by
    have hc : Continuous (massExponent σ) := by unfold massExponent; fun_prop
    have h := (hc.tendsto 0).comp hzt
    have h1 : massExponent σ 0 = 0 := by simp [massExponent]
    rw [h1] at h; exact h
  have hmono : ∀ᵐ x ∂μ, Monotone fun n => ENNReal.ofReal (f n x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx n m hnm
    have hx : 0 < x := hx
    refine ENNReal.ofReal_le_ofReal ?_
    have hzle : z m ≤ z n := by
      simp only [z]
      gcongr
    have hale : a m ≤ a n := by
      simp only [a, massExponent]
      have : Real.cosh (σ * z m / 2) ≤ Real.cosh (σ * z n / 2) := by
        rw [Real.cosh_le_cosh, abs_of_pos (by have := hzpos m; positivity),
          abs_of_pos (by have := hzpos n; positivity)]
        gcongr
      have h4 : (0 : ℝ) ≤ 4 / σ ^ 2 := by positivity
      nlinarith
    have hexp : Real.exp (-a n / x) ≤ Real.exp (-a m / x) := by
      gcongr
    exact mul_le_mul_of_nonneg_left hexp (mul_nonneg (inv_nonneg.2 hx.le) (hnn x hx))
  have htend : ∀ᵐ x ∂μ, Tendsto (fun n => ENNReal.ofReal (f n x)) atTop
      (𝓝 (ENNReal.ofReal (x⁻¹ * φ0 x))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    refine ENNReal.tendsto_ofReal ?_
    have : Tendsto (fun n => Real.exp (-a n / x)) atTop (𝓝 1) := by
      have hc : Continuous fun b : ℝ => Real.exp (-b / x) := by fun_prop
      have h : Tendsto (fun n => Real.exp (-a n / x)) atTop
          (𝓝 (Real.exp (-(0 : ℝ) / x))) := (hc.tendsto 0).comp ha_tend
      rwa [show Real.exp (-(0 : ℝ) / x) = 1 by simp] at h
    simpa using this.const_mul (x⁻¹ * φ0 x)
  have hmeas : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (f n x)) μ := fun n =>
    (hfint n).aemeasurable.ennreal_ofReal
  have hL := lintegral_tendsto_of_tendsto_of_monotone hmeas hmono htend
  have hL' : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (f n x) ∂μ) atTop
      (𝓝 (ENNReal.ofReal (1 / t))) := by
    refine (ENNReal.tendsto_ofReal hlim).congr fun n => ?_
    rw [← hval n, ofReal_integral_eq_lintegral_ofReal (hfint n) (hfnn n)]
  have huniq := tendsto_nhds_unique hL hL'
  have hFnn : 0 ≤ᵐ[μ] fun x => x⁻¹ * φ0 x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx : 0 < x := hx
    exact mul_nonneg (inv_nonneg.2 hx.le) (hnn x hx)
  have hFm : AEStronglyMeasurable (fun x => x⁻¹ * φ0 x) μ :=
    measurable_inv.aestronglyMeasurable.mul hint.aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae hFnn hFm, huniq,
    ENNReal.toReal_ofReal (by have := ht.le; positivity)]

end MassToMoments

end Lyasoff2016
