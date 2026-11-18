/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Evaluation of the `1/x`-Laplace transform of Yor's density via a Cauchy rectangle contour
and identification of `IsJointDensity P W 2 0 t (yorDensity t)` without classical axioms.
-/
module

public import Lyasoff2016.JointLawLaplaceInv
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real Interval

noncomputable section
namespace Lyasoff2016

section ContourIntegral

private lemma cosh_re_im (x y : ℝ) :
    (Complex.cosh (x + y * I)).re = Real.cosh x * Real.cos y ∧
    (Complex.cosh (x + y * I)).im = Real.sinh x * Real.sin y := by
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  simp [← Complex.ofReal_cosh, ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

private lemma sinh_re_im (x y : ℝ) :
    (Complex.sinh (x + y * I)).re = Real.sinh x * Real.cos y ∧
    (Complex.sinh (x + y * I)).im = Real.cosh x * Real.sin y := by
  rw [Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  simp [← Complex.ofReal_cosh, ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

private lemma norm_cosh_ge_abs_sinh (x y : ℝ) :
    |Real.sinh x| ≤ ‖Complex.cosh (x + y * I)‖ := by
  obtain ⟨hre, him⟩ := cosh_re_im x y
  rw [← Real.sqrt_sq_eq_abs (Real.sinh x), Complex.norm_def, Complex.normSq_apply, hre, him]
  apply Real.sqrt_le_sqrt
  have h1 : Real.sinh x ^ 2 * Real.sin y ^ 2 + Real.cosh x ^ 2 * Real.cos y ^ 2 =
      Real.sinh x ^ 2 + Real.cos y ^ 2 := by
    have hsc : Real.cosh x ^ 2 - Real.sinh x ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq x
    have hcs : Real.sin y ^ 2 + Real.cos y ^ 2 = 1 := Real.sin_sq_add_cos_sq y
    nlinarith
  nlinarith [sq_nonneg (Real.cos y)]

private lemma norm_sinh_le_cosh (x y : ℝ) :
    ‖Complex.sinh (x + y * I)‖ ≤ Real.cosh x := by
  obtain ⟨hre, him⟩ := sinh_re_im x y
  rw [← Real.sqrt_sq (Real.cosh_pos x).le, Complex.norm_def, Complex.normSq_apply, hre, him]
  apply Real.sqrt_le_sqrt
  have h1 : Real.sinh x ^ 2 * Real.cos y ^ 2 + Real.cosh x ^ 2 * Real.sin y ^ 2 ≤
      Real.cosh x ^ 2 := by
    have hsc : Real.cosh x ^ 2 - Real.sinh x ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq x
    have hcs : Real.sin y ^ 2 + Real.cos y ^ 2 = 1 := Real.sin_sq_add_cos_sq y
    nlinarith
  linarith

private lemma cosh_eq_cosh_real_strip_iff {α : ℝ} (hα : 0 < α) {z : ℂ}
    (hz : |z.im| ≤ Real.pi) (heq : Complex.cosh z = Complex.cosh (α : ℂ)) :
    z = (α : ℂ) ∨ z = -(α : ℂ) := by
  have hz_eq : z = z.re + z.im * I := (Complex.re_add_im z).symm
  rw [hz_eq] at heq ⊢
  obtain ⟨hre, him⟩ := cosh_re_im z.re z.im
  have hre' : Real.cosh z.re * Real.cos z.im = Real.cosh α := by
    have := congr_arg Complex.re heq
    rw [hre, ← Complex.ofReal_cosh, Complex.ofReal_re] at this
    exact this
  have him' : Real.sinh z.re * Real.sin z.im = 0 := by
    have := congr_arg Complex.im heq
    rw [him, ← Complex.ofReal_cosh, Complex.ofReal_im] at this
    exact this
  have h1_lt : 1 < Real.cosh α := by
    rw [← Real.cosh_zero]
    exact Real.cosh_lt_cosh.mpr (by rw [abs_zero, abs_of_pos hα]; exact hα)
  rcases mul_eq_zero.mp him' with hsinh | hsin
  · have hzr : z.re = 0 := Real.sinh_eq_zero.mp hsinh
    rw [hzr, Real.cosh_zero, one_mul] at hre'
    linarith [Real.cos_le_one z.im]
  · have hsin_cases : z.im = 0 ∨ z.im = Real.pi ∨ z.im = -Real.pi := by
      rw [Real.sin_eq_zero_iff] at hsin
      obtain ⟨k, hk⟩ := hsin
      have hk1 : |(k : ℝ)| ≤ 1 := by
        have hpi : 0 < Real.pi := Real.pi_pos
        rw [← hk, abs_mul, abs_of_pos hpi] at hz
        exact (mul_le_iff_le_one_left hpi).mp hz
      have hk1' : -1 ≤ k ∧ k ≤ 1 := by
        rcases abs_le.mp hk1 with ⟨h1, h2⟩
        exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
      have hk' : k = 0 ∨ k = 1 ∨ k = -1 := by omega
      rcases hk' with rfl | rfl | rfl
      · left; simp [← hk]
      · right; left; simp [← hk]
      · right; right; simp [← hk]
    rcases hsin_cases with him0 | himpi | himnpi
    · rw [him0, Real.cos_zero, mul_one] at hre'
      have habs : |z.re| = α := by
        rw [← Real.cosh_abs z.re] at hre'
        exact Real.cosh_strictMonoOn.injOn (abs_nonneg z.re) hα.le hre'
      rcases abs_eq hα.le |>.mp habs with h | h
      · left; simp [h, him0]
      · right; simp [h, him0]
    · rw [himpi, Real.cos_pi, mul_neg_one] at hre'
      linarith [Real.one_le_cosh z.re]
    · rw [himnpi, Real.cos_neg, Real.cos_pi, mul_neg_one] at hre'
      linarith [Real.one_le_cosh z.re]

private lemma log_neg_of_im_pos {w : ℂ} (hw : 0 < w.im) :
    Complex.log (-w) = Complex.log w - Real.pi * I := by
  simp only [Complex.log, norm_neg, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hw]
  push_cast
  ring

private lemma log_neg_of_im_neg {w : ℂ} (hw : w.im < 0) :
    Complex.log (-w) = Complex.log w + Real.pi * I := by
  simp only [Complex.log, norm_neg, Complex.arg_neg_eq_arg_add_pi_of_im_neg hw]
  push_cast
  ring

private lemma integral_boundary_rect_sub_inv_eq {c R : ℝ} (hcR : |c| < R) :
    ((∫ x : ℝ in (-R)..R, (↑x + (-Real.pi) * I - (c : ℂ))⁻¹) -
      ∫ x : ℝ in (-R)..R, (↑x + Real.pi * I - (c : ℂ))⁻¹) +
    I • ((∫ y : ℝ in (-Real.pi)..Real.pi, ((R : ℂ) + ↑y * I - (c : ℂ))⁻¹) -
      ∫ y : ℝ in (-Real.pi)..Real.pi, ((-R : ℂ) + ↑y * I - (c : ℂ))⁻¹) =
    2 * Real.pi * I := by
  have hRc_pos : 0 < R - c := by linarith [le_abs_self c]
  have hRc_neg_pos : 0 < R + c := by linarith [neg_le_abs c]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  let z₁ : ℂ := (R - c : ℝ) + Real.pi * I
  let z₂ : ℂ := (R - c : ℝ) + (-Real.pi) * I
  let w₁ : ℂ := (R + c : ℝ) + Real.pi * I
  let w₂ : ℂ := (R + c : ℝ) + (-Real.pi) * I
  have h_bot : ∫ x : ℝ in (-R)..R, (↑x + (-Real.pi) * I - (c : ℂ))⁻¹ =
      Complex.log z₂ - Complex.log (-w₁) := by
    have hcont : Continuous (fun x : ℝ => (↑x + (-Real.pi) * I - (c : ℂ))⁻¹) := by
      refine Continuous.inv₀ (by fun_prop) fun x heq => ?_
      have := congr_arg Complex.im heq
      simp at this
    have hd : ∀ x ∈ uIcc (-R) R, HasDerivAt (fun x' : ℝ => Complex.log (↑x' + (-Real.pi) * I - (c : ℂ)))
        (↑x + (-Real.pi) * I - (c : ℂ))⁻¹ x := by
      intro x _
      have hslit : (↑x + (-Real.pi) * I - (c : ℂ)) ∈ Complex.slitPlane := by
        right; simp [hpi.ne']
      have hlin : HasDerivAt (fun x' : ℝ => (↑x' + (-Real.pi) * I - (c : ℂ))) 1 x := by
        have h1 : HasDerivAt (fun x' : ℝ => (x' : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
        simpa using (h1.add_const ((-Real.pi) * I)).sub_const (c : ℂ)
      have hcomp := (Complex.hasDerivAt_log hslit).scomp x hlin
      exact hcomp.congr_deriv (by ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _)]
    congr 2
    · simp only [z₂]; push_cast; ring
    · simp only [w₁]; push_cast; ring
  have h_top : ∫ x : ℝ in (-R)..R, (↑x + Real.pi * I - (c : ℂ))⁻¹ =
      Complex.log z₁ - Complex.log (-w₂) := by
    have hcont : Continuous (fun x : ℝ => (↑x + Real.pi * I - (c : ℂ))⁻¹) := by
      refine Continuous.inv₀ (by fun_prop) fun x heq => ?_
      have := congr_arg Complex.im heq
      simp at this
    have hd : ∀ x ∈ uIcc (-R) R, HasDerivAt (fun x' : ℝ => Complex.log (↑x' + Real.pi * I - (c : ℂ)))
        (↑x + Real.pi * I - (c : ℂ))⁻¹ x := by
      intro x _
      have hslit : (↑x + Real.pi * I - (c : ℂ)) ∈ Complex.slitPlane := by
        right; simp [hpi.ne']
      have hlin : HasDerivAt (fun x' : ℝ => (↑x' + Real.pi * I - (c : ℂ))) 1 x := by
        have h1 : HasDerivAt (fun x' : ℝ => (x' : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
        simpa using (h1.add_const (Real.pi * I)).sub_const (c : ℂ)
      have hcomp := (Complex.hasDerivAt_log hslit).scomp x hlin
      exact hcomp.congr_deriv (by ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _)]
    congr 2
    · simp only [z₁]; push_cast; ring
    · simp only [w₂]; push_cast; ring
  have h_right : I * ∫ y : ℝ in (-Real.pi)..Real.pi, ((R : ℂ) + ↑y * I - (c : ℂ))⁻¹ =
      Complex.log z₁ - Complex.log z₂ := by
    have hcont : Continuous (fun y : ℝ => ((R : ℂ) + ↑y * I - (c : ℂ))⁻¹) := by
      refine Continuous.inv₀ (by fun_prop) fun y heq => ?_
      have := congr_arg Complex.re heq
      simp at this; linarith
    have hd : ∀ y ∈ uIcc (-Real.pi) Real.pi,
        HasDerivAt (fun y' : ℝ => Complex.log ((R : ℂ) + ↑y' * I - (c : ℂ)))
          (I * ((R : ℂ) + ↑y * I - (c : ℂ))⁻¹) y := by
      intro y _
      have hslit : ((R : ℂ) + ↑y * I - (c : ℂ)) ∈ Complex.slitPlane := by
        left; simp; linarith
      have hlin : HasDerivAt (fun y' : ℝ => (R : ℂ) + ↑y' * I - (c : ℂ)) I y := by
        have h1 : HasDerivAt (fun y' : ℝ => (y' : ℂ)) 1 y := Complex.ofRealCLM.hasDerivAt
        simpa using ((h1.mul_const I).const_add (R : ℂ)).sub_const (c : ℂ)
      have hcomp := (Complex.hasDerivAt_log hslit).scomp y hlin
      exact hcomp.congr_deriv (by ring)
    have hint' := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((continuous_const.mul hcont).intervalIntegrable _ _)
    rw [intervalIntegral.integral_const_mul] at hint'
    rw [hint']
    congr 1
    · simp only [z₁]; push_cast; ring_nf
    · simp only [z₂]; push_cast; ring_nf
  have h_left : I * ∫ y : ℝ in (-Real.pi)..Real.pi, ((-R : ℂ) + ↑y * I - (c : ℂ))⁻¹ =
      Complex.log w₂ - Complex.log w₁ := by
    have hcont : Continuous (fun y : ℝ => ((-R : ℂ) + ↑y * I - (c : ℂ))⁻¹) := by
      refine Continuous.inv₀ (by fun_prop) fun y heq => ?_
      have := congr_arg Complex.re heq
      simp at this; linarith
    have hd : ∀ y ∈ uIcc (-Real.pi) Real.pi,
        HasDerivAt (fun y' : ℝ => Complex.log ((R + c : ℝ) - ↑y' * I))
          (I * ((-R : ℂ) + ↑y * I - (c : ℂ))⁻¹) y := by
      intro y _
      have hslit : ((R + c : ℝ) - ↑y * I) ∈ Complex.slitPlane := by
        left; simp; linarith
      have hlin : HasDerivAt (fun y' : ℝ => (R + c : ℝ) - ↑y' * I) (-I) y := by
        have h1 : HasDerivAt (fun y' : ℝ => (y' : ℂ)) 1 y := Complex.ofRealCLM.hasDerivAt
        simpa using (h1.mul_const I).const_sub ((R + c : ℝ) : ℂ)
      have hcomp := (Complex.hasDerivAt_log hslit).scomp y hlin
      refine hcomp.congr_deriv ?_
      have hneg : -((R + c : ℝ) - ↑y * I) = (-R : ℂ) + ↑y * I - (c : ℂ) := by push_cast; ring
      rw [← hneg]
      simp only [inv_neg, mul_neg]
      ring
    have hint' := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((continuous_const.mul hcont).intervalIntegrable _ _)
    rw [intervalIntegral.integral_const_mul] at hint'
    rw [hint']
    congr 1
    · simp only [w₂]; push_cast; ring_nf
    · simp only [w₁]; push_cast; ring_nf
  rw [smul_eq_mul, mul_sub, h_bot, h_top, h_right, h_left]
  have hw1_im : 0 < w₁.im := by simp [w₁]; exact hpi
  have hw2_im : w₂.im < 0 := by simp [w₂]; exact hpi
  rw [log_neg_of_im_pos hw1_im, log_neg_of_im_neg hw2_im]
  ring

/-- Hartman–Watson / Yor contour integral identity: for `t > 0` and `α > 0`,
`e^{π²/(2t)} ∫₀^∞ e^{-u²/(2t)} sinh u * sin(π u / t) / (cosh u + cosh α) du = π e^{-α²/(2t)}`. -/
theorem hartman_watson_contour {t α : ℝ} (ht : 0 < t) (hα : 0 < α) :
    Real.exp (Real.pi ^ 2 / (2 * t)) *
      ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * t)) *
        (Real.sinh u * Real.sin (Real.pi * u / t) / (Real.cosh u + Real.cosh α)) =
      Real.pi * Real.exp (-α ^ 2 / (2 * t)) := by
  let f : ℂ → ℂ := fun z => Complex.exp (-z ^ 2 / (2 * (t : ℂ)))
  let H : ℂ → ℂ := fun z => f z * Complex.sinh z / (Complex.cosh z - Complex.cosh (α : ℂ))
  let P_pole : ℂ → ℂ := fun z => f (α : ℂ) * ((z - (α : ℂ))⁻¹ + (z + (α : ℂ))⁻¹)
  let q₁ : ℂ → ℂ := dslope Complex.cosh (α : ℂ)
  let q : ℂ → ℂ := dslope q₁ (-(α : ℂ))
  let num : ℂ → ℂ := fun z => f z * Complex.sinh z - f (α : ℂ) * (2 * z) * q z
  let num₁ : ℂ → ℂ := dslope (dslope num (α : ℂ)) (-(α : ℂ))
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hα0 : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα.ne'
  have hα_ne : (-(α : ℂ)) ≠ (α : ℂ) := by
    intro h
    have : -α = α := by exact_mod_cast h
    linarith
  have hf_an : ∀ z, AnalyticAt ℂ f z := fun z => by unfold f; fun_prop
  have hq1_an : ∀ z, AnalyticAt ℂ q₁ z := fun z => analyticAt_cosh.dslope (α : ℂ)
  have hq_an : ∀ z, AnalyticAt ℂ q z := fun z => (hq1_an z).dslope (-(α : ℂ))
  have hnum_an : ∀ z, AnalyticAt ℂ num z := fun z => by
    unfold num
    exact ((hf_an z).mul analyticAt_sinh).sub
      ((analyticAt_const.mul (analyticAt_const.mul analyticAt_id)).mul (hq_an z))
  have hnum1_an : ∀ z, AnalyticAt ℂ num₁ z := fun z =>
    ((hnum_an z).dslope (α : ℂ)).dslope (-(α : ℂ))
  have hq1_neg : q₁ (-(α : ℂ)) = 0 := by
    simp only [q₁, dslope_of_ne _ hα_ne, slope_def_field, Complex.cosh_neg, sub_self, zero_div]
  have hq_at_pos : q (α : ℂ) = Complex.sinh (α : ℂ) / (2 * (α : ℂ)) := by
    have hq1_pos : q₁ (α : ℂ) = Complex.sinh (α : ℂ) := by
      simp only [q₁, dslope_same, Complex.deriv_cosh]
    have hq_eq : q (α : ℂ) = (q₁ (α : ℂ) - q₁ (-(α : ℂ))) / ((α : ℂ) - (-(α : ℂ))) :=
      (dslope_of_ne q₁ hα_ne.symm).trans (slope_def_field q₁ _ _)
    rw [hq_eq, hq1_pos, hq1_neg, sub_zero, sub_neg_eq_add]
    ring
  have hq_at_neg : q (-(α : ℂ)) = Complex.sinh (α : ℂ) / (2 * (α : ℂ)) := by
    have h_eq : q (-(α : ℂ)) = deriv q₁ (-(α : ℂ)) := dslope_same q₁ (-(α : ℂ))
    have hd : HasDerivAt q₁ (Complex.sinh (α : ℂ) / (2 * (α : ℂ))) (-(α : ℂ)) := by
      have h_ev : q₁ =ᶠ[𝓝 (-(α : ℂ))] fun z => (Complex.cosh z - Complex.cosh (α : ℂ)) / (z - (α : ℂ)) :=
        (dslope_eventuallyEq_slope_of_ne Complex.cosh hα_ne).mono fun z hz => by
          simpa [slope_def_field] using hz
      refine HasDerivAt.congr_of_eventuallyEq ?_ h_ev
      have h1 : HasDerivAt (fun z => Complex.cosh z - Complex.cosh (α : ℂ))
          (Complex.sinh (-(α : ℂ))) (-(α : ℂ)) :=
        (Complex.hasDerivAt_cosh (-(α : ℂ))).sub_const (Complex.cosh (α : ℂ))
      have h2 : HasDerivAt (fun z => z - (α : ℂ)) 1 (-(α : ℂ)) := (hasDerivAt_id _).sub_const _
      have hdiv := h1.div h2 (sub_ne_zero.mpr hα_ne)
      refine hdiv.congr_deriv ?_
      rw [Complex.cosh_neg, sub_self, Complex.sinh_neg]
      field_simp [hα0]; ring
    rw [h_eq, hd.deriv]
  have hsinh_ne : Complex.sinh (α : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sinh]
    exact Complex.ofReal_ne_zero.mpr (Real.sinh_ne_zero.mpr hα.ne')
  have hq_ne_strip : ∀ z : ℂ, |z.im| ≤ Real.pi → q z ≠ 0 := by
    intro z hz hqz
    by_cases hz1 : z = (α : ℂ)
    · rw [hz1, hq_at_pos] at hqz
      exact hsinh_ne ((div_eq_zero_iff.mp hqz).resolve_right (mul_ne_zero two_ne_zero hα0))
    · by_cases hz2 : z = -(α : ℂ)
      · rw [hz2, hq_at_neg] at hqz
        exact hsinh_ne ((div_eq_zero_iff.mp hqz).resolve_right (mul_ne_zero two_ne_zero hα0))
      · have hq_eq : q z = (Complex.cosh z - Complex.cosh (α : ℂ)) / ((z - (α : ℂ)) * (z + (α : ℂ))) := by
          have h1 : q z = (q₁ z - q₁ (-(α : ℂ))) / (z - (-(α : ℂ))) :=
            (dslope_of_ne q₁ hz2).trans (slope_def_field q₁ _ _)
          have h2 : q₁ z = (Complex.cosh z - Complex.cosh (α : ℂ)) / (z - (α : ℂ)) :=
            (dslope_of_ne Complex.cosh hz1).trans (slope_def_field Complex.cosh _ _)
          rw [h1, hq1_neg, sub_zero, h2, sub_neg_eq_add, div_div]
        rw [hq_eq, div_eq_zero_iff, sub_eq_zero] at hqz
        rcases hqz with hcosh | hden
        · rcases cosh_eq_cosh_real_strip_iff hα hz hcosh with rfl | rfl
          · exact hz1 rfl
          · exact hz2 rfl
        · rcases mul_eq_zero.mp hden with h | h
          · exact hz1 (sub_eq_zero.mp h)
          · exact hz2 (add_eq_zero_iff_eq_neg.mp h)
  have hnum_pos : num (α : ℂ) = 0 := by
    simp only [num, hq_at_pos]
    field_simp [hα0]; ring
  have hnum_neg : num (-(α : ℂ)) = 0 := by
    have hf_neg : f (-(α : ℂ)) = f (α : ℂ) := by simp [f]
    simp only [num, hf_neg, Complex.sinh_neg, hq_at_neg]
    field_simp [hα0]; ring
  have hG_eq : ∀ z : ℂ, z ≠ (α : ℂ) → z ≠ -(α : ℂ) → Complex.cosh z ≠ Complex.cosh (α : ℂ) →
      num₁ z / q z = H z - P_pole z := by
    intro z hz1 hz2 hcosh
    have hq1z : q₁ z = (Complex.cosh z - Complex.cosh (α : ℂ)) / (z - (α : ℂ)) :=
      (dslope_of_ne Complex.cosh hz1).trans (slope_def_field Complex.cosh _ _)
    have hqz : q z = (Complex.cosh z - Complex.cosh (α : ℂ)) / ((z - (α : ℂ)) * (z + (α : ℂ))) := by
      have h1 : q z = (q₁ z - q₁ (-(α : ℂ))) / (z - (-(α : ℂ))) :=
        (dslope_of_ne q₁ hz2).trans (slope_def_field q₁ _ _)
      rw [h1, hq1_neg, sub_zero, hq1z, sub_neg_eq_add, div_div]
    have hd1 : dslope num (α : ℂ) (-(α : ℂ)) = 0 := by
      have h1 : dslope num (α : ℂ) (-(α : ℂ)) = (num (-(α : ℂ)) - num (α : ℂ)) / (-(α : ℂ) - (α : ℂ)) :=
        (dslope_of_ne num hα_ne).trans (slope_def_field num _ _)
      rw [h1, hnum_neg, hnum_pos, sub_self, zero_div]
    have hnum1z : num₁ z = num z / ((z - (α : ℂ)) * (z + (α : ℂ))) := by
      have h1 : num₁ z = (dslope num (α : ℂ) z - dslope num (α : ℂ) (-(α : ℂ))) / (z - (-(α : ℂ))) :=
        (dslope_of_ne (dslope num (α : ℂ)) hz2).trans (slope_def_field _ _ _)
      have h2 : dslope num (α : ℂ) z = (num z - num (α : ℂ)) / (z - (α : ℂ)) :=
        (dslope_of_ne num hz1).trans (slope_def_field num _ _)
      rw [h1, hd1, sub_zero, h2, hnum_pos, sub_zero, sub_neg_eq_add, div_div]
    have hz1' : z - (α : ℂ) ≠ 0 := sub_ne_zero.mpr hz1
    have hz2' : z + (α : ℂ) ≠ 0 := fun h => hz2 (add_eq_zero_iff_eq_neg.mp h)
    have hcosh' : Complex.cosh z - Complex.cosh (α : ℂ) ≠ 0 := sub_ne_zero.mpr hcosh
    rw [hnum1z, hqz]
    dsimp only [num, H, P_pole]
    rw [hqz]
    field_simp [hz1', hz2', hcosh']
    ring
  have h_bdry : ∀ R > α + 1, ∀ z : ℂ, |z.im| ≤ Real.pi →
      (z.im = Real.pi ∨ z.im = -Real.pi ∨ |z.re| = R) →
      z ≠ (α : ℂ) ∧ z ≠ -(α : ℂ) ∧ Complex.cosh z ≠ Complex.cosh (α : ℂ) := by
    intro R hR z hzim hbd
    have hz_ne1 : z ≠ (α : ℂ) := by
      intro h; rw [h] at hbd
      simp only [Complex.ofReal_im, Complex.ofReal_re] at hbd
      rcases hbd with h1 | h1 | h1
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
      · rw [abs_of_pos hα] at h1; linarith
    have hz_ne2 : z ≠ -(α : ℂ) := by
      intro h; rw [h] at hbd
      simp only [Complex.neg_im, Complex.ofReal_im, neg_zero, Complex.neg_re, Complex.ofReal_re, abs_neg] at hbd
      rcases hbd with h1 | h1 | h1
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
      · rw [abs_of_pos hα] at h1; linarith
    have hcosh_ne : Complex.cosh z ≠ Complex.cosh (α : ℂ) := by
      intro hcosh
      rcases cosh_eq_cosh_real_strip_iff hα hzim hcosh with h | h
      · exact hz_ne1 h
      · exact hz_ne2 h
    exact ⟨hz_ne1, hz_ne2, hcosh_ne⟩
  have h_rect : ∀ R > α + 1,
      ((∫ x : ℝ in (-R)..R, H (↑x + (-Real.pi) * I)) - ∫ x : ℝ in (-R)..R, H (↑x + Real.pi * I)) +
      I • ((∫ y : ℝ in (-Real.pi)..Real.pi, H ((R : ℂ) + ↑y * I)) -
        ∫ y : ℝ in (-Real.pi)..Real.pi, H ((-R : ℂ) + ↑y * I)) =
      4 * Real.pi * I * f (α : ℂ) := by
    intro R hR
    have hR0 : 0 < R := by linarith
    have hDiff : DifferentiableOn ℂ (fun z => num₁ z / q z)
        ([[((-R : ℝ) + (-Real.pi) * I).re, ((R : ℝ) + Real.pi * I).re]] ×ℂ
          [[((-R : ℝ) + (-Real.pi) * I).im, ((R : ℝ) + Real.pi * I).im]]) := by
      intro z hz
      have hzim : |z.im| ≤ Real.pi := by
        have him := hz.2
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          mul_zero, mul_one, add_zero, zero_add, Complex.neg_im] at him
        exact abs_le.mpr (by simpa [uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)] using him)
      exact ((hnum1_an z).differentiableAt.div (hq_an z).differentiableAt (hq_ne_strip z hzim)).differentiableWithinAt
    have hCG := integral_boundary_rect_eq_zero_of_differentiableOn (fun z => num₁ z / q z)
      ((-R : ℝ) + (-Real.pi) * I) ((R : ℝ) + Real.pi * I) hDiff
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, add_zero, Complex.add_im, Complex.ofReal_im, mul_one, zero_add,
      Complex.neg_im, Complex.neg_re, Complex.ofReal_neg, neg_zero, sub_self] at hCG
    rw [show ((-Real.pi : ℂ) * I).im = -Real.pi by simp,
      show ((Real.pi : ℂ) * I).im = Real.pi by simp] at hCG
    simp only [Complex.ofReal_neg] at hCG
    have h_seg_bot : ∫ x : ℝ in (-R)..R, num₁ (↑x + (-Real.pi) * I) / q (↑x + (-Real.pi) * I) =
        (∫ x : ℝ in (-R)..R, H (↑x + (-Real.pi) * I)) -
          ∫ x : ℝ in (-R)..R, P_pole (↑x + (-Real.pi) * I) := by
      have him_eq : ∀ x : ℝ, |(↑x + (-Real.pi : ℂ) * I).im| ≤ Real.pi := fun x => by
        simp [abs_of_pos Real.pi_pos]
      have hcongr : ∀ x : ℝ, num₁ (↑x + (-Real.pi) * I) / q (↑x + (-Real.pi) * I) =
          H (↑x + (-Real.pi) * I) - P_pole (↑x + (-Real.pi) * I) := fun x => by
        obtain ⟨h1, h2, h3⟩ := h_bdry R hR _ (him_eq x) (Or.inr (Or.inl (by simp)))
        exact hG_eq _ h1 h2 h3
      simp_rw [hcongr]
      have hH_c : Continuous (fun x : ℝ => H (↑x + (-Real.pi) * I)) := by
        refine Continuous.div (by unfold f; fun_prop) (by fun_prop) fun x => ?_
        exact sub_ne_zero.mpr (h_bdry R hR _ (him_eq x) (Or.inr (Or.inl (by simp)))).2.2
      have hP_c : Continuous (fun x : ℝ => P_pole (↑x + (-Real.pi) * I)) := by
        refine continuous_const.mul (Continuous.add ?_ ?_)
        · refine Continuous.inv₀ (by fun_prop) fun x => ?_
          exact sub_ne_zero.mpr (h_bdry R hR _ (him_eq x) (Or.inr (Or.inl (by simp)))).1
        · refine Continuous.inv₀ (by fun_prop) fun x h => ?_
          exact (h_bdry R hR _ (him_eq x) (Or.inr (Or.inl (by simp)))).2.1 (add_eq_zero_iff_eq_neg.mp h)
      exact intervalIntegral.integral_sub (hH_c.intervalIntegrable _ _) (hP_c.intervalIntegrable _ _)
    have h_seg_top : ∫ x : ℝ in (-R)..R, num₁ (↑x + Real.pi * I) / q (↑x + Real.pi * I) =
        (∫ x : ℝ in (-R)..R, H (↑x + Real.pi * I)) -
          ∫ x : ℝ in (-R)..R, P_pole (↑x + Real.pi * I) := by
      have him_eq : ∀ x : ℝ, |(↑x + (Real.pi : ℂ) * I).im| ≤ Real.pi := fun x => by
        simp [abs_of_pos Real.pi_pos]
      have hcongr : ∀ x : ℝ, num₁ (↑x + Real.pi * I) / q (↑x + Real.pi * I) =
          H (↑x + Real.pi * I) - P_pole (↑x + Real.pi * I) := fun x => by
        obtain ⟨h1, h2, h3⟩ := h_bdry R hR _ (him_eq x) (Or.inl (by simp))
        exact hG_eq _ h1 h2 h3
      simp_rw [hcongr]
      have hH_c : Continuous (fun x : ℝ => H (↑x + Real.pi * I)) := by
        refine Continuous.div (by unfold f; fun_prop) (by fun_prop) fun x => ?_
        exact sub_ne_zero.mpr (h_bdry R hR _ (him_eq x) (Or.inl (by simp))).2.2
      have hP_c : Continuous (fun x : ℝ => P_pole (↑x + Real.pi * I)) := by
        refine continuous_const.mul (Continuous.add ?_ ?_)
        · refine Continuous.inv₀ (by fun_prop) fun x => ?_
          exact sub_ne_zero.mpr (h_bdry R hR _ (him_eq x) (Or.inl (by simp))).1
        · refine Continuous.inv₀ (by fun_prop) fun x h => ?_
          exact (h_bdry R hR _ (him_eq x) (Or.inl (by simp))).2.1 (add_eq_zero_iff_eq_neg.mp h)
      exact intervalIntegral.integral_sub (hH_c.intervalIntegrable _ _) (hP_c.intervalIntegrable _ _)
    have h_seg_right : ∫ y : ℝ in (-Real.pi)..Real.pi, num₁ ((R : ℂ) + ↑y * I) / q ((R : ℂ) + ↑y * I) =
        (∫ y : ℝ in (-Real.pi)..Real.pi, H ((R : ℂ) + ↑y * I)) -
          ∫ y : ℝ in (-Real.pi)..Real.pi, P_pole ((R : ℂ) + ↑y * I) := by
      have hcongr : ∀ y ∈ uIcc (-Real.pi) Real.pi,
          num₁ ((R : ℂ) + ↑y * I) / q ((R : ℂ) + ↑y * I) =
            H ((R : ℂ) + ↑y * I) - P_pole ((R : ℂ) + ↑y * I) := fun y hy => by
        have hy_abs : |y| ≤ Real.pi := by
          simpa [uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi), abs_le] using hy
        obtain ⟨h1, h2, h3⟩ := h_bdry R hR ((R : ℂ) + ↑y * I) (by simpa using hy_abs)
          (Or.inr (Or.inr (by simp [abs_of_pos hR0])))
        exact hG_eq _ h1 h2 h3
      rw [intervalIntegral.integral_congr hcongr]
      have hH_c : ContinuousOn (fun y : ℝ => H ((R : ℂ) + ↑y * I)) (uIcc (-Real.pi) Real.pi) := by
        intro y hy
        have hy_abs : |y| ≤ Real.pi := by
          simpa [uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi), abs_le] using hy
        have hne := (h_bdry R hR ((R : ℂ) + ↑y * I) (by simpa using hy_abs)
          (Or.inr (Or.inr (by simp [abs_of_pos hR0])))).2.2
        exact ((by unfold f; fun_prop : Continuous fun y : ℝ => f ((R : ℂ) + ↑y * I) *
          Complex.sinh ((R : ℂ) + ↑y * I)).continuousAt.div (by fun_prop) (sub_ne_zero.mpr hne)).continuousWithinAt
      have hP_c : ContinuousOn (fun y : ℝ => P_pole ((R : ℂ) + ↑y * I)) (uIcc (-Real.pi) Real.pi) := by
        intro y hy
        have hy_abs : |y| ≤ Real.pi := by
          simpa [uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi), abs_le] using hy
        have hbd := h_bdry R hR ((R : ℂ) + ↑y * I) (by simpa using hy_abs)
          (Or.inr (Or.inr (by simp [abs_of_pos hR0])))
        have h1 : ContinuousAt (fun y : ℝ => ((R : ℂ) + ↑y * I - (α : ℂ))⁻¹) y :=
          (by fun_prop : ContinuousAt _ y).inv₀ (sub_ne_zero.mpr hbd.1)
        have h2 : ContinuousAt (fun y : ℝ => ((R : ℂ) + ↑y * I + (α : ℂ))⁻¹) y :=
          (by fun_prop : ContinuousAt _ y).inv₀ (fun h => hbd.2.1 (add_eq_zero_iff_eq_neg.mp h))
        exact (continuousAt_const.mul (h1.add h2)).continuousWithinAt
      exact intervalIntegral.integral_sub (hH_c.intervalIntegrable) (hP_c.intervalIntegrable)
    have h_seg_left : ∫ y : ℝ in (-Real.pi)..Real.pi, num₁ ((-R : ℂ) + ↑y * I) / q ((-R : ℂ) + ↑y * I) =
        (∫ y : ℝ in (-Real.pi)..Real.pi, H ((-R : ℂ) + ↑y * I)) -
          ∫ y : ℝ in (-Real.pi)..Real.pi, P_pole ((-R : ℂ) + ↑y * I) := by
      have hcongr : ∀ y ∈ uIcc (-Real.pi) Real.pi,
          num₁ ((-R : ℂ) + ↑y * I) / q ((-R : ℂ) + ↑y * I) =
            H ((-R : ℂ) + ↑y * I) - P_pole ((-R : ℂ) + ↑y * I) := fun y hy => by
        have hy_abs : |y| ≤ Real.pi := by
          simpa [uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi), abs_le] using hy
        obtain ⟨h1, h2, h3⟩ := h_bdry R hR ((-R : ℂ) + ↑y * I) (by simpa using hy_abs)
          (Or.inr (Or.inr (by simp [abs_of_pos hR0])))
        exact hG_eq _ h1 h2 h3
      rw [intervalIntegral.integral_congr hcongr]
      have hH_c : ContinuousOn (fun y : ℝ => H ((-R : ℂ) + ↑y * I)) (uIcc (-Real.pi) Real.pi) := by
        intro y hy
        have hy_abs : |y| ≤ Real.pi := by
          simpa [uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi), abs_le] using hy
        have hne := (h_bdry R hR ((-R : ℂ) + ↑y * I) (by simpa using hy_abs)
          (Or.inr (Or.inr (by simp [abs_of_pos hR0])))).2.2
        exact ((by unfold f; fun_prop : Continuous fun y : ℝ => f ((-R : ℂ) + ↑y * I) *
          Complex.sinh ((-R : ℂ) + ↑y * I)).continuousAt.div (by fun_prop) (sub_ne_zero.mpr hne)).continuousWithinAt
      have hP_c : ContinuousOn (fun y : ℝ => P_pole ((-R : ℂ) + ↑y * I)) (uIcc (-Real.pi) Real.pi) := by
        intro y hy
        have hy_abs : |y| ≤ Real.pi := by
          simpa [uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi), abs_le] using hy
        have hbd := h_bdry R hR ((-R : ℂ) + ↑y * I) (by simpa using hy_abs)
          (Or.inr (Or.inr (by simp [abs_of_pos hR0])))
        have h1 : ContinuousAt (fun y : ℝ => ((-R : ℂ) + ↑y * I - (α : ℂ))⁻¹) y :=
          (by fun_prop : ContinuousAt _ y).inv₀ (sub_ne_zero.mpr hbd.1)
        have h2 : ContinuousAt (fun y : ℝ => ((-R : ℂ) + ↑y * I + (α : ℂ))⁻¹) y :=
          (by fun_prop : ContinuousAt _ y).inv₀ (fun h => hbd.2.1 (add_eq_zero_iff_eq_neg.mp h))
        exact (continuousAt_const.mul (h1.add h2)).continuousWithinAt
      exact intervalIntegral.integral_sub (hH_c.intervalIntegrable) (hP_c.intervalIntegrable)
    have hP_split :
        ((∫ x : ℝ in (-R)..R, P_pole (↑x + (-Real.pi) * I)) -
          ∫ x : ℝ in (-R)..R, P_pole (↑x + Real.pi * I)) +
        I • ((∫ y : ℝ in (-Real.pi)..Real.pi, P_pole ((R : ℂ) + ↑y * I)) -
          ∫ y : ℝ in (-Real.pi)..Real.pi, P_pole ((-R : ℂ) + ↑y * I)) =
        4 * Real.pi * I * f (α : ℂ) := by
      have h1 : |α| < R := by rw [abs_of_pos hα]; linarith
      have h2 : |-α| < R := by rw [abs_neg, abs_of_pos hα]; linarith
      have hp1 := integral_boundary_rect_sub_inv_eq h1
      have hp2 := integral_boundary_rect_sub_inv_eq h2
      have h_int_add : ∀ a b : ℝ, ∀ g₁ g₂ : ℝ → ℂ,
          IntervalIntegrable g₁ volume a b → IntervalIntegrable g₂ volume a b →
          (∫ x in a..b, f (α : ℂ) * (g₁ x + g₂ x)) =
            f (α : ℂ) * ((∫ x in a..b, g₁ x) + (∫ x in a..b, g₂ x)) := fun a b g₁ g₂ hg₁ hg₂ => by
        simp_rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hg₁ hg₂]
      have hP_bot : ∫ x : ℝ in (-R)..R, P_pole (↑x + (-Real.pi) * I) =
          f (α : ℂ) * ((∫ x : ℝ in (-R)..R, (↑x + (-Real.pi) * I - (α : ℂ))⁻¹) +
            (∫ x : ℝ in (-R)..R, (↑x + (-Real.pi) * I - (-(α : ℂ)))⁻¹)) := by
        simp only [P_pole, sub_neg_eq_add]
        exact h_int_add _ _ _ _
          ((Continuous.inv₀ (by fun_prop) fun x heq => by
            have := congr_arg Complex.im heq; simp at this).intervalIntegrable _ _)
          ((Continuous.inv₀ (by fun_prop) fun x heq => by
            have := congr_arg Complex.im heq; simp at this).intervalIntegrable _ _)
      have hP_top : ∫ x : ℝ in (-R)..R, P_pole (↑x + Real.pi * I) =
          f (α : ℂ) * ((∫ x : ℝ in (-R)..R, (↑x + Real.pi * I - (α : ℂ))⁻¹) +
            (∫ x : ℝ in (-R)..R, (↑x + Real.pi * I - (-(α : ℂ)))⁻¹)) := by
        simp only [P_pole, sub_neg_eq_add]
        exact h_int_add _ _ _ _
          ((Continuous.inv₀ (by fun_prop) fun x heq => by
            have := congr_arg Complex.im heq; simp at this).intervalIntegrable _ _)
          ((Continuous.inv₀ (by fun_prop) fun x heq => by
            have := congr_arg Complex.im heq; simp at this).intervalIntegrable _ _)
      have hP_right : ∫ y : ℝ in (-Real.pi)..Real.pi, P_pole ((R : ℂ) + ↑y * I) =
          f (α : ℂ) * ((∫ y : ℝ in (-Real.pi)..Real.pi, ((R : ℂ) + ↑y * I - (α : ℂ))⁻¹) +
            (∫ y : ℝ in (-Real.pi)..Real.pi, ((R : ℂ) + ↑y * I - (-(α : ℂ)))⁻¹)) := by
        simp only [P_pole, sub_neg_eq_add]
        exact h_int_add _ _ _ _
          ((Continuous.inv₀ (by fun_prop) fun y heq => by
            have := congr_arg Complex.re heq; simp at this; linarith).intervalIntegrable _ _)
          ((Continuous.inv₀ (by fun_prop) fun y heq => by
            have := congr_arg Complex.re heq; simp at this; linarith).intervalIntegrable _ _)
      have hP_left : ∫ y : ℝ in (-Real.pi)..Real.pi, P_pole ((-R : ℂ) + ↑y * I) =
          f (α : ℂ) * ((∫ y : ℝ in (-Real.pi)..Real.pi, ((-R : ℂ) + ↑y * I - (α : ℂ))⁻¹) +
            (∫ y : ℝ in (-Real.pi)..Real.pi, ((-R : ℂ) + ↑y * I - (-(α : ℂ)))⁻¹)) := by
        simp only [P_pole, sub_neg_eq_add]
        exact h_int_add _ _ _ _
          ((Continuous.inv₀ (by fun_prop) fun y heq => by
            have := congr_arg Complex.re heq; simp at this; linarith).intervalIntegrable _ _)
          ((Continuous.inv₀ (by fun_prop) fun y heq => by
            have := congr_arg Complex.re heq; simp at this; linarith).intervalIntegrable _ _)
      rw [hP_bot, hP_top, hP_right, hP_left, smul_eq_mul]
      simp only [Complex.ofReal_neg] at hp2
      linear_combination f (α : ℂ) * (hp1 + hp2)
    rw [h_seg_bot, h_seg_top, h_seg_right, h_seg_left] at hCG
    simp only [smul_eq_mul] at hCG hP_split ⊢
    linear_combination hCG + hP_split
  let φ : ℝ → ℝ := fun u =>
    Real.exp (-u ^ 2 / (2 * t)) *
      (Real.sinh u * Real.sin (Real.pi * u / t) / (Real.cosh u + Real.cosh α))
  have hφ_even : ∀ u : ℝ, φ (-u) = φ u := fun u => by
    simp only [φ, neg_sq, Real.sinh_neg, mul_neg, Real.sin_neg, neg_div, Real.cosh_neg]
    ring
  have hφ_cont : Continuous φ := by
    refine Continuous.mul (by fun_prop) (Continuous.div (by fun_prop) (by fun_prop) fun u => ?_)
    linarith [Real.one_le_cosh u, Real.one_le_cosh α]
  have hφ_int : IntegrableOn φ (Ioi 0) := by
    have hgauss : IntegrableOn (fun u : ℝ => Real.exp (-(1 / (2 * t)) * u ^ 2)) (Ioi 0) :=
      (integrable_exp_neg_mul_sq (by positivity : 0 < 1 / (2 * t))).integrableOn
    refine hgauss.mono' hφ_cont.aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun u _ => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h_num : |Real.sinh u| ≤ Real.cosh u := by
      rw [Real.sinh_eq, Real.cosh_eq, abs_div, abs_of_pos (two_pos : (0 : ℝ) < 2)]
      refine div_le_div_of_nonneg_right ((abs_sub _ _).trans ?_) two_pos.le
      rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    have h_ratio : |Real.sinh u * Real.sin (Real.pi * u / t) / (Real.cosh u + Real.cosh α)| ≤ 1 := by
      rw [abs_div, abs_mul, abs_of_pos (add_pos (Real.cosh_pos u) (Real.cosh_pos α))]
      refine div_le_one_of_le₀ ?_ (by positivity)
      calc |Real.sinh u| * |Real.sin (Real.pi * u / t)|
          ≤ Real.cosh u * 1 := mul_le_mul h_num (Real.abs_sin_le_one _) (abs_nonneg _) (Real.cosh_pos u).le
        _ ≤ Real.cosh u + Real.cosh α := by linarith [Real.cosh_pos α]
    calc Real.exp (-u ^ 2 / (2 * t)) *
          |Real.sinh u * Real.sin (Real.pi * u / t) / (Real.cosh u + Real.cosh α)|
        ≤ Real.exp (-u ^ 2 / (2 * t)) * 1 := mul_le_mul_of_nonneg_left h_ratio (Real.exp_pos _).le
      _ = Real.exp (-(1 / (2 * t)) * u ^ 2) := by ring_nf
  have h_horiz : ∀ R : ℝ,
      (∫ x : ℝ in (-R)..R, H (↑x + (-Real.pi) * I)) - ∫ x : ℝ in (-R)..R, H (↑x + Real.pi * I) =
        (4 * I * (Real.exp (Real.pi ^ 2 / (2 * t)) : ℂ)) * (∫ x in (0 : ℝ)..R, (φ x : ℂ)) := by
    intro R
    have h_c : ∀ x : ℝ,
        H (↑x + (-Real.pi) * I) - H (↑x + Real.pi * I) =
          (2 * I * (Real.exp (Real.pi ^ 2 / (2 * t)) : ℂ)) * (φ x : ℂ) := by
      intro x
      have hcosh_p : Complex.cosh ((x : ℂ) + Real.pi * I) = -(Real.cosh x : ℂ) := by
        rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cos,
          ← Complex.ofReal_sin, Real.cos_pi, Real.sin_pi]
        simp [Complex.ofReal_cosh]
      have hcosh_m : Complex.cosh ((x : ℂ) + (-Real.pi) * I) = -(Real.cosh x : ℂ) := by
        rw [Complex.cosh_add, show ((-Real.pi : ℂ) * I) = ((-Real.pi : ℝ) : ℂ) * I by simp,
          Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cos,
          ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, Real.cos_pi, Real.sin_pi]
        simp [Complex.ofReal_cosh]
      have hsinh_p : Complex.sinh ((x : ℂ) + Real.pi * I) = -(Real.sinh x : ℂ) := by
        rw [Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cos,
          ← Complex.ofReal_sin, Real.cos_pi, Real.sin_pi]
        simp [Complex.ofReal_sinh]
      have hsinh_m : Complex.sinh ((x : ℂ) + (-Real.pi) * I) = -(Real.sinh x : ℂ) := by
        rw [Complex.sinh_add, show ((-Real.pi : ℂ) * I) = ((-Real.pi : ℝ) : ℂ) * I by simp,
          Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cos,
          ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, Real.cos_pi, Real.sin_pi]
        simp [Complex.ofReal_sinh]
      have hf_diff : f ((x : ℂ) + (-Real.pi) * I) - f ((x : ℂ) + Real.pi * I) =
          (Real.exp (-x ^ 2 / (2 * t)) : ℂ) * (Real.exp (Real.pi ^ 2 / (2 * t)) : ℂ) *
            (2 * I * Real.sin (Real.pi * x / t)) := by
        have h1 : -((x : ℂ) + (-Real.pi) * I) ^ 2 / (2 * (t : ℂ)) =
            ((-x ^ 2 / (2 * t) + Real.pi ^ 2 / (2 * t) : ℝ) : ℂ) + ((Real.pi * x / t : ℝ) : ℂ) * I := by
          push_cast; ring_nf; rw [I_sq]; field_simp [ht0]
        have h2 : -((x : ℂ) + Real.pi * I) ^ 2 / (2 * (t : ℂ)) =
            ((-x ^ 2 / (2 * t) + Real.pi ^ 2 / (2 * t) : ℝ) : ℂ) + (-(Real.pi * x / t : ℝ) : ℂ) * I := by
          push_cast; ring_nf; rw [I_sq]; field_simp [ht0]
        dsimp only [f]
        rw [h1, h2, Complex.exp_add, Complex.exp_add, Complex.exp_mul_I, Complex.exp_mul_I]
        rw [← Complex.ofReal_exp, Real.exp_add]
        push_cast
        rw [Complex.cos_neg, Complex.sin_neg]
        ring
      dsimp only [H]
      rw [hcosh_m, hcosh_p, hsinh_m, hsinh_p, ← Complex.ofReal_cosh]
      rw [show (-(Real.cosh x : ℂ) - (Real.cosh α : ℂ)) = -((Real.cosh x : ℂ) + (Real.cosh α : ℂ)) by ring]
      rw [mul_neg, neg_div_neg_eq, mul_neg, neg_div_neg_eq, ← sub_div, ← sub_mul, hf_diff]
      simp only [φ]
      push_cast
      ring
    have him_m : ∀ x : ℝ, |(↑x + (-Real.pi : ℂ) * I).im| ≤ Real.pi := fun x => by
      simp [abs_of_pos Real.pi_pos]
    have him_p : ∀ x : ℝ, |(↑x + (Real.pi : ℂ) * I).im| ≤ Real.pi := fun x => by
      simp [abs_of_pos Real.pi_pos]
    have hH_m : Continuous (fun x : ℝ => H (↑x + (-Real.pi) * I)) := by
      refine Continuous.div (by unfold f; fun_prop) (by fun_prop) fun x => ?_
      intro heq
      rw [sub_eq_zero] at heq
      rcases cosh_eq_cosh_real_strip_iff hα (him_m x) heq with h | h
      · have := congr_arg Complex.im h; simp [Real.pi_pos.ne'] at this
      · have := congr_arg Complex.im h; simp [Real.pi_pos.ne'] at this
    have hH_p : Continuous (fun x : ℝ => H (↑x + Real.pi * I)) := by
      refine Continuous.div (by unfold f; fun_prop) (by fun_prop) fun x => ?_
      intro heq
      rw [sub_eq_zero] at heq
      rcases cosh_eq_cosh_real_strip_iff hα (him_p x) heq with h | h
      · have := congr_arg Complex.im h; simp [Real.pi_pos.ne'] at this
      · have := congr_arg Complex.im h; simp [Real.pi_pos.ne'] at this
    rw [← intervalIntegral.integral_sub (hH_m.intervalIntegrable _ _) (hH_p.intervalIntegrable _ _)]
    simp_rw [h_c, intervalIntegral.integral_const_mul]
    have hφc : Continuous (fun x : ℝ => (φ x : ℂ)) := Complex.continuous_ofReal.comp hφ_cont
    have heven : ∫ x in (-R)..R, (φ x : ℂ) = 2 * ∫ x in (0 : ℝ)..R, (φ x : ℂ) := by
      have h1 : ∫ x in (-R)..(0 : ℝ), (φ x : ℂ) = ∫ x in (0 : ℝ)..R, (φ x : ℂ) := by
        have hsub := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := R) (fun x => (φ x : ℂ))
        simpa [hφ_even] using hsub.symm
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hφc.intervalIntegrable (-R) 0) (hφc.intervalIntegrable 0 R), h1]
      ring
    rw [heven]
    ring
  have h_vert_tendsto : Tendsto (fun R : ℝ =>
      I • ((∫ y : ℝ in (-Real.pi)..Real.pi, H ((R : ℂ) + ↑y * I)) -
        ∫ y : ℝ in (-Real.pi)..Real.pi, H ((-R : ℂ) + ↑y * I))) atTop (nhds 0) := by
    let R₀ : ℝ := max (α + 1) (Real.log (8 * Real.cosh α + 4)) + 2
    have h_bound : ∀ R ≥ R₀,
        ‖I • ((∫ y : ℝ in (-Real.pi)..Real.pi, H ((R : ℂ) + ↑y * I)) -
          ∫ y : ℝ in (-Real.pi)..Real.pi, H ((-R : ℂ) + ↑y * I))‖ ≤
        (24 * Real.pi * Real.exp (Real.pi ^ 2 / (2 * t))) * Real.exp (-R ^ 2 / (2 * t)) := by
      intro R hR
      have hR2 : 2 ≤ R := le_trans (by linarith [le_max_left (α + 1) (Real.log (8 * Real.cosh α + 4))]) hR
      have hR_log : Real.log (8 * Real.cosh α + 4) ≤ R :=
        le_trans (by linarith [le_max_right (α + 1) (Real.log (8 * Real.cosh α + 4))]) hR
      have hexpR : 8 * Real.cosh α + 4 ≤ Real.exp R := by
        rw [← Real.exp_log (by positivity : 0 < 8 * Real.cosh α + 4)]
        exact Real.exp_le_exp.mpr hR_log
      have hexp_negR : Real.exp (-R) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have hsinh_ge : 4 * Real.cosh α + 1 ≤ Real.sinh R := by
        rw [Real.sinh_eq]; linarith
      have hsinh_pos : 0 < Real.sinh R := by linarith [Real.cosh_pos α]
      have hcosh_le : Real.cosh R ≤ 3 * Real.sinh R := by
        rw [Real.cosh_eq, Real.sinh_eq]; linarith [Real.cosh_pos α, hexpR, hexp_negR]
      have h_side : ∀ s ∈ ({1, -1} : Set ℝ),
          ‖∫ y : ℝ in (-Real.pi)..Real.pi, H (((s * R : ℝ) : ℂ) + ↑y * I)‖ ≤
            (12 * Real.pi * Real.exp (Real.pi ^ 2 / (2 * t))) * Real.exp (-R ^ 2 / (2 * t)) := by
        intro s hs
        have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
        have h_pt : ∀ y ∈ uIcc (-Real.pi) Real.pi,
            ‖H (((s * R : ℝ) : ℂ) + ↑y * I)‖ ≤
              (6 * Real.exp (Real.pi ^ 2 / (2 * t))) * Real.exp (-R ^ 2 / (2 * t)) := by
          intro y hy
          have hy_abs : |y| ≤ Real.pi := by
            simpa [uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi), abs_le] using hy
          have hy2 : y ^ 2 ≤ Real.pi ^ 2 :=
            sq_le_sq' (by linarith [abs_le.mp hy_abs]) (by linarith [abs_le.mp hy_abs])
          have hf_norm : ‖f (((s * R : ℝ) : ℂ) + ↑y * I)‖ ≤
              Real.exp (Real.pi ^ 2 / (2 * t)) * Real.exp (-R ^ 2 / (2 * t)) := by
            have hre : (-(((s * R : ℝ) : ℂ) + (y : ℂ) * I) ^ 2 / (2 * (t : ℂ))).re =
                (-R ^ 2 + y ^ 2) / (2 * t) := by
              have hre' : (-(((s * R : ℝ) : ℂ) + (y : ℂ) * I) ^ 2).re = -(s * R) ^ 2 + y ^ 2 := by
                have hsq : (((s * R : ℝ) : ℂ) + (y : ℂ) * I) ^ 2 =
                    (((s * R) ^ 2 - y ^ 2 : ℝ) : ℂ) + ((2 * (s * R) * y : ℝ) : ℂ) * I := by
                  push_cast; ring_nf; rw [I_sq]; ring
                rw [hsq, neg_add, Complex.add_re, Complex.neg_re, Complex.ofReal_re]
                simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
                ring
              have hdiv : -(((s * R : ℝ) : ℂ) + (y : ℂ) * I) ^ 2 / (2 * (t : ℂ)) =
                  (-(((s * R : ℝ) : ℂ) + (y : ℂ) * I) ^ 2) * (((2 * t : ℝ)⁻¹ : ℝ) : ℂ) := by
                push_cast; rw [div_eq_mul_inv]
              rw [hdiv]
              rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hre']
              have : -(s * R) ^ 2 + y ^ 2 = -R ^ 2 + y ^ 2 := by
                rw [mul_pow, hs2, one_mul]
              rw [this, div_eq_mul_inv]
            dsimp only [f]
            rw [Complex.norm_exp, hre, show (-R ^ 2 + y ^ 2) / (2 * t) =
                Real.pi ^ 2 / (2 * t) + (-R ^ 2 / (2 * t)) + (y ^ 2 - Real.pi ^ 2) / (2 * t) by ring]
            rw [Real.exp_add, Real.exp_add]
            have hexp_le : Real.exp ((y ^ 2 - Real.pi ^ 2) / (2 * t)) ≤ 1 :=
              Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hy2) (by positivity))
            calc Real.exp (Real.pi ^ 2 / (2 * t)) * Real.exp (-R ^ 2 / (2 * t)) *
                  Real.exp ((y ^ 2 - Real.pi ^ 2) / (2 * t))
                ≤ Real.exp (Real.pi ^ 2 / (2 * t)) * Real.exp (-R ^ 2 / (2 * t)) * 1 :=
                  mul_le_mul_of_nonneg_left hexp_le (by positivity)
              _ = Real.exp (Real.pi ^ 2 / (2 * t)) * Real.exp (-R ^ 2 / (2 * t)) := mul_one _
          have hsinh_norm : ‖Complex.sinh (((s * R : ℝ) : ℂ) + ↑y * I)‖ ≤ 3 * Real.sinh R := by
            have h1 := norm_sinh_le_cosh (s * R) y
            have h2 : Real.cosh (s * R) = Real.cosh R := by
              rcases hs with rfl | rfl <;> simp
            linarith
          have hden_norm : (1 / 2 : ℝ) * Real.sinh R ≤
              ‖Complex.cosh (((s * R : ℝ) : ℂ) + ↑y * I) - Complex.cosh (α : ℂ)‖ := by
            have h1 : |Real.sinh (s * R)| ≤ ‖Complex.cosh (((s * R : ℝ) : ℂ) + ↑y * I)‖ :=
              norm_cosh_ge_abs_sinh (s * R) y
            have h2 : |Real.sinh (s * R)| = Real.sinh R := by
              rcases hs with rfl | rfl <;> simp [abs_of_pos hsinh_pos]
            have h3 : ‖Complex.cosh (α : ℂ)‖ = Real.cosh α := by
              rw [← Complex.ofReal_cosh, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos α)]
            have htri := norm_sub_norm_le (Complex.cosh (((s * R : ℝ) : ℂ) + ↑y * I)) (Complex.cosh (α : ℂ))
            linarith
          have hden_pos : 0 < ‖Complex.cosh (((s * R : ℝ) : ℂ) + ↑y * I) - Complex.cosh (α : ℂ)‖ :=
            lt_of_lt_of_le (by positivity) hden_norm
          dsimp only [H]
          rw [norm_div, norm_mul]
          calc ‖f (((s * R : ℝ) : ℂ) + ↑y * I)‖ * ‖Complex.sinh (((s * R : ℝ) : ℂ) + ↑y * I)‖ /
                ‖Complex.cosh (((s * R : ℝ) : ℂ) + ↑y * I) - Complex.cosh (α : ℂ)‖
              ≤ (Real.exp (Real.pi ^ 2 / (2 * t)) * Real.exp (-R ^ 2 / (2 * t))) * (3 * Real.sinh R) /
                  ((1 / 2 : ℝ) * Real.sinh R) := by
                gcongr
            _ = (6 * Real.exp (Real.pi ^ 2 / (2 * t))) * Real.exp (-R ^ 2 / (2 * t)) := by
                field_simp [hsinh_pos.ne']; ring
        have h_int_norm := intervalIntegral.norm_integral_le_of_norm_le_const (a := -Real.pi) (b := Real.pi)
          (C := (6 * Real.exp (Real.pi ^ 2 / (2 * t))) * Real.exp (-R ^ 2 / (2 * t)))
          (fun y hy => h_pt y (uIoc_subset_uIcc hy))
        calc ‖∫ y : ℝ in (-Real.pi)..Real.pi, H (((s * R : ℝ) : ℂ) + ↑y * I)‖
            ≤ (6 * Real.exp (Real.pi ^ 2 / (2 * t))) * Real.exp (-R ^ 2 / (2 * t)) * |Real.pi - -Real.pi| := h_int_norm
          _ = (12 * Real.pi * Real.exp (Real.pi ^ 2 / (2 * t))) * Real.exp (-R ^ 2 / (2 * t)) := by
              rw [sub_neg_eq_add, abs_of_pos (by linarith [Real.pi_pos])]; ring
      have hR_side := h_side 1 (by simp)
      have hL_side := h_side (-1) (by simp)
      simp only [one_mul, neg_mul, Complex.ofReal_neg] at hR_side hL_side
      rw [smul_eq_mul, norm_mul, Complex.norm_I, one_mul]
      exact (norm_sub_le _ _).trans (by linarith)
    have h_lim : Tendsto (fun R : ℝ =>
        (24 * Real.pi * Real.exp (Real.pi ^ 2 / (2 * t))) * Real.exp (-R ^ 2 / (2 * t))) atTop (nhds 0) := by
      have h_exp : Tendsto (fun R : ℝ => Real.exp (-R ^ 2 / (2 * t))) atTop (nhds 0) := by
        have ht_atBot : Tendsto (fun R : ℝ => -R ^ 2 / (2 * t)) atTop atBot := by
          have h1 : Tendsto (fun R : ℝ => R ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
          have h2 : Tendsto (fun R : ℝ => -(1 / (2 * t)) * R ^ 2) atTop atBot :=
            Tendsto.const_mul_atTop_of_neg (by linarith [show (0 : ℝ) < 1 / (2 * t) by positivity]) h1
          exact h2.congr fun R => by ring
        exact Real.tendsto_exp_atBot.comp ht_atBot
      simpa using h_exp.const_mul (24 * Real.pi * Real.exp (Real.pi ^ 2 / (2 * t)))
    refine squeeze_zero_norm' ?_ h_lim
    filter_upwards [eventually_ge_atTop R₀] with R hR
    exact h_bound R hR
  have h_horiz_tendsto : Tendsto (fun R : ℝ =>
      (∫ x : ℝ in (-R)..R, H (↑x + (-Real.pi) * I)) - ∫ x : ℝ in (-R)..R, H (↑x + Real.pi * I))
      atTop (nhds ((4 * I * (Real.exp (Real.pi ^ 2 / (2 * t)) : ℂ)) *
        ((∫ u in Ioi (0 : ℝ), φ u : ℝ) : ℂ))) := by
    have h_int_t : Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, φ x) atTop (nhds (∫ u in Ioi (0 : ℝ), φ u)) :=
      intervalIntegral_tendsto_integral_Ioi 0 hφ_int tendsto_id
    have h_int_c : Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, (φ x : ℂ)) atTop
        (nhds ((∫ u in Ioi (0 : ℝ), φ u : ℝ) : ℂ)) := by
      have h_eq : (fun R : ℝ => ∫ x in (0 : ℝ)..R, (φ x : ℂ)) =
          fun R : ℝ => ((∫ x in (0 : ℝ)..R, φ x : ℝ) : ℂ) := by
        funext R
        exact intervalIntegral.integral_ofReal
      rw [h_eq]
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp h_int_t
    have h_eq' : (fun R : ℝ =>
        (∫ x : ℝ in (-R)..R, H (↑x + (-Real.pi) * I)) - ∫ x : ℝ in (-R)..R, H (↑x + Real.pi * I)) =
        fun R : ℝ => (4 * I * (Real.exp (Real.pi ^ 2 / (2 * t)) : ℂ)) * (∫ x in (0 : ℝ)..R, (φ x : ℂ)) :=
      funext h_horiz
    rw [h_eq']
    exact h_int_c.const_mul _
  have h_sum_lim := h_horiz_tendsto.add h_vert_tendsto
  rw [add_zero] at h_sum_lim
  have h_const_lim : Tendsto (fun R : ℝ =>
      ((∫ x : ℝ in (-R)..R, H (↑x + (-Real.pi) * I)) - ∫ x : ℝ in (-R)..R, H (↑x + Real.pi * I)) +
      I • ((∫ y : ℝ in (-Real.pi)..Real.pi, H ((R : ℂ) + ↑y * I)) -
        ∫ y : ℝ in (-Real.pi)..Real.pi, H ((-R : ℂ) + ↑y * I)))
      atTop (nhds (4 * Real.pi * I * f (α : ℂ))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (α + 1)] with R hR
    exact (h_rect R hR).symm
  have h_eq_C := tendsto_nhds_unique h_sum_lim h_const_lim
  have hf_val : f (α : ℂ) = (Real.exp (-α ^ 2 / (2 * t)) : ℂ) := by
    dsimp only [f]
    rw [show (-(α : ℂ) ^ 2 / (2 * (t : ℂ))) = ((-α ^ 2 / (2 * t) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp]
  rw [hf_val] at h_eq_C
  have h_cancel : (4 : ℂ) * I ≠ 0 := by simp [I_ne_zero]
  have h_eq_C' : (Real.exp (Real.pi ^ 2 / (2 * t)) : ℂ) * ((∫ u in Ioi (0 : ℝ), φ u : ℝ) : ℂ) =
      (Real.pi * Real.exp (-α ^ 2 / (2 * t)) : ℝ) := by
    apply mul_left_cancel₀ h_cancel
    push_cast at h_eq_C ⊢
    linear_combination h_eq_C
  have h_re := congr_arg Complex.re h_eq_C'
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at h_re
  simpa [φ] using h_re

end ContourIntegral

end Lyasoff2016
