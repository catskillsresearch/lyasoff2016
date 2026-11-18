/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Constructive identification of the higher-order π-formulae.
-/
module

public import Lyasoff2016.ContourEq
public import Lyasoff2016.Foliation
public import Lyasoff2016.PiFormulaScaling

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/-- The real integrand on the lower edge of the `a = π` contour, written with
the positive denominator which occurs after the inverse-Gamma integration. -/
private def piContourReal (p : ℕ) (T A u : ℝ) : ℝ :=
  Real.sinh u * (gFun p T (u - I * π)).re / (Real.cosh u + A) ^ (p - 1)

private lemma piContourReal_eq_contourIntegrand
    (p : ℕ) (hp : p = 2 ∨ p = 3 ∨ p = 4) (T A u : ℝ) (hA : 1 ≤ A) :
    (contourIntegrand p T π (Real.arcosh A) u).re =
      (-1 : ℝ) ^ p * piContourReal p T A u := by
  have hcosh : Complex.cosh ((u : ℂ) - I * π) = -(Real.cosh u : ℂ) := by
    have harg : ((u : ℂ) - I * π) = (u : ℂ) - (π : ℂ) * I := by ring
    rw [harg, Complex.cosh_sub_pi_mul_I]
    simp
  have hsinh : Complex.sinh ((u : ℂ) - I * π) = -(Real.sinh u : ℂ) := by
    have harg : ((u : ℂ) - I * π) = (u : ℂ) - (π : ℂ) * I := by ring
    rw [harg, Complex.sinh_sub_pi_mul_I]
    simp
  have harc : Complex.cosh (Real.arcosh A : ℂ) = (A : ℂ) := by
    apply Complex.ext
    · rw [Complex.cosh_ofReal_re, Real.cosh_arcosh hA]
      simp
    · simp [Complex.cosh_ofReal_im]
  have hpos : 0 < Real.cosh u + A := by
    linarith [Real.one_le_cosh u]
  have hne : (((Real.cosh u + A : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hpos.ne'
  have hneC : Complex.cosh (u : ℂ) + (A : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    have hr' : Real.cosh u + A = 0 := by
      simpa only [add_re, Complex.cosh_ofReal_re, ofReal_re, zero_re] using hr
    exact hpos.ne' hr'
  have hbase : -(Real.cosh u : ℂ) - (A : ℂ) =
      -(((Real.cosh u + A : ℝ) : ℂ)) := by
    push_cast
    ring
  have hcomplex :
      contourIntegrand p T π (Real.arcosh A) u =
        ((((-1 : ℝ) ^ p * Real.sinh u /
          (Real.cosh u + A) ^ (p - 1) : ℝ) : ℂ) *
            gFun p T ((u : ℂ) - I * π)) := by
    unfold contourIntegrand
    rw [hcosh, hsinh, harc, hbase]
    rcases hp with rfl | rfl | rfl <;>
      norm_num only [Nat.reduceSub] <;> field_simp [hne, hneC] <;> push_cast <;>
      field_simp [hneC]
  rw [hcomplex]
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  unfold piContourReal
  ring

private lemma piContourReal_even
    (p : ℕ) (hp : p = 2 ∨ p = 3 ∨ p = 4) (T A : ℝ) :
    Function.Even (piContourReal p T A) := by
  intro u
  have hz : (((-u : ℝ) : ℂ) - I * π) =
      -(starRingEnd ℂ ((u : ℂ) - I * π)) := by
    simp only [map_sub, conj_ofReal, map_mul, conj_I, neg_mul]
    push_cast
    ring
  have hg : gFun p T (((-u : ℝ) : ℂ) - I * π) =
      -starRingEnd ℂ (gFun p T ((u : ℂ) - I * π)) := by
    rw [hz, gFun.even, gFun.conj p hp]
  unfold piContourReal
  rw [Real.sinh_neg, Real.cosh_neg, hg]
  simp only [neg_re, conj_re]
  ring

private lemma piContourReal_integrable
    {p : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 4)
    {T : ℝ} (hT : 0 < T) {A : ℝ} (hA : 1 ≤ A) :
    Integrable (piContourReal p T A) := by
  have hc := g_solves_contour_equation p hp T hT (Real.arcosh A) π
    (by constructor <;> linarith [Real.pi_pos])
  have hi := hc.1.re
  rcases hp with rfl | rfl | rfl
  · exact hi.congr (ae_of_all _ fun u => by
      have h := piContourReal_eq_contourIntegrand 2 (Or.inl rfl) T A u hA
      norm_num at h ⊢
      exact h)
  · exact hi.neg.congr (ae_of_all _ fun u => by
      have h := piContourReal_eq_contourIntegrand 3 (Or.inr (Or.inl rfl)) T A u hA
      norm_num at h ⊢
      linarith)
  · exact hi.congr (ae_of_all _ fun u => by
      have h := piContourReal_eq_contourIntegrand 4 (Or.inr (Or.inr rfl)) T A u hA
      norm_num at h ⊢
      exact h)

private lemma piContourReal_integral
    {p : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 4)
    {T : ℝ} (hT : 0 < T) {A : ℝ} (hA : 1 ≤ A) :
    ∫ u in Ioi (0 : ℝ), piContourReal p T A u =
      (-4 : ℝ) ^ (p - 2) / (((p - 2).factorial : ℝ) * 4 * (-1 : ℝ) ^ p) *
        Real.exp (-2 * Real.arcosh A ^ 2 / T) := by
  have hc := g_solves_contour_equation p hp T hT (Real.arcosh A) π
    (by constructor <;> linarith [Real.pi_pos])
  rcases hc with ⟨hcint, hceq⟩
  have heven := piContourReal_even p hp T A
  have habs :
      (fun u : ℝ => piContourReal p T A |u|) = piContourReal p T A := by
    funext u
    rcases le_total 0 u with hu | hu
    · rw [abs_of_nonneg hu]
    · rw [abs_of_nonpos hu, heven u]
  have hfull :
      ∫ u : ℝ, piContourReal p T A u =
        2 * ∫ u in Ioi (0 : ℝ), piContourReal p T A u := by
    rw [← habs, integral_comp_abs, habs]
  have hcontour :
      ∫ u : ℝ, (contourIntegrand p T π (Real.arcosh A) u).re =
        (-1 : ℝ) ^ p * ∫ u : ℝ, piContourReal p T A u := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun u =>
      piContourReal_eq_contourIntegrand p hp T A u hA)
  rw [hcontour, hfull] at hceq
  rcases hp with rfl | rfl | rfl <;>
    norm_num [Nat.factorial] at hceq ⊢ <;> linarith

private def piKernel (p : ℕ) (T v y x u : ℝ) : ℝ :=
  (Real.sinh u * (gFun p T (u - I * π)).re) *
    (Real.exp (-v / x) *
      (1 / x ^ p * Real.exp (-(Real.exp y *
        (Real.cosh y + Real.cosh u)) / x)))

private lemma charA_one_le {v y : ℝ} (hv : 0 ≤ v) :
    1 ≤ charA v y := by
  unfold charA
  exact (Real.one_le_cosh y).trans
    (le_add_of_nonneg_right (mul_nonneg hv (Real.exp_pos _).le))

private lemma piKernel_scale
    (v y u : ℝ) :
    v + Real.exp y * (Real.cosh y + Real.cosh u) =
      Real.exp y * (charA v y + Real.cosh u) := by
  unfold charA
  have he : Real.exp y * Real.exp (-y) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [mul_add, mul_add]
  calc
    v + (Real.exp y * Real.cosh y + Real.exp y * Real.cosh u) =
        Real.exp y * Real.cosh y + v + Real.exp y * Real.cosh u := by ring
    _ = Real.exp y * Real.cosh y +
        Real.exp y * (v * Real.exp (-y)) + Real.exp y * Real.cosh u := by
      rw [show Real.exp y * (v * Real.exp (-y)) = v by
        calc
          _ = v * (Real.exp y * Real.exp (-y)) := by ring
          _ = v := by rw [he, mul_one]]
    _ = _ := by ring

private lemma piKernel_inner_integrable
    {p : ℕ} (hp : 2 ≤ p) {T v y : ℝ} (hv : 0 ≤ v) (u : ℝ) :
    IntegrableOn (fun x => piKernel p T v y x u) (Ioi 0) := by
  have hscale : 0 < v + Real.exp y * (Real.cosh y + Real.cosh u) := by
    rw [piKernel_scale]
    have hA := charA_one_le (v := v) (y := y) hv
    positivity
  have hi := integrableOn_exp_neg_div_mul_inv_pow_exp_neg_div hp hscale
  refine (hi.congr_fun (fun x hx => ?_) measurableSet_Ioi).const_mul _
  rw [zpow_neg, zpow_natCast]
  field_simp

private lemma piKernel_inner_integral
    {p : ℕ} (hp : 2 ≤ p) {T v y : ℝ} (hv : 0 ≤ v) (u : ℝ) :
    ∫ x in Ioi (0 : ℝ), piKernel p T v y x u =
      (Real.sinh u * (gFun p T (u - I * π)).re) *
        (((p - 2).factorial : ℝ) /
          (Real.exp y * (charA v y + Real.cosh u)) ^ (p - 1)) := by
  unfold piKernel
  rw [integral_const_mul,
    integral_exp_neg_div_mul_one_div_pow_exp_neg_div hp]
  · rw [piKernel_scale]
  · rw [piKernel_scale]
    have hA := charA_one_le (v := v) (y := y) hv
    positivity

private lemma piKernel_inner_norm_integral
    {p : ℕ} (hp : 2 ≤ p) {T v y : ℝ} (hv : 0 ≤ v) (u : ℝ) :
    ∫ x in Ioi (0 : ℝ), ‖piKernel p T v y x u‖ =
      |Real.sinh u * (gFun p T (u - I * π)).re| *
        (((p - 2).factorial : ℝ) /
          (Real.exp y * (charA v y + Real.cosh u)) ^ (p - 1)) := by
  have hpoint : ∀ x ∈ Ioi (0 : ℝ), ‖piKernel p T v y x u‖ =
      |Real.sinh u * (gFun p T (u - I * π)).re| *
        (Real.exp (-v / x) *
          (1 / x ^ p * Real.exp (-(Real.exp y *
            (Real.cosh y + Real.cosh u)) / x))) := by
    intro x hx
    unfold piKernel
    have hx0 : 0 < x := hx
    have hk : 0 ≤ Real.exp (-v / x) *
        (1 / x ^ p * Real.exp (-(Real.exp y *
          (Real.cosh y + Real.cosh u)) / x)) := by positivity
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint, integral_const_mul,
    integral_exp_neg_div_mul_one_div_pow_exp_neg_div hp]
  · rw [piKernel_scale]
  · rw [piKernel_scale]
    have hA := charA_one_le (v := v) (y := y) hv
    positivity

private lemma piKernel_integrable
    {p : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 4)
    {t : ℝ} (ht : 0 < t) {v : ℝ} (hv : 0 ≤ v) (y : ℝ) :
    Integrable (Function.uncurry (piKernel p (t * 4) v y))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hp2 : 2 ≤ p := by omega
  have hA := charA_one_le (v := v) (y := y) hv
  have hcont := piContourReal_integrable hp (by positivity : 0 < t * 4) hA
  have hsm : StronglyMeasurable
      (Function.uncurry (piKernel p (t * 4) v y)) := by
    have hg : Continuous (gFun p (t * 4)) := (gFun.contDiff p (t * 4)).continuous
    apply Measurable.stronglyMeasurable
    unfold piKernel Function.uncurry
    fun_prop
  rw [integrable_prod_iff' hsm.aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · exact ae_of_all _ fun u => piKernel_inner_integrable hp2 hv u
  · have hnorm :
        (fun u => ∫ x in Ioi (0 : ℝ),
          ‖piKernel p (t * 4) v y x u‖) =
        fun u => ((p - 2).factorial : ℝ) *
          Real.exp (-y * ((p : ℝ) - 1)) *
            ‖piContourReal p (t * 4) (charA v y) u‖ := by
      funext u
      rw [piKernel_inner_norm_integral hp2 hv]
      unfold piContourReal
      rw [Real.norm_eq_abs]
      have hpos : 0 < charA v y + Real.cosh u := by
        linarith [Real.one_le_cosh u]
      have hexppow :
          (Real.exp y * (charA v y + Real.cosh u)) ^ (p - 1) =
            Real.exp (y * ((p : ℝ) - 1)) *
              (charA v y + Real.cosh u) ^ (p - 1) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
        ring
      have hexpneg :
          Real.exp (-y * ((p : ℝ) - 1)) =
            (Real.exp (y * ((p : ℝ) - 1)))⁻¹ := by
        rw [show -y * ((p : ℝ) - 1) = -(y * ((p : ℝ) - 1)) by ring,
          Real.exp_neg]
      rw [hexppow, hexpneg, abs_div]
      have hpos' : 0 < Real.cosh u + charA v y := by linarith
      rw [abs_pow, abs_of_pos hpos']
      field_simp
      ring
    change Integrable (fun u => ∫ x in Ioi (0 : ℝ),
      ‖piKernel p (t * 4) v y x u‖) (volume.restrict (Ioi 0))
    rw [hnorm]
    simpa [mul_assoc] using
      (hcont.integrableOn.norm.const_mul
        (Real.exp (-y * ((p : ℝ) - 1)))).const_mul
          (((p - 2).factorial : ℝ))

private lemma piFormula_scaled_eq_kernel
    {p : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 4)
    {t : ℝ} (ht : 0 < t) {v : ℝ} (x y : ℝ) (hx : 0 < x) :
    Real.exp (-v / x) * (2 ^ 2 : ℝ)⁻¹ *
        piFormula p 2 t (x * 2 ^ 2) (y * 2) =
      (4 : ℝ) ^ ((3 : ℤ) - (p : ℤ)) *
        Real.exp (y * ((p : ℝ) - 1) + y ^ 2 / (2 * t)) *
          ∫ u in Ioi (0 : ℝ), piKernel p (t * 4) v y x u := by
  have hinner :
      ∫ u in Ioi (0 : ℝ), piKernel p (t * 4) v y x u =
        (Real.exp (-v / x) *
          (1 / x ^ p * Real.exp (-(Real.exp y * Real.cosh y) / x))) *
        ∫ u in Ioi (0 : ℝ), Real.sinh u *
          (Real.exp (-(Real.exp y * Real.cosh u) / x) *
            (gFun p (t * 4) (u - I * π)).re) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    unfold piKernel
    have he :
        Real.exp (-(Real.exp y * (Real.cosh y + Real.cosh u)) / x) =
          Real.exp (-(Real.exp y * Real.cosh y) / x) *
            Real.exp (-(Real.exp y * Real.cosh u) / x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    ring
  rw [hinner]
  rw [piFormula, ite_eq_left (by positivity : 0 < x * 2 ^ 2)]
  simp only [re_ofReal_mul]
  have ht0 : (t : ℝ) ≠ 0 := ht.ne'
  have he : Real.exp y * Real.exp (-y) = 1 := by
    rw [← Real.exp_add]
    simp
  have hcosh : Real.exp (y * 2) + 1 =
      2 * Real.exp y * Real.cosh y := by
    rw [Real.cosh_eq]
    calc
      Real.exp (y * 2) + 1 =
          Real.exp y * Real.exp y + Real.exp y * Real.exp (-y) := by
        rw [he, ← Real.exp_add]
        congr 2
        ring
      _ = _ := by ring
  have hexp :
      Real.exp ((y * 2) * (((p : ℕ) : ℝ) - 1) / 2 +
          (y * 2) ^ 2 / (2 * (t * 4)) -
          2 * (Real.exp (y * 2) + 1) / (x * 4)) =
        Real.exp (y * (((p : ℕ) : ℝ) - 1) + y ^ 2 / (2 * t)) *
          Real.exp (-(Real.exp y * Real.cosh y) / x) := by
    rw [← Real.exp_add]
    congr 1
    rw [hcosh]
    field_simp [hx.ne', ht0]
    ring
  norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num]
  rw [hexp]
  rcases hp with rfl | rfl | rfl <;>
    norm_num [Nat.factorial] <;>
    field_simp [hx.ne', ht0] <;> ring

/-- For every paper order `p = 2,3,4`, the `σ = 2` π-formula has Yor's
conditional `1/x`-Laplace transform. -/
theorem piFormula_sigma_two_laplace
    {p : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 4)
    (t : ℝ≥0) (ht : 0 < t) {v : ℝ} (hv : 0 ≤ v) (y : ℝ) :
    IntegrableOn
      (fun x => Real.exp (-v / x) *
        (2 ^ 2 : ℝ)⁻¹ * piFormula p 2 t (x * 2 ^ 2) (y * 2))
      (Ioi 0) ∧
    ∫ x in Ioi (0 : ℝ), Real.exp (-v / x) *
        (2 ^ 2 : ℝ)⁻¹ * piFormula p 2 t (x * 2 ^ 2) (y * 2) =
      (gaussianPDFReal 0 t y)⁻¹ *
        gaussianPDFReal 0 t (Real.arcosh (charA v y)) := by
  have htR : (0 : ℝ) < t := ht
  have hk := piKernel_integrable hp htR hv y
  have hsections :
      IntegrableOn (fun x => ∫ u in Ioi (0 : ℝ),
        piKernel p ((t : ℝ) * 4) v y x u) (Ioi 0) :=
    hk.integral_prod_left
  let C : ℝ := (4 : ℝ) ^ ((3 : ℤ) - (p : ℤ)) *
    Real.exp (y * ((p : ℝ) - 1) + y ^ 2 / (2 * (t : ℝ)))
  have hpoint : ∀ x ∈ Ioi (0 : ℝ),
      Real.exp (-v / x) * (2 ^ 2 : ℝ)⁻¹ *
          piFormula p 2 t (x * 2 ^ 2) (y * 2) =
        C * ∫ u in Ioi (0 : ℝ), piKernel p ((t : ℝ) * 4) v y x u := by
    intro x hx
    exact piFormula_scaled_eq_kernel hp htR (v := v) x y hx
  constructor
  · refine (hsections.const_mul C).congr ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => (hpoint x hx).symm
  · rw [setIntegral_congr_fun measurableSet_Ioi hpoint, integral_const_mul]
    rw [integral_integral_swap hk]
    have hinner :
        (fun u => ∫ x in Ioi (0 : ℝ),
          piKernel p ((t : ℝ) * 4) v y x u) =
        fun u => (Real.sinh u *
            (gFun p ((t : ℝ) * 4) (u - I * π)).re) *
          (((p - 2).factorial : ℝ) /
            (Real.exp y * (charA v y + Real.cosh u)) ^ (p - 1)) := by
      funext u
      exact piKernel_inner_integral (by omega) hv u
    rw [hinner]
    have hfactor :
        (fun u => (Real.sinh u *
            (gFun p ((t : ℝ) * 4) (u - I * π)).re) *
          (((p - 2).factorial : ℝ) /
            (Real.exp y * (charA v y + Real.cosh u)) ^ (p - 1))) =
        fun u => ((p - 2).factorial : ℝ) *
          Real.exp (-y * ((p : ℝ) - 1)) *
            piContourReal p ((t : ℝ) * 4) (charA v y) u := by
      funext u
      unfold piContourReal
      have hA := charA_one_le (v := v) (y := y) hv
      have hpos : 0 < charA v y + Real.cosh u := by
        linarith [Real.one_le_cosh u]
      have hexppow :
          (Real.exp y * (charA v y + Real.cosh u)) ^ (p - 1) =
            Real.exp (y * ((p : ℝ) - 1)) *
              (charA v y + Real.cosh u) ^ (p - 1) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
        ring
      rw [hexppow]
      have hexpneg :
          Real.exp (-y * ((p : ℝ) - 1)) =
            (Real.exp (y * ((p : ℝ) - 1)))⁻¹ := by
        rw [show -y * ((p : ℝ) - 1) = -(y * ((p : ℝ) - 1)) by ring,
          Real.exp_neg]
      rw [hexpneg]
      field_simp
      ring
    rw [hfactor, integral_const_mul,
      piContourReal_integral hp (by positivity : 0 < (t : ℝ) * 4)
        (charA_one_le (v := v) (y := y) hv)]
    dsimp [C]
    have hsqrt : √(2 * π * (t : ℝ)) ≠ 0 := by positivity
    have hgauss :
        (gaussianPDFReal 0 t y)⁻¹ *
            gaussianPDFReal 0 t (Real.arcosh (charA v y)) =
          Real.exp (y ^ 2 / (2 * (t : ℝ))) *
            Real.exp (-(Real.arcosh (charA v y) ^ 2) / (2 * (t : ℝ))) := by
      simp only [gaussianPDFReal_def, sub_zero]
      field_simp [hsqrt]
      rw [← Real.exp_add]
      convert Real.exp_zero.symm using 1; ring_nf
    rw [hgauss]
    have hq :
        -2 * Real.arcosh (charA v y) ^ 2 / ((t : ℝ) * 4) =
          -(Real.arcosh (charA v y) ^ 2) / (2 * (t : ℝ)) := by
      field_simp [htR.ne']
      ring
    rw [hq]
    rcases hp with rfl | rfl | rfl
    all_goals norm_num [Nat.factorial]
    all_goals ring_nf
    all_goals repeat rw [← Real.exp_add]
    all_goals (congr 1; field_simp [htR.ne']; ring)

lemma piFormula_sigma_two_measurable
    (p : ℕ) (t : ℝ) :
    Measurable (fun q : ℝ × ℝ =>
      (2 ^ 2 : ℝ)⁻¹ * piFormula p 2 t (q.1 * 2 ^ 2) (q.2 * 2)) := by
  have hg : Continuous (gFun p (t * 4)) := (gFun.contDiff p (t * 4)).continuous
  have hsm : StronglyMeasurable (fun q : (ℝ × ℝ) × ℝ =>
      Real.sinh q.2 *
        (((Real.exp (-(4 / (q.1.1 * 4)) * Real.exp q.1.2 *
          Real.cosh q.2) : ℝ) : ℂ) *
            gFun p (t * 4) (q.2 - I * π)).re) := by
    apply Measurable.stronglyMeasurable
    fun_prop
  have hi : Measurable (fun q : ℝ × ℝ =>
      ∫ u in Ioi (0 : ℝ), Real.sinh u *
        (((Real.exp (-(4 / (q.1 * 4)) * Real.exp q.2 *
          Real.cosh u) : ℝ) : ℂ) *
            gFun p (t * 4) (u - I * π)).re) :=
    (StronglyMeasurable.integral_prod_right
      (ν := volume.restrict (Ioi (0 : ℝ))) hsm).measurable
  let A : ℝ × ℝ → ℝ := fun q =>
    (2 ^ 2 : ℝ)⁻¹ *
      (2 ^ 4 * (16 / (q.1 * 2 ^ 2) ^ p) *
        Real.exp (q.2 * 2 * (((p : ℕ) : ℝ) - 1) / 2 +
          (q.2 * 2) ^ 2 / (2 * (t * 2 ^ 2)) -
          2 * (Real.exp (q.2 * 2) + 1) / (q.1 * 2 ^ 2)))
  have hA : Measurable A := by
    dsimp [A]
    fun_prop
  have hfun : (fun q : ℝ × ℝ =>
      (2 ^ 2 : ℝ)⁻¹ * piFormula p 2 t (q.1 * 2 ^ 2) (q.2 * 2)) =
      fun q => if 0 < q.1 then A q *
        (∫ u in Ioi (0 : ℝ), Real.sinh u *
          (((Real.exp (-(4 / (q.1 * 4)) * Real.exp q.2 *
            Real.cosh u) : ℝ) : ℂ) *
              gFun p (t * 4) (u - I * π)).re) else 0 := by
    funext q
    unfold piFormula A
    by_cases hq : 0 < q.1
    · rw [ite_eq_left hq, ite_eq_left (by positivity : 0 < q.1 * 2 ^ 2)]
      norm_num
      simp only [sub_eq_add_neg, add_comm]
      ring
    · rw [ite_eq_right (not_lt.mpr (le_of_not_gt hq)),
        ite_eq_right (not_lt.mpr
          (mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hq) (sq_nonneg 2)))]
      ring
  rw [hfun]
  apply Measurable.ite
  · exact measurableSet_lt measurable_const measurable_fst
  · exact hA.mul hi
  · exact measurable_const

/-- The `σ = 2` π-formula is a constructive joint density for every paper
order `p = 2,3,4`. -/
theorem pi_formula_sigma_two
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (t : ℝ≥0) (ht : 0 < t)
    (p : ℕ) (hp : p = 2 ∨ p = 3 ∨ p = 4) :
    IsJointDensity P W 2 0 t (fun x y =>
      gaussianPDFReal 0 t y * (2 ^ 2 : ℝ)⁻¹ *
        piFormula p 2 t (x * 2 ^ 2) (y * 2)) := by
  let φp : ℝ → ℝ → ℝ := fun x y =>
    (2 ^ 2 : ℝ)⁻¹ * piFormula p 2 t (x * 2 ^ 2) (y * 2)
  let φ2 : ℝ → ℝ → ℝ := fun x y =>
    (2 ^ 2 : ℝ)⁻¹ * piFormula 2 2 t (x * 2 ^ 2) (y * 2)
  have hae : ∀ y : ℝ, ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
      φp x y = φ2 x y := by
    intro y
    have hp0 := piFormula_sigma_two_laplace hp t ht (v := 0) (by norm_num) y
    have h20 := piFormula_sigma_two_laplace (p := 2) (Or.inl rfl) t ht
      (v := 0) (by norm_num) y
    have hpint : IntegrableOn (fun x => φp x y) (Ioi 0) := by
      simpa only [φp, neg_zero, zero_div, Real.exp_zero, one_mul] using hp0.1
    have h2int : IntegrableOn (fun x => φ2 x y) (Ioi 0) := by
      simpa only [φ2, neg_zero, zero_div, Real.exp_zero, one_mul] using h20.1
    apply prop_4_4 (fun x => φp x y) (fun x => φ2 x y)
      hpint.aestronglyMeasurable h2int.aestronglyMeasurable hpint h2int
    intro u hu
    have hpu := piFormula_sigma_two_laplace hp t ht (v := u) hu y
    have h2u := piFormula_sigma_two_laplace (p := 2) (Or.inl rfl) t ht
      (v := u) hu y
    simpa only [laplaceCond, φp, φ2, mul_assoc] using hpu.2.trans h2u.2.symm
  have haeFull : ∀ y : ℝ, ∀ᵐ x ∂volume, φp x y = φ2 x y := by
    intro y
    have hrest := (ae_restrict_iff' measurableSet_Ioi).mp (hae y)
    filter_upwards [hrest] with x hx
    by_cases hxp : 0 < x
    · exact hx hxp
    · simp [φp, φ2, piFormula, hxp]
  have hφpm : Measurable (Function.uncurry φp) := by
    change Measurable (fun q : ℝ × ℝ =>
      (2 ^ 2 : ℝ)⁻¹ * piFormula p 2 t (q.1 * 2 ^ 2) (q.2 * 2))
    exact piFormula_sigma_two_measurable p (t : ℝ)
  have hφ2m : Measurable (Function.uncurry φ2) := by
    change Measurable (fun q : ℝ × ℝ =>
      (2 ^ 2 : ℝ)⁻¹ * piFormula 2 2 t (q.1 * 2 ^ 2) (q.2 * 2))
    exact piFormula_sigma_two_measurable 2 (t : ℝ)
  have heqset : MeasurableSet {q : ℝ × ℝ | φp q.1 q.2 = φ2 q.1 q.2} := by
    have hz := measurableSet_singleton (0 : ℝ)
    convert hz.preimage (hφpm.sub hφ2m) using 1
    ext q
    simp [Function.uncurry, sub_eq_zero]
  have haeprod : ∀ᵐ q ∂(volume : Measure ℝ).prod volume,
      φp q.1 q.2 = φ2 q.1 q.2 := by
    rw [Measure.ae_prod_iff_ae_ae heqset, Measure.ae_ae_comm heqset]
    exact ae_of_all _ haeFull
  have h2 := pi_formula_two_sigma_two P W hW t ht
  unfold IsJointDensity at h2 ⊢
  rw [h2]
  apply withDensity_congr_ae
  filter_upwards [haeprod] with q hq
  dsimp [φp, φ2] at hq
  simpa [mul_assoc] using congrArg
    (fun z : ℝ => ENNReal.ofReal (gaussianPDFReal 0 t q.2 * z)) hq.symm

/-- The π-formula is a constructive joint density for `p = 2,3,4`, every
positive volatility, and every positive horizon. -/
theorem pi_formula_general
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W)
    (σ : ℝ) (T : ℝ≥0) (hσ : 0 < σ) (hT : 0 < T)
    (p : ℕ) (hp : p = 2 ∨ p = 3 ∨ p = 4) :
    IsJointDensity P W σ 0 T fun x y =>
      gaussianPDFReal 0 T y * (σ ^ 2)⁻¹ *
        piFormula p σ T (x * σ ^ 2) (y * σ) := by
  let τ := referenceTimeFromTwo σ T
  have hτ : 0 < τ := by
    simpa [τ] using referenceTimeFromTwo_pos hσ hT
  let φ₂ : ℝ → ℝ → ℝ := fun x y =>
    gaussianPDFReal 0 τ y * ((2 : ℝ) ^ 2)⁻¹ *
      piFormula p 2 τ (x * (2 : ℝ) ^ 2) (y * 2)
  have hφ₂ : IsJointDensity P W 2 0 τ φ₂ :=
    pi_formula_sigma_two P W hW τ hτ p hp
  have hmcond : Measurable (fun q : ℝ × ℝ =>
      ((2 : ℝ) ^ 2)⁻¹ * piFormula p 2 τ
        (q.1 * (2 : ℝ) ^ 2) (q.2 * 2)) :=
    piFormula_sigma_two_measurable p (τ : ℝ)
  have hm₂ : Measurable (fun q : ℝ × ℝ => ENNReal.ofReal (φ₂ q.1 q.2)) := by
    apply ENNReal.measurable_ofReal.comp
    have hg : Measurable (fun q : ℝ × ℝ => gaussianPDFReal 0 τ q.2) := by
      fun_prop
    dsimp [φ₂]
    convert hg.mul hmcond using 1
    funext q
    simp only [Pi.mul_apply]
    ring
  have hs := IsJointDensity_scaling_from_two_fixed
    P W hW hσ T φ₂ hφ₂ hm₂
  have hfun :
      (fun x y : ℝ =>
        (σ / 2) ^ 3 * φ₂ (σ ^ 2 / 4 * x) (σ / 2 * y)) =
      (fun x y =>
        gaussianPDFReal 0 T y * (σ ^ 2)⁻¹ *
          piFormula p σ T (x * σ ^ 2) (y * σ)) := by
    funext x y
    dsimp [φ₂]
    rw [gaussianPDFReal_referenceTimeFromTwo hσ T y,
      piFormula_sigma_covariant_fixed p σ T x y hσ]
    simp only [τ]
    field_simp [hσ.ne']
    ring_nf
  rwa [hfun] at hs

end Lyasoff2016
