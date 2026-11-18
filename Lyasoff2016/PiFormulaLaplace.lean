/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Constructive Laplace-transform facts for the π-formula.
-/
module

public import Lyasoff2016.PiFormula
public import Lyasoff2016.InverseGammaIntegral
public import Lyasoff2016.YorJointDensity


@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/-- The positive scale appearing after the two exponentials in the π-formula
are combined. -/
lemma piFormula_inverseGamma_scale_pos (v y u : ℝ) (hv : 0 ≤ v) :
    0 < v + (2 * (Real.exp y + 1) +
      4 * Real.exp (y / 2) * Real.cosh u) := by
  have he : 0 < Real.exp y := Real.exp_pos y
  have he2 : 0 < Real.exp (y / 2) := Real.exp_pos _
  have hcosh : 0 < Real.cosh u := Real.cosh_pos u
  positivity

/-- The inner `x`-integration in the paper's route from (5.4) to (5.3).
It is valid simultaneously for all integer orders `p ≥ 2`, hence in particular
for `p ∈ {2,3,4}`. -/
theorem piFormula_inner_x_integral
    {p : ℕ} (hp : 2 ≤ p) {v : ℝ} (hv : 0 ≤ v) (y u : ℝ) :
    ∫ x in Ioi (0 : ℝ), Real.exp (-v / x) *
        (1 / x ^ p *
          Real.exp (-(2 * (Real.exp y + 1) +
            4 * Real.exp (y / 2) * Real.cosh u) / x))
      = ((p - 2).factorial : ℝ) /
          (v + (2 * (Real.exp y + 1) +
            4 * Real.exp (y / 2) * Real.cosh u)) ^ (p - 1) := by
  exact integral_exp_neg_div_mul_one_div_pow_exp_neg_div hp
    (piFormula_inverseGamma_scale_pos v y u hv)

/-- Paper, display before (5.9a)/(5.9b) with `σ = 2`. -/
lemma gFun_two_re (t : ℝ) (ht : 0 < t) (u : ℝ) :
    (gFun 2 (t * 2 ^ 2) (u - I * π)).re =
      Real.exp (π ^ 2 / (2 * t)) / (4 * π) *
        (Real.exp (-u ^ 2 / (2 * t)) * Real.sin (π * u / t)) := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hπ0 : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hexp : (-2 * ((u : ℂ) - I * π) ^ 2 / ((t * 2 ^ 2 : ℝ) : ℂ)) =
      (((π ^ 2 - u ^ 2) / (2 * t) : ℝ) : ℂ) + ((π * u / t : ℝ) : ℂ) * I := by
    push_cast
    field_simp
    linear_combination (-(π : ℂ) ^ 2) * I_sq
  have hval : gFun 2 (t * 2 ^ 2) (u - I * π) =
      ((Real.exp ((π ^ 2 - u ^ 2) / (2 * t)) * Real.sin (π * u / t) / (4 * π) : ℝ) : ℂ) +
        ((-(Real.exp ((π ^ 2 - u ^ 2) / (2 * t)) * Real.cos (π * u / t) / (4 * π)) : ℝ) : ℂ) *
          I := by
    simp only [gFun]
    rw [hexp, Complex.exp_add, Complex.exp_mul_I, ← ofReal_exp, ← ofReal_cos, ← ofReal_sin]
    push_cast
    field_simp
    linear_combination (Complex.cos ((π : ℂ) * u / t)) * I_sq
  rw [hval]
  simp only [add_re, ofReal_re, re_ofReal_mul, I_re, mul_zero, add_zero]
  have : Real.exp ((π ^ 2 - u ^ 2) / (2 * t)) =
      Real.exp (π ^ 2 / (2 * t)) * Real.exp (-u ^ 2 / (2 * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this]; ring

/-- The real and imaginary parts of `g_{4t,2}` on the lower `π/2` edge.
This is the phase expansion used in the paper's cosine form (5.10a). -/
lemma gFun_two_re_half (t : ℝ) (ht : 0 < t) (u : ℝ) :
    (gFun 2 (t * 2 ^ 2) (u - I * (π / 2))).re =
        Real.exp (π ^ 2 / (8 * t)) / (4 * π) *
          (Real.exp (-u ^ 2 / (2 * t)) * Real.sin (π * u / (2 * t))) ∧
    (gFun 2 (t * 2 ^ 2) (u - I * (π / 2))).im =
        -(Real.exp (π ^ 2 / (8 * t)) / (4 * π) *
          (Real.exp (-u ^ 2 / (2 * t)) * Real.cos (π * u / (2 * t)))) := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hπ0 : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hexp :
      (-2 * ((u : ℂ) - I * ((π : ℂ) / 2)) ^ 2 /
          ((t * 2 ^ 2 : ℝ) : ℂ)) =
        ((((π ^ 2 / 4 - u ^ 2) / (2 * t) : ℝ) : ℂ) +
          ((π * u / (2 * t) : ℝ) : ℂ) * I) := by
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring
  have hval :
      gFun 2 (t * 2 ^ 2) (u - I * (π / 2)) =
        ((Real.exp ((π ^ 2 / 4 - u ^ 2) / (2 * t)) *
            Real.sin (π * u / (2 * t)) / (4 * π) : ℝ) : ℂ) +
          ((-(Real.exp ((π ^ 2 / 4 - u ^ 2) / (2 * t)) *
            Real.cos (π * u / (2 * t)) / (4 * π)) : ℝ) : ℂ) * I := by
    simp only [gFun]
    rw [hexp, Complex.exp_add, Complex.exp_mul_I, ← ofReal_exp, ← ofReal_cos,
      ← ofReal_sin]
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring
  have hsplit :
      Real.exp ((π ^ 2 / 4 - u ^ 2) / (2 * t)) =
        Real.exp (π ^ 2 / (8 * t)) * Real.exp (-u ^ 2 / (2 * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hval]
  simp only [add_re, add_im, ofReal_re, ofReal_im, re_ofReal_mul, im_ofReal_mul,
    I_re, I_im, mul_zero, mul_one, add_zero, zero_add]
  rw [hsplit]
  constructor <;> ring

/-- Algebraic core of Remark 5.1 (no sign restriction on `x`). -/
lemma remark_5_1_aux (t : ℝ≥0) (x y : ℝ) (ht : 0 < t) :
    gaussianPDFReal 0 t y * (2 ^ 2 : ℝ)⁻¹ * piFormula 2 2 t (x * 2 ^ 2) (y * 2) =
      yorDensity t x y := by
  have ht' : (0 : ℝ) < t := ht
  rw [piFormula]
  split_ifs with hxscaled
  rotate_left
  · have hx : x ≤ 0 := by nlinarith
    simpa using (yorDensity_zero_of_nonpos ht' hx y).symm
  unfold yorDensity theta
  rw [gaussianPDFReal_def]
  have hint : ∫ u in Ioi (0 : ℝ), Real.sinh u *
      (((Real.exp (-(4 / (x * 2 ^ 2)) * Real.exp (y * 2 / 2) * Real.cosh u) : ℝ) : ℂ) *
        gFun 2 ((t : ℝ) * 2 ^ 2) (u - I * π)).re =
      Real.exp (π ^ 2 / (2 * t)) / (4 * π) *
        ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * t)) *
          Real.exp (-(Real.exp y / x) * Real.cosh u) *
          Real.sinh u * Real.sin (π * u / t) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    have he : -(4 / (x * 2 ^ 2)) * Real.exp (y * 2 / 2) * Real.cosh u =
        -(Real.exp y / x) * Real.cosh u := by
      rw [show y * 2 / 2 = y by ring]; field_simp; norm_num
    simp only [re_ofReal_mul, gFun_two_re (t : ℝ) ht' u, he]
    ring
  rw [hint]
  have hs : √(2 * π ^ 3 * t) = π * √(2 * π * t) := by
    rw [show 2 * π ^ 3 * (t : ℝ) = π ^ 2 * (2 * π * t) by ring, Real.sqrt_mul (sq_nonneg π),
      Real.sqrt_sq Real.pi_pos.le]
  have hexp : Real.exp (-(y - 0) ^ 2 / (2 * t)) *
      Real.exp (y * 2 * (((2 : ℕ) : ℝ) - 1) / 2 + (y * 2) ^ 2 / (2 * ((t : ℝ) * 2 ^ 2)) -
        2 * (Real.exp (y * 2) + 1) / (x * 2 ^ 2)) =
      Real.exp y * Real.exp (-(1 + Real.exp (2 * y)) / (2 * x)) := by
    rw [← Real.exp_add, ← Real.exp_add, show y * 2 = 2 * y by ring]
    congr 1
    push_cast
    field_simp
    ring
  rw [hs]
  calc (√(2 * π * t))⁻¹ * Real.exp (-(y - 0) ^ 2 / (2 * t)) * (2 ^ 2 : ℝ)⁻¹ *
        (2 ^ 4 * (16 / (x * 2 ^ 2) ^ 2) *
          Real.exp (y * 2 * (((2 : ℕ) : ℝ) - 1) / 2 + (y * 2) ^ 2 / (2 * ((t : ℝ) * 2 ^ 2)) -
            2 * (Real.exp (y * 2) + 1) / (x * 2 ^ 2)) *
          (Real.exp (π ^ 2 / (2 * t)) / (4 * π) *
            ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * t)) *
              Real.exp (-(Real.exp y / x) * Real.cosh u) *
              Real.sinh u * Real.sin (π * u / t)))
      = (Real.exp (-(y - 0) ^ 2 / (2 * t)) *
          Real.exp (y * 2 * (((2 : ℕ) : ℝ) - 1) / 2 + (y * 2) ^ 2 / (2 * ((t : ℝ) * 2 ^ 2)) -
            2 * (Real.exp (y * 2) + 1) / (x * 2 ^ 2))) *
          ((√(2 * π * t))⁻¹ * (2 ^ 2 : ℝ)⁻¹ * (2 ^ 4 * (16 / (x * 2 ^ 2) ^ 2)) *
            (Real.exp (π ^ 2 / (2 * t)) / (4 * π) *
              ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * t)) *
                Real.exp (-(Real.exp y / x) * Real.cosh u) *
                Real.sinh u * Real.sin (π * u / t))) := by ring
    _ = _ := by
      rw [hexp]
      field_simp
      ring

/-- Remark 5.1: the order-two π-formula at `σ = 2` is Yor's density. -/
theorem remark_5_1 (t : ℝ≥0) (x y : ℝ) (ht : 0 < t) (_hx : 0 < x) :
    gaussianPDFReal 0 t y * (2 ^ 2 : ℝ)⁻¹ *
        piFormula 2 2 t (x * 2 ^ 2) (y * 2) =
      yorDensity t x y :=
  remark_5_1_aux t x y ht

/-- The scaled order-two π-formula is constructively a joint density at `σ = 2`. -/
theorem pi_formula_two_sigma_two
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (t : ℝ≥0) (ht : 0 < t) :
    IsJointDensity P W 2 0 t (fun x y =>
      gaussianPDFReal 0 t y * (2 ^ 2 : ℝ)⁻¹ * piFormula 2 2 t (x * 2 ^ 2) (y * 2)) := by
  have h := yor_joint_density P W hW t ht
  have hfun : (fun x y : ℝ =>
      gaussianPDFReal 0 t y * ((2 : ℝ) ^ 2)⁻¹ *
        piFormula 2 2 t (x * (2 : ℝ) ^ 2) (y * 2)) =
      fun x y => yorDensity t x y := by
    funext x y
    exact remark_5_1_aux t x y ht
  rwa [← hfun] at h

/-- At `(p, σ) = (2, 2)`, the scaled π-formula has the conditional `1/x`-Laplace
transform obtained from Yor's joint density. This includes the endpoint `v = 0`. -/
theorem piFormula_two_sigma_two_laplace
    (t : ℝ≥0) (ht : 0 < t) {v : ℝ} (hv : 0 ≤ v) (y : ℝ) :
    IntegrableOn
      (fun x => Real.exp (-v / x) *
        (2 ^ 2 : ℝ)⁻¹ * piFormula 2 2 t (x * 2 ^ 2) (y * 2))
      (Ioi 0) ∧
    ∫ x in Ioi (0 : ℝ), Real.exp (-v / x) *
        (2 ^ 2 : ℝ)⁻¹ * piFormula 2 2 t (x * 2 ^ 2) (y * 2) =
      (gaussianPDFReal 0 t y)⁻¹ *
        gaussianPDFReal 0 t (Real.arcosh (charA v y)) := by
  have hG : gaussianPDFReal 0 t y ≠ 0 := by
    rw [gaussianPDFReal_def]
    positivity
  have hfun : (fun x => Real.exp (-v / x) *
        (2 ^ 2 : ℝ)⁻¹ * piFormula 2 2 t (x * 2 ^ 2) (y * 2)) =
      fun x => (gaussianPDFReal 0 t y)⁻¹ *
        (Real.exp (-v / x) * yorDensity t x y) := by
    funext x
    rw [← remark_5_1_aux t x y ht]
    field_simp
  rw [hfun]
  rcases hv.eq_or_lt with rfl | hv
  · obtain ⟨M, _, hM⟩ := yorDensity_abs_bound t ht
    obtain ⟨_, hyor_int, _⟩ := hM y
    have harc : Real.arcosh (charA 0 y) = |y| := by
      rw [charA, zero_mul, add_zero]
      rcases le_total 0 y with hy | hy
      · rw [abs_of_nonneg hy, Real.arcosh_cosh hy]
      · rw [abs_of_nonpos hy, ← Real.cosh_neg y, Real.arcosh_cosh (neg_nonneg.mpr hy)]
    have hgauss :
        gaussianPDFReal 0 t (Real.arcosh (charA 0 y)) = gaussianPDFReal 0 t y := by
      rw [harc]
      simp only [gaussianPDFReal_def, sub_zero]
      rw [sq_abs]
    constructor
    · simp only [neg_zero, zero_div, Real.exp_zero, one_mul]
      change Integrable
        (fun x => (gaussianPDFReal 0 t y)⁻¹ * yorDensity t x y)
        (volume.restrict (Ioi 0))
      exact hyor_int.const_mul _
    · simp only [neg_zero, zero_div, Real.exp_zero, one_mul]
      rw [integral_const_mul, yorDensity_integral_x_eq_gaussian t ht y, hgauss]
  · have hyor := yorDensity_laplace_x t ht hv y
    constructor
    · exact hyor.1.const_mul _
    · rw [integral_const_mul, hyor.2]

/-- The second conjunct of `pi_formula` at `(p, σ) = (2, 2)` is already constructive. -/
theorem pi_formula_second_two_sigma_two
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (t : ℝ≥0) (ht : 0 < t) :
    IsJointDensity P W 2 0 t (fun x y =>
      gaussianPDFReal 0 t y * ((2 : ℝ) ^ 2)⁻¹ *
        piFormula 2 2 t (x * (2 : ℝ) ^ 2) (y * 2)) :=
  pi_formula_two_sigma_two P W hW t ht

end Lyasoff2016
