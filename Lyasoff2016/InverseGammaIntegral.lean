/-
Normalization of the inverse-Gamma kernel used in the introductory density.
-/
module

public import Lyasoff2016.UpperGamma


@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/-- The inverse-Gamma kernel with integer shape is integrable on `(0, ∞)`. -/
theorem integrableOn_inv_pow_exp_neg_div
    {p : ℕ} (hp : 2 ≤ p) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => x ^ (-(p : ℤ)) * Real.exp (-c / x)) (Ioi 0) := by
  have hp' : -1 < (p : ℝ) - 2 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hGamma :
      IntegrableOn (fun y : ℝ => y ^ ((p : ℝ) - 2) * Real.exp (-(c * y))) (Ioi 0) := by
    have hbase :
        IntegrableOn (fun u : ℝ => Real.exp (-u) * u ^ ((p : ℝ) - 2)) (Ioi 0) := by
      simpa only [show (p : ℝ) - 1 - 1 = (p : ℝ) - 2 by ring] using
        (Real.GammaIntegral_convergent (show 0 < (p : ℝ) - 1 by linarith))
    have hscale := (integrableOn_Ioi_comp_mul_left_iff
      (fun u : ℝ => Real.exp (-u) * u ^ ((p : ℝ) - 2)) 0 hc).mpr
        (by simpa using hbase)
    refine IntegrableOn.congr_fun
      (hscale.const_mul (c ^ ((p : ℝ) - 2))⁻¹) (fun y hy => ?_) measurableSet_Ioi
    rw [Real.mul_rpow hc.le hy.le]
    field_simp [(Real.rpow_pos_of_pos hc _).ne']
  have hsubst := (integrableOn_Ioi_comp_rpow_iff
    (fun y : ℝ => y ^ ((p : ℝ) - 2) * Real.exp (-(c * y)))
    (show (-1 : ℝ) ≠ 0 by norm_num)).mpr hGamma
  refine hsubst.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hz : x ^ (-(p : ℤ)) = x ^ (-(p : ℝ)) := by
    rw [zpow_neg, zpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_neg (le_of_lt hx)]
  have hpow :
      x ^ ((-1 : ℝ) - 1) * (x ^ (-1 : ℝ)) ^ ((p : ℝ) - 2) =
        x ^ (-(p : ℝ)) := by
    rw [← Real.rpow_mul hx.le,
      show (-1 : ℝ) * ((p : ℝ) - 2) = 2 - p by ring,
      ← Real.rpow_add hx]
    congr 1
    ring
  simp only [abs_neg, abs_one, one_mul, smul_eq_mul]
  rw [← mul_assoc, hpow, ← hz]
  congr 1
  rw [Real.rpow_neg_one]
  field_simp

/-- The inverse-Gamma normalization integral for integer shape `p - 1`. -/
theorem integral_inv_pow_exp_neg_div
    {p : ℕ} (hp : 2 ≤ p) {c : ℝ} (hc : 0 < c) :
    ∫ x in Ioi (0 : ℝ), (x : ℝ) ^ (-(p : ℤ)) * Real.exp (-c / x)
      = ((p - 2).factorial : ℝ) / c ^ (p - 1) := by
  have hp' : 0 < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hpoint :
      ∀ x ∈ Ioi (0 : ℝ),
        x ^ (-(p : ℤ)) * Real.exp (-c / x) =
          (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) *
            ((x ^ (-1 : ℝ)) ^ ((p : ℝ) - 2) *
              Real.exp (-(c * x ^ (-1 : ℝ)))) := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hz : x ^ (-(p : ℤ)) = x ^ (-(p : ℝ)) := by
      rw [zpow_neg, zpow_natCast, ← Real.rpow_natCast,
        ← Real.rpow_neg (le_of_lt hx)]
    have hpow :
        x ^ ((-1 : ℝ) - 1) * (x ^ (-1 : ℝ)) ^ ((p : ℝ) - 2) =
          x ^ (-(p : ℝ)) := by
      rw [← Real.rpow_mul hx.le,
        show (-1 : ℝ) * ((p : ℝ) - 2) = 2 - p by ring,
        ← Real.rpow_add hx]
      congr 1
      ring
    rw [abs_neg, abs_one, one_mul, hz, ← mul_assoc, hpow]
    congr 1
    rw [Real.rpow_neg_one]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint]
  have hsubst := integral_comp_rpow_Ioi
    (g := fun y : ℝ => y ^ ((p : ℝ) - 2) * Real.exp (-(c * y)))
    (p := (-1 : ℝ)) (by norm_num)
  rw [show (∫ x in Ioi (0 : ℝ),
      (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) *
        ((x ^ (-1 : ℝ)) ^ ((p : ℝ) - 2) *
          Real.exp (-(c * x ^ (-1 : ℝ)))) =
      ∫ y in Ioi (0 : ℝ), y ^ ((p : ℝ) - 2) * Real.exp (-(c * y))) by
        simpa only [smul_eq_mul] using hsubst]
  rw [show (p : ℝ) - 2 = ((p : ℝ) - 1) - 1 by ring,
    Real.integral_rpow_mul_exp_neg_mul_Ioi hp' hc]
  have hcast : (p : ℝ) - 1 = ((p - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
  have hGamma : Real.Gamma ((p : ℝ) - 1) = ((p - 2).factorial : ℝ) := by
    rw [hcast]
    have hnat : p - 1 = (p - 2) + 1 := by omega
    rw [hnat]
    exact_mod_cast Real.Gamma_nat_eq_factorial (p - 2)
  rw [hGamma, hcast, Real.rpow_natCast]
  rw [div_eq_mul_inv]
  ring

/-- Laplace multiplication only shifts the inverse-Gamma scale parameter.
This is the one-dimensional `x` integral used after expanding (5.4). -/
theorem integrableOn_exp_neg_div_mul_inv_pow_exp_neg_div
    {p : ℕ} (hp : 2 ≤ p) {v c : ℝ} (hvc : 0 < v + c) :
    IntegrableOn
      (fun x : ℝ =>
        Real.exp (-v / x) * (x ^ (-(p : ℤ)) * Real.exp (-c / x)))
      (Ioi 0) := by
  refine (integrableOn_inv_pow_exp_neg_div hp hvc).congr_fun ?_ measurableSet_Ioi
  intro x _
  change x ^ (-(p : ℤ)) * Real.exp (-(v + c) / x) =
    Real.exp (-v / x) * (x ^ (-(p : ℤ)) * Real.exp (-c / x))
  have he : Real.exp (-v / x) * Real.exp (-c / x) =
      Real.exp (-(v + c) / x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← he]
  ring

/-- The shifted inverse-Gamma integral:
`∫₀∞ exp (-v/x) x⁻ᵖ exp (-c/x) dx = (p-2)! / (v+c)^(p-1)`. -/
theorem integral_exp_neg_div_mul_inv_pow_exp_neg_div
    {p : ℕ} (hp : 2 ≤ p) {v c : ℝ} (hvc : 0 < v + c) :
    ∫ x in Ioi (0 : ℝ),
        Real.exp (-v / x) * (x ^ (-(p : ℤ)) * Real.exp (-c / x))
      = ((p - 2).factorial : ℝ) / (v + c) ^ (p - 1) := by
  rw [show (∫ x in Ioi (0 : ℝ),
      Real.exp (-v / x) * (x ^ (-(p : ℤ)) * Real.exp (-c / x))) =
      ∫ x in Ioi (0 : ℝ), x ^ (-(p : ℤ)) * Real.exp (-(v + c) / x) by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    have he : Real.exp (-v / x) * Real.exp (-c / x) =
        Real.exp (-(v + c) / x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← he]
    ring]
  exact integral_inv_pow_exp_neg_div hp hvc

/-- Paper-shaped version of the shifted inverse-Gamma integral, using `1 / x^p`. -/
theorem integral_exp_neg_div_mul_one_div_pow_exp_neg_div
    {p : ℕ} (hp : 2 ≤ p) {v c : ℝ} (hvc : 0 < v + c) :
    ∫ x in Ioi (0 : ℝ),
        Real.exp (-v / x) * (1 / x ^ p * Real.exp (-c / x))
      = ((p - 2).factorial : ℝ) / (v + c) ^ (p - 1) := by
  rw [show (∫ x in Ioi (0 : ℝ),
      Real.exp (-v / x) * (1 / x ^ p * Real.exp (-c / x))) =
      ∫ x in Ioi (0 : ℝ),
        Real.exp (-v / x) * (x ^ (-(p : ℤ)) * Real.exp (-c / x)) by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [zpow_neg, zpow_natCast]
    field_simp]
  exact integral_exp_neg_div_mul_inv_pow_exp_neg_div hp hvc

/- The complex inverse-Gamma integral needed by the oscillatory `a = π/2`
kernel.  The positivity assumption is exactly the condition ensuring
exponential decay after the substitution `y = x⁻¹`. -/

private theorem integrableOn_pow_mul_cexp_neg
    (n : ℕ) {c : ℂ} (hc : 0 < c.re) :
    IntegrableOn (fun y : ℝ => (y : ℂ) ^ n * cexp (-c * y)) (Ioi 0) := by
  have hr := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (n : ℝ)) (p := (1 : ℝ)) (b := c.re) (by linarith) (by norm_num) hc
  refine hr.mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [norm_mul, norm_pow, norm_real, Complex.norm_exp]
  simp only [mul_re, neg_re, ofReal_re, ofReal_im, mul_zero, sub_zero,
    Real.rpow_one]
  rw [Real.norm_eq_abs, abs_of_pos hy, Real.rpow_natCast]

private theorem integral_pow_mul_cexp_neg
    (n : ℕ) {c : ℂ} (hc : 0 < c.re) :
    ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ n * cexp (-c * y) =
      (n.factorial : ℂ) / c ^ (n + 1) := by
  induction n with
  | zero =>
      simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add]
      rw [integral_exp_mul_complex_Ioi (a := -c) (by simpa using hc) 0]
      simp
  | succ n ih =>
      have hcn : c ≠ 0 := fun h => by
        subst c
        norm_num at hc
      let F : ℝ → ℂ := fun y => -(1 / c) * ((y : ℂ) ^ (n + 1) * cexp (-c * y))
      have hderiv : ∀ y ∈ Ici (0 : ℝ), HasDerivAt F
          ((y : ℂ) ^ (n + 1) * cexp (-c * y) -
            ((n + 1 : ℕ) : ℂ) / c * ((y : ℂ) ^ n * cexp (-c * y))) y := by
        intro y _
        dsimp [F]
        have hy : HasDerivAt (fun z : ℝ => (z : ℂ)) 1 y :=
          Complex.ofRealCLM.hasFDerivAt.hasDerivAt
        have he : HasDerivAt (fun z : ℝ => cexp (-c * z))
            (cexp (-c * y) * (-c)) y := by
          convert (hy.const_mul (-c)).cexp using 1; ring
        have hm := (hy.pow (n + 1)).mul he
        simp only [Pi.pow_apply, Nat.add_sub_cancel] at hm
        convert hm.const_mul (-(1 / c)) using 1
        field_simp [hcn]; ring
      have hfi : IntegrableOn (fun y : ℝ =>
          (y : ℂ) ^ (n + 1) * cexp (-c * y) -
            ((n + 1 : ℕ) : ℂ) / c * ((y : ℂ) ^ n * cexp (-c * y))) (Ioi 0) :=
        (integrableOn_pow_mul_cexp_neg (n + 1) hc).sub
          ((integrableOn_pow_mul_cexp_neg n hc).const_mul _)
      have hlim : Tendsto F atTop (𝓝 0) := by
        rw [Metric.tendsto_atTop]
        intro ε hε
        have hnorm := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
          ((n + 1 : ℕ) : ℝ) c.re hc
        rw [Metric.tendsto_atTop] at hnorm
        have hcst : 0 < ‖-(1 / c)‖ :=
          norm_pos_iff.mpr (neg_ne_zero.mpr (one_div_ne_zero hcn))
        obtain ⟨a, ha⟩ := hnorm (ε / ‖-(1 / c)‖) (div_pos hε hcst)
        refine ⟨max a 0, fun y hy => ?_⟩
        have hy0 : 0 ≤ y := le_trans (le_max_right _ _) hy
        have hay : a ≤ y := le_trans (le_max_left _ _) hy
        have hb := ha y hay
        rw [Real.dist_eq, sub_zero] at hb
        rw [dist_zero_right]
        dsimp [F]
        rw [norm_mul, norm_mul, norm_pow, norm_real, Complex.norm_exp]
        simp only [mul_re, neg_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
        rw [Real.norm_eq_abs, abs_of_nonneg hy0, ← Real.rpow_natCast]
        rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hy0 _) (Real.exp_pos _).le)] at hb
        simpa [mul_comm] using (lt_div_iff₀ hcst).mp hb
      have hzero : F 0 = 0 := by simp [F]
      have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hfi hlim
      rw [hzero, sub_zero] at hftc
      rw [integral_sub (integrableOn_pow_mul_cexp_neg (n + 1) hc)
        ((integrableOn_pow_mul_cexp_neg n hc).const_mul _),
        integral_const_mul, ih] at hftc
      apply (sub_eq_zero.mp hftc).trans
      push_cast
      field_simp [hcn]
      rw [Nat.factorial_succ]
      push_cast
      ring

/-- Complex inverse-Gamma normalization:
`∫₀∞ x⁻ᵖ exp (-c/x) dx = (p-2)! / c^(p-1)` for `0 < re c`. -/
theorem integral_inv_pow_cexp_neg_div
    {p : ℕ} (hp : 2 ≤ p) {c : ℂ} (hc : 0 < c.re) :
    ∫ x in Ioi (0 : ℝ), (1 : ℂ) / (x : ℂ) ^ p * cexp (-c / x) =
      ((p - 2).factorial : ℂ) / c ^ (p - 1) := by
  let k := p - 2
  have hpk : p = k + 2 := by omega
  have hpoint : ∀ x ∈ Ioi (0 : ℝ),
      (1 : ℂ) / (x : ℂ) ^ p * cexp (-c / x) =
        (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) •
          (((x ^ (-1 : ℝ) : ℝ) : ℂ) ^ (p - 2) *
            cexp (-c * (((x ^ (-1 : ℝ)) : ℝ) : ℂ))) := by
    intro x hx
    have hx0 : x ≠ 0 := hx.ne'
    have he : -c / (x : ℂ) = -c * ((x⁻¹ : ℝ) : ℂ) := by
      push_cast
      rw [div_eq_mul_inv]
    have hcoef :
        (1 : ℂ) / (x : ℂ) ^ p =
          (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) •
            (((x ^ (-1 : ℝ) : ℝ) : ℂ) ^ (p - 2)) := by
      simp only [abs_neg, abs_one, one_mul]
      rw [show (-1 : ℝ) - 1 = -2 by ring, Real.rpow_neg hx.le,
        Real.rpow_two, Real.rpow_neg_one, hpk, pow_add]
      push_cast
      rw [Algebra.smul_def]
      push_cast
      field_simp [hx0]
      rw [one_div, inv_pow]
      field_simp [hx0]
      rfl
    rw [he, hcoef]
    simp only [Real.rpow_neg_one]
    rw [smul_mul_assoc]
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint]
  rw [show (∫ x in Ioi (0 : ℝ),
      (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) •
        (((x ^ (-1 : ℝ) : ℝ) : ℂ) ^ (p - 2) *
          cexp (-c * (((x ^ (-1 : ℝ)) : ℝ) : ℂ)))) =
      ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (p - 2) * cexp (-c * y) by
        simpa using (integral_comp_rpow_Ioi
          (g := fun y : ℝ => (y : ℂ) ^ (p - 2) * cexp (-c * y))
          (p := (-1 : ℝ)) (by norm_num))]
  rw [integral_pow_mul_cexp_neg (p - 2) hc]
  congr 2
  omega

/-- Integrability companion to `integral_inv_pow_cexp_neg_div`. -/
theorem integrableOn_inv_pow_cexp_neg_div
    {p : ℕ} (hp : 2 ≤ p) {c : ℂ} (hc : 0 < c.re) :
    IntegrableOn
      (fun x : ℝ => (1 : ℂ) / (x : ℂ) ^ p * cexp (-c / x)) (Ioi 0) := by
  let k := p - 2
  have hpk : p = k + 2 := by omega
  have hs := (integrableOn_Ioi_comp_rpow_iff
    (fun y : ℝ => (y : ℂ) ^ (p - 2) * cexp (-c * y))
    (show (-1 : ℝ) ≠ 0 by norm_num)).mpr
      (integrableOn_pow_mul_cexp_neg (p - 2) hc)
  refine hs.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx0 : x ≠ 0 := hx.ne'
  have he : -c / (x : ℂ) = -c * ((x⁻¹ : ℝ) : ℂ) := by
    push_cast
    rw [div_eq_mul_inv]
  have hcoef :
      (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) •
          (((x ^ (-1 : ℝ) : ℝ) : ℂ) ^ (p - 2)) =
        (1 : ℂ) / (x : ℂ) ^ p := by
    simp only [abs_neg, abs_one, one_mul]
    rw [show (-1 : ℝ) - 1 = -2 by ring, Real.rpow_neg hx.le,
      Real.rpow_two, Real.rpow_neg_one, hpk, pow_add]
    push_cast
    rw [Algebra.smul_def]
    push_cast
    field_simp [hx0]
    rw [one_div, inv_pow]
    field_simp [hx0]
    rfl
  rw [he, ← hcoef]
  simp only [Real.rpow_neg_one]
  rw [smul_mul_assoc]

end Lyasoff2016
