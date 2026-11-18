/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
# The bent-path identity for the Asian integrand `F`

The `u`-integral of `Re F_{t,σ,ν,k}(u,w)` in `asian_price_formula` can be computed along
the sech-bent contour `u ↦ u + i θ₀ sech u`:

  `∫₀^∞ Re F(u,w) du = ½ Re ∫_ℝ F(u + iθ₀ sech u, w) (1 + iθ₀ (sech)'(u)) du`,

for the entire extension `FfunC` of `F` in `u`, whenever the homotopy between the real line
and the bent contour is dominated by an integrable function (`BendDominated`).  Numerically
this bending removes the catastrophic cancellation of the paper's line (≈1e86 for Table 1;
see `scripts/table_cert_phase1_contour.py`).  No numerical value is asserted here.
-/
module

public import Lyasoff2016.Ffun
public import Lyasoff2016.ContourBend

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real ComplexConjugate

noncomputable section
namespace Lyasoff2016

/-! ### `SfunC k 4` is entire in `A` -/

private lemma integrableOn_sfun_weight {k : ℝ} (hk : 0 < k) :
    IntegrableOn (fun x : ℝ => (x - k) * x ^ (-(4 : ℤ))) (Ioi k) := by
  have hint : IntegrableOn (fun x : ℝ => x ^ (-3 : ℝ)) (Ioi k) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hk
  refine hint.mono' ((show Measurable fun x : ℝ => (x - k) * x ^ (-(4 : ℤ)) by fun_prop)
    |>.aestronglyMeasurable) (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_)
  have hx0 : 0 < x := hk.trans hx
  have hxk : 0 ≤ x - k := sub_nonneg.mpr (le_of_lt ‹x ∈ Ioi k›)

  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hxk (zpow_nonneg hx0.le _)),
    Real.rpow_neg hx0.le, zpow_neg, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h4 : x ^ (4 : ℤ) = x ^ 3 * x := by rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by rfl, zpow_natCast]; ring
  rw [h4, mul_inv, ← mul_assoc]
  have : (x - k) * (x ^ 3)⁻¹ * x⁻¹ = (x ^ 3)⁻¹ * ((x - k) / x) := by ring
  rw [this]
  have hq : (x - k) / x ≤ 1 := by rw [div_le_one hx0]; linarith
  have hp : 0 ≤ (x ^ 3)⁻¹ := by positivity
  nlinarith

lemma SfunC_four_hasDerivAt {k : ℝ} (hk : 0 < k) (A : ℂ) :
    HasDerivAt (fun B => SfunC k 4 B)
      (∫ x in Ioi k, (((x - k) * x ^ (-(4 : ℤ)) : ℝ) : ℂ) * (-(1 / (x : ℂ)) *
        Complex.exp (-A / x))) A := by
  set E : ℝ := Real.exp ((‖A‖ + 1) / k)
  let bound : ℝ → ℝ := fun x => (x - k) * x ^ (-(4 : ℤ)) * (1 / k * E)
  have hwint := integrableOn_sfun_weight hk
  have hbint : Integrable bound (volume.restrict (Ioi k)) := hwint.mul_const _
  have key : ∀ x ∈ Ioi k, ∀ B ∈ Metric.ball A 1,
      ‖(((x - k) * x ^ (-(4 : ℤ)) : ℝ) : ℂ) * (-(1 / (x : ℂ)) * Complex.exp (-B / x))‖ ≤
        bound x := by
    intro x hx B hB
    have hx0 : 0 < x := hk.trans hx
    have hxk : 0 ≤ x - k := by linarith [(show k < x from hx)]
    have hw : 0 ≤ (x - k) * x ^ (-(4 : ℤ)) := mul_nonneg hxk (zpow_nonneg hx0.le _)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw, norm_neg,
      Complex.norm_exp]
    have h1 : ‖(1 / (x : ℂ))‖ ≤ 1 / k := by
      rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
      exact one_div_le_one_div_of_le hk (le_of_lt hx)
    have hBn : ‖B‖ ≤ ‖A‖ + 1 := by
      have := norm_le_norm_add_norm_sub' B A
      have hd : ‖B - A‖ < 1 := by simpa [dist_eq_norm] using hB
      linarith
    have h2 : Real.exp ((-B / (x : ℂ)).re) ≤ E := by
      apply Real.exp_le_exp.2
      have hre : (-B / (x : ℂ)).re = -B.re / x := by
        simp [Complex.div_ofReal_re]
      rw [hre]
      have : -B.re ≤ ‖A‖ + 1 := by
        have := Complex.abs_re_le_norm B
        have := neg_abs_le B.re
        linarith [abs_le.1 (le_refl |B.re|)]
      have hpos : 0 ≤ ‖A‖ + 1 := by positivity
      calc -B.re / x ≤ (‖A‖ + 1) / x := by gcongr
        _ ≤ (‖A‖ + 1) / k := div_le_div_of_nonneg_left hpos hk (le_of_lt hx)
    exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by positivity) (by positivity)) hw
  have hmeasF : ∀ B : ℂ, AEStronglyMeasurable
      (fun x : ℝ => (((x - k) * x ^ (-(4 : ℤ)) : ℝ) : ℂ) * Complex.exp (-B / x))
      (volume.restrict (Ioi k)) := fun B =>
    (show Measurable fun x : ℝ =>
      (((x - k) * x ^ (-(4 : ℤ)) : ℝ) : ℂ) * Complex.exp (-B / x) by fun_prop).aestronglyMeasurable
  have hFint : Integrable
      (fun x : ℝ => (((x - k) * x ^ (-(4 : ℤ)) : ℝ) : ℂ) * Complex.exp (-A / x))
      (volume.restrict (Ioi k)) := by
    refine (hwint.mul_const E).mono' (hmeasF A)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_)
    have hx0 : 0 < x := hk.trans hx
    have hw : 0 ≤ (x - k) * x ^ (-(4 : ℤ)) :=
      mul_nonneg (by linarith [(show k < x from hx)]) (zpow_nonneg hx0.le _)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw, Complex.norm_exp]
    gcongr
    apply Real.exp_le_exp.2
    rw [show (-A / (x : ℂ)).re = -A.re / x by simp [Complex.div_ofReal_re]]
    have : -A.re ≤ ‖A‖ + 1 := by
      have := Complex.abs_re_le_norm A; have := neg_abs_le A.re; linarith
    calc -A.re / x ≤ (‖A‖ + 1) / x := by gcongr
      _ ≤ (‖A‖ + 1) / k := div_le_div_of_nonneg_left (by positivity) hk (le_of_lt hx)
  have hmain := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi k))
    (F := fun B x => (((x - k) * x ^ (-(4 : ℤ)) : ℝ) : ℂ) * Complex.exp (-B / x))
    (F' := fun B x => (((x - k) * x ^ (-(4 : ℤ)) : ℝ) : ℂ) * (-(1 / (x : ℂ)) *
      Complex.exp (-B / x)))
    (x₀ := A) (bound := bound) (Metric.ball_mem_nhds A one_pos)
    (Eventually.of_forall hmeasF) hFint
    ((show Measurable fun x : ℝ => (((x - k) * x ^ (-(4 : ℤ)) : ℝ) : ℂ) *
      (-(1 / (x : ℂ)) * Complex.exp (-A / x)) by fun_prop).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx B hB => key x hx B hB) hbint
    (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx B _ => by
      have hd : HasDerivAt (fun B : ℂ => -B / (x : ℂ)) (-(1 / (x : ℂ))) B := by
        have := ((hasDerivAt_id B).neg).div_const (x : ℂ)
        simpa [neg_div] using this
      exact (hd.cexp.const_mul _).congr_deriv (by ring)))
  simpa [SfunC] using hmain.2

lemma differentiable_SfunC_four {k : ℝ} (hk : 0 < k) : Differentiable ℂ (fun A => SfunC k 4 A) :=
  fun A => (SfunC_four_hasDerivAt hk A).differentiableAt

lemma SfunC_conj (k : ℝ) (p : ℕ) (A : ℂ) : SfunC k p (conj A) = conj (SfunC k p A) := by
  simp only [SfunC]
  rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, map_div₀]

/-! ### The entire extension of `F` in `u` -/

/-- `A(z,w)` for complex `z`. -/
def AfunC (σ ν t w : ℝ) (z : ℂ) : ℂ :=
  (2 * w ^ 2 * Real.exp (ν * t) + 4 * Complex.I * w * Real.exp (ν * t / 2) * Complex.sinh z + 2) /
    σ ^ 2

/-- The `u`-independent real coefficient of `C(u,w)` for `p = 4`. -/
def cfunCoef (σ ν t w : ℝ) : ℝ :=
  8 * √2 * σ ^ (-2 * ((4 : ℕ) : ℤ) + 2) * w ^ (((4 : ℕ) : ℤ) - 1) *
    Real.exp (ν * ((4 : ℕ) : ℝ) * t / 2 - ν * t / 2) / √(π * t)

/-- Entire extension of `F_{t,σ,ν,k}(·, w)` to complex `u`. -/
def FfunC (σ ν t k w : ℝ) (z : ℂ) : ℂ :=
  (Bfun σ ν t w : ℂ) * ((cfunCoef σ ν t w : ℂ) * Complex.cosh z * Complex.I) *
    gFour (σ ^ 2 * t) (z - Complex.I * (π / 2)) * SfunC k 4 (AfunC σ ν t w z)

lemma Cfun_four_eq (σ ν t u w : ℝ) :
    Cfun 4 σ ν t u w = (cfunCoef σ ν t w : ℂ) * Complex.cosh (u : ℂ) * Complex.I := by
  rw [← Complex.ofReal_cosh]
  simp only [Cfun, cfunCoef]
  push_cast
  ring

lemma FfunC_ofReal (σ ν t k w u : ℝ) : FfunC σ ν t k w (u : ℂ) = Ffun σ ν t k u w := by
  have hA : AfunC σ ν t w (u : ℂ) = Afun σ ν t u w := by
    simp only [AfunC, Afun, ← Complex.ofReal_sinh]
  simp only [FfunC, Ffun, hA, Cfun_four_eq]

lemma differentiable_FfunC (σ ν t w : ℝ) {k : ℝ} (hk : 0 < k) :
    Differentiable ℂ (FfunC σ ν t k w) := by
  have hg : Differentiable ℂ (gFour (σ ^ 2 * t)) :=
    (gFun.four_contDiff (σ ^ 2 * t)).differentiable (by simp)
  have hS := differentiable_SfunC_four hk
  have hA : Differentiable ℂ (AfunC σ ν t w) := by unfold AfunC; fun_prop
  unfold FfunC
  have h1 : Differentiable ℂ fun z : ℂ => gFour (σ ^ 2 * t) (z - Complex.I * (π / 2)) :=
    hg.comp (by fun_prop)
  have h2 : Differentiable ℂ fun z => SfunC k 4 (AfunC σ ν t w z) := hS.comp hA
  fun_prop

lemma FfunC_neg_ofReal (σ ν t k w u : ℝ) :
    FfunC σ ν t k w (-(u : ℂ)) = conj (FfunC σ ν t k w (u : ℂ)) := by
  have hA : AfunC σ ν t w (-(u : ℂ)) = conj (AfunC σ ν t w (u : ℂ)) := by
    simp only [AfunC, Complex.sinh_neg, map_div₀, map_add, map_mul, map_pow, map_ofNat,
      Complex.conj_ofReal, Complex.conj_I, ← Complex.ofReal_sinh]
    ring
  have hg : gFour (σ ^ 2 * t) (-(u : ℂ) - Complex.I * (π / 2)) =
      -conj (gFour (σ ^ 2 * t) ((u : ℂ) - Complex.I * (π / 2))) := by
    have he := gFun.four_even (σ ^ 2 * t) ((u : ℂ) + Complex.I * (π / 2))
    have hc := gFun.four_conj (σ ^ 2 * t) ((u : ℂ) - Complex.I * (π / 2))
    have h1 : -(u : ℂ) - Complex.I * (π / 2) = -((u : ℂ) + Complex.I * (π / 2)) := by ring
    have h2 : conj ((u : ℂ) - Complex.I * (π / 2)) = (u : ℂ) + Complex.I * (π / 2) := by
      simp only [map_sub, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I,
        map_ofNat]
      ring

    rw [h2] at hc
    simp only [gFour]
    rw [h1, he, hc]
  simp only [FfunC, hA, hg, SfunC_conj, Complex.cosh_neg, map_mul, Complex.conj_ofReal,
    Complex.conj_I, ← Complex.ofReal_cosh]
  ring

/-! ### The sech bend -/

/-- Height of the sech-bent contour: `θ₀ sech u`. -/
def sechBend (θ₀ : ℝ) (u : ℝ) : ℝ := θ₀ * (Real.cosh u)⁻¹

/-- Derivative of `sechBend θ₀`. -/
def sechBend' (θ₀ : ℝ) (u : ℝ) : ℝ := θ₀ * (-(Real.sinh u) / Real.cosh u ^ 2)

lemma sechBend_hasDerivAt (θ₀ u : ℝ) : HasDerivAt (sechBend θ₀) (sechBend' θ₀ u) u := by
  have h := (Real.hasDerivAt_cosh u).inv (Real.cosh_pos u).ne'
  exact (h.const_mul θ₀).congr_deriv (by simp [sechBend'])

lemma continuous_sechBend' (θ₀ : ℝ) : Continuous (sechBend' θ₀) := by
  unfold sechBend'
  exact continuous_const.mul ((Real.continuous_sinh.neg).div (Real.continuous_cosh.pow 2)
    fun u => pow_ne_zero 2 (Real.cosh_pos u).ne')

/-- The homotopy from `ℝ` to the graph of `θ` is dominated by one integrable function. -/
def BendDominated (f : ℂ → ℂ) (θ θ' : ℝ → ℝ) : Prop :=
  ∃ g : ℝ → ℝ, Integrable g ∧
    (∀ s ∈ Icc (0 : ℝ) 1, ∀ u, ‖bendF f θ θ' s u‖ ≤ g u) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, ∀ u, ‖bendH f θ s u‖ ≤ g u) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, ∀ u, ‖bendD f θ θ' s u‖ ≤ g u)

/-- **Bent-path identity** for the Asian integrand: for `k > 0`, if the homotopy between the
real `u`-line and the sech-bent contour `u + iθ₀ sech u` is dominated (`BendDominated`), then
`∫₀^∞ Re F(u,w) du = ½ Re ∫_ℝ F(u + iθ₀ sech u, w) (1 + iθ₀ sech'(u)) du`. -/
theorem integral_Ioi_re_Ffun_eq_sechBend (σ ν t k w θ₀ : ℝ) (hk : 0 < k)
    (hdom : BendDominated (FfunC σ ν t k w) (sechBend θ₀) (sechBend' θ₀)) :
    ∫ u in Ioi (0 : ℝ), (Ffun σ ν t k u w).re =
      (1 / 2) * (∫ u : ℝ, FfunC σ ν t k w ((u : ℂ) + (sechBend θ₀ u : ℂ) * Complex.I) *
        (1 + (sechBend' θ₀ u : ℂ) * Complex.I)).re := by
  obtain ⟨g, hg, hF, hH, hD⟩ := hdom
  have hbend := integral_eq_integral_bend (differentiable_FfunC σ ν t w hk)
    (sechBend_hasDerivAt θ₀) (continuous_sechBend' θ₀) hg hF hH hD
  rw [← hbend]
  -- integrability on the real line (the `s = 0` bound)
  have hint : Integrable (fun u : ℝ => FfunC σ ν t k w (u : ℂ)) := by
    refine hg.mono' ?_ (ae_of_all _ fun u => ?_)
    · exact ((differentiable_FfunC σ ν t w hk).continuous.comp
        Complex.continuous_ofReal).aestronglyMeasurable
    · simpa [bendF, bendPt] using hF 0 ⟨le_rfl, zero_le_one⟩ u
  have hre : (∫ u : ℝ, FfunC σ ν t k w (u : ℂ)).re =
      ∫ u : ℝ, (FfunC σ ν t k w (u : ℂ)).re := (integral_re hint).symm
  rw [hre]
  have heven : ∀ u : ℝ, (FfunC σ ν t k w (u : ℂ)).re = (Ffun σ ν t k |u| w).re := by
    intro u
    rcases le_total 0 u with hu | hu
    · rw [abs_of_nonneg hu, FfunC_ofReal]
    · rw [abs_of_nonpos hu, ← FfunC_ofReal, Complex.ofReal_neg, FfunC_neg_ofReal,
        Complex.conj_re]
  simp_rw [heven]
  rw [integral_comp_abs (f := fun u => (Ffun σ ν t k u w).re)]
  ring

end Lyasoff2016
