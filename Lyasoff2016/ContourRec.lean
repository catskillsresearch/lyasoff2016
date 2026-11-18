/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
The contour equation (5.3) for p = 3, 4: reduction to p = 2 by integration by parts along the
lower edge u ↦ u − ia, using g_{t,p}' = −4 sinh · g_{t,p−1}.
-/
module

public import Lyasoff2016.ContourTwo


@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real Interval

noncomputable section
namespace Lyasoff2016

/- Paper: p. 1082–1085, (5.7)–(5.8).
   Plain recap: the functions g_{t,p} of (5.8) satisfy g_{t,3}' = −4 sinh · g_{t,2} and
   g_{t,4}' = −4 sinh · g_{t,3} (this is what makes the residue recipe (5.7) produce (5.5)).
   Along the lower edge z = u − ia, with D = cosh z − cosh y,
     d/du [ g_{t,p}(z) / D^{p−2} ] = −4 g_{t,p−1}(z) sinh z / D^{p−2}
                                      − (p−2) g_{t,p}(z) sinh z / D^{p−1},
   and g_{t,p}(z) / D^{p−2} → 0 as u → ±∞ (cerf is bounded on horizontal lines and
   |D| ≥ cosh u when cos a ≤ 0).  Integrating over ℝ gives
     ∫ (5.3)-integrand for p = −(4/(p−2)) ∫ (5.3)-integrand for p−1,
   which is the recursion (−4)^{p−2}/(p−2)! of the right-hand side of (5.3). -/
namespace ContourRec

open ContourTwo

/-! ### `cerf` is bounded on horizontal lines -/

lemma cerf_bdd_line (β : ℝ) : ∃ C : ℝ, ∀ x : ℝ, ‖cerf (x + β * I)‖ ≤ C := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => cerf (x + β * I))
      ((2 / Real.sqrt Real.pi : ℂ) * cexp (-((x : ℂ) + β * I) ^ 2)) x := by
    intro x
    have h := (cerf.hasDerivAt ((x : ℂ) + β * I)).comp_add_const (x : ℂ) (β * I)
    exact h.comp_ofReal
  have hcont : Continuous fun x : ℝ =>
      (2 / Real.sqrt Real.pi : ℂ) * cexp (-((x : ℂ) + β * I) ^ 2) := by fun_prop
  have hnorm : ∀ s : ℝ, ‖(2 / Real.sqrt Real.pi : ℂ) * cexp (-((s : ℂ) + β * I) ^ 2)‖ =
      2 / √π * Real.exp (β ^ 2) * Real.exp (-1 * s ^ 2) := by
    intro s
    have h2 : ‖(2 / Real.sqrt Real.pi : ℂ)‖ = 2 / √π := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      simp
    have hre : (-((s : ℂ) + β * I) ^ 2).re = β ^ 2 + -1 * s ^ 2 := by
      simp [pow_two]
      ring
    rw [norm_mul, h2, Complex.norm_exp, hre, Real.exp_add, mul_assoc]
  have hGint : Integrable fun s : ℝ => 2 / √π * Real.exp (β ^ 2) * Real.exp (-1 * s ^ 2) :=
    (integrable_exp_neg_mul_sq one_pos).const_mul _
  refine ⟨‖cerf (β * I)‖ + ∫ s : ℝ, 2 / √π * Real.exp (β ^ 2) * Real.exp (-1 * s ^ 2),
    fun x => ?_⟩
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := x)
    (fun s _ => hderiv s) (hcont.intervalIntegrable _ _)
  have hb : ‖∫ s in (0 : ℝ)..x, (2 / Real.sqrt Real.pi : ℂ) * cexp (-((s : ℂ) + β * I) ^ 2)‖ ≤
      ∫ s : ℝ, 2 / √π * Real.exp (β ^ 2) * Real.exp (-1 * s ^ 2) := by
    calc _ ≤ ∫ s in Ι 0 x, ‖(2 / Real.sqrt Real.pi : ℂ) * cexp (-((s : ℂ) + β * I) ^ 2)‖ :=
          intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ = ∫ s in Ι 0 x, 2 / √π * Real.exp (β ^ 2) * Real.exp (-1 * s ^ 2) := by
          simp_rw [hnorm]
      _ ≤ _ := setIntegral_le_integral hGint (Eventually.of_forall fun s => by positivity)
  have hx : cerf (x + β * I) = cerf (β * I) +
      ∫ s in (0 : ℝ)..x, (2 / Real.sqrt Real.pi : ℂ) * cexp (-((s : ℂ) + β * I) ^ 2) := by
    rw [hFTC]; simp
  rw [hx]
  exact (norm_add_le _ _).trans (add_le_add le_rfl hb)

lemma cerf_affine_bdd (t m d a : ℝ) :
    ∃ C : ℝ, ∀ u : ℝ, ‖cerf (((t : ℂ) + (m : ℂ) * (u - I * a)) / (d : ℂ))‖ ≤ C := by
  obtain ⟨C, hC⟩ := cerf_bdd_line (-(m * a) / d)
  refine ⟨C, fun u => ?_⟩
  have e : ((t : ℂ) + (m : ℂ) * (u - I * a)) / (d : ℂ) =
      (((t + m * u) / d : ℝ) : ℂ) + ((-(m * a) / d : ℝ) : ℂ) * I := by push_cast; ring
  rw [e]
  exact hC _

/-! ### Bounds along the lower edge `u ↦ u − ia` -/

lemma line_re (u a : ℝ) : ((u : ℂ) - I * a).re = u := by simp

lemma line_im (u a : ℝ) : ((u : ℂ) - I * a).im = -a := by simp

lemma norm_sinh_line_le (u a : ℝ) : ‖Complex.sinh ((u : ℂ) - I * a)‖ ≤ Real.cosh u := by
  have h := norm_sinh_le_cosh ((u : ℂ) - I * a)
  rwa [line_re] at h

lemma norm_cosh_line_le' (u a : ℝ) : ‖Complex.cosh ((u : ℂ) - I * a)‖ ≤ Real.cosh u := by
  have h := norm_cosh_le_cosh ((u : ℂ) - I * a)
  rwa [line_re] at h

/-- `|cosh(u − ia) − cosh y| ≥ cosh u` when `cos a ≤ 0`. -/
lemma cosh_le_norm_den {a : ℝ} (hc : Real.cos a ≤ 0) (y u : ℝ) :
    Real.cosh u ≤ ‖Complex.cosh ((u : ℂ) - I * a) - Complex.cosh y‖ := by
  obtain ⟨hre, him⟩ := cosh_re_im ((u : ℂ) - I * a)
  rw [line_re, line_im] at hre him
  have hDre : (Complex.cosh ((u : ℂ) - I * a) - Complex.cosh y).re =
      Real.cosh u * Real.cos a - Real.cosh y := by
    rw [Complex.sub_re, hre, Real.cos_neg, ← Complex.ofReal_cosh, Complex.ofReal_re]
  have hDim : (Complex.cosh ((u : ℂ) - I * a) - Complex.cosh y).im =
      -(Real.sinh u * Real.sin a) := by
    rw [Complex.sub_im, him, Real.sin_neg, ← Complex.ofReal_cosh, Complex.ofReal_im]
    ring
  refine (pow_le_pow_iff_left₀ (Real.cosh_pos _).le (norm_nonneg _) two_ne_zero).1 ?_
  rw [Complex.sq_norm, Complex.normSq_apply, hDre, hDim]
  have hsc : Real.cosh u ^ 2 - Real.sinh u ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq u
  have hcs : Real.sin a ^ 2 + Real.cos a ^ 2 = 1 := Real.sin_sq_add_cos_sq a
  have hC : 0 < Real.cosh u := Real.cosh_pos u
  have hY : 1 ≤ Real.cosh y := Real.one_le_cosh y
  have hS : Real.sinh u ^ 2 * Real.sin a ^ 2 = (Real.cosh u ^ 2 - 1) * (1 - Real.cos a ^ 2) := by
    rw [show Real.sinh u ^ 2 = Real.cosh u ^ 2 - 1 by linarith,
      show Real.sin a ^ 2 = 1 - Real.cos a ^ 2 by linarith]
  have h1 : 0 ≤ -(Real.cosh u * Real.cos a) * Real.cosh y :=
    mul_nonneg (neg_nonneg.2 (mul_nonpos_of_nonneg_of_nonpos hC.le hc)) (by linarith)
  have hY2 : 1 ≤ Real.cosh y ^ 2 := by nlinarith
  nlinarith [hS, h1, hY2, sq_nonneg (Real.cos a)]

lemma den_ne_zero {a : ℝ} (hc : Real.cos a ≤ 0) (y u : ℝ) :
    Complex.cosh ((u : ℂ) - I * a) - Complex.cosh y ≠ 0 :=
  norm_pos_iff.1 ((Real.cosh_pos u).trans_le (cosh_le_norm_den hc y u))

lemma bound_aux {N C c d : ℝ} (m : ℕ) (hc : 0 < c) (hcd : c ≤ d) (hN : N ≤ C * c ^ m)
    (hC : 0 ≤ C) : N / d ^ (m + 1) ≤ C * c⁻¹ := by
  calc N / d ^ (m + 1) ≤ (C * c ^ m) / c ^ (m + 1) :=
        div_le_div₀ (by positivity) hN (by positivity) (pow_le_pow_left₀ hc.le hcd _)
    _ = C * c⁻¹ := by
        rw [pow_succ]
        field_simp

lemma norm_gFun_three_line_le (t a : ℝ) :
    ∃ C : ℝ, ∀ u : ℝ, ‖gFun 3 t (u - I * a)‖ ≤ C := by
  obtain ⟨C1, hC1⟩ := cerf_affine_bdd t 4 (2 * √(2 * t)) a
  obtain ⟨C2, hC2⟩ := cerf_affine_bdd t (-4) (2 * √(2 * t)) a
  refine ⟨‖(Real.exp (t / 8) : ℂ) * (√t / (4 * I * √(2 * π)))‖ * (C1 + C2), fun u => ?_⟩
  have h1 : ‖cerf (((t : ℂ) + 4 * (u - I * a)) / (2 * √(2 * t)))‖ ≤ C1 := by
    have e : ((t : ℂ) + 4 * (u - I * a)) / (2 * √(2 * t)) =
        ((t : ℂ) + ((4 : ℝ) : ℂ) * (u - I * a)) / ((2 * √(2 * t) : ℝ) : ℂ) := by
      push_cast; ring
    rw [e]; exact hC1 u
  have h2 : ‖cerf (((t : ℂ) - 4 * (u - I * a)) / (2 * √(2 * t)))‖ ≤ C2 := by
    have e : ((t : ℂ) - 4 * (u - I * a)) / (2 * √(2 * t)) =
        ((t : ℂ) + ((-4 : ℝ) : ℂ) * (u - I * a)) / ((2 * √(2 * t) : ℝ) : ℂ) := by
      push_cast; ring
    rw [e]; exact hC2 u
  rw [gFun.three_apply, norm_mul]
  exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add h1 h2)) (norm_nonneg _)

lemma norm_gFun_four_line_le (t a : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, ‖gFun 4 t (u - I * a)‖ ≤ C * Real.cosh u := by
  obtain ⟨C1, hC1⟩ := cerf_affine_bdd t 4 (2 * √(2 * t)) a
  obtain ⟨C2, hC2⟩ := cerf_affine_bdd t (-4) (2 * √(2 * t)) a
  obtain ⟨D1, hD1⟩ := cerf_affine_bdd t 2 (√(2 * t)) a
  obtain ⟨D2, hD2⟩ := cerf_affine_bdd t (-2) (√(2 * t)) a
  have hC10 : 0 ≤ C1 := (norm_nonneg _).trans (hC1 0)
  have hC20 : 0 ≤ C2 := (norm_nonneg _).trans (hC2 0)
  have hD10 : 0 ≤ D1 := (norm_nonneg _).trans (hD1 0)
  have hD20 : 0 ≤ D2 := (norm_nonneg _).trans (hD2 0)
  refine ⟨‖(Real.exp (t / 2) : ℂ) * (√t / (2 * I * √(2 * π)))‖ * (D1 + D2) +
    ‖(Real.exp (t / 8) : ℂ)‖ * ‖((√t : ℝ) : ℂ) / (I * √(2 * π))‖ * (C1 + C2),
    by positivity, fun u => ?_⟩
  have h1 : ‖cerf (((t : ℂ) + 4 * (u - I * a)) / (2 * √(2 * t)))‖ ≤ C1 := by
    have e : ((t : ℂ) + 4 * (u - I * a)) / (2 * √(2 * t)) =
        ((t : ℂ) + ((4 : ℝ) : ℂ) * (u - I * a)) / ((2 * √(2 * t) : ℝ) : ℂ) := by
      push_cast; ring
    rw [e]; exact hC1 u
  have h2 : ‖cerf (((t : ℂ) - 4 * (u - I * a)) / (2 * √(2 * t)))‖ ≤ C2 := by
    have e : ((t : ℂ) - 4 * (u - I * a)) / (2 * √(2 * t)) =
        ((t : ℂ) + ((-4 : ℝ) : ℂ) * (u - I * a)) / ((2 * √(2 * t) : ℝ) : ℂ) := by
      push_cast; ring
    rw [e]; exact hC2 u
  have h3 : ‖cerf (((t : ℂ) + 2 * (u - I * a)) / √(2 * t))‖ ≤ D1 := by
    have e : ((t : ℂ) + 2 * (u - I * a)) / √(2 * t) =
        ((t : ℂ) + ((2 : ℝ) : ℂ) * (u - I * a)) / ((√(2 * t) : ℝ) : ℂ) := by
      push_cast; ring
    rw [e]; exact hD1 u
  have h4 : ‖cerf (((t : ℂ) - 2 * (u - I * a)) / √(2 * t))‖ ≤ D2 := by
    have e : ((t : ℂ) - 2 * (u - I * a)) / √(2 * t) =
        ((t : ℂ) + ((-2 : ℝ) : ℂ) * (u - I * a)) / ((√(2 * t) : ℝ) : ℂ) := by
      push_cast; ring
    rw [e]; exact hD2 u
  have hcosh := norm_cosh_line_le' u a
  have hone : 1 ≤ Real.cosh u := Real.one_le_cosh u
  have hA : ‖(Real.exp (t / 2) : ℂ) * (√t / (2 * I * √(2 * π))) *
      (cerf (((t : ℂ) + 2 * (u - I * a)) / √(2 * t)) +
        cerf (((t : ℂ) - 2 * (u - I * a)) / √(2 * t)))‖ ≤
      ‖(Real.exp (t / 2) : ℂ) * (√t / (2 * I * √(2 * π)))‖ * (D1 + D2) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add h3 h4)) (norm_nonneg _)
  have hB : ‖(Real.exp (t / 8) : ℂ) * Complex.cosh ((u : ℂ) - I * a) * (√t / (I * √(2 * π))) *
      (cerf (((t : ℂ) + 4 * (u - I * a)) / (2 * √(2 * t))) +
        cerf (((t : ℂ) - 4 * (u - I * a)) / (2 * √(2 * t))))‖ ≤
      ‖(Real.exp (t / 8) : ℂ)‖ * Real.cosh u * ‖((√t : ℝ) : ℂ) / (I * √(2 * π))‖ * (C1 + C2) := by
    rw [norm_mul, norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcosh (norm_nonneg _)) (norm_nonneg _))
      ((norm_add_le _ _).trans (add_le_add h1 h2)) (norm_nonneg _) (by positivity)
  rw [gFun.four_apply]
  have hK : 0 ≤ ‖(Real.exp (t / 2) : ℂ) * (√t / (2 * I * √(2 * π)))‖ * (D1 + D2) := by
    positivity
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ ‖(Real.exp (t / 2) : ℂ) * (√t / (2 * I * √(2 * π)))‖ * (D1 + D2) +
          ‖(Real.exp (t / 8) : ℂ)‖ * Real.cosh u * ‖((√t : ℝ) : ℂ) / (I * √(2 * π))‖ *
            (C1 + C2) := add_le_add hA hB
    _ ≤ ‖(Real.exp (t / 2) : ℂ) * (√t / (2 * I * √(2 * π)))‖ * (D1 + D2) * Real.cosh u +
          ‖(Real.exp (t / 8) : ℂ)‖ * Real.cosh u * ‖((√t : ℝ) : ℂ) / (I * √(2 * π))‖ *
            (C1 + C2) := by
        have := mul_le_mul_of_nonneg_left hone hK
        linarith
    _ = _ := by ring

/-! ### Integrability of the integrands for `p = 3, 4` -/

lemma integrable_three (t y : ℝ) {a : ℝ} (hc : Real.cos a ≤ 0) :
    Integrable fun u : ℝ => gFun 3 t (u - I * a) * Complex.sinh (u - I * a) /
      (Complex.cosh (u - I * a) - Complex.cosh y) ^ 2 := by
  obtain ⟨C, hC⟩ := norm_gFun_three_line_le t a
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hcont : Continuous fun u : ℝ => gFun 3 t (u - I * a) * Complex.sinh (u - I * a) /
      (Complex.cosh (u - I * a) - Complex.cosh y) ^ 2 := by
    refine Continuous.div ?_ (by fun_prop) (fun u => pow_ne_zero _ (den_ne_zero hc y u))
    exact ((gFun.contDiff 3 t).continuous.comp (by fun_prop)).mul (by fun_prop)
  refine (integrable_inv_cosh.const_mul C).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [norm_div, norm_mul, norm_pow]
  refine bound_aux 1 (Real.cosh_pos u) (cosh_le_norm_den hc y u) ?_ hC0
  rw [pow_one]
  exact mul_le_mul (hC u) (norm_sinh_line_le u a) (norm_nonneg _) hC0

lemma integrable_four (t y : ℝ) {a : ℝ} (hc : Real.cos a ≤ 0) :
    Integrable fun u : ℝ => gFun 4 t (u - I * a) * Complex.sinh (u - I * a) /
      (Complex.cosh (u - I * a) - Complex.cosh y) ^ 3 := by
  obtain ⟨C, hC0, hC⟩ := norm_gFun_four_line_le t a
  have hcont : Continuous fun u : ℝ => gFun 4 t (u - I * a) * Complex.sinh (u - I * a) /
      (Complex.cosh (u - I * a) - Complex.cosh y) ^ 3 := by
    refine Continuous.div ?_ (by fun_prop) (fun u => pow_ne_zero _ (den_ne_zero hc y u))
    exact ((gFun.contDiff 4 t).continuous.comp (by fun_prop)).mul (by fun_prop)
  refine (integrable_inv_cosh.const_mul C).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [norm_div, norm_mul, norm_pow]
  refine bound_aux 2 (Real.cosh_pos u) (cosh_le_norm_den hc y u) ?_ hC0
  calc ‖gFun 4 t (u - I * a)‖ * ‖Complex.sinh ((u : ℂ) - I * a)‖
      ≤ (C * Real.cosh u) * Real.cosh u :=
        mul_le_mul (hC u) (norm_sinh_line_le u a) (norm_nonneg _)
          (mul_nonneg hC0 (Real.cosh_pos u).le)
    _ = C * Real.cosh u ^ 2 := by ring

/-! ### The recursion `p − 1 → p` -/

lemma hasDerivAt_line {f : ℂ → ℂ} {f' : ℂ} (a u : ℝ)
    (hf : HasDerivAt f f' ((u : ℂ) - I * a)) :
    HasDerivAt (fun u : ℝ => f ((u : ℂ) - I * a)) f' u :=
  (hf.comp_sub_const (u : ℂ) (I * a)).comp_ofReal

/-- `∫ (5.3)-integrand for p = 3` is `−4 ∫ (5.3)-integrand for p = 2`. -/
theorem integral_three {t : ℝ} (ht : 0 < t) (y : ℝ) {a : ℝ} (hc : Real.cos a ≤ 0)
    (h2 : Integrable fun u : ℝ => gFun 2 t (u - I * a) * Complex.sinh (u - I * a) /
      (Complex.cosh (u - I * a) - Complex.cosh y)) :
    ∫ u : ℝ, gFun 3 t (u - I * a) * Complex.sinh (u - I * a) /
        (Complex.cosh (u - I * a) - Complex.cosh y) ^ 2 =
      -4 * ∫ u : ℝ, gFun 2 t (u - I * a) * Complex.sinh (u - I * a) /
        (Complex.cosh (u - I * a) - Complex.cosh y) := by
  have h3 := integrable_three t y hc
  obtain ⟨C, hC⟩ := norm_gFun_three_line_le t a
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hderiv : ∀ u : ℝ, HasDerivAt
      (fun u : ℝ => gFun 3 t (u - I * a) / (Complex.cosh (u - I * a) - Complex.cosh y))
      (-4 * (gFun 2 t (u - I * a) * Complex.sinh (u - I * a) /
          (Complex.cosh (u - I * a) - Complex.cosh y)) -
        gFun 3 t (u - I * a) * Complex.sinh (u - I * a) /
          (Complex.cosh (u - I * a) - Complex.cosh y) ^ 2) u := by
    intro u
    have hD := den_ne_zero hc y u
    have hg := hasDerivAt_line a u (gFun.three_hasDerivAt ht ((u : ℂ) - I * a))
    have hd := hasDerivAt_line a u
      ((Complex.hasDerivAt_cosh ((u : ℂ) - I * a)).sub_const (Complex.cosh y))
    refine (hg.div hd hD).congr_deriv ?_
    rw [ContourTwo.gFun_two_apply]
    field_simp
  have hbound : ∀ u : ℝ,
      ‖gFun 3 t (u - I * a) / (Complex.cosh (u - I * a) - Complex.cosh y)‖ ≤
        C * (Real.cosh u)⁻¹ := by
    intro u
    rw [norm_div]
    have := bound_aux (N := ‖gFun 3 t (u - I * a)‖) 0 (Real.cosh_pos u)
      (cosh_le_norm_den hc y u) (by simpa using hC u) hC0
    simpa using this
  have htop : Tendsto
      (fun u : ℝ => gFun 3 t (u - I * a) / (Complex.cosh (u - I * a) - Complex.cosh y))
      atTop (𝓝 0) :=
    squeeze_zero_norm hbound (by simpa using tendsto_inv_cosh_atTop.const_mul C)
  have hbot : Tendsto
      (fun u : ℝ => gFun 3 t (u - I * a) / (Complex.cosh (u - I * a) - Complex.cosh y))
      atBot (𝓝 0) :=
    squeeze_zero_norm hbound (by simpa using tendsto_inv_cosh_atBot.const_mul C)
  have hint := integral_of_hasDerivAt_of_tendsto hderiv ((h2.const_mul (-4)).sub h3) hbot htop
  rw [integral_sub (h2.const_mul (-4)) h3, integral_const_mul] at hint
  linear_combination -hint

/-- `∫ (5.3)-integrand for p = 4` is `−2 ∫ (5.3)-integrand for p = 3`. -/
theorem integral_four {t : ℝ} (ht : 0 < t) (y : ℝ) {a : ℝ} (hc : Real.cos a ≤ 0) :
    ∫ u : ℝ, gFun 4 t (u - I * a) * Complex.sinh (u - I * a) /
        (Complex.cosh (u - I * a) - Complex.cosh y) ^ 3 =
      -2 * ∫ u : ℝ, gFun 3 t (u - I * a) * Complex.sinh (u - I * a) /
        (Complex.cosh (u - I * a) - Complex.cosh y) ^ 2 := by
  have h3 := integrable_three t y hc
  have h4 := integrable_four t y hc
  obtain ⟨C, hC0, hC⟩ := norm_gFun_four_line_le t a
  have hderiv : ∀ u : ℝ, HasDerivAt
      (fun u : ℝ => gFun 4 t (u - I * a) / (Complex.cosh (u - I * a) - Complex.cosh y) ^ 2)
      (-4 * (gFun 3 t (u - I * a) * Complex.sinh (u - I * a) /
          (Complex.cosh (u - I * a) - Complex.cosh y) ^ 2) -
        2 * (gFun 4 t (u - I * a) * Complex.sinh (u - I * a) /
          (Complex.cosh (u - I * a) - Complex.cosh y) ^ 3)) u := by
    intro u
    have hD := den_ne_zero hc y u
    have hg := hasDerivAt_line a u (gFun.four_hasDerivAt ht ((u : ℂ) - I * a))
    have hd := hasDerivAt_line a u
      (((Complex.hasDerivAt_cosh ((u : ℂ) - I * a)).sub_const (Complex.cosh y)).fun_pow 2)
    refine (hg.div hd (pow_ne_zero _ hD)).congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    field_simp
  have hbound : ∀ u : ℝ,
      ‖gFun 4 t (u - I * a) / (Complex.cosh (u - I * a) - Complex.cosh y) ^ 2‖ ≤
        C * (Real.cosh u)⁻¹ := by
    intro u
    rw [norm_div, norm_pow]
    exact bound_aux (N := ‖gFun 4 t (u - I * a)‖) 1 (Real.cosh_pos u)
      (cosh_le_norm_den hc y u) (by simpa using hC u) hC0
  have htop : Tendsto
      (fun u : ℝ => gFun 4 t (u - I * a) / (Complex.cosh (u - I * a) - Complex.cosh y) ^ 2)
      atTop (𝓝 0) :=
    squeeze_zero_norm hbound (by simpa using tendsto_inv_cosh_atTop.const_mul C)
  have hbot : Tendsto
      (fun u : ℝ => gFun 4 t (u - I * a) / (Complex.cosh (u - I * a) - Complex.cosh y) ^ 2)
      atBot (𝓝 0) :=
    squeeze_zero_norm hbound (by simpa using tendsto_inv_cosh_atBot.const_mul C)
  have hint := integral_of_hasDerivAt_of_tendsto hderiv
    ((h3.const_mul (-4)).sub (h4.const_mul 2)) hbot htop
  rw [integral_sub (h3.const_mul (-4)) (h4.const_mul 2), integral_const_mul,
    integral_const_mul] at hint
  linear_combination (-1 / 2 : ℂ) * hint

end ContourRec

end Lyasoff2016
