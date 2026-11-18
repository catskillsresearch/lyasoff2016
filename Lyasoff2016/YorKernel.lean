/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Smoothness and rapid decay at `0` and `∞` of the Hartman–Watson integral kernel
`J(t, r) = ∫₀^∞ exp(-u²/(2t) - r cosh u) sinh u sin(π u / t) du` and all its derivatives.
-/
module

public import Lyasoff2016.YorJointDensity
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real
open Complex (I)

noncomputable section
namespace Lyasoff2016

section KernelSmoothness

/-- `m`-th formal derivative of the Hartman–Watson integral kernel:
`Jm t m r = (-1)^m ∫₀^∞ (cosh u)^m exp(-u²/(2t) - r cosh u) sinh u sin(π u / t) du`. -/
def Jm (t : ℝ) (m : ℕ) (r : ℝ) : ℝ :=
  (-1 : ℝ) ^ m * ∫ u in Ioi (0 : ℝ), (Real.cosh u) ^ m *
    Real.exp (-u ^ 2 / (2 * t) - r * Real.cosh u) * Real.sinh u * Real.sin (Real.pi * u / t)

/-- Integrability of `(cosh u)^m * exp(-u²/(2t)) * sinh u` on `Ioi 0`. -/
lemma integrableOn_cosh_pow_exp_neg_quad_mul_sinh {t : ℝ} (ht : 0 < t) (m : ℕ) :
    IntegrableOn (fun u : ℝ => (Real.cosh u) ^ m * Real.exp (-u ^ 2 / (2 * t)) * Real.sinh u)
      (Ioi 0) := by
  let C : ℝ := Real.exp (((m : ℝ) + 1) ^ 2 * t / 2)
  have hgauss : Integrable (fun u : ℝ =>
      C * Real.exp (-(1 / (2 * t)) * (u - ((m : ℝ) + 1) * t) ^ 2)) :=
    ((integrable_exp_neg_mul_sq (by positivity : 0 < 1 / (2 * t))).comp_sub_right
      (((m : ℝ) + 1) * t)).const_mul C
  refine hgauss.integrableOn.mono' (by fun_prop) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
  have hsinh_nn : 0 ≤ Real.sinh u := Real.sinh_nonneg_iff.mpr hu.out.le
  have hcosh_le : Real.cosh u ≤ Real.exp u := by
    rw [Real.cosh_eq]
    have h1 : Real.exp (-u) ≤ Real.exp u := Real.exp_le_exp.mpr (by linarith [hu.out])
    linarith
  have hsinh_le : Real.sinh u ≤ Real.exp u := by
    rw [Real.sinh_eq]; linarith [Real.exp_pos (-u), Real.exp_pos u]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg (Real.cosh_pos u).le _),
    abs_of_pos (Real.exp_pos _), abs_of_nonneg hsinh_nn]
  calc (Real.cosh u) ^ m * Real.exp (-u ^ 2 / (2 * t)) * Real.sinh u
      ≤ (Real.exp u) ^ m * Real.exp (-u ^ 2 / (2 * t)) * Real.exp u := by
        gcongr
    _ = Real.exp (-u ^ 2 / (2 * t) + ((m : ℝ) + 1) * u) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1; ring
    _ = C * Real.exp (-(1 / (2 * t)) * (u - ((m : ℝ) + 1) * t) ^ 2) := by
        dsimp only [C]
        rw [← Real.exp_add]; congr 1; field_simp [ht.ne']; ring

/-- `Jm t m` is continuous on `[0, ∞)` for every `t > 0, m : ℕ`. -/
lemma Jm_continuousOn {t : ℝ} (ht : 0 < t) (m : ℕ) :
    ContinuousOn (Jm t m) (Ici 0) := by
  unfold Jm
  refine ContinuousOn.mul continuousOn_const ?_
  refine continuousOn_iff_continuous_domRestrict.mpr ?_
  have hc : Continuous (fun r : Ici (0 : ℝ) =>
      ∫ u in Ioi (0 : ℝ), (Real.cosh u) ^ m * Real.exp (-u ^ 2 / (2 * t) - r.1 * Real.cosh u) *
        Real.sinh u * Real.sin (Real.pi * u / t)) := by
    refine continuous_of_dominated
      (bound := fun u => (Real.cosh u) ^ m * Real.exp (-u ^ 2 / (2 * t)) * Real.sinh u)
      ?_ ?_ (integrableOn_cosh_pow_exp_neg_quad_mul_sinh ht m) ?_
    · intro r; exact (by fun_prop : Continuous fun u => _).aestronglyMeasurable
    · intro r
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
      have hr0 : 0 ≤ r.1 := r.2
      have hexp_split : Real.exp (-u ^ 2 / (2 * t) - r.1 * Real.cosh u) =
          Real.exp (-u ^ 2 / (2 * t)) * Real.exp (-r.1 * Real.cosh u) := by
        rw [sub_eq_add_neg, Real.exp_add, neg_mul]
      have h1 : Real.exp (-r.1 * Real.cosh u) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hr0) (Real.cosh_pos u).le)
      have h2 : |Real.sin (Real.pi * u / t)| ≤ 1 := Real.abs_sin_le_one _
      have hs : 0 ≤ Real.sinh u := Real.sinh_nonneg_iff.mpr hu.out.le
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (pow_nonneg (Real.cosh_pos u).le _), abs_of_pos (Real.exp_pos _),
        abs_of_nonneg hs, hexp_split]
      calc (Real.cosh u) ^ m * (Real.exp (-u ^ 2 / (2 * t)) * Real.exp (-r.1 * Real.cosh u)) *
            Real.sinh u * |Real.sin (Real.pi * u / t)|
          ≤ (Real.cosh u) ^ m * (Real.exp (-u ^ 2 / (2 * t)) * 1) * Real.sinh u * 1 := by gcongr
        _ = (Real.cosh u) ^ m * Real.exp (-u ^ 2 / (2 * t)) * Real.sinh u := by ring
    · filter_upwards with u
      have hv : Continuous (fun r : Ici (0 : ℝ) => r.1) := continuous_subtype_val
      fun_prop
  exact (continuous_iff_continuousAt.mpr fun r => hc.continuousAt)

/-- Derivative of `Jm t m` on `(0, ∞)` is `Jm t (m + 1)`. -/
lemma Jm_hasDerivAt {t : ℝ} (ht : 0 < t) (m : ℕ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (Jm t m) (Jm t (m + 1) r) r := by
  let F : ℝ → ℝ → ℝ := fun r' u =>
    (-1 : ℝ) ^ m * ((Real.cosh u) ^ m * Real.exp (-u ^ 2 / (2 * t) - r' * Real.cosh u) *
      Real.sinh u * Real.sin (Real.pi * u / t))
  let F' : ℝ → ℝ → ℝ := fun r' u =>
    (-1 : ℝ) ^ (m + 1) * ((Real.cosh u) ^ (m + 1) * Real.exp (-u ^ 2 / (2 * t) - r' * Real.cosh u) *
      Real.sinh u * Real.sin (Real.pi * u / t))
  have hJ_eq : ∀ r', Jm t m r' = ∫ u in Ioi (0 : ℝ), F r' u := fun r' => by
    unfold Jm; rw [← integral_const_mul]
  have hJ'_eq : Jm t (m + 1) r = ∫ u in Ioi (0 : ℝ), F' r u := by
    unfold Jm; rw [← integral_const_mul]
  rw [hJ'_eq]
  have h_eq_fn : Jm t m = fun r' => ∫ u in Ioi (0 : ℝ), F r' u := funext hJ_eq
  rw [h_eq_fn]
  let s : Set ℝ := Ioo (r / 2) (r + 1)
  have hs_nhds : s ∈ 𝓝 r := isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have hF_meas : ∀ᶠ r' in 𝓝 r, AEStronglyMeasurable (F r') (volume.restrict (Ioi 0)) := by
    filter_upwards with r'
    exact (by fun_prop : Continuous fun u => F r' u).aestronglyMeasurable
  have hF_int : Integrable (F r) (volume.restrict (Ioi 0)) := by
    refine ((integrableOn_cosh_pow_exp_neg_quad_mul_sinh ht m).mono' ?_ ?_)
    · exact (by fun_prop : Continuous fun u => F r u).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
      have hexp_split : Real.exp (-u ^ 2 / (2 * t) - r * Real.cosh u) =
          Real.exp (-u ^ 2 / (2 * t)) * Real.exp (-r * Real.cosh u) := by
        rw [sub_eq_add_neg, Real.exp_add, neg_mul]
      have h1 : Real.exp (-r * Real.cosh u) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hr.le) (Real.cosh_pos u).le)
      have h2 : |Real.sin (Real.pi * u / t)| ≤ 1 := Real.abs_sin_le_one _
      have hs : 0 ≤ Real.sinh u := Real.sinh_nonneg_iff.mpr hu.out.le
      rw [Real.norm_eq_abs]
      simp only [F, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (pow_nonneg (Real.cosh_pos u).le _), abs_of_pos (Real.exp_pos _),
        abs_of_nonneg hs, hexp_split]
      calc (Real.cosh u) ^ m * (Real.exp (-u ^ 2 / (2 * t)) * Real.exp (-r * Real.cosh u)) *
            Real.sinh u * |Real.sin (Real.pi * u / t)|
          ≤ (Real.cosh u) ^ m * (Real.exp (-u ^ 2 / (2 * t)) * 1) * Real.sinh u * 1 := by gcongr
        _ = (Real.cosh u) ^ m * Real.exp (-u ^ 2 / (2 * t)) * Real.sinh u := by ring
  have hF'_meas : AEStronglyMeasurable (F' r) (volume.restrict (Ioi 0)) :=
    (by fun_prop : Continuous fun u => F' r u).aestronglyMeasurable
  have h_bound : ∀ᵐ u ∂(volume.restrict (Ioi 0)), ∀ r' ∈ s,
      ‖F' r' u‖ ≤ (Real.cosh u) ^ (m + 1) * Real.exp (-u ^ 2 / (2 * t)) * Real.sinh u := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu r' hr' => ?_
    have hr'0 : 0 ≤ r' := by linarith [hr'.1]
    have hexp_split : Real.exp (-u ^ 2 / (2 * t) - r' * Real.cosh u) =
        Real.exp (-u ^ 2 / (2 * t)) * Real.exp (-r' * Real.cosh u) := by
      rw [sub_eq_add_neg, Real.exp_add, neg_mul]
    have h1 : Real.exp (-r' * Real.cosh u) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hr'0) (Real.cosh_pos u).le)
    have h2 : |Real.sin (Real.pi * u / t)| ≤ 1 := Real.abs_sin_le_one _
    have hs : 0 ≤ Real.sinh u := Real.sinh_nonneg_iff.mpr hu.out.le
    rw [Real.norm_eq_abs]
    simp only [F', abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (pow_nonneg (Real.cosh_pos u).le _), abs_of_pos (Real.exp_pos _),
      abs_of_nonneg hs, hexp_split]
    calc (Real.cosh u) ^ (m + 1) * (Real.exp (-u ^ 2 / (2 * t)) * Real.exp (-r' * Real.cosh u)) *
          Real.sinh u * |Real.sin (Real.pi * u / t)|
        ≤ (Real.cosh u) ^ (m + 1) * (Real.exp (-u ^ 2 / (2 * t)) * 1) * Real.sinh u * 1 := by gcongr
      _ = (Real.cosh u) ^ (m + 1) * Real.exp (-u ^ 2 / (2 * t)) * Real.sinh u := by ring
  have h_diff : ∀ᵐ u ∂(volume.restrict (Ioi 0)), ∀ r' ∈ s, HasDerivAt (F · u) (F' r' u) r' := by
    refine ae_of_all _ fun u r' _ => ?_
    have hlin : HasDerivAt (fun x : ℝ => -u ^ 2 / (2 * t) - x * Real.cosh u) (-Real.cosh u) r' := by
      have h := ((hasDerivAt_id' r').mul_const (Real.cosh u)).const_sub (-u ^ 2 / (2 * t))
      simpa using h
    have hexp := hlin.exp
    have hmul := ((hexp.const_mul ((Real.cosh u) ^ m)).mul_const (Real.sinh u)).mul_const
      (Real.sin (Real.pi * u / t)) |>.const_mul ((-1 : ℝ) ^ m)
    refine hmul.congr_deriv ?_
    dsimp only [F']
    rw [pow_succ, pow_succ]
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs_nhds hF_meas hF_int hF'_meas
    h_bound (integrableOn_cosh_pow_exp_neg_quad_mul_sinh ht (m + 1)) h_diff).2

/-- `Jm t m` is `C^k` on `(0, ∞)` for every `k, m : ℕ`. -/
lemma Jm_contDiffOn {t : ℝ} (ht : 0 < t) :
    ∀ k m : ℕ, ContDiffOn ℝ k (Jm t m) (Ioi 0) := by
  intro k
  induction k with
  | zero =>
      intro m
      rw [Nat.cast_zero, contDiffOn_zero]
      exact (Jm_continuousOn ht m).mono Ioi_subset_Ici_self
  | succ k ih =>
      intro m
      rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
      refine ⟨fun r hr => (Jm_hasDerivAt ht m hr).differentiableAt.differentiableWithinAt,
        fun hk => by simp at hk, ?_⟩
      have heq : EqOn (deriv (Jm t m)) (Jm t (m + 1)) (Ioi 0) := fun r hr =>
        (Jm_hasDerivAt ht m hr).deriv
      exact (ih (m + 1)).congr heq

/-- Iterated derivative of `Jm t 0` at `r > 0` equals `Jm t k r`. -/
lemma iteratedDeriv_Jm {t : ℝ} (ht : 0 < t) (k : ℕ) {r : ℝ} (hr : 0 < r) :
    iteratedDeriv k (Jm t 0) r = Jm t k r := by
  have hgen : ∀ m : ℕ, ∀ r' ∈ Ioi (0 : ℝ), iteratedDeriv k (Jm t m) r' = Jm t (m + k) r' := by
    induction k with
    | zero => intro m r' _; simp
    | succ k' ih =>
        intro m r' hr'
        rw [iteratedDeriv_succ']
        have heq : deriv (Jm t m) =ᶠ[𝓝 r'] Jm t (m + 1) := by
          filter_upwards [isOpen_Ioi.mem_nhds hr'] with y hy
          exact (Jm_hasDerivAt ht m hy).deriv
        rw [heq.iteratedDeriv_eq, ih (m + 1) r' hr']
        congr 1; ring
  simpa using hgen 0 r hr

end KernelSmoothness

section KernelVanishingAndDecay

private lemma integral_exp_linear_quad_sin_eq_zero {t : ℝ} (ht : 0 < t) (k : ℤ) :
    ∫ u : ℝ, Real.exp ((k : ℝ) * u - u ^ 2 / (2 * t)) * Real.sin (Real.pi * u / t) = 0 := by
  have hb : (-(1 / (2 * (t : ℂ)))).re < 0 := by
    rw [show (-(1 / (2 * (t : ℂ))) : ℂ) = ((-1 / (2 * t) : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
    exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  let b : ℂ := -(1 / (2 * (t : ℂ)))
  let c : ℂ := (k : ℂ) + (Real.pi / (t : ℂ)) * I
  have h_quad := integral_cexp_quadratic hb c 0
  have h_int : Integrable (fun u : ℝ => Complex.exp (b * (u : ℂ) ^ 2 + c * (u : ℂ) + 0)) := by
    have h_dom : Integrable (fun u : ℝ =>
        Real.exp ((k : ℝ) ^ 2 * t / 2) * Real.exp (-(1 / (2 * t)) * (u - (k : ℝ) * t) ^ 2)) :=
      ((integrable_exp_neg_mul_sq (by positivity : 0 < 1 / (2 * t))).comp_sub_right ((k : ℝ) * t)).const_mul _
    refine h_dom.mono' (by fun_prop) (ae_of_all _ fun u => ?_)
    have hre : (b * (u : ℂ) ^ 2 + c * (u : ℂ) + 0).re = (k : ℝ) * u - u ^ 2 / (2 * t) := by
      dsimp only [b, c]
      have h1 : (-(1 / (2 * (t : ℂ))) * (u : ℂ) ^ 2).re = -u ^ 2 / (2 * t) := by
        rw [show -(1 / (2 * (t : ℂ))) * (u : ℂ) ^ 2 = ((-u ^ 2 / (2 * t) : ℝ) : ℂ) by
          push_cast; ring]
        exact Complex.ofReal_re _
      have h2 : (((k : ℂ) + (Real.pi / (t : ℂ)) * I) * (u : ℂ)).re = (k : ℝ) * u := by
        rw [add_mul, Complex.add_re]
        have h2a : ((k : ℂ) * (u : ℂ)).re = (k : ℝ) * u := by
          rw [← Complex.ofReal_intCast, ← Complex.ofReal_mul, Complex.ofReal_re]
        have h2b : ((Real.pi / (t : ℂ)) * I * (u : ℂ)).re = 0 := by
          rw [show (Real.pi / (t : ℂ)) * I * (u : ℂ) = ((Real.pi * u / t : ℝ) : ℂ) * I by
            push_cast; ring]
          simp
        rw [h2a, h2b, add_zero]
      rw [add_zero, Complex.add_re, h1, h2]
      ring
    rw [Complex.norm_exp, hre]
    have halg : (k : ℝ) * u - u ^ 2 / (2 * t) =
        (k : ℝ) ^ 2 * t / 2 + -(1 / (2 * t)) * (u - (k : ℝ) * t) ^ 2 := by
      field_simp [ht.ne']; ring
    rw [halg, Real.exp_add]
  have h_im_int : (∫ u : ℝ, Complex.exp (b * (u : ℂ) ^ 2 + c * (u : ℂ) + 0)).im =
      ∫ u : ℝ, (Complex.exp (b * (u : ℂ) ^ 2 + c * (u : ℂ) + 0)).im := by
    have h1 := (Complex.imCLM.integral_comp_comm h_int)
    simpa using h1.symm
  have h_pt_im : ∀ u : ℝ, (Complex.exp (b * (u : ℂ) ^ 2 + c * (u : ℂ) + 0)).im =
      Real.exp ((k : ℝ) * u - u ^ 2 / (2 * t)) * Real.sin (Real.pi * u / t) := by
    intro u
    let a : ℝ := (k : ℝ) * u - u ^ 2 / (2 * t)
    let th : ℝ := Real.pi * u / t
    have harg : b * (u : ℂ) ^ 2 + c * (u : ℂ) + 0 = (a : ℂ) + (th : ℂ) * I := by
      dsimp only [a, th, b, c]
      push_cast; ring
    rw [harg, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
    simp only [Complex.mul_im, Complex.add_im, Complex.I_im, Complex.I_re, Complex.ofReal_im,
      Complex.ofReal_re, mul_one, mul_zero, zero_mul, add_zero, zero_add]
    dsimp only [a, th]
  have h_rhs_im : ((Real.pi / -b) ^ (1 / 2 : ℂ) * Complex.exp (0 - c ^ 2 / (4 * b))).im = 0 := by
    have h_sqrt : (Real.pi / -b) ^ (1 / 2 : ℂ) = ((Real.sqrt (2 * Real.pi * t) : ℝ) : ℂ) := by
      have hpos : (Real.pi / -b) = ((2 * Real.pi * t : ℝ) : ℂ) := by
        dsimp only [b]
        push_cast; field_simp [Complex.ofReal_ne_zero.mpr ht.ne']
      rw [hpos, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl,
        ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow]
    have h_exp_c : Complex.exp (0 - c ^ 2 / (4 * b)) =
        ((Real.exp (t * (k : ℝ) ^ 2 / 2 - Real.pi ^ 2 / (2 * t)) : ℝ) : ℂ) * (-1 : ℂ) ^ k := by
      have harg : (0 : ℂ) - c ^ 2 / (4 * b) =
          ((t * (k : ℝ) ^ 2 / 2 - Real.pi ^ 2 / (2 * t) : ℝ) : ℂ) + (k : ℤ) * (Real.pi * I) := by
        dsimp only [b, c]
        have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
        push_cast
        rw [add_sq, mul_pow, Complex.I_sq]
        field_simp [ht0]
        ring
      rw [harg, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_int_mul, Complex.exp_pi_mul_I]
    have h_zpow : (-1 : ℂ) ^ k = (((-1 : ℝ) ^ k : ℝ) : ℂ) := by
      push_cast; rfl
    rw [h_sqrt, h_exp_c, h_zpow]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_im]
  have h_final : ∫ u : ℝ, Real.exp ((k : ℝ) * u - u ^ 2 / (2 * t)) * Real.sin (Real.pi * u / t) =
      (∫ u : ℝ, Complex.exp (b * (u : ℂ) ^ 2 + c * (u : ℂ) + 0)).im := by
    rw [h_im_int]
    refine integral_congr_ae (ae_of_all _ fun u => (h_pt_im u).symm)
  rw [h_final, h_quad, h_rhs_im]

/-- Every derivative of the Hartman–Watson kernel vanishes at `r = 0`: `Jm t m 0 = 0`. -/
lemma Jm_zero_eq_zero {t : ℝ} (ht : 0 < t) (m : ℕ) : Jm t m 0 = 0 := by
  unfold Jm
  let f : ℝ → ℝ := fun u =>
    (Real.cosh u) ^ m * Real.exp (-u ^ 2 / (2 * t) - 0 * Real.cosh u) *
      Real.sinh u * Real.sin (Real.pi * u / t)
  have hf_even : ∀ u : ℝ, f (-u) = f u := fun u => by
    simp only [f, Real.cosh_neg, neg_sq, zero_mul, sub_zero, Real.sinh_neg, mul_neg, Real.sin_neg,
      neg_div]
    ring
  have hf_int_Ioi : IntegrableOn f (Ioi 0) := by
    refine (integrableOn_cosh_pow_exp_neg_quad_mul_sinh ht m).mono'
      (by fun_prop : Continuous f).aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
    have hs : 0 ≤ Real.sinh u := Real.sinh_nonneg_iff.mpr hu.out.le
    rw [Real.norm_eq_abs]
    simp only [f, zero_mul, sub_zero, abs_mul, abs_of_nonneg (pow_nonneg (Real.cosh_pos u).le _),
      abs_of_pos (Real.exp_pos _), abs_of_nonneg hs]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)
  have hf_int_Iio : IntegrableOn f (Iio 0) := by
    have h_neg_img : (Neg.neg '' Ioi (0 : ℝ)) = Iio 0 := by
      ext u; simp only [mem_image, mem_Ioi, mem_Iio]
      exact ⟨fun ⟨v, hv, h⟩ => by linarith, fun hu => ⟨-u, by linarith, neg_neg u⟩⟩
    rw [← h_neg_img, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      (fun u _ => (hasDerivAt_neg u).hasDerivWithinAt) neg_injective.injOn]
    simpa [hf_even] using hf_int_Ioi
  have hf_int_Ici : IntegrableOn f (Ici 0) :=
    hf_int_Ioi.congr_set_ae Ioi_ae_eq_Ici.symm
  have hf_int_R : Integrable f := by
    rw [← integrableOn_univ, ← Iio_union_Ici]
    exact hf_int_Iio.union hf_int_Ici
  have h_even_split : ∫ u in Ioi (0 : ℝ), f u = (1 / 2 : ℝ) * ∫ u : ℝ, f u := by
    have h_neg : ∫ u in Iio (0 : ℝ), f u = ∫ u in Ioi (0 : ℝ), f u := by
      have h_neg_img : (Neg.neg '' Ioi (0 : ℝ)) = Iio 0 := by
        ext u; simp only [mem_image, mem_Ioi, mem_Iio]
        exact ⟨fun ⟨v, hv, h⟩ => by linarith, fun hu => ⟨-u, by linarith, neg_neg u⟩⟩
      rw [← h_neg_img, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
        (fun u _ => (hasDerivAt_neg u).hasDerivWithinAt) neg_injective.injOn]
      simp [hf_even]
    have h_ici : ∫ u in Ici (0 : ℝ), f u = ∫ u in Ioi (0 : ℝ), f u :=
      integral_Ici_eq_integral_Ioi
    have h_tot : ∫ u : ℝ, f u = (∫ u in Iio (0 : ℝ), f u) + ∫ u in Ici (0 : ℝ), f u := by
      rw [← setIntegral_univ, ← Iio_union_Ici, setIntegral_union (Set.Iio_disjoint_Ici le_rfl)
        measurableSet_Ici hf_int_Iio hf_int_Ici]
    rw [h_neg, h_ici] at h_tot
    linarith
  have h_full_zero : ∫ u : ℝ, f u = 0 := by
    let g_term : ℤ → ℝ → ℝ := fun k u => Real.exp ((k : ℝ) * u - u ^ 2 / (2 * t)) * Real.sin (Real.pi * u / t)
    have hg_int : ∀ k : ℤ, Integrable (g_term k) := by
      intro k
      have h_dom : Integrable (fun u : ℝ =>
          Real.exp ((k : ℝ) ^ 2 * t / 2) * Real.exp (-(1 / (2 * t)) * (u - (k : ℝ) * t) ^ 2)) :=
        ((integrable_exp_neg_mul_sq (by positivity : 0 < 1 / (2 * t))).comp_sub_right ((k : ℝ) * t)).const_mul _
      refine h_dom.mono' (by fun_prop : Continuous (g_term k)).aestronglyMeasurable (ae_of_all _ fun u => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have halg : (k : ℝ) * u - u ^ 2 / (2 * t) =
          (k : ℝ) ^ 2 * t / 2 + -(1 / (2 * t)) * (u - (k : ℝ) * t) ^ 2 := by
        field_simp [ht.ne']; ring
      calc Real.exp ((k : ℝ) * u - u ^ 2 / (2 * t)) * |Real.sin (Real.pi * u / t)|
          ≤ Real.exp ((k : ℝ) * u - u ^ 2 / (2 * t)) * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (Real.exp_pos _).le
        _ = Real.exp ((k : ℝ) ^ 2 * t / 2) * Real.exp (-(1 / (2 * t)) * (u - (k : ℝ) * t) ^ 2) := by
            rw [halg, Real.exp_add, mul_one]
    have h_expand : ∀ u : ℝ, f u = (1 / (2 : ℝ) ^ (m + 1)) *
        ∑ j ∈ Finset.range (m + 1), ((m.choose j : ℝ) *
          (g_term (2 * (j : ℤ) - m + 1) u - g_term (2 * (j : ℤ) - m - 1) u)) := by
      intro u
      have h1 : (Real.cosh u) ^ m * Real.sinh u = (1 / (2 : ℝ) ^ (m + 1)) *
          ((Real.exp u + Real.exp (-u)) ^ m * (Real.exp u - Real.exp (-u))) := by
        rw [Real.cosh_eq, Real.sinh_eq, div_pow, pow_succ]
        ring
      have h2 : (Real.exp u + Real.exp (-u)) ^ m =
          ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * (Real.exp u ^ j * Real.exp (-u) ^ (m - j)) := by
        rw [add_pow]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [show f u = ((Real.cosh u) ^ m * Real.sinh u) * (Real.exp (-u ^ 2 / (2 * t)) * Real.sin (Real.pi * u / t)) by
        simp only [f, zero_mul, sub_zero]; ring]
      rw [h1, h2, mul_assoc, Finset.sum_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj_le : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hexp_mul : ∀ a : ℤ, Real.exp ((a : ℝ) * u) * Real.exp (-u ^ 2 / (2 * t)) * Real.sin (Real.pi * u / t) =
          g_term a u := fun a => by
        dsimp only [g_term]
        rw [← Real.exp_add, show (a : ℝ) * u + -u ^ 2 / (2 * t) = (a : ℝ) * u - u ^ 2 / (2 * t) by ring]
      have ha1 : Real.exp u ^ j * Real.exp (-u) ^ (m - j) * Real.exp u =
          Real.exp (((2 * (j : ℤ) - m + 1 : ℤ) : ℝ) * u) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1
        push_cast [Nat.cast_sub hj_le]
        ring
      have ha2 : Real.exp u ^ j * Real.exp (-u) ^ (m - j) * Real.exp (-u) =
          Real.exp (((2 * (j : ℤ) - m - 1 : ℤ) : ℝ) * u) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1
        push_cast [Nat.cast_sub hj_le]
        ring
      calc (m.choose j : ℝ) * (Real.exp u ^ j * Real.exp (-u) ^ (m - j)) *
            (Real.exp u - Real.exp (-u)) * (Real.exp (-u ^ 2 / (2 * t)) * Real.sin (Real.pi * u / t))
          = (m.choose j : ℝ) *
              ((Real.exp u ^ j * Real.exp (-u) ^ (m - j) * Real.exp u) *
                  Real.exp (-u ^ 2 / (2 * t)) * Real.sin (Real.pi * u / t) -
               (Real.exp u ^ j * Real.exp (-u) ^ (m - j) * Real.exp (-u)) *
                  Real.exp (-u ^ 2 / (2 * t)) * Real.sin (Real.pi * u / t)) := by ring
        _ = (m.choose j : ℝ) *
              (g_term (2 * (j : ℤ) - m + 1) u - g_term (2 * (j : ℤ) - m - 1) u) := by
            rw [ha1, ha2, hexp_mul, hexp_mul]
    simp_rw [h_expand, integral_const_mul]
    have h_int_sum : (∫ u : ℝ, ∑ j ∈ Finset.range (m + 1),
        (m.choose j : ℝ) * (g_term (2 * (j : ℤ) - m + 1) u - g_term (2 * (j : ℤ) - m - 1) u)) =
        ∑ j ∈ Finset.range (m + 1), ∫ u : ℝ,
          (m.choose j : ℝ) * (g_term (2 * (j : ℤ) - m + 1) u - g_term (2 * (j : ℤ) - m - 1) u) :=
      integral_finsetSum (Finset.range (m + 1))
        (f := fun j u => (m.choose j : ℝ) * (g_term (2 * (j : ℤ) - m + 1) u - g_term (2 * (j : ℤ) - m - 1) u))
        fun j _ => ((hg_int _).sub (hg_int _)).const_mul _
    rw [h_int_sum]
    have h_zero_sum : ∑ j ∈ Finset.range (m + 1), ∫ u : ℝ,
        (m.choose j : ℝ) * (g_term (2 * (j : ℤ) - m + 1) u - g_term (2 * (j : ℤ) - m - 1) u) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [integral_const_mul, integral_sub (hg_int _) (hg_int _),
        integral_exp_linear_quad_sin_eq_zero ht _, integral_exp_linear_quad_sin_eq_zero ht _]
      ring
    rw [h_zero_sum, mul_zero]
  change (-1 : ℝ) ^ m * ∫ u in Ioi (0 : ℝ), f u = 0
  rw [h_even_split, h_full_zero, mul_zero, mul_zero]

/-- Exponential decay of `Jm t m r` for `r ≥ 0`. -/
lemma Jm_exp_decay {t : ℝ} (ht : 0 < t) (m : ℕ) :
    ∃ C ≥ 0, ∀ r ≥ 0, |Jm t m r| ≤ C * Real.exp (-r) := by
  let I₀ : ℝ := ∫ u in Ioi (0 : ℝ), (Real.cosh u) ^ m * Real.exp (-u ^ 2 / (2 * t)) * Real.sinh u
  have hI₀_nn : 0 ≤ I₀ := setIntegral_nonneg measurableSet_Ioi fun u hu =>
    mul_nonneg (mul_nonneg (pow_nonneg (Real.cosh_pos u).le _) (Real.exp_pos _).le)
      (Real.sinh_nonneg_iff.mpr hu.out.le)
  refine ⟨I₀, hI₀_nn, fun r hr => ?_⟩
  unfold Jm
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, ← Real.norm_eq_abs]
  have h_pt : ∀ u ∈ Ioi (0 : ℝ),
      ‖(Real.cosh u) ^ m * Real.exp (-u ^ 2 / (2 * t) - r * Real.cosh u) *
          Real.sinh u * Real.sin (Real.pi * u / t)‖ ≤
        Real.exp (-r) * ((Real.cosh u) ^ m * Real.exp (-u ^ 2 / (2 * t)) * Real.sinh u) := by
    intro u hu
    have hexp_split : Real.exp (-u ^ 2 / (2 * t) - r * Real.cosh u) =
        Real.exp (-u ^ 2 / (2 * t)) * Real.exp (-r * Real.cosh u) := by
      rw [sub_eq_add_neg, Real.exp_add, neg_mul]
    have h1 : Real.exp (-r * Real.cosh u) ≤ Real.exp (-r) := by
      refine Real.exp_le_exp.mpr ?_
      have := Real.one_le_cosh u
      nlinarith
    have hs : 0 ≤ Real.sinh u := Real.sinh_nonneg_iff.mpr hu.out.le
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (pow_nonneg (Real.cosh_pos u).le _), abs_of_pos (Real.exp_pos _),
      abs_of_nonneg hs, hexp_split]
    calc (Real.cosh u) ^ m * (Real.exp (-u ^ 2 / (2 * t)) * Real.exp (-r * Real.cosh u)) *
          Real.sinh u * |Real.sin (Real.pi * u / t)|
        ≤ (Real.cosh u) ^ m * (Real.exp (-u ^ 2 / (2 * t)) * Real.exp (-r)) * Real.sinh u * 1 := by
          gcongr; exact Real.abs_sin_le_one _
      _ = Real.exp (-r) * ((Real.cosh u) ^ m * Real.exp (-u ^ 2 / (2 * t)) * Real.sinh u) := by ring
  have h_norm_int : IntegrableOn (fun u => ‖(Real.cosh u) ^ m *
      Real.exp (-u ^ 2 / (2 * t) - r * Real.cosh u) * Real.sinh u * Real.sin (Real.pi * u / t)‖) (Ioi 0) :=
    ((integrableOn_cosh_pow_exp_neg_quad_mul_sinh ht m).const_mul (Real.exp (-r))).mono'
      (by fun_prop : Continuous fun u => _).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => by
        rw [Real.norm_eq_abs, abs_norm]
        exact h_pt u hu)
  calc ‖∫ u in Ioi (0 : ℝ), (Real.cosh u) ^ m * Real.exp (-u ^ 2 / (2 * t) - r * Real.cosh u) *
          Real.sinh u * Real.sin (Real.pi * u / t)‖
      ≤ ∫ u in Ioi (0 : ℝ), ‖(Real.cosh u) ^ m * Real.exp (-u ^ 2 / (2 * t) - r * Real.cosh u) *
          Real.sinh u * Real.sin (Real.pi * u / t)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in Ioi (0 : ℝ), Real.exp (-r) * ((Real.cosh u) ^ m * Real.exp (-u ^ 2 / (2 * t)) * Real.sinh u) :=
        setIntegral_mono_on h_norm_int ((integrableOn_cosh_pow_exp_neg_quad_mul_sinh ht m).const_mul _)
          measurableSet_Ioi h_pt
    _ = I₀ * Real.exp (-r) := by rw [integral_const_mul, mul_comm]

/-- Polynomial vanishing of `Jm t m r` as `r → 0⁺` for every `m, N : ℕ`. -/
lemma Jm_poly_decay {t : ℝ} (ht : 0 < t) :
    ∀ N m : ℕ, ∃ C ≥ 0, ∀ r ≥ 0, |Jm t m r| ≤ C * r ^ N := by
  intro N
  induction N with
  | zero =>
      intro m
      obtain ⟨C, hC0, hC⟩ := Jm_exp_decay ht m
      refine ⟨C, hC0, fun r hr => ?_⟩
      have hexp : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr)
      calc |Jm t m r| ≤ C * Real.exp (-r) := hC r hr
        _ ≤ C * 1 := mul_le_mul_of_nonneg_left hexp hC0
        _ = C * r ^ 0 := by simp
  | succ N ih =>
      intro m
      obtain ⟨C, hC0, hC⟩ := ih (m + 1)
      refine ⟨C, hC0, fun r hr => ?_⟩
      rcases eq_or_lt_of_le hr with rfl | hr_pos
      · simp [Jm_zero_eq_zero ht m]
      · have hcont : ContinuousOn (Jm t m) (Icc 0 r) :=
          (Jm_continuousOn ht m).mono Icc_subset_Ici_self
        have hderiv : ∀ x ∈ Ioo 0 r, HasDerivAt (Jm t m) (Jm t (m + 1) x) x := fun x hx =>
          Jm_hasDerivAt ht m hx.1
        obtain ⟨c, hc_mem, hc⟩ := exists_hasDerivAt_eq_slope (Jm t m) (Jm t (m + 1)) hr_pos hcont hderiv
        have h_sub : Jm t m r = Jm t (m + 1) c * (r - 0) := by
          have := (div_eq_iff (sub_ne_zero.mpr hr_pos.ne')).mp hc.symm
          rw [Jm_zero_eq_zero ht m, sub_zero] at this
          simpa [sub_zero] using this
        rw [h_sub, sub_zero, abs_mul, abs_of_pos hr_pos]
        have hc0 : 0 ≤ c := hc_mem.1.le
        have hcr : c ≤ r := hc_mem.2.le
        calc |Jm t (m + 1) c| * r ≤ (C * c ^ N) * r :=
              mul_le_mul_of_nonneg_right (hC c hc0) hr_pos.le
          _ ≤ (C * r ^ N) * r := by gcongr
          _ = C * r ^ (N + 1) := by ring

/-- Combined kernel bound: `|Jm t m r| ≤ C * r^N * exp(-r / 2)` for all `r ≥ 0` and `m, N : ℕ`. -/
lemma Jm_bound {t : ℝ} (ht : 0 < t) (m N : ℕ) :
    ∃ C ≥ 0, ∀ r ≥ 0, |Jm t m r| ≤ C * r ^ N * Real.exp (-r / 2) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := Jm_poly_decay ht (2 * N) m
  obtain ⟨C₂, hC₂0, hC₂⟩ := Jm_exp_decay ht m
  refine ⟨Real.sqrt (C₁ * C₂), Real.sqrt_nonneg _, fun r hr => ?_⟩
  have hsq : |Jm t m r| ^ 2 ≤ (Real.sqrt (C₁ * C₂) * r ^ N * Real.exp (-r / 2)) ^ 2 := by
    have h1 := hC₁ r hr
    have h2 := hC₂ r hr
    have hpow : (r ^ N) ^ 2 = r ^ (2 * N) := by ring
    have hexp : (Real.exp (-r / 2)) ^ 2 = Real.exp (-r) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hC₁0 hC₂0), hpow, hexp]
    calc |Jm t m r| ^ 2 = |Jm t m r| * |Jm t m r| := sq _
      _ ≤ (C₁ * r ^ (2 * N)) * (C₂ * Real.exp (-r)) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = C₁ * C₂ * r ^ (2 * N) * Real.exp (-r) := by ring
  exact le_of_sq_le_sq hsq (by positivity)

end KernelVanishingAndDecay

end Lyasoff2016
