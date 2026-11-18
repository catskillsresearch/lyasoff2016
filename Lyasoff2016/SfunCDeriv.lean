/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Strike derivative of `SfunC`: `∂_k S_{k,p}(A) = S'_{k,p}(A)` (p. 1091).
-/
module

public import Lyasoff2016.SfunDerivC
public import Lyasoff2016.SfunC
public import Lyasoff2016.InverseGammaIntegral


@[expose] public section

open MeasureTheory Set Filter Topology Metric Complex
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

namespace SfunC

/-- Rewrite `SfunC` over the fixed domain `(0, ∞)` using `(x − k)₊`. -/
theorem eq_max (k : ℝ) (p : ℕ) (A : ℂ) (hk : 0 ≤ k) :
    SfunC k p A =
      ∫ x in Ioi (0 : ℝ),
        (((max (x - k) 0) * x ^ (-(p : ℤ)) : ℝ) : ℂ) * Complex.exp (-A / x) := by
  have hset :
      (∫ x in Ioi (0 : ℝ),
          (((max (x - k) 0) * x ^ (-(p : ℤ)) : ℝ) : ℂ) * Complex.exp (-A / x)) =
        ∫ x in Ioi k,
          (((x - k) * x ^ (-(p : ℤ)) : ℝ) : ℂ) * Complex.exp (-A / x) := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (Ioi_subset_Ioi hk)]
    · refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      rw [max_eq_left (sub_nonneg.mpr (le_of_lt hx))]
    · intro x hx
      have hxk : x ≤ k := by simpa using hx.2
      rw [max_eq_right (sub_nonpos.mpr hxk)]
      simp
  simpa [SfunC] using hset.symm

/-- Pointwise: `∂_κ max(x − κ, 0) = −1` for `κ < x` and `0` for `κ > x`. -/
lemma hasDerivAt_max_sub (x κ : ℝ) (h : κ ≠ x) :
    HasDerivAt (fun κ' => max (x - κ') 0)
      (if κ < x then (-1 : ℝ) else 0) κ := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have hnhd : ∀ᶠ κ' in nhds κ, max (x - κ') 0 = x - κ' :=
      (eventually_lt_nhds hlt).mono fun κ' hκ' => max_eq_left (sub_nonneg.mpr hκ'.le)
    have := (hasDerivAt_const κ x).sub (hasDerivAt_id κ)
    exact this.congr_of_eventuallyEq hnhd |>.congr_deriv (by simp [hlt])
  · have hnhd : ∀ᶠ κ' in nhds κ, max (x - κ') 0 = 0 :=
      (eventually_gt_nhds hgt).mono fun κ' hκ' => max_eq_right (sub_nonpos.mpr hκ'.le)
    exact (hasDerivAt_const κ (0 : ℝ)).congr_of_eventuallyEq hnhd |>.congr_deriv
      (by simp [not_lt.mpr hgt.le])

lemma lipschitzWith_one_max_sub (x : ℝ) :
    LipschitzWith 1 (fun κ : ℝ => max (x - κ) 0) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  simp only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul]
  have h1 : |max (x - a) 0 - max (x - b) 0| ≤ |(x - a) - (x - b)| :=
    abs_max_sub_max_le_abs (x - a) (x - b) 0
  calc
    |max (x - a) 0 - max (x - b) 0| ≤ |b - a| := by simpa [sub_sub_sub_cancel_left] using h1
    _ = |a - b| := abs_sub_comm _ _

private lemma norm_kernel (p : ℕ) (A : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖((x ^ (-(p : ℤ)) : ℝ) : ℂ) * Complex.exp (-A / x)‖ =
      x ^ (-(p : ℤ)) * Real.exp (-A.re / x) := by
  have hre : (-A / (x : ℂ)).re = -A.re / x := by
    rw [div_eq_mul_inv, mul_re]
    simp
    field_simp
  have hx0 : 0 ≤ x ^ (-(p : ℤ)) := zpow_nonneg hx.le _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0, Complex.norm_exp, hre]

private lemma F_eq_max_mul_kernel (p : ℕ) (A : ℂ) (κ x : ℝ) :
    (((max (x - κ) 0) * x ^ (-(p : ℤ)) : ℝ) : ℂ) * Complex.exp (-A / x) =
      ((max (x - κ) 0 : ℝ) : ℂ) *
        (((x ^ (-(p : ℤ)) : ℝ) : ℂ) * Complex.exp (-A / x)) := by
  push_cast
  ring

private lemma zpow_neg_pred {p : ℕ} (hp : 1 ≤ p) {x : ℝ} (hx : x ≠ 0) :
    x ^ (-((p - 1 : ℕ) : ℤ)) = x * x ^ (-(p : ℤ)) := by
  have hp' : (p : ℤ) = (p - 1 : ℕ) + 1 := by omega
  rw [hp', neg_add, zpow_add₀ hx, zpow_neg_one]
  field_simp [hx]

private lemma max_kernel_le_inv_pow (k : ℝ) (hk : 0 ≤ k) {p : ℕ} (hp : 1 ≤ p)
    {x : ℝ} (hx : 0 < x) :
    max (x - k) 0 * x ^ (-(p : ℤ)) ≤ x ^ (-((p - 1 : ℕ) : ℤ)) := by
  rcases le_or_gt x k with hxk | hxk
  · rw [max_eq_right (sub_nonpos.mpr hxk), zero_mul]
    exact zpow_nonneg hx.le _
  · rw [max_eq_left (sub_nonneg.mpr hxk.le), zpow_neg_pred hp hx.ne']
    exact mul_le_mul_of_nonneg_right (sub_le_self x hk) (zpow_nonneg hx.le _)

/-- Leibniz rule for `SfunC` in the strike (Lyasoff p. 1091): boundary term vanishes and
`∂_k` of the `(x − k)` factor yields `SfunDerivC`. Requires `3 ≤ p` so that
`(x − k)₊ x^{-p}` is integrable at infinity under `Re A > 0`. -/
theorem hasDerivAt (k : ℝ) (p : ℕ) (A : ℂ)
    (hk : 0 < k) (hp : 3 ≤ p) (hA : 0 < A.re) :
    HasDerivAt (fun κ => SfunC κ p A) (SfunDerivC k p A) k := by
  let F : ℝ → ℝ → ℂ := fun κ x =>
    (((max (x - κ) 0) * x ^ (-(p : ℤ)) : ℝ) : ℂ) * Complex.exp (-A / x)
  let g : ℝ → ℂ := fun x =>
    ((x ^ (-(p : ℤ)) : ℝ) : ℂ) * Complex.exp (-A / x)
  let F' : ℝ → ℂ := fun x => (if k < x then (-1 : ℂ) else 0) * g x
  let bound : ℝ → ℝ := fun x => x ^ (-(p : ℤ)) * Real.exp (-A.re / x)
  let s : Set ℝ := Metric.ball k (k / 2)
  have hs : s ∈ 𝓝 k := Metric.ball_mem_nhds k (half_pos hk)
  have hp2 : 2 ≤ p := by omega
  have hp1 : 2 ≤ p - 1 := by omega
  have hFg : ∀ κ x, F κ x = ((max (x - κ) 0 : ℝ) : ℂ) * g x := fun κ x =>
    F_eq_max_mul_kernel p A κ x
  have heq :
      (fun κ => SfunC κ p A) =ᶠ[nhds k]
        fun κ => ∫ x in Ioi (0 : ℝ), F κ x := by
    filter_upwards [eventually_ge_nhds hk] with κ hκ
    simpa [F] using eq_max κ p A hκ
  have hF_meas : ∀ᶠ κ in 𝓝 k, AEStronglyMeasurable (F κ) (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards with κ
    exact (by fun_prop : Measurable (F κ)).aestronglyMeasurable.restrict
  have hbound_int : Integrable bound (volume.restrict (Ioi (0 : ℝ))) :=
    integrableOn_inv_pow_exp_neg_div hp2 hA
  have hF_int : Integrable (F k) (volume.restrict (Ioi (0 : ℝ))) := by
    refine Integrable.mono'
      (integrableOn_inv_pow_exp_neg_div (p := p - 1) hp1 hA)
      hF_meas.self_of_nhds ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 < x := hx
    have hnorm :
        ‖F k x‖ = max (x - k) 0 * x ^ (-(p : ℤ)) * Real.exp (-A.re / x) := by
      rw [hFg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _),
        norm_kernel p A hx0]
      ring
    have hp1' : 1 ≤ p := by omega
    rw [hnorm]
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_right (max_kernel_le_inv_pow k hk.le hp1' hx0) (Real.exp_pos _).le)
  have hF'_meas : AEStronglyMeasurable F' (volume.restrict (Ioi (0 : ℝ))) := by
    have hite : Measurable fun x : ℝ => (if k < x then (-1 : ℂ) else 0) :=
      Measurable.ite (measurableSet_lt measurable_const measurable_id)
        measurable_const measurable_const
    exact (hite.mul (by fun_prop : Measurable g)).aestronglyMeasurable.restrict
  have hlip : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
      LipschitzOnWith (Real.nnabs (bound x)) (fun κ => F κ x) s := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 < x := hx
    have hL : LipschitzWith (Real.nnabs (bound x)) (fun κ => F κ x) := by
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      have hmax : |max (x - a) 0 - max (x - b) 0| ≤ dist a b := by
        simpa [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul] using
          (lipschitzWith_one_max_sub x).dist_le_mul a b
      have hbn : 0 ≤ bound x :=
        mul_nonneg (zpow_nonneg hx0.le _) (Real.exp_pos _).le
      calc
        dist (F a x) (F b x)
            = ‖((max (x - a) 0 : ℝ) : ℂ) * g x - ((max (x - b) 0 : ℝ) : ℂ) * g x‖ := by
                simp only [hFg, dist_eq_norm]
        _ = ‖((max (x - a) 0 - max (x - b) 0 : ℝ) : ℂ) * g x‖ := by
                congr 1; push_cast; ring
        _ = |max (x - a) 0 - max (x - b) 0| * ‖g x‖ := by
                rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ = |max (x - a) 0 - max (x - b) 0| * bound x := by
                rw [show ‖g x‖ = bound x from norm_kernel p A hx0]
        _ ≤ dist a b * bound x := by gcongr
        _ = (Real.nnabs (bound x) : ℝ) * dist a b := by
                simp [abs_of_nonneg hbn, mul_comm]
    exact hL.lipschitzOnWith
  have hdiff : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)), HasDerivAt (fun κ => F κ x) (F' x) k := by
    have : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)), x ≠ k := by
      rw [ae_iff, Measure.restrict_apply' measurableSet_Ioi]
      simp only [ne_eq, not_not]
      exact measure_mono_null inter_subset_left (measure_singleton k)
    filter_upwards [this] with x hx
    have hpt := hasDerivAt_max_sub x k hx.symm
    have hof := hpt.ofReal_comp
    have hmul := hof.mul (hasDerivAt_const k (g x))
    refine (hmul.congr_of_eventuallyEq (Eventually.of_forall fun κ => ?_)).congr_deriv ?_
    · simp [hFg, Pi.mul_apply]
    · dsimp [F']
      split_ifs <;> push_cast <;> ring
  have hmain :=
    hasDerivAt_integral_of_dominated_loc_of_lip (μ := volume.restrict (Ioi (0 : ℝ)))
      (F := F) (F' := F') (bound := bound) hs hF_meas hF_int hF'_meas hlip hbound_int hdiff
  have hident : (∫ x in Ioi (0 : ℝ), F' x) = SfunDerivC k p A := by
    have hset : (∫ x in Ioi (0 : ℝ), F' x) = ∫ x in Ioi k, (-g x) := by
      have hsub : Ioi k ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi hk.le
      rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub]
      · refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
        have hx' : k < x := mem_Ioi.mp hx
        dsimp [F', g]
        simp [hx']
      · intro x hx
        have hxk : ¬ k < x := not_lt.mpr (by simpa using hx.2)
        dsimp [F', g]
        simp [hxk]
    rw [hset, integral_neg, SfunDerivC]
  have hderiv : HasDerivAt (fun κ => ∫ x in Ioi (0 : ℝ), F κ x) (SfunDerivC k p A) k := by
    convert hmain.2 using 1
    exact hident.symm
  exact hderiv.congr_of_eventuallyEq heq

end SfunC

end Lyasoff2016
