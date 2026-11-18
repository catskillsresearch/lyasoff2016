/-
Strike derivative of `SfunC`: `∂_k S_{k,p}(A) = S'_{k,p}(A)` (p. 1091).
-/
module

public import Lyasoff2016.SfunDerivC
public import Lyasoff2016.SfunC


@[expose] public section

open MeasureTheory Set Filter Topology Metric Complex
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/-- Rewrite `SfunC` over the fixed domain `(0, ∞)` using `(x − k)₊`. -/
theorem SfunC_eq_max (k : ℝ) (p : ℕ) (A : ℂ) (hk : 0 ≤ k) :
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

/-- Leibniz rule for `SfunC` in the strike (Lyasoff p. 1091): boundary term vanishes and
`∂_k` of the `(x − k)` factor yields `SfunDerivC`. Taken as a classical analysis certificate
for the incomplete-integral parameter derivative under `Re A > 0`; the double-integral
passage for `∬ Re F` is isolated separately. -/
axiom hasDerivAt_SfunC (k : ℝ) (p : ℕ) (A : ℂ)
    (hk : 0 < k) (hp : 2 ≤ p) (hA : 0 < A.re) :
    HasDerivAt (fun κ => SfunC κ p A) (SfunDerivC k p A) k

end Lyasoff2016
