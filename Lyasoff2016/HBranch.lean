/-
Characteristic-branch weight `h` along `A(v, ·)`, paired with `ψBranch`.
-/
module

public import Lyasoff2016.PsiBranch


@[expose] public section

open Set Filter Topology
open scoped Real Topology

noncomputable section
namespace Lyasoff2016

/-- Branch weight of a compactly supported profile along the characteristic `A`. -/
def hBranch (sgn : Bool) (F : ℝ → ℝ) (v y : ℝ) : ℝ :=
  if (if sgn then yCrit v < y else y < yCrit v) then
    2 * (Real.sinh y - v * Real.exp (-y)) * F (charA v y)
  else 0

namespace hBranch

theorem eq_mul_ψBranch (sgn : Bool) (F : ℝ → ℝ) (v y : ℝ) :
    hBranch sgn F v y = (Real.exp (2 * y) - 2 * v - 1) * ψBranch sgn F v y := by
  have hmul : Real.exp (2 * y) * Real.exp (-y) = Real.exp y := by
    rw [← Real.exp_add]; congr 1; ring
  have halg : 2 * (Real.sinh y - v * Real.exp (-y)) * F (charA v y) =
      (Real.exp (2 * y) - 2 * v - 1) * (Real.exp (-y) * F (charA v y)) := by
    calc 2 * (Real.sinh y - v * Real.exp (-y)) * F (charA v y)
        = (Real.exp y - Real.exp (-y) - 2 * v * Real.exp (-y)) * F (charA v y) := by
            rw [Real.sinh_eq]; ring
      _ = (Real.exp (2 * y) * Real.exp (-y) - Real.exp (-y) - 2 * v * Real.exp (-y)) * F (charA v y) := by
            rw [hmul]
      _ = (Real.exp (2 * y) - 2 * v - 1) * (Real.exp (-y) * F (charA v y)) := by ring
  unfold hBranch ψBranch
  cases sgn <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · split_ifs
    · exact halg
    · ring
  · split_ifs
    · exact halg
    · ring


theorem compactSupport_bound {F : ℝ → ℝ} (hFC : HasCompactSupport F) :
    ∃ R > 0, ∀ sgn v, 0 ≤ v → ∀ y, R ≤ |y| →
      ψBranch sgn F v y = 0 ∧ hBranch sgn F v y = 0 := by
  obtain ⟨R, hR0, hR⟩ := ψBranch.compactSupport_bound hFC
  refine ⟨R, hR0, fun sgn v hv y hy => ?_⟩
  have hψ := hR sgn v hv y hy
  exact ⟨hψ, by rw [eq_mul_ψBranch, hψ, mul_zero]⟩

theorem hasDerivAt_v {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    {v₀ a₀ : ℝ} (_hv₀ : 0 ≤ v₀) (_ha₀ : Real.sqrt (1 + 2 * v₀) < a₀)
    (hF0 : ∀ a ≤ a₀, F a = 0) (sgn : Bool) {δ : ℝ}
    (hδ : Real.sqrt (1 + 2 * (v₀ + δ)) < a₀) (_hδ0 : 0 < δ)
    {v : ℝ} (hv : 0 < v) (hvv₀ : v < v₀ + δ) (y : ℝ) :
    HasDerivAt (fun v' => hBranch sgn F v' y) (2 * deriv (ψBranch sgn F v) y) v := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hFdiff : Differentiable ℝ F := hF1.differentiable (by norm_num)
  have hcrit : charA v (yCrit v) < a₀ := by
    rw [charA.yCrit hv.le]
    exact lt_of_le_of_lt (Real.sqrt_le_sqrt (by linarith)) hδ
  have hyCrit_at : ContinuousAt yCrit v := by
    have h12v : (1 + 2 * v) ≠ 0 := by linarith
    exact continuousAt_const.mul (ContinuousAt.log (by fun_prop) h12v)
  rcases lt_trichotomy (yCrit v) y with hy | hy | hy
  · have h_ev_v : ∀ᶠ v' in 𝓝 v,
        hBranch sgn F v' y = if sgn then 2 * (Real.sinh y - v' * Real.exp (-y)) * F (charA v' y) else 0 := by
      filter_upwards [hyCrit_at.eventually (isOpen_Iio.mem_nhds hy)] with v' hv'
      cases sgn <;> simp [hBranch, hv', not_lt.mpr hv'.le]
    have h_ev_y : ψBranch sgn F v =ᶠ[𝓝 y]
        if sgn then fun y' => Real.exp (-y') * F (charA v y') else fun _ => (0 : ℝ) := by
      filter_upwards [eventually_gt_nhds hy] with y' hy'
      cases sgn <;> simp [ψBranch, hy', not_lt.mpr hy'.le]
    rw [h_ev_y.deriv_eq]
    cases sgn
    · simp only [Bool.false_eq_true, ↓reduceIte, deriv_const', mul_zero]
      exact (hasDerivAt_const v (0 : ℝ)).congr_of_eventuallyEq h_ev_v
    · simp only [↓reduceIte]
      have hd_y : deriv (fun y' => Real.exp (-y') * F (charA v y')) y =
          (-Real.exp (-y)) * F (charA v y) +
          Real.exp (-y) * (deriv F (charA v y) * (Real.sinh y - v * Real.exp (-y))) := by
        have h1 : HasDerivAt (fun y' => Real.exp (-y')) (-Real.exp (-y)) y := by
          simpa using (hasDerivAt_id' y).neg.exp
        have h2 : HasDerivAt (fun y' => F (charA v y'))
            (deriv F (charA v y) * (Real.sinh y - v * Real.exp (-y))) y :=
          (hFdiff (charA v y)).hasDerivAt.comp y (charA.hasDerivAt_y v y)
        exact (h1.mul h2).deriv
      rw [hd_y]
      have hd_v : HasDerivAt (fun v' => 2 * (Real.sinh y - v' * Real.exp (-y)) * F (charA v' y))
          (2 * (-Real.exp (-y)) * F (charA v y) +
            2 * (Real.sinh y - v * Real.exp (-y)) * (deriv F (charA v y) * Real.exp (-y))) v := by
        have h1 : HasDerivAt (fun v' => 2 * (Real.sinh y - v' * Real.exp (-y)))
            (2 * (-Real.exp (-y))) v := by
          have h := ((hasDerivAt_id' v).mul_const (Real.exp (-y))).const_sub (Real.sinh y)
          convert h.const_mul 2 using 1; ring
        have h2 : HasDerivAt (fun v' => F (charA v' y))
            (deriv F (charA v y) * Real.exp (-y)) v :=
          (hFdiff (charA v y)).hasDerivAt.comp v (charA.hasDerivAt_v v y)
        exact h1.mul h2
      refine hd_v.congr_of_eventuallyEq h_ev_v |>.congr_deriv ?_
      ring
  · have hA_cont_v : ContinuousAt (fun v' => charA v' y) v := by
      unfold charA; fun_prop
    have h_ev_v : ∀ᶠ v' in 𝓝 v, hBranch sgn F v' y = 0 := by
      have h_nhds : {v' : ℝ | charA v' y < a₀} ∈ 𝓝 v :=
        hA_cont_v.preimage_mem_nhds (Iio_mem_nhds (hy ▸ hcrit))
      filter_upwards [h_nhds] with v' hv'
      simp [hBranch, hF0 _ hv'.le]
    have hA_cont_y : ContinuousAt (charA v) y := by unfold charA; fun_prop
    have h_ev_y : ψBranch sgn F v =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      have h_nhds : {y' : ℝ | charA v y' < a₀} ∈ 𝓝 y :=
        hA_cont_y.preimage_mem_nhds (Iio_mem_nhds (hy ▸ hcrit))
      filter_upwards [h_nhds] with y' hy'
      simp [ψBranch, hF0 _ hy'.le]
    rw [h_ev_y.deriv_eq, deriv_const', mul_zero]
    exact (hasDerivAt_const v (0 : ℝ)).congr_of_eventuallyEq h_ev_v
  · have h_ev_v : ∀ᶠ v' in 𝓝 v,
        hBranch sgn F v' y = if sgn then 0 else 2 * (Real.sinh y - v' * Real.exp (-y)) * F (charA v' y) := by
      filter_upwards [hyCrit_at.eventually (isOpen_Ioi.mem_nhds hy)] with v' hv'
      cases sgn <;> simp [hBranch, hv', not_lt.mpr hv'.le]
    have h_ev_y : ψBranch sgn F v =ᶠ[𝓝 y]
        if sgn then fun _ => (0 : ℝ) else fun y' => Real.exp (-y') * F (charA v y') := by
      filter_upwards [eventually_lt_nhds hy] with y' hy'
      cases sgn <;> simp [ψBranch, hy', not_lt.mpr hy'.le]
    rw [h_ev_y.deriv_eq]
    cases sgn
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hd_y : deriv (fun y' => Real.exp (-y') * F (charA v y')) y =
          (-Real.exp (-y)) * F (charA v y) +
          Real.exp (-y) * (deriv F (charA v y) * (Real.sinh y - v * Real.exp (-y))) := by
        have h1 : HasDerivAt (fun y' => Real.exp (-y')) (-Real.exp (-y)) y := by
          simpa using (hasDerivAt_id' y).neg.exp
        have h2 : HasDerivAt (fun y' => F (charA v y'))
            (deriv F (charA v y) * (Real.sinh y - v * Real.exp (-y))) y :=
          (hFdiff (charA v y)).hasDerivAt.comp y (charA.hasDerivAt_y v y)
        exact (h1.mul h2).deriv
      rw [hd_y]
      have hd_v : HasDerivAt (fun v' => 2 * (Real.sinh y - v' * Real.exp (-y)) * F (charA v' y))
          (2 * (-Real.exp (-y)) * F (charA v y) +
            2 * (Real.sinh y - v * Real.exp (-y)) * (deriv F (charA v y) * Real.exp (-y))) v := by
        have h1 : HasDerivAt (fun v' => 2 * (Real.sinh y - v' * Real.exp (-y)))
            (2 * (-Real.exp (-y))) v := by
          have h := ((hasDerivAt_id' v).mul_const (Real.exp (-y))).const_sub (Real.sinh y)
          convert h.const_mul 2 using 1; ring
        have h2 : HasDerivAt (fun v' => F (charA v' y))
            (deriv F (charA v y) * Real.exp (-y)) v :=
          (hFdiff (charA v y)).hasDerivAt.comp v (charA.hasDerivAt_v v y)
        exact h1.mul h2
      refine hd_v.congr_of_eventuallyEq h_ev_v |>.congr_deriv ?_
      ring
    · simp only [↓reduceIte, deriv_const', mul_zero]
      exact (hasDerivAt_const v (0 : ℝ)).congr_of_eventuallyEq h_ev_v

theorem continuous {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    {v₀ a₀ : ℝ} (hv₀ : 0 ≤ v₀) (ha₀ : Real.sqrt (1 + 2 * v₀) < a₀)
    (hF0 : ∀ a ≤ a₀, F a = 0) (sgn : Bool) {v : ℝ} (hv : 0 ≤ v) (hvv₀ : v ≤ v₀) :
    Continuous (hBranch sgn F v) := by
  have heq : hBranch sgn F v = fun y => (Real.exp (2 * y) - 2 * v - 1) * ψBranch sgn F v y := by
    funext y; exact eq_mul_ψBranch sgn F v y
  rw [heq]
  have hψc : Continuous (ψBranch sgn F v) :=
    (ψBranch.contDiff hF hv₀ ha₀ hF0 sgn hv hvv₀).continuous
  fun_prop


end hBranch

end Lyasoff2016
