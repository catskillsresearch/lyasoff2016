/-
Characteristic-branch cutoff `ψ` along `A(v, ·)`.
-/
module

public import Lyasoff2016.CharA
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Topology.MetricSpace.Basic


@[expose] public section

open Set Filter Topology Metric
open scoped Real Topology

noncomputable section
namespace Lyasoff2016

/-- Branch cutoff of a compactly supported profile along the characteristic `A`. -/
def ψBranch (sgn : Bool) (F : ℝ → ℝ) (v y : ℝ) : ℝ :=
  if (if sgn then yCrit v < y else y < yCrit v) then Real.exp (-y) * F (charA v y) else 0

lemma abs_sinh_le_cosh (y : ℝ) : |Real.sinh y| ≤ Real.cosh y := by
  rw [Real.sinh_eq, Real.cosh_eq, abs_div, abs_of_pos (two_pos : (0 : ℝ) < 2)]
  refine div_le_div_of_nonneg_right ?_ two_pos.le
  refine (abs_sub _ _).trans ?_
  rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]

namespace ψBranch

theorem compactSupport_bound {F : ℝ → ℝ} (hFC : HasCompactSupport F) :
    ∃ R > 0, ∀ sgn v, 0 ≤ v → ∀ y, R ≤ |y| →
      ψBranch sgn F v y = 0 := by
  obtain ⟨M, hM0, hM⟩ : ∃ M > 0, ∀ a, M ≤ |a| → F a = 0 := by
    obtain ⟨M, hM⟩ := hFC.isCompact.isBounded.subset_closedBall (0 : ℝ)
    refine ⟨max M 1 + 1, by positivity, fun a ha => ?_⟩
    by_contra hne
    have hmem : a ∈ tsupport F := subset_tsupport F hne
    have := hM hmem
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    linarith [le_max_left M 1, le_max_right M 1]
  refine ⟨max (Real.log (2 * (M + 1))) 1, by positivity, fun sgn v hv y hy => ?_⟩
  have hlog : Real.log (2 * (M + 1)) ≤ |y| := (le_max_left _ _).trans hy
  have hexp : 2 * (M + 1) ≤ Real.exp |y| := by
    rw [← Real.exp_log (by positivity : 0 < 2 * (M + 1))]
    exact Real.exp_le_exp.mpr hlog
  have hA : M ≤ |charA v y| := by
    have h1 := charA.lower_bound hv (y := y)
    have h2 : 0 ≤ charA v y := (by positivity : 0 ≤ Real.exp |y| / 2).trans h1
    rw [abs_of_nonneg h2]
    linarith
  have hF0 : F (charA v y) = 0 := hM (charA v y) hA
  simp [ψBranch, hF0]

theorem contDiff {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    {v₀ a₀ : ℝ} (_hv₀ : 0 ≤ v₀) (ha₀ : Real.sqrt (1 + 2 * v₀) < a₀)
    (hF0 : ∀ a ≤ a₀, F a = 0) (sgn : Bool) {v : ℝ} (hv : 0 ≤ v) (hvv₀ : v ≤ v₀) :
    ContDiff ℝ 3 (ψBranch sgn F v) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  have hcrit : charA v (yCrit v) < a₀ := by
    rw [charA.yCrit hv]
    exact lt_of_le_of_lt (Real.sqrt_le_sqrt (by linarith)) ha₀
  rcases lt_trichotomy (yCrit v) y with hy | hy | hy
  · have hF_smooth : ContDiffAt ℝ 3 (fun y' => Real.exp (-y') * F (charA v y')) y := by
      have hA : ContDiff ℝ 3 (charA v) := by unfold charA; fun_prop
      exact (contDiff_id.neg.exp.contDiffAt).mul ((hF.comp hA).contDiffAt)
    cases sgn
    · have h_ev : ψBranch false F v =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        filter_upwards [eventually_gt_nhds hy] with y' hy'
        simp [ψBranch, not_lt.mpr hy'.le]
      exact contDiffAt_const.congr_of_eventuallyEq h_ev
    · have h_ev : ψBranch true F v =ᶠ[𝓝 y] fun y' => Real.exp (-y') * F (charA v y') := by
        filter_upwards [eventually_gt_nhds hy] with y' hy'
        simp [ψBranch, hy']
      exact hF_smooth.congr_of_eventuallyEq h_ev
  · have hAcont : Continuous (charA v) := by unfold charA; fun_prop
    have h_nhds : {y' : ℝ | charA v y' < a₀} ∈ 𝓝 (yCrit v) :=
      hAcont.continuousAt.preimage_mem_nhds (Iio_mem_nhds hcrit)
    have h_ev : ψBranch sgn F v =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      rw [← hy]
      filter_upwards [h_nhds] with y' hy'
      simp [ψBranch, hF0 _ (le_of_lt hy')]
    exact contDiffAt_const.congr_of_eventuallyEq h_ev
  · have hF_smooth : ContDiffAt ℝ 3 (fun y' => Real.exp (-y') * F (charA v y')) y := by
      have hA : ContDiff ℝ 3 (charA v) := by unfold charA; fun_prop
      exact (contDiff_id.neg.exp.contDiffAt).mul ((hF.comp hA).contDiffAt)
    cases sgn
    · have h_ev : ψBranch false F v =ᶠ[𝓝 y] fun y' => Real.exp (-y') * F (charA v y') := by
        filter_upwards [eventually_lt_nhds hy] with y' hy'
        simp [ψBranch, hy']
      exact hF_smooth.congr_of_eventuallyEq h_ev
    · have h_ev : ψBranch true F v =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        filter_upwards [eventually_lt_nhds hy] with y' hy'
        simp [ψBranch, not_lt.mpr hy'.le]
      exact contDiffAt_const.congr_of_eventuallyEq h_ev


theorem hasCompactSupport {F : ℝ → ℝ} (hFC : HasCompactSupport F)
    (sgn : Bool) {v : ℝ} (hv : 0 ≤ v) :
    HasCompactSupport (ψBranch sgn F v) := by
  obtain ⟨R, hR0, hR⟩ := compactSupport_bound hFC
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -R) (b := R)) ?_
  intro y hy
  by_contra hnot
  have habs : R ≤ |y| := by
    change ¬(-R ≤ y ∧ y ≤ R) at hnot
    push_neg at hnot
    by_cases hyR : -R ≤ y
    · exact le_trans (hnot hyR).le (le_abs_self y)
    · exact le_trans (by linarith [lt_of_not_ge hyR]) (neg_le_abs y)
  exact hy (hR sgn v hv y habs)


theorem deriv_continuous {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    {v₀ a₀ : ℝ} (hv₀ : 0 ≤ v₀) (ha₀ : Real.sqrt (1 + 2 * v₀) < a₀)
    (hF0 : ∀ a ≤ a₀, F a = 0) (sgn : Bool) {v : ℝ} (hv : 0 ≤ v) (hvv₀ : v ≤ v₀) :
    Continuous (deriv (ψBranch sgn F v)) := by
  have hψ3 := contDiff hF hv₀ ha₀ hF0 sgn hv hvv₀
  exact ((contDiff_succ_iff_deriv (n := 2)).mp hψ3).2.2.continuous


theorem deriv_bound {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F) (_hFC : HasCompactSupport F)
    {v₀ a₀ : ℝ} (hv₀ : 0 ≤ v₀) (ha₀ : Real.sqrt (1 + 2 * v₀) < a₀)
    (hF0 : ∀ a ≤ a₀, F a = 0) (sgn : Bool) {R CF : ℝ} (hR0 : 0 < R) (hCF0 : 0 ≤ CF)
    (hR : ∀ sgn' v', 0 ≤ v' → ∀ y, R ≤ |y| → ψBranch sgn' F v' y = 0)
    (hF_bdd : ∀ a, |F a| ≤ CF) (hF'_bdd : ∀ a, |deriv F a| ≤ CF)
    {v : ℝ} (hv : 0 ≤ v) (hvv₀ : v ≤ v₀) (y : ℝ) :
    |deriv (ψBranch sgn F v) y| ≤
      Real.exp R * CF + Real.exp R * CF * (Real.cosh R + v₀ * Real.exp R) := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hFdiff : Differentiable ℝ F := hF1.differentiable (by norm_num)
  by_cases hyR : R < |y|
  · have h_ev : ψBranch sgn F v =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      have h_nhds : {y' : ℝ | R < |y'|} ∈ 𝓝 y :=
        isOpen_lt continuous_const continuous_abs |>.mem_nhds hyR
      filter_upwards [h_nhds] with y' hy'
      exact hR sgn v hv y' hy'.le
    rw [h_ev.deriv_eq, deriv_const', abs_zero]
    have hc : 0 ≤ Real.cosh R + v₀ * Real.exp R := by positivity
    positivity
  · have hyR' : |y| ≤ R := not_lt.mp hyR
    have hcrit : charA v (yCrit v) < a₀ := by
      rw [charA.yCrit hv]
      exact lt_of_le_of_lt (Real.sqrt_le_sqrt (by linarith)) ha₀
    have hexp_le : Real.exp (-y) ≤ Real.exp R := Real.exp_le_exp.mpr ((neg_le_abs y).trans hyR')
    have hfac_le : |Real.sinh y - v * Real.exp (-y)| ≤ Real.cosh R + v₀ * Real.exp R := by
      calc |Real.sinh y - v * Real.exp (-y)|
          ≤ |Real.sinh y| + |v * Real.exp (-y)| := abs_sub _ _
        _ ≤ Real.cosh y + v * Real.exp (-y) := by
            rw [abs_mul, abs_of_nonneg hv, abs_of_pos (Real.exp_pos _)]
            exact add_le_add (abs_sinh_le_cosh y) le_rfl
        _ ≤ Real.cosh R + v₀ * Real.exp R :=
            add_le_add (Real.cosh_le_cosh.mpr (by rw [abs_of_pos hR0]; exact hyR'))
              (mul_le_mul hvv₀ hexp_le (Real.exp_pos _).le hv₀)
    have hval_le : |-Real.exp (-y) * F (charA v y) +
          Real.exp (-y) * (deriv F (charA v y) * (Real.sinh y - v * Real.exp (-y)))| ≤
        Real.exp R * CF + Real.exp R * CF * (Real.cosh R + v₀ * Real.exp R) := by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul hexp_le (hF_bdd _) (abs_nonneg _) (Real.exp_pos _).le
      · rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_mul]
        calc Real.exp (-y) * (|deriv F (charA v y)| * |Real.sinh y - v * Real.exp (-y)|)
            ≤ Real.exp R * (CF * (Real.cosh R + v₀ * Real.exp R)) :=
              mul_le_mul hexp_le (mul_le_mul (hF'_bdd _) hfac_le (abs_nonneg _) hCF0)
                (by positivity) (Real.exp_pos _).le
          _ = Real.exp R * CF * (Real.cosh R + v₀ * Real.exp R) := by ring
    rcases lt_trichotomy (yCrit v) y with hy | hy | hy
    · have h_ev_y : ψBranch sgn F v =ᶠ[𝓝 y]
          if sgn then fun y' => Real.exp (-y') * F (charA v y') else fun _ => (0 : ℝ) := by
        filter_upwards [eventually_gt_nhds hy] with y' hy'
        cases sgn <;> simp [ψBranch, hy', not_lt.mpr hy'.le]
      rw [h_ev_y.deriv_eq]
      cases sgn
      · simp only [Bool.false_eq_true, ↓reduceIte, deriv_const', abs_zero]
        have hc : 0 ≤ Real.cosh R + v₀ * Real.exp R := by positivity
        positivity
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
        exact hval_le
    · have hA_cont_y : ContinuousAt (charA v) y := by unfold charA; fun_prop
      have h_ev_y : ψBranch sgn F v =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        have h_nhds : {y' : ℝ | charA v y' < a₀} ∈ 𝓝 y :=
          hA_cont_y.preimage_mem_nhds (Iio_mem_nhds (hy ▸ hcrit))
        filter_upwards [h_nhds] with y' hy'
        simp [ψBranch, hF0 _ hy'.le]
      rw [h_ev_y.deriv_eq, deriv_const', abs_zero]
      have hc : 0 ≤ Real.cosh R + v₀ * Real.exp R := by positivity
      positivity
    · have h_ev_y : ψBranch sgn F v =ᶠ[𝓝 y]
          if sgn then fun _ => (0 : ℝ) else fun y' => Real.exp (-y') * F (charA v y') := by
        filter_upwards [eventually_lt_nhds hy] with y' hy'
        cases sgn <;> simp [ψBranch, hy', not_lt.mpr hy'.le]
      rw [h_ev_y.deriv_eq]
      cases sgn
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hd_y : deriv (fun y' => Real.exp (-y')) y = -Real.exp (-y) := by
          simpa using ((hasDerivAt_id' y).neg.exp).deriv
        have hd_y' : deriv (fun y' => Real.exp (-y') * F (charA v y')) y =
            (-Real.exp (-y)) * F (charA v y) +
            Real.exp (-y) * (deriv F (charA v y) * (Real.sinh y - v * Real.exp (-y))) := by
          have h1 : HasDerivAt (fun y' => Real.exp (-y')) (-Real.exp (-y)) y := by
            simpa using (hasDerivAt_id' y).neg.exp
          have h2 : HasDerivAt (fun y' => F (charA v y'))
              (deriv F (charA v y) * (Real.sinh y - v * Real.exp (-y))) y :=
            (hFdiff (charA v y)).hasDerivAt.comp y (charA.hasDerivAt_y v y)
          exact (h1.mul h2).deriv
        rw [hd_y']
        exact hval_le
      · simp only [↓reduceIte, deriv_const', abs_zero]
        have hc : 0 ≤ Real.cosh R + v₀ * Real.exp R := by positivity
        positivity

end ψBranch

end Lyasoff2016
