/-
Helpers for Brownian time-reversal on a fixed interval [0, t].
Used by `time_reversal` (paper (1.3), p. 1063).

The process coincides with `s ↦ W_t − W_{t−s}` on `[0, t]` and with `W` thereafter,
so that the result remains a Brownian motion on all of `ℝ≥0`.
-/
import Mathlib.Probability.BrownianMotion.Basic

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

/- Paper: p. 1063, proof of (1.3).
   Plain recap: on [0,t], the process s ↦ W_t − W_{t−s} is again Brownian; past t we keep W. -/
def timeReversed (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun s ω => if s ≤ t then W t ω - W (t - s) ω else W s ω

theorem timeReversed_zero (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    timeReversed W t 0 ω = 0 := by
  simp [timeReversed]

theorem timeReversed_eq_on_Icc (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) {s : ℝ≥0} (hs : s ≤ t) (ω : Ω) :
    timeReversed W t s ω = W t ω - W (t - s) ω := by
  simp [timeReversed, hs]

theorem timeReversed_eq_of_gt (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) {s : ℝ≥0} (hs : ¬ s ≤ t) (ω : Ω) :
    timeReversed W t s ω = W s ω := by
  simp [timeReversed, hs]

/- Paper: p. 1063.
   Plain recap: for s,u ≤ t the time-reversed increments have BM covariance min(s,u). -/
theorem covariance_timeReversed_le (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsPreBrownianReal W P) (t : ℝ≥0) {s u : ℝ≥0}
    (hs : s ≤ t) (hu : u ≤ t) :
    covariance (fun ω => W t ω - W (t - s) ω) (fun ω => W t ω - W (t - u) ω) P =
      ↑(min s u) := by
  have hWt : MemLp (W t) 2 P := (hW.hasLaw_eval t).memLp (memLp_id_gaussianReal (2 : ℝ≥0))
  have hWs : MemLp (W (t - s)) 2 P :=
    (hW.hasLaw_eval (t - s)).memLp (memLp_id_gaussianReal (2 : ℝ≥0))
  have hWu : MemLp (W (t - u)) 2 P :=
    (hW.hasLaw_eval (t - u)).memLp (memLp_id_gaussianReal (2 : ℝ≥0))
  have hbilin :=
    covariance_fun_sub_fun_sub (X := W t) (Y := W (t - s)) (Z := W t) (T := W (t - u))
      hWt hWs hWt hWu
  rw [hbilin]
  have h1 : covariance (W t) (W t) P = ↑t := by simpa using hW.covariance_eval t t
  have h2 : covariance (W t) (W (t - u)) P = ↑(min t (t - u)) := by
    simpa using hW.covariance_eval t (t - u)
  have h3 : covariance (W (t - s)) (W t) P = ↑(min (t - s) t) := by
    simpa using hW.covariance_eval (t - s) t
  have h4 : covariance (W (t - s)) (W (t - u)) P = ↑(min (t - s) (t - u)) := by
    simpa using hW.covariance_eval (t - s) (t - u)
  rw [h1, h2, h3, h4]
  have htu : min t (t - u) = t - u := min_eq_right tsub_le_self
  have hts : min (t - s) t = t - s := min_eq_left tsub_le_self
  rw [htu, hts]
  have hmin : min (t - s) (t - u) = t - max s u := by
    cases le_total s u with
    | inl h =>
      have : t - u ≤ t - s := tsub_le_tsub_left h t
      rw [min_eq_right this, max_eq_right h]
    | inr h =>
      have : t - s ≤ t - u := tsub_le_tsub_left h t
      rw [min_eq_left this, max_eq_left h]
  rw [hmin]
  have hsu : s ≤ t := hs
  have huu : u ≤ t := hu
  have hmax : max s u ≤ t := max_le hsu huu
  have hcoe1 : (↑(t - u) : ℝ) = ↑t - ↑u := NNReal.coe_sub huu
  have hcoe2 : (↑(t - s) : ℝ) = ↑t - ↑s := NNReal.coe_sub hsu
  have hcoe3 : (↑(t - max s u) : ℝ) = ↑t - ↑(max s u) := NNReal.coe_sub hmax
  rw [hcoe1, hcoe2, hcoe3, NNReal.coe_max, NNReal.coe_min]
  have hsm : (s : ℝ) + ↑u - max ↑s ↑u = min ↑s ↑u := by
    cases le_total (s : ℝ) (u : ℝ) with
    | inl h => rw [max_eq_right h, min_eq_left h]; ring
    | inr h => rw [max_eq_left h, min_eq_right h]; ring
  convert hsm using 1
  ring

private theorem timeReversed_eq_fun_le (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) {s : ℝ≥0} (hs : s ≤ t) :
    timeReversed W t s = fun ω => W t ω - W (t - s) ω :=
  funext fun ω => timeReversed_eq_on_Icc W t hs ω

private theorem timeReversed_eq_fun_gt (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) {s : ℝ≥0} (hs : ¬ s ≤ t) :
    timeReversed W t s = W s :=
  funext fun ω => timeReversed_eq_of_gt W t hs ω

private theorem covariance_timeReversed_aux (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsPreBrownianReal W P) (t : ℝ≥0) (s u : ℝ≥0) :
    covariance (timeReversed W t s) (timeReversed W t u) P = ↑(min s u) := by
  by_cases hs : s ≤ t <;> by_cases hu : u ≤ t
  · -- both ≤ t
    rw [timeReversed_eq_fun_le W t hs, timeReversed_eq_fun_le W t hu]
    exact covariance_timeReversed_le P W hW t hs hu
  · -- s ≤ t < u
    have hu' : t ≤ u := le_of_not_ge hu
    rw [timeReversed_eq_fun_le W t hs, timeReversed_eq_fun_gt W t hu]
    have hWt : MemLp (W t) 2 P := (hW.hasLaw_eval t).memLp (memLp_id_gaussianReal (2 : ℝ≥0))
    have hWs : MemLp (W (t - s)) 2 P :=
      (hW.hasLaw_eval (t - s)).memLp (memLp_id_gaussianReal (2 : ℝ≥0))
    have hWu : MemLp (W u) 2 P := (hW.hasLaw_eval u).memLp (memLp_id_gaussianReal (2 : ℝ≥0))
    rw [covariance_fun_sub_left hWt hWs hWu, hW.covariance_fun_eval, hW.covariance_fun_eval]
    have h1 : min t u = t := min_eq_left hu'
    have h2 : min (t - s) u = t - s := min_eq_left (le_trans tsub_le_self hu')
    rw [h1, h2, NNReal.coe_sub hs, NNReal.coe_min]
    have hsu : (s : ℝ) ≤ u :=
      (NNReal.coe_le_coe.mpr hs).trans (NNReal.coe_le_coe.mpr hu')
    rw [min_eq_left hsu]
    ring
  · -- u ≤ t < s
    have hs' : t ≤ s := le_of_not_ge hs
    rw [timeReversed_eq_fun_gt W t hs, timeReversed_eq_fun_le W t hu]
    have hWt : MemLp (W t) 2 P := (hW.hasLaw_eval t).memLp (memLp_id_gaussianReal (2 : ℝ≥0))
    have hWu : MemLp (W (t - u)) 2 P :=
      (hW.hasLaw_eval (t - u)).memLp (memLp_id_gaussianReal (2 : ℝ≥0))
    have hWs : MemLp (W s) 2 P := (hW.hasLaw_eval s).memLp (memLp_id_gaussianReal (2 : ℝ≥0))
    rw [covariance_fun_sub_right hWs hWt hWu, hW.covariance_fun_eval, hW.covariance_fun_eval]
    have h1 : min s t = t := min_eq_right hs'
    have h2 : min s (t - u) = t - u := min_eq_right (le_trans tsub_le_self hs')
    rw [h1, h2, NNReal.coe_sub hu, NNReal.coe_min]
    have hus : (u : ℝ) ≤ s :=
      (NNReal.coe_le_coe.mpr hu).trans (NNReal.coe_le_coe.mpr hs')
    rw [min_eq_right hus]
    ring
  · -- both > t
    rw [timeReversed_eq_fun_gt W t hs, timeReversed_eq_fun_gt W t hu]
    simpa using hW.covariance_eval s u

private theorem isGaussianProcess_timeReversed (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (hW : IsGaussianProcess W P) (t : ℝ≥0) :
    IsGaussianProcess (timeReversed W t) P := by
  classical
  refine hW.of_isGaussianProcess fun s ↦ ?_
  by_cases hs : s ≤ t
  · refine ⟨{t, t - s},
      { toFun x := x ⟨t, by simp⟩ - x ⟨t - s, by simp⟩
        map_add' x y := by
          simp only [Pi.add_apply]
          abel
        map_smul' c x := by
          simp only [Pi.smul_apply, RingHom.id_apply]
          module }, ?_⟩
    intro ω
    rw [timeReversed_eq_on_Icc W t hs]
    simp [Finset.restrict_def]
  · refine ⟨{s},
      { toFun x := x ⟨s, by simp⟩
        map_add' := by simp
        map_smul' := by simp }, ?_⟩
    intro ω
    rw [timeReversed_eq_of_gt W t hs]
    simp [Finset.restrict_def]

/- The finite-dimensional laws of the time-reversed process match those of BM. -/
theorem isPreBrownianReal_timeReversed (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBrownianReal W P) (t : ℝ≥0) :
    IsPreBrownianReal (timeReversed W t) P := by
  have : IsProbabilityMeasure P := hW.isGaussianProcess.isProbabilityMeasure
  refine IsGaussianProcess.isPreBrownianReal_of_covariance
    (isGaussianProcess_timeReversed P W hW.isGaussianProcess t) (fun s ↦ ?_) (fun s u hsu ↦ ?_)
  · by_cases hs : s ≤ t
    · rw [timeReversed_eq_fun_le W t hs, integral_sub, hW.integral_eval, hW.integral_eval,
        sub_zero]
      · exact (hW.isGaussianProcess.hasGaussianLaw_eval _).integrable
      · exact (hW.isGaussianProcess.hasGaussianLaw_eval _).integrable
    · rw [timeReversed_eq_fun_gt W t hs]
      exact hW.integral_eval s
  · have hcov := covariance_timeReversed_aux (P := P) W hW.toIsPreBrownianReal t s u
    rwa [min_eq_left hsu] at hcov

theorem isBrownianReal_timeReversed (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBrownianReal W P) (t : ℝ≥0) :
    IsBrownianReal (timeReversed W t) P := by
  refine ⟨isPreBrownianReal_timeReversed P W hW t, ?_⟩
  filter_upwards [hW.cont, hW.eval_zero_ae_eq_zero] with ω hω h0
  refine Continuous.if_le
    (continuous_const.sub (hω.comp (continuous_const.sub continuous_id))) hω
    continuous_id continuous_const ?_
  intro x hx
  -- at the interface x = t: W t − W 0 = W t since W 0 = 0 a.s.
  simp [hx, h0]

end Lyasoff2016
