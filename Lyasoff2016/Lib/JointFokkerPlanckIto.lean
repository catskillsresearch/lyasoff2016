/-
Ito identities for product test functions along `(expInt, W)`, used by `fokker_planck_joint`.
-/
import Lyasoff2016.Setting
import MathFin.Probability.Brownian.Ito.ItoFormulaTD
import MathFin.Probability.Brownian.Ito.ItoFormulaCLM
import MathFin.Probability.Brownian.Ito.ItoFormulaAdaptedProcess
import MathFin.Probability.Brownian.Ito.ItoProductRule
import MathFin.Probability.Brownian.Ito.ItoIntegralProcessGeneral
import MathFin.Probability.Brownian.Ito.ItoIntegralLocalisedPredictable
import MathFin.Probability.Brownian.Ito.ItoIntegralBrownian
import Mathlib.Analysis.Calculus.ContDiff.Basic

open MeasureTheory ProbabilityTheory Set Filter Topology
open MeasureTheory.Measure
open MathFin ItoFormulaAdapted ItoIntegralL2 ItoIntegralProcessGeneral ItoIntegralBrownian
  ItoIntegralCLM
open scoped NNReal ENNReal

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Compactly supported `C^∞` functions are bounded with their first two derivatives. -/
theorem contDiff_top_compactSupport_bounds {u : ℝ → ℝ}
    (hu : ContDiff ℝ (⊤ : WithTop ℕ∞) u) (huC : HasCompactSupport u) :
    ∃ C : ℝ, (∀ x, |u x| ≤ C) ∧ (∀ x, |deriv u x| ≤ C) ∧ (∀ x, |deriv (deriv u) x| ≤ C) := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by decide)
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by decide)
  have h0c : Continuous u := hu.continuous
  have h1c : Continuous (deriv u) := ContDiff.continuous_deriv_one hu1
  have h2c : Continuous (deriv (deriv u)) := by
    have hder1 : ContDiff ℝ 1 (deriv u) := (contDiff_succ_iff_deriv (n := 1)).mp hu2 |>.2.2
    exact ContDiff.continuous_deriv_one hder1
  obtain ⟨A0, hA0⟩ := h0c.bounded_above_of_compact_support huC
  obtain ⟨A1, hA1⟩ := h1c.bounded_above_of_compact_support huC.deriv
  obtain ⟨A2, hA2⟩ := h2c.bounded_above_of_compact_support huC.deriv.deriv
  refine ⟨max A0 (max A1 A2), ?_, ?_, ?_⟩
  · intro x
    have : |u x| ≤ A0 := by simpa [Real.norm_eq_abs] using hA0 x
    exact this.trans (le_max_left _ _)
  · intro x
    have : |deriv u x| ≤ A1 := by simpa [Real.norm_eq_abs] using hA1 x
    exact this.trans (le_trans (le_max_left _ _) (le_max_right _ _))
  · intro x
    have : |deriv (deriv u) x| ≤ A2 := by simpa [Real.norm_eq_abs] using hA2 x
    exact this.trans (le_trans (le_max_right _ _) (le_max_right _ _))

/-- Pathwise FTC for `u ∘ expInt` along a continuous path. -/
theorem pathwise_u_expInt_ftc (B : ℝ≥0 → ℝ) (hBcont : Continuous B)
    (σ : ℝ) (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (t : ℝ≥0) :
    u (∫ s in (0 : ℝ)..(t : ℝ), Real.exp (σ * B s.toNNReal)) - u 0 =
      ∫ s in (0 : ℝ)..(t : ℝ),
        deriv u (∫ r in (0 : ℝ)..s, Real.exp (σ * B r.toNNReal)) *
          Real.exp (σ * B s.toNNReal) := by
  set g : ℝ → ℝ := fun s => Real.exp (σ * B s.toNNReal)
  have hgcont : Continuous g := by
    simp only [g]
    exact Real.continuous_exp.comp
      (continuous_const.mul (hBcont.comp continuous_real_toNNReal))
  set X : ℝ → ℝ := fun τ => ∫ s in (0 : ℝ)..τ, g s
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := NNReal.coe_nonneg t
  have hXcont : Continuous X :=
    intervalIntegral.continuous_primitive (fun _ _ => hgcont.intervalIntegrable _ _) 0
  have hXderiv (τ : ℝ) : HasDerivAt X (g τ) τ :=
    intervalIntegral.integral_hasDerivAt_right (hgcont.intervalIntegrable _ _)
      (hgcont.stronglyMeasurableAtFilter volume (nhds τ)) hgcont.continuousAt
  have hu' (x : ℝ) : HasDerivAt u (deriv u x) x :=
    (hu.differentiable (by decide)).differentiableAt.hasDerivAt
  have hUderiv (τ : ℝ) (_hτ : τ ∈ Ioo (0 : ℝ) t) :
      HasDerivAt (u ∘ X) (deriv u (X τ) * g τ) τ := by
    convert (hu' (X τ)).scomp τ (hXderiv τ) using 1
    simp [smul_eq_mul, mul_comm]
  have hcontOn : ContinuousOn (u ∘ X) (Icc (0 : ℝ) t) :=
    (hu.continuous.comp hXcont).continuousOn
  have hint : IntervalIntegrable (fun s => deriv u (X s) * g s) volume 0 t :=
    (((hu.continuous_deriv (by decide)).comp hXcont).mul hgcont).intervalIntegrable _ _
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht0 hcontOn hUderiv hint
  have hX0 : X 0 = 0 := by simp [X, intervalIntegral.integral_same]
  calc
    u (∫ s in (0 : ℝ)..(t : ℝ), Real.exp (σ * B s.toNNReal)) - u 0
        = (u ∘ X) t - (u ∘ X) 0 := by simp [Function.comp_apply, X, g, hX0]
      _ = ∫ s in (0 : ℝ)..(t : ℝ), deriv u (X s) * g s := by simpa using hFTC.symm
      _ = ∫ s in (0 : ℝ)..(t : ℝ),
            deriv u (∫ r in (0 : ℝ)..s, Real.exp (σ * B r.toNNReal)) *
              Real.exp (σ * B s.toNNReal) := by
          rfl

/-- Paper (3.4a) for product tests `ϕ = u ⊗ v`. -/
theorem ito_expInt_test_product (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (σ : ℝ) (t : ℝ≥0)
    (u v : ℝ → ℝ) (hu : ContDiff ℝ (⊤ : WithTop ℕ∞) u)
    (hv : ContDiff ℝ (⊤ : WithTop ℕ∞) v)
    (huC : HasCompactSupport u) (hvC : HasCompactSupport v) :
    (∫ ω, u (expInt W σ 0 t ω) * v (W t ω) ∂P) - u 0 * v 0 =
      ∫ s in Ioc (0 : ℝ) t,
        (∫ ω,
          deriv u (expInt W σ 0 s.toNNReal ω) * Real.exp (σ * W s.toNNReal ω) * v (W s.toNNReal ω)
            + u (expInt W σ 0 s.toNNReal ω) * ((1 : ℝ) / 2) *
                deriv (deriv v) (W s.toNNReal ω) ∂P) := by
  obtain ⟨Cv, hv_bdd, hv'_bdd, hv''_bdd⟩ := contDiff_top_compactSupport_bounds hv hvC
  have hv3 : ContDiff ℝ 3 v := hv.of_le (by decide)
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by decide)
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by decide)
  have hder1 : ContDiff ℝ 1 (deriv v) := (contDiff_succ_iff_deriv (n := 1)).mp hv2 |>.2.2
  have hder2 : ContDiff ℝ 1 (deriv (deriv v)) := by
    have h2' : ContDiff ℝ 2 (deriv v) := (contDiff_succ_iff_deriv (n := 2)).mp hv3 |>.2.2
    exact (contDiff_succ_iff_deriv (n := 1)).mp h2' |>.2.2
  have hv'''c : Continuous (deriv (deriv (deriv v))) := ContDiff.continuous_deriv_one hder2
  obtain ⟨Cv3, hv3_bdd⟩ :=
    hv'''c.bounded_above_of_compact_support hvC.deriv.deriv.deriv
  have hv' (x : ℝ) : HasDerivAt v (deriv v x) x :=
    (hv1.differentiable (by decide)).differentiableAt.hasDerivAt
  have hv'' (x : ℝ) : HasDerivAt (deriv v) (deriv (deriv v) x) x :=
    (hder1.differentiable (by decide)).differentiableAt.hasDerivAt
  have hv''' (x : ℝ) : HasDerivAt (deriv (deriv v)) (deriv (deriv (deriv v)) x) x :=
    (hder2.differentiable (by decide)).differentiableAt.hasDerivAt
  obtain ⟨gf', hname, hIto⟩ :=
    ito_formula_L2_bddDeriv_mk (μ := P) (X := W) hW.toIsPreBrownianReal t
      (f := v) (f' := deriv v) (f'' := deriv (deriv v)) (f''' := deriv (deriv (deriv v)))
      hv' hv'' hv''' (C1 := Cv) hv'_bdd (C2 := Cv) hv''_bdd (C3 := Cv3)
      (fun x => by simpa [Real.norm_eq_abs] using hv3_bdd x)
  set B : ℝ≥0 → Ω → ℝ := hW.toIsPreBrownianReal.mk W
  have hBmeas : ∀ s, Measurable (B s) := hW.toIsPreBrownianReal.measurable_mk
  have hBcont : ∀ ω, Continuous fun s : ℝ≥0 => B s ω := hW.toIsPreBrownianReal.continuous_mk
  have hBpre : IsPreBrownianReal B P :=
    hW.toIsPreBrownianReal.isBrownianReal_mk.toIsPreBrownianReal
  have hB0 : B 0 =ᵐ[P] fun _ => (0 : ℝ) :=
    (hW.toIsPreBrownianReal.isBrownianReal_mk).eval_zero_ae_eq_zero
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by decide)
  -- Pathwise FTC along continuous modification paths
  have hFTC : ∀ ω,
      u (∫ s in (0 : ℝ)..(t : ℝ), Real.exp (σ * B s.toNNReal ω)) - u 0 =
        ∫ s in (0 : ℝ)..(t : ℝ),
          deriv u (∫ r in (0 : ℝ)..s, Real.exp (σ * B r.toNNReal ω)) *
            Real.exp (σ * B s.toNNReal ω) := fun ω =>
    pathwise_u_expInt_ftc (fun s => B s ω) (hBcont ω) σ u hu1 t
  -- Center the Itô integral
  have hMart : ∫ ω, (itoIntegralCLM (hB := hBpre) t hBmeas gf') ω ∂P = 0 :=
    ItoIntegralProcessGeneral.integral_itoIntegralCLM hBpre t hBmeas gf'
  -- From `hIto` and `hB0`: v(B_t) - v(0) =ᵐ M_t + ½∫ v''(B).
  have hIto0 : (fun ω => v (B t ω) - v 0) =ᵐ[P]
      fun ω => (itoIntegralCLM (hB := hBpre) t hBmeas gf') ω
        + (1 / 2) * ∫ s in Ioc (0 : ℝ≥0) t, deriv (deriv v) (B s ω) ∂timeMeasure := by
    filter_upwards [hIto, hB0] with ω hω h0
    have hB0ω : B 0 ω = 0 := h0
    rw [show v (B t ω) - v 0 = v (B t ω) - v (B 0 ω) by rw [hB0ω]]
    simpa [B] using hω
  -- Terminal expectations agree for `B` and `W` (ae modification).
  have hBae : ∀ s, B s =ᵐ[P] W s := fun s => hW.toIsPreBrownianReal.mk_ae_eq s
  have hexpInt : expInt B σ 0 t =ᵐ[P] expInt W σ 0 t := by
    have hpath : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, B s ω = W s ω :=
      indistinguishable_of_modification (ae_of_all _ hBcont) hW.cont hBae
    filter_upwards [hpath] with ω hpath
    simp only [expInt, zero_mul, add_zero]
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hsI : s ∈ Icc (0 : ℝ) t := by
      simpa [uIcc_of_le (NNReal.coe_nonneg t)] using hs
    simp [hpath s.toNNReal, Real.coe_toNNReal s hsI.1]
  have hterm :
      (∫ ω, u (expInt W σ 0 t ω) * v (W t ω) ∂P) =
        ∫ ω, u (expInt B σ 0 t ω) * v (B t ω) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hexpInt, hBae t] with ω hX hWt
    rw [hX, hWt]
  -- Pathwise product identity (FTC × Itô) + centering + Fubini.
  rw [hterm]
  -- Claim: E[u(X_t)v(B_t)] - u0 v0
  --   = E[v(B_t)(u(X_t)-u0)] + u0 E[v(B_t)-v0]
  --   = E[v(B_t) ∫α] + u0 E[∫γ]   (center M via hMart)
  --   = ∫ E[α_s v(B_s)] ds + ∫ E[u(X_s) γ_s] ds
  --     by tower/Fubini on the Ito remainder (v(B_t)-v(B_s)).
  -- Algebraic split + centering + Fubini/tower assembly.
  -- Pointwise: `uv - u0v0 = v(u-u0) + u0(v-v0)`; center the Itô integral; convert FTC
  -- integrals via Fubini and the martingale property of `M`.
  obtain ⟨_Cu, _hu_bdd, _hu'_bdd, _⟩ := contDiff_top_compactSupport_bounds hu huC
  have _ := hname
  have _ := hIto0
  have _ := hFTC
  have _ := hMart
  sorry

/-- Paper (3.4b) after time-reversal, for product tests. -/
theorem ito_timeReversed_expInt_test_product (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (_ht : 0 < t)
    (u v : ℝ → ℝ) (hu : ContDiff ℝ (⊤ : WithTop ℕ∞) u)
    (hv : ContDiff ℝ (⊤ : WithTop ℕ∞) v)
    (huC : HasCompactSupport u) (hvC : HasCompactSupport v) :
    (∫ ω, u (expInt W σ 0 t ω) * v (W t ω) ∂P) - u 0 * v 0 =
      ∫ s in Ioc (0 : ℝ) t,
        (∫ ω,
          let X := expInt W σ 0 s.toNNReal ω
          let Y := W s.toNNReal ω
          (1 : ℝ) * deriv u X * v Y
            + (σ ^ 2 / 2) * X * deriv u X * v Y
            + (σ ^ 2 / 2) * X ^ 2 * deriv (deriv u) X * v Y
            + σ * X * deriv u X * deriv v Y
            + (1 / 2) * u X * deriv (deriv v) Y ∂P) := by
  -- Ito for `Y_s = ∫₀ˢ exp(σ(W_s-W_u)) du` (dY = (1+σ²Y/2)ds + σY dW), then
  -- replace Y by X in expectation via `time_reversal` at each horizon.
  have _tr := time_reversal (P := P) (W := W) hW 1
    (fun _ => fun _s w => Real.exp (σ * w)) (fun _ => by fun_prop) t
  sorry

end Lyasoff2016
