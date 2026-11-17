/-
Ito identities for product test functions along `(expInt, W)`, used by `fokker_planck_joint`.
-/
module

public import Lyasoff2016.Setting
public import MathFin.Probability.Brownian.Ito.ItoFormulaTD
public import MathFin.Probability.Brownian.Ito.ItoFormulaCLM
public import MathFin.Probability.Brownian.Ito.ItoFormulaAdaptedProcess
public import MathFin.Probability.Brownian.Ito.ItoProductRule
public import MathFin.Probability.Brownian.Ito.ItoIntegralProcessGeneral
public import MathFin.Probability.Brownian.Ito.ItoIntegralLocalisedPredictable
public import MathFin.Probability.Brownian.Ito.ItoIntegralBrownian
public import MathFin.Probability.Brownian.Ito.ItoDriftExpectation
public import Mathlib.Analysis.Calculus.ContDiff.Basic


@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open MeasureTheory.Measure
open MathFin ItoFormulaAdapted ItoIntegralL2 ItoIntegralProcessGeneral ItoIntegralBrownian
  ItoIntegralCLM ItoIntegralLocalised ItoIntegralProcessContinuousModification AdaptedDrift
  LocalisationInMeasure ItoIntegralRiemannBridge
open scoped NNReal ENNReal

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Compactly supported `C^∞` functions are bounded with their first two derivatives. -/
theorem contDiff_top_compactSupport_bounds {u : ℝ → ℝ}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (huC : HasCompactSupport u) :
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
        = (u ∘ X) t - (u ∘ X) 0 := by
          simp only [Function.comp_apply, X, g, hX0]
      _ = ∫ s in (0 : ℝ)..(t : ℝ), deriv u (X s) * g s := by simpa using hFTC.symm
      _ = ∫ s in (0 : ℝ)..(t : ℝ),
            deriv u (∫ r in (0 : ℝ)..s, Real.exp (σ * B r.toNNReal)) *
              Real.exp (σ * B s.toNNReal) := by
          rfl

/-- The local Itô integral of a constant integrand `a` is `a * B`, up to indistinguishability
on `[0, T]`: its Riemann sums telescope, and `B 0 = 0` almost surely. -/
theorem ae_localItoIntegral_const_eq {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) (a : ℝ) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc 0 T,
      localItoIntegral (μ := μ) T hBmeas (σ := fun _ _ ↦ a)
        (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) t ω = a * B t ω := by
  have hsum (t : ℝ≥0) {n : ℕ} (hn : n ≠ 0) (ω : Ω) :
      riemannσ (B := B) (fun _ _ ↦ a) t n ω = a * (B t ω - B 0 ω) := by
    simp only [riemannσ]
    rw [← Finset.mul_sum, Finset.sum_range_sub (fun k ↦ B (unifPart t n k) ω),
      unifPart_self t hn, unifPart_zero]
  have hconv (t : ℝ≥0) :
      TendstoInMeasure μ (fun n ω ↦ riemannσ (B := B) (fun _ _ ↦ a) t n ω)
        atTop (fun ω ↦ a * (B t ω - B 0 ω)) :=
    tendstoInMeasure_of_tendsto_ae
      (fun n ↦ (Finset.measurable_sum _ fun k _ ↦
        measurable_const.mul ((hBmeas _).sub (hBmeas _))).aestronglyMeasurable)
      (ae_of_all _ fun ω ↦ tendsto_const_nhds.congr'
        ((eventually_ne_atTop 0).mono fun n hn ↦ (hsum t hn ω).symm))
  filter_upwards [ae_forall_eq_of_tendstoInMeasure (T := T)
      (Y' := fun t ω ↦ a * (B t ω - B 0 ω))
      (ae_continuousOn_localItoIntegral hB T hBmeas hBcont (σ := fun _ _ ↦ a)
        (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const))
      (ae_of_all _ fun ω ↦
        (continuous_const.mul ((hBcont ω).sub continuous_const)).continuousOn)
      (fun t ht ↦ tendstoInMeasure_riemannσ_localItoIntegral hB T hBmeas hBcont _ _ ht.2)
      (fun t _ ↦ hconv t), eval_zero_ae hB hBmeas] with ω h h0 t ht
  rw [h t ht, h0, Pi.zero_apply, sub_zero]

/-- The predictable Itô integral of an integrand that is almost surely bounded on `[0, T]` is
integrable and centered at the horizon: there it is the `L²` Itô integral of the clipped
integrand. -/
theorem integral_predItoIntegral_eq_zero_of_ae_bdd {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    {θ : ℝ≥0 → Ω → ℝ} (hpred : IsStronglyPredictable (natFiltration hBmeas) θ)
    (hθc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ θ t ω) (Icc 0 T))
    (N : ℕ) (hbdd : ∀ᵐ ω ∂μ, ∀ s ∈ Icc 0 T, |θ s ω| ≤ N) :
    Integrable (predItoIntegral (μ := μ) T hBmeas hpred T) μ ∧
      ∫ ω, predItoIntegral (μ := μ) T hBmeas hpred T ω ∂μ = 0 := by
  set φ := processToLpPredictable (μ := μ) T hBmeas
    (clip_isStronglyPredictable hBmeas hpred N) (abs_clip_le N θ) with hφ
  have h1 : predItoIntegral (μ := μ) T hBmeas hpred T =ᵐ[μ] itoIntegralCLM hB T hBmeas φ := by
    have hmod := itoContinuousMod_modification hB T hBmeas hBcont φ (le_refl T)
    rw [itoProcessCLM_terminal_eq] at hmod
    filter_upwards [ae_predItoIntegral_eq hB T hBmeas hBcont hpred hθc, hbdd, hmod] with ω h hb hm
    rw [h N T ⟨zero_le, le_rfl⟩ fun s hs ↦ hb s hs]
    exact hm
  exact ⟨((Lp.memLp _).integrable one_le_two).congr h1.symm,
    by rw [integral_congr_ae h1, integral_itoIntegralCLM]⟩

/-- Paper (3.4a) for product tests, along a pre-Brownian motion with every path continuous,
with the time integral over `ℝ≥0`. -/
theorem ito_expInt_product_of_continuous {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) (σ : ℝ) (T : ℝ≥0)
    (u v : ℝ → ℝ) (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (huC : HasCompactSupport u) (hvC : HasCompactSupport v) :
    (∫ ω, u (driftPath (fun s ω ↦ Real.exp (σ * B s ω)) T ω) * v (B T ω) ∂μ) - u 0 * v 0 =
      ∫ s in Ioc (0 : ℝ≥0) T,
        (∫ ω,
          deriv u (driftPath (fun s ω ↦ Real.exp (σ * B s ω)) s ω) * Real.exp (σ * B s ω)
              * v (B s ω)
            + u (driftPath (fun s ω ↦ Real.exp (σ * B s ω)) s ω) * ((1 : ℝ) / 2) *
                deriv (deriv v) (B s ω) ∂μ) ∂timeMeasure := by
  obtain ⟨Cu, hu_bdd, hu'_bdd, -⟩ := contDiff_top_compactSupport_bounds hu huC
  obtain ⟨Cv, hv_bdd, hv'_bdd, hv''_bdd⟩ := contDiff_top_compactSupport_bounds hv hvC
  have hCu : 0 ≤ Cu := (abs_nonneg _).trans (hu_bdd 0)
  have hCv : 0 ≤ Cv := (abs_nonneg _).trans (hv_bdd 0)
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by decide)
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by decide)
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by decide)
  have hdv1 : ContDiff ℝ 1 (deriv v) := (contDiff_succ_iff_deriv (n := 1)).mp hv2 |>.2.2
  have huc : Continuous u := hu.continuous
  have hu'c : Continuous (deriv u) := ContDiff.continuous_deriv_one hu1
  have hvc : Continuous v := hv.continuous
  have hv'c : Continuous (deriv v) := ContDiff.continuous_deriv_one hv1
  have hv''c : Continuous (deriv (deriv v)) := ContDiff.continuous_deriv_one hdv1
  have hv' (x : ℝ) : HasDerivAt v (deriv v x) x :=
    (hv1.differentiable (by decide)).differentiableAt.hasDerivAt
  have hv'' (x : ℝ) : HasDerivAt (deriv v) (deriv (deriv v) x) x :=
    (hdv1.differentiable (by decide)).differentiableAt.hasDerivAt
  -- the coefficient processes
  have hBadap : ∀ s, StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)] (B s) :=
    stronglyAdapted_natFiltration hBmeas
  set b₁ : ℝ≥0 → Ω → ℝ := fun s ω ↦ Real.exp (σ * B s ω) with hb₁
  have hb₁a : ∀ s, StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)] (b₁ s) :=
    fun s ↦ (show Continuous fun x : ℝ ↦ Real.exp (σ * x) by fun_prop).comp_stronglyMeasurable
      (hBadap s)
  have hb₁c : ∀ ω, Continuous fun s ↦ b₁ s ω := fun ω ↦
    Real.continuous_exp.comp (continuous_const.mul (hBcont ω))
  set X : ℝ≥0 → Ω → ℝ := driftPath b₁ with hX
  have hXa : ∀ s, StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)] (X s) :=
    (driftPath_isStronglyPredictable_of_continuous hBmeas hb₁a hb₁c).stronglyAdapted
  have hXc : ∀ ω, Continuous fun s ↦ X s ω := fun ω ↦
    continuous_driftPath_of_continuous (hb₁c ω)
  set bU : ℝ≥0 → Ω → ℝ := fun s ω ↦ deriv u (X s ω) * b₁ s ω with hbU
  have hbUa : ∀ s, StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)] (bU s) :=
    fun s ↦ (hu'c.comp_stronglyMeasurable (hXa s)).mul (hb₁a s)
  have hbUc : ∀ ω, Continuous fun s ↦ bU s ω := fun ω ↦ (hu'c.comp (hXc ω)).mul (hb₁c ω)
  set τ : ℝ≥0 → Ω → ℝ := fun s ω ↦ deriv v (B s ω) with hτ
  have hτa : ∀ s, StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)] (τ s) :=
    fun s ↦ hv'c.comp_stronglyMeasurable (hBadap s)
  have hτc : ∀ ω, Continuous fun s ↦ τ s ω := fun ω ↦ hv'c.comp (hBcont ω)
  set c : ℝ≥0 → Ω → ℝ := fun s ω ↦ 1 / 2 * deriv (deriv v) (B s ω) with hc
  have hca : ∀ s, StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)] (c s) :=
    fun s ↦ (hv''c.comp_stronglyMeasurable (hBadap s)).const_mul (1 / 2)
  have hcc : ∀ ω, Continuous fun s ↦ c s ω := fun ω ↦
    continuous_const.mul (hv''c.comp (hBcont ω))
  -- pathwise FTC: `u ∘ X` is a pure-drift process
  have hFTC : ∀ ω (t : ℝ≥0), u (X t ω) = u 0 + driftPath bU t ω := by
    intro ω t
    have h := pathwise_u_expInt_ftc (fun s ↦ B s ω) (hBcont ω) σ u hu1 t
    have hXint : ∀ s : ℝ≥0, X s ω = ∫ r in (0 : ℝ)..(s : ℝ), Real.exp (σ * B r.toNNReal ω) :=
      fun s ↦ timeMeasure_Ioc_eq_interval (g := fun r ↦ Real.exp (σ * B r ω)) s
    have hU : driftPath bU t ω = ∫ s in (0 : ℝ)..(t : ℝ),
        deriv u (∫ r in (0 : ℝ)..s, Real.exp (σ * B r.toNNReal ω)) *
          Real.exp (σ * B s.toNNReal ω) := by
      rw [driftPath, timeMeasure_Ioc_eq_interval (g := fun s ↦ bU s ω) t]
      refine intervalIntegral.integral_congr fun s hs ↦ ?_
      have hs0 : 0 ≤ s := by
        rw [uIcc_of_le (NNReal.coe_nonneg t)] at hs
        exact hs.1
      simp only [bU, b₁]
      rw [hXint s.toNNReal, Real.coe_toNNReal s hs0]
    rw [hXint t, hU]
    linarith
  -- the two Itô processes of the product rule
  set LU : ℝ≥0 → Ω → ℝ := localItoProcess (μ := μ) T hBmeas (σ := fun _ _ ↦ (0 : ℝ))
    (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) (u 0) bU with hLUdef
  set LV : ℝ≥0 → Ω → ℝ := localItoProcess (μ := μ) T hBmeas hτa hτc (v 0) c with hLVdef
  have hLU : ∀ᵐ ω ∂μ, ∀ s ∈ Icc 0 T, LU s ω = u (X s ω) := by
    filter_upwards [ae_localItoIntegral_const_eq hB T hBmeas hBcont 0] with ω hω s hs
    simp only [LU, localItoProcess, hω s hs, hFTC ω s, zero_mul, add_zero]
  have hLV : ∀ᵐ ω ∂μ, ∀ s ∈ Icc 0 T, LV s ω = v (B s ω) := by
    set Xp : ℝ≥0 → Ω → ℝ := localItoProcess (μ := μ) T hBmeas
      (σ := fun _ _ ↦ (1 : ℝ)) (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) 0
      (fun _ _ ↦ (0 : ℝ)) with hXp
    have hθX : IsStronglyPredictable (natFiltration hBmeas)
        fun s ω ↦ deriv v (Xp s ω) * 1 :=
      itoIntegrand_isStronglyPredictable hB T hBmeas hBcont
        (σ := fun _ _ ↦ (1 : ℝ)) (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const)
        (b := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) 0
        (f_x := fun _ x ↦ deriv v x) (hv'c.comp continuous_snd)
    have hIto : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, v (Xp t ω) = v 0
        + ∫ s in Ioc 0 t, (deriv v (Xp s ω) * 0
            + 1 / 2 * (deriv (deriv v) (Xp s ω) * 1 ^ 2)) ∂timeMeasure
        + predItoIntegral (μ := μ) T hBmeas hθX t ω :=
      ito_formula_adapted_unbounded_C2_process hB T hBmeas hBcont
        (σ := fun _ _ ↦ (1 : ℝ)) (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const)
        (b := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) 0
        (f := v) (f' := deriv v) (f'' := deriv (deriv v)) hv' hv'' hv''c
    have hX1 : ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ≥0) T, localItoIntegral (μ := μ) T hBmeas
        (σ := fun _ _ ↦ (1 : ℝ)) (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) t ω
          = B t ω := by
      filter_upwards [ae_localItoIntegral_const_eq hB T hBmeas hBcont 1] with ω hω t ht
      rw [hω t ht, one_mul]
    have hXpc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ Xp t ω) (Icc 0 T) :=
      ae_continuousOn_localItoProcess hB T hBmeas hBcont
        (σ := fun _ _ ↦ (1 : ℝ)) (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const)
        (b := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ continuous_const) 0
    have hθXc : ∀ᵐ ω ∂μ, ContinuousOn (fun s : ℝ≥0 ↦ deriv v (Xp s ω) * 1) (Icc 0 T) :=
      hXpc.mono fun ω h ↦ (hv'c.comp_continuousOn h).mul continuousOn_const
    have hXs (ω : Ω) (hω : ∀ t ∈ Icc (0 : ℝ≥0) T, localItoIntegral (μ := μ) T hBmeas
        (σ := fun _ _ ↦ (1 : ℝ)) (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) t ω
          = B t ω) (s : ℝ≥0) (hs : s ∈ Icc (0 : ℝ≥0) T) : Xp s ω = B s ω := by
      simp [Xp, localItoProcess, AdaptedDrift.driftPath, hω s hs]
    have hcongr := ae_predItoIntegral_congr hB T hBmeas hBcont hθX hθXc
      (isStronglyPredictable_of_bdd_adapted_cont hBmeas hτa hτc)
      (ae_of_all _ fun ω ↦ (hτc ω).continuousOn)
      (by
        filter_upwards [hX1] with ω hω s hs
        rw [hXs ω hω s hs, mul_one])
    filter_upwards [hIto, hX1, hcongr,
      ae_predItoIntegral_eq_localItoIntegral hB T hBmeas hBcont hτa hτc] with ω h1 hXω hc1 hc2 t ht
    have hint : ∫ s in Ioc 0 t, (deriv v (Xp s ω) * 0
          + 1 / 2 * (deriv (deriv v) (Xp s ω) * 1 ^ 2)) ∂timeMeasure = driftPath c t ω := by
      refine setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ ?_
      have hsT : s ∈ Icc (0 : ℝ≥0) T := ⟨zero_le, hs.2.trans ht.2⟩
      simp only [hXs ω hXω s hsT, c]
      ring
    have key := h1 t ht
    rw [hXs ω hXω t ht, hint, hc1 t ht, hc2 t ht] at key
    simp only [LV, localItoProcess]
    exact key.symm
  -- the product rule
  have hθ : IsStronglyPredictable (natFiltration hBmeas)
      fun s ω ↦ LU s ω * τ s ω + LV s ω * 0 :=
    productIntegrand_isStronglyPredictable hB T hBmeas hBcont (σ := fun _ _ ↦ (0 : ℝ))
      (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) hτa hτc hbUa hbUc hca hcc
      (u 0) (v 0)
  have hprod : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, LU t ω * LV t ω = u 0 * v 0
      + ∫ s in Ioc 0 t, (LU s ω * c s ω + LV s ω * bU s ω + 0 * τ s ω) ∂timeMeasure
      + predItoIntegral (μ := μ) T hBmeas hθ t ω :=
    ito_product_rule_process hB T hBmeas hBcont (σ := fun _ _ ↦ (0 : ℝ))
      (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) hτa hτc hbUa hbUc hca hcc
      (u 0) (v 0)
  -- the stochastic term is centered: its integrand is bounded
  have hθeq : ∀ᵐ ω ∂μ, ∀ s ∈ Icc 0 T,
      LU s ω * τ s ω + LV s ω * 0 = u (X s ω) * deriv v (B s ω) := by
    filter_upwards [hLU] with ω h s hs
    rw [h s hs, mul_zero, add_zero]
  have hθc : ∀ᵐ ω ∂μ, ContinuousOn (fun s ↦ LU s ω * τ s ω + LV s ω * 0) (Icc 0 T) := by
    filter_upwards [hθeq] with ω h
    exact ((huc.comp (hXc ω)).mul (hv'c.comp (hBcont ω))).continuousOn.congr h
  have hθbdd : ∀ᵐ ω ∂μ, ∀ s ∈ Icc 0 T,
      |LU s ω * τ s ω + LV s ω * 0| ≤ (⌈Cu * Cv⌉₊ : ℕ) := by
    filter_upwards [hθeq] with ω h s hs
    rw [h s hs, abs_mul]
    exact (mul_le_mul (hu_bdd _) (hv'_bdd _) (abs_nonneg _) hCu).trans (Nat.le_ceil _)
  obtain ⟨hMint, hMzero⟩ :=
    integral_predItoIntegral_eq_zero_of_ae_bdd hB T hBmeas hBcont hθ hθc ⌈Cu * Cv⌉₊ hθbdd
  -- the drift weight
  set w : ℝ≥0 → Ω → ℝ := fun s ω ↦
    deriv u (X s ω) * Real.exp (σ * B s ω) * v (B s ω)
      + u (X s ω) * ((1 : ℝ) / 2) * deriv (deriv v) (B s ω) with hw
  have hXm : ∀ s, Measurable (X s) := fun s ↦
    ((hXa s).mono ((natFiltration hBmeas).le s)).measurable
  have hw_meas : ∀ s, Measurable (w s) := fun s ↦
    (((hu'c.measurable.comp (hXm s)).mul
      (Real.continuous_exp.measurable.comp ((hBmeas s).const_mul σ))).mul
        (hvc.measurable.comp (hBmeas s))).add
      (((huc.measurable.comp (hXm s)).mul_const (1 / 2)).mul
        (hv''c.measurable.comp (hBmeas s)))
  have hw_cont : ∀ ω, Continuous fun s ↦ w s ω := fun ω ↦
    (((hu'c.comp (hXc ω)).mul (hb₁c ω)).mul (hvc.comp (hBcont ω))).add
      (((huc.comp (hXc ω)).mul continuous_const).mul (hv''c.comp (hBcont ω)))
  obtain ⟨K, hK⟩ := (show Continuous ((fun y : ℝ ↦ Real.exp (σ * y)) * v) from
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hvc
    ).bounded_above_of_compact_support hvC.mul_left
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hC0 : 0 ≤ Cu * K + Cu * (1 / 2) * Cv := by positivity
  have hw_bdd : ∀ s ω, |w s ω| ≤ Cu * K + Cu * (1 / 2) * Cv := by
    intro s ω
    have h1 : |deriv u (X s ω) * Real.exp (σ * B s ω) * v (B s ω)| ≤ Cu * K := by
      rw [mul_assoc, abs_mul]
      refine mul_le_mul (hu'_bdd _) ?_ (abs_nonneg _) hCu
      simpa [Real.norm_eq_abs] using hK (B s ω)
    have h2 : |u (X s ω) * ((1 : ℝ) / 2) * deriv (deriv v) (B s ω)| ≤ Cu * (1 / 2) * Cv := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact mul_le_mul (mul_le_mul_of_nonneg_right (hu_bdd _) (by norm_num)) (hv''_bdd _)
        (abs_nonneg _) (by positivity)
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  have hpathint : Integrable (fun ω ↦ ∫ s in Ioc 0 T, w s ω ∂timeMeasure) μ :=
    (memLp_pathIntegral_process hw_meas hw_cont hC0 hw_bdd T).integrable one_le_two
  -- the pathwise identity at the horizon
  have hid : ∀ᵐ ω ∂μ, u (X T ω) * v (B T ω) = u 0 * v 0
      + ∫ s in Ioc 0 T, w s ω ∂timeMeasure + predItoIntegral (μ := μ) T hBmeas hθ T ω := by
    filter_upwards [hprod, hLU, hLV] with ω hp hU hV
    have hT : T ∈ Icc (0 : ℝ≥0) T := ⟨zero_le, le_rfl⟩
    have h1 := hp T hT
    rw [hU T hT, hV T hT] at h1
    have hint : ∫ s in Ioc 0 T, (LU s ω * c s ω + LV s ω * bU s ω + 0 * τ s ω) ∂timeMeasure
        = ∫ s in Ioc 0 T, w s ω ∂timeMeasure := by
      refine setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ ?_
      have hsT : s ∈ Icc (0 : ℝ≥0) T := ⟨zero_le, hs.2⟩
      simp only [hU s hsT, hV s hsT, w, c, bU, b₁]
      ring
    rw [h1, hint]
  calc (∫ ω, u (X T ω) * v (B T ω) ∂μ) - u 0 * v 0
      = (∫ ω, (u 0 * v 0 + ∫ s in Ioc 0 T, w s ω ∂timeMeasure
          + predItoIntegral (μ := μ) T hBmeas hθ T ω) ∂μ) - u 0 * v 0 := by
        rw [integral_congr_ae hid]
    _ = ∫ ω, (∫ s in Ioc 0 T, w s ω ∂timeMeasure) ∂μ := by
        have hsum : Integrable
            (fun ω ↦ u 0 * v 0 + ∫ s in Ioc 0 T, w s ω ∂timeMeasure) μ :=
          (integrable_const _).add hpathint
        rw [integral_add hsum hMint, integral_add (integrable_const _) hpathint, hMzero,
          integral_const]
        simp
    _ = ∫ s in Ioc 0 T, (∫ ω, w s ω ∂μ) ∂timeMeasure :=
        expectation_pathIntegral_eq hw_meas (ae_of_all _ hw_cont) hC0 hw_bdd T

/-- Paper (3.4a) for product tests `ϕ = u ⊗ v`. -/
theorem ito_expInt_test_product (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (σ : ℝ) (t : ℝ≥0)
    (u v : ℝ → ℝ) (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (huC : HasCompactSupport u) (hvC : HasCompactSupport v) :
    (∫ ω, u (expInt W σ 0 t ω) * v (W t ω) ∂P) - u 0 * v 0 =
      ∫ s in Ioc (0 : ℝ) t,
        (∫ ω,
          deriv u (expInt W σ 0 s.toNNReal ω) * Real.exp (σ * W s.toNNReal ω) * v (W s.toNNReal ω)
            + u (expInt W σ 0 s.toNNReal ω) * ((1 : ℝ) / 2) *
                deriv (deriv v) (W s.toNNReal ω) ∂P) := by
  -- Work along the continuous modification `B` of `W`.
  set B : ℝ≥0 → Ω → ℝ := hW.toIsPreBrownianReal.mk W
  have hBmeas : ∀ s, Measurable (B s) := hW.toIsPreBrownianReal.measurable_mk
  have hBcont : ∀ ω, Continuous fun s : ℝ≥0 => B s ω := hW.toIsPreBrownianReal.continuous_mk
  have hBpre : IsPreBrownianReal B P :=
    hW.toIsPreBrownianReal.isBrownianReal_mk.toIsPreBrownianReal
  have hBae : ∀ s, B s =ᵐ[P] W s := fun s => hW.toIsPreBrownianReal.mk_ae_eq s
  have hpath : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, B s ω = W s ω :=
    indistinguishable_of_modification (ae_of_all _ hBcont) hW.cont hBae
  -- The drift path of `exp(σ B)` is `expInt W`, on almost every path at all times.
  have hdrift : ∀ᵐ ω ∂P, ∀ s : ℝ≥0,
      driftPath (fun r ω ↦ Real.exp (σ * B r ω)) s ω = expInt W σ 0 s ω := by
    filter_upwards [hpath] with ω hω s
    rw [driftPath, timeMeasure_Ioc_eq_interval (g := fun r ↦ Real.exp (σ * B r ω)) s]
    simp only [expInt, zero_mul, add_zero, hω]
  -- The identity along `B` (product rule), then transport back to `W`.
  have key := ito_expInt_product_of_continuous hBpre hBmeas hBcont σ t u v hu hv huC hvC
  have hterm : (∫ ω, u (expInt W σ 0 t ω) * v (W t ω) ∂P) =
      ∫ ω, u (driftPath (fun r ω ↦ Real.exp (σ * B r ω)) t ω) * v (B t ω) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hpath, hdrift] with ω h1 h2
    rw [h2 t, h1 t]
  rw [hterm, key, timeMeasure_Ioc_eq_interval t,
    intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]
  refine setIntegral_congr_fun measurableSet_Ioc fun s _ ↦ integral_congr_ae ?_
  filter_upwards [hpath, hdrift] with ω h1 h2
  rw [h2 s.toNNReal, h1 s.toNNReal]

/-! ### Toolkit for (3.4b): Itô processes with explicit versions -/

/-- **Itô's formula along an explicit version.** If the Itô process with coefficients `(σ, b)`
started at `x₀` is, almost surely on `[0, T]`, the explicit process `X`, then for `f` of class
`C²` the Itô process with coefficients `(f'(X) σ, f'(X) b + ½ f''(X) σ²)` started at `f x₀` is,
almost surely on `[0, T]`, the process `f ∘ X`. -/
theorem ae_localItoProcess_comp_of_version {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    {σ b X σ' b' : ℝ≥0 → Ω → ℝ} {x₀ y₀ : ℝ}
    (hσa : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
    (hσc : ∀ ω, Continuous fun t : ℝ≥0 ↦ σ t ω)
    (hba : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (b t))
    (hbc : ∀ ω, Continuous fun t : ℝ≥0 ↦ b t ω)
    (hX : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      localItoProcess (μ := μ) T hBmeas hσa hσc x₀ b t ω = X t ω)
    {f f' f'' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : Continuous f'')
    (hσ'a : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ' t))
    (hσ'c : ∀ ω, Continuous fun t : ℝ≥0 ↦ σ' t ω)
    (hσ' : ∀ s ω, σ' s ω = f' (X s ω) * σ s ω)
    (hb' : ∀ s ω, b' s ω = f' (X s ω) * b s ω + 1 / 2 * (f'' (X s ω) * σ s ω ^ 2))
    (hy₀ : y₀ = f x₀) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      localItoProcess (μ := μ) T hBmeas hσ'a hσ'c y₀ b' t ω = f (X t ω) := by
  have hf'c : Continuous f' := Differentiable.continuous fun x ↦ (hf' x).differentiableAt
  set L : ℝ≥0 → Ω → ℝ := localItoProcess (μ := μ) T hBmeas hσa hσc x₀ b with hL
  have hθL : IsStronglyPredictable (natFiltration hBmeas) fun s ω ↦ f' (L s ω) * σ s ω :=
    itoIntegrand_isStronglyPredictable hB T hBmeas hBcont hσa hσc hba hbc x₀
      (f_x := fun _ x ↦ f' x) (hf'c.comp continuous_snd)
  have hIto : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, f (L t ω) = f x₀
      + ∫ s in Ioc 0 t, (f' (L s ω) * b s ω + 1 / 2 * (f'' (L s ω) * σ s ω ^ 2)) ∂timeMeasure
      + predItoIntegral (μ := μ) T hBmeas hθL t ω :=
    ito_formula_adapted_unbounded_C2_process hB T hBmeas hBcont hσa hσc hba hbc x₀ hf hf' hf''
  have hLc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ L t ω) (Icc 0 T) :=
    ae_continuousOn_localItoProcess hB T hBmeas hBcont hσa hσc hbc x₀
  have hθLc : ∀ᵐ ω ∂μ, ContinuousOn (fun s : ℝ≥0 ↦ f' (L s ω) * σ s ω) (Icc 0 T) :=
    hLc.mono fun ω h ↦ (hf'c.comp_continuousOn h).mul (hσc ω).continuousOn
  have hcongr := ae_predItoIntegral_congr hB T hBmeas hBcont hθL hθLc
    (isStronglyPredictable_of_bdd_adapted_cont hBmeas hσ'a hσ'c)
    (ae_of_all _ fun ω ↦ (hσ'c ω).continuousOn)
    (by
      filter_upwards [hX] with ω hω s hs
      rw [hω s hs, hσ'])
  filter_upwards [hIto, hX, hcongr,
    ae_predItoIntegral_eq_localItoIntegral hB T hBmeas hBcont hσ'a hσ'c] with ω h1 hXω hc1 hc2 t ht
  have hint : ∫ s in Ioc 0 t, (f' (L s ω) * b s ω + 1 / 2 * (f'' (L s ω) * σ s ω ^ 2))
      ∂timeMeasure = driftPath b' t ω := by
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ ?_
    have hsT : s ∈ Icc (0 : ℝ≥0) T := ⟨zero_le, hs.2.trans ht.2⟩
    simp only [hXω s hsT, hb']
  have key := h1 t ht
  rw [hXω t ht, hint, hc1 t ht, hc2 t ht] at key
  simp only [localItoProcess, hy₀]
  exact key.symm

/-- **The product rule along explicit versions.** If the Itô processes with coefficients
`(σ₁, b₁)`, `(σ₂, b₂)` started at `x₁`, `x₂` are, almost surely on `[0, T]`, the explicit processes
`X₁`, `X₂`, then the Itô process with coefficients `(X₁ σ₂ + X₂ σ₁, X₁ b₂ + X₂ b₁ + σ₁ σ₂)`
started at `x₁ x₂` is, almost surely on `[0, T]`, the product `X₁ X₂`. -/
theorem ae_localItoProcess_mul_of_version {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    {σ₁ b₁ σ₂ b₂ X₁ X₂ σ' b' : ℝ≥0 → Ω → ℝ} {x₁ x₂ y₀ : ℝ}
    (hσ₁a : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ₁ t))
    (hσ₁c : ∀ ω, Continuous fun t : ℝ≥0 ↦ σ₁ t ω)
    (hb₁a : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (b₁ t))
    (hb₁c : ∀ ω, Continuous fun t : ℝ≥0 ↦ b₁ t ω)
    (hσ₂a : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ₂ t))
    (hσ₂c : ∀ ω, Continuous fun t : ℝ≥0 ↦ σ₂ t ω)
    (hb₂a : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (b₂ t))
    (hb₂c : ∀ ω, Continuous fun t : ℝ≥0 ↦ b₂ t ω)
    (hX₁ : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      localItoProcess (μ := μ) T hBmeas hσ₁a hσ₁c x₁ b₁ t ω = X₁ t ω)
    (hX₂ : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      localItoProcess (μ := μ) T hBmeas hσ₂a hσ₂c x₂ b₂ t ω = X₂ t ω)
    (hσ'a : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ' t))
    (hσ'c : ∀ ω, Continuous fun t : ℝ≥0 ↦ σ' t ω)
    (hσ' : ∀ s ω, σ' s ω = X₁ s ω * σ₂ s ω + X₂ s ω * σ₁ s ω)
    (hb' : ∀ s ω, b' s ω = X₁ s ω * b₂ s ω + X₂ s ω * b₁ s ω + σ₁ s ω * σ₂ s ω)
    (hy₀ : y₀ = x₁ * x₂) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      localItoProcess (μ := μ) T hBmeas hσ'a hσ'c y₀ b' t ω = X₁ t ω * X₂ t ω := by
  set L₁ : ℝ≥0 → Ω → ℝ := localItoProcess (μ := μ) T hBmeas hσ₁a hσ₁c x₁ b₁ with hL₁
  set L₂ : ℝ≥0 → Ω → ℝ := localItoProcess (μ := μ) T hBmeas hσ₂a hσ₂c x₂ b₂ with hL₂
  have hθ : IsStronglyPredictable (natFiltration hBmeas)
      fun s ω ↦ L₁ s ω * σ₂ s ω + L₂ s ω * σ₁ s ω :=
    productIntegrand_isStronglyPredictable hB T hBmeas hBcont hσ₁a hσ₁c hσ₂a hσ₂c hb₁a hb₁c
      hb₂a hb₂c x₁ x₂
  have hprod : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, L₁ t ω * L₂ t ω = x₁ * x₂
      + ∫ s in Ioc 0 t, (L₁ s ω * b₂ s ω + L₂ s ω * b₁ s ω + σ₁ s ω * σ₂ s ω) ∂timeMeasure
      + predItoIntegral (μ := μ) T hBmeas hθ t ω :=
    ito_product_rule_process hB T hBmeas hBcont hσ₁a hσ₁c hσ₂a hσ₂c hb₁a hb₁c hb₂a hb₂c x₁ x₂
  have hL₁c : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ L₁ t ω) (Icc 0 T) :=
    ae_continuousOn_localItoProcess hB T hBmeas hBcont hσ₁a hσ₁c hb₁c x₁
  have hL₂c : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ L₂ t ω) (Icc 0 T) :=
    ae_continuousOn_localItoProcess hB T hBmeas hBcont hσ₂a hσ₂c hb₂c x₂
  have hθc : ∀ᵐ ω ∂μ,
      ContinuousOn (fun s : ℝ≥0 ↦ L₁ s ω * σ₂ s ω + L₂ s ω * σ₁ s ω) (Icc 0 T) := by
    filter_upwards [hL₁c, hL₂c] with ω h1 h2
    exact (h1.mul (hσ₂c ω).continuousOn).add (h2.mul (hσ₁c ω).continuousOn)
  have hcongr := ae_predItoIntegral_congr hB T hBmeas hBcont hθ hθc
    (isStronglyPredictable_of_bdd_adapted_cont hBmeas hσ'a hσ'c)
    (ae_of_all _ fun ω ↦ (hσ'c ω).continuousOn)
    (by
      filter_upwards [hX₁, hX₂] with ω h1 h2 s hs
      rw [h1 s hs, h2 s hs, hσ'])
  filter_upwards [hprod, hX₁, hX₂, hcongr,
    ae_predItoIntegral_eq_localItoIntegral hB T hBmeas hBcont hσ'a hσ'c]
    with ω hp h1 h2 hc1 hc2 t ht
  have hint : ∫ s in Ioc 0 t, (L₁ s ω * b₂ s ω + L₂ s ω * b₁ s ω + σ₁ s ω * σ₂ s ω)
      ∂timeMeasure = driftPath b' t ω := by
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ ?_
    have hsT : s ∈ Icc (0 : ℝ≥0) T := ⟨zero_le, hs.2.trans ht.2⟩
    simp only [h1 s hsT, h2 s hsT, hb']
  have key := hp t ht
  rw [h1 t ht, h2 t ht, hint, hc1 t ht, hc2 t ht] at key
  simp only [localItoProcess, hy₀]
  exact key.symm

/-- The time-reversed twin of `expInt`: `Y_s = e^{σ B_s} ∫₀ˢ e^{-σ B_r} dr = ∫₀ˢ e^{σ (B_s - B_r)} dr`.
It solves `dY = (1 + σ² Y / 2) ds + σ Y dB`, and `(Y_s, B_s)` has the law of
`(∫₀ˢ e^{σ B_r} dr, B_s)` at each fixed `s`. -/
def expIntTwin (B : ℝ≥0 → Ω → ℝ) (σ : ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (σ * B s ω) * driftPath (fun r ω ↦ Real.exp (-σ * B r ω)) s ω

/-- The integrand of paper (3.4b) for a product test `u ⊗ v`: the generator of `(expIntTwin, B)`
applied to `u ⊗ v`. -/
def twinGenerator (σ : ℝ) (u v : ℝ → ℝ) (x y : ℝ) : ℝ :=
  (1 : ℝ) * deriv u x * v y
    + (σ ^ 2 / 2) * x * deriv u x * v y
    + (σ ^ 2 / 2) * x ^ 2 * deriv (deriv u) x * v y
    + σ * x * deriv u x * deriv v y
    + (1 / 2) * u x * deriv (deriv v) y

/-- The integrand of (3.4b) is jointly continuous for smooth tests. -/
theorem continuous_twinGenerator (σ : ℝ) {u v : ℝ → ℝ}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v) :
    Continuous fun p : ℝ × ℝ ↦ twinGenerator σ u v p.1 p.2 := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by decide)
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by decide)
  have hdu1 : ContDiff ℝ 1 (deriv u) := (contDiff_succ_iff_deriv (n := 1)).mp hu2 |>.2.2
  have huc : Continuous u := hu.continuous
  have hu'c : Continuous (deriv u) := ContDiff.continuous_deriv_one hu1
  have hu''c : Continuous (deriv (deriv u)) := ContDiff.continuous_deriv_one hdu1
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by decide)
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by decide)
  have hdv1 : ContDiff ℝ 1 (deriv v) := (contDiff_succ_iff_deriv (n := 1)).mp hv2 |>.2.2
  have hvc : Continuous v := hv.continuous
  have hv'c : Continuous (deriv v) := ContDiff.continuous_deriv_one hv1
  have hv''c : Continuous (deriv (deriv v)) := ContDiff.continuous_deriv_one hdv1
  unfold twinGenerator
  fun_prop

/-- The time integral of `e^{a B}` up to a fixed time is measurable. -/
theorem measurable_driftPath_exp {B : ℝ≥0 → Ω → ℝ} (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) (a : ℝ) (s : ℝ≥0) :
    Measurable (driftPath (fun r ω ↦ Real.exp (a * B r ω)) s) :=
  measurable_pathIntegral (w := fun r ω ↦ Real.exp (a * B r ω))
    (fun r ↦ Real.continuous_exp.measurable.comp ((hBmeas r).const_mul a))
    (fun ω ↦ Real.continuous_exp.comp (continuous_const.mul (hBcont ω))) s

/-- The twin is measurable at each time. -/
theorem measurable_expIntTwin {B : ℝ≥0 → Ω → ℝ} (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) (σ : ℝ) (s : ℝ≥0) :
    Measurable (expIntTwin B σ s) :=
  (Real.continuous_exp.measurable.comp ((hBmeas s).const_mul σ)).mul
    (measurable_driftPath_exp hBmeas hBcont (-σ) s)

/-- The twin is adapted to the natural filtration of `B`. -/
theorem stronglyAdapted_expIntTwin {B : ℝ≥0 → Ω → ℝ} (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) (σ : ℝ) (s : ℝ≥0) :
    StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)] (expIntTwin B σ s) :=
  ((show Continuous fun x : ℝ ↦ Real.exp (σ * x) by fun_prop).comp_stronglyMeasurable
    (stronglyAdapted_natFiltration hBmeas s)).mul
    ((driftPath_isStronglyPredictable_of_continuous hBmeas
      (fun r ↦ (show Continuous fun x : ℝ ↦ Real.exp (-σ * x) by fun_prop).comp_stronglyMeasurable
        (stronglyAdapted_natFiltration hBmeas r))
      (fun ω ↦ Real.continuous_exp.comp (continuous_const.mul (hBcont ω)))).stronglyAdapted s)

omit [MeasurableSpace Ω] in
/-- Every path of the twin is continuous. -/
theorem continuous_expIntTwin {B : ℝ≥0 → Ω → ℝ}
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) (σ : ℝ) (ω : Ω) :
    Continuous fun s ↦ expIntTwin B σ s ω :=
  (Real.continuous_exp.comp (continuous_const.mul (hBcont ω))).mul
    (continuous_driftPath_of_continuous (b := fun r ω ↦ Real.exp (-σ * B r ω))
      (Real.continuous_exp.comp (continuous_const.mul (hBcont ω))))

/-- A pre-Brownian motion with continuous paths is the Itô process `∫ 1 dB`, almost surely on
`[0, T]`. -/
theorem ae_localItoProcess_one_eq {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, localItoProcess (μ := μ) T hBmeas
      (σ := fun _ _ ↦ (1 : ℝ)) (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) 0
      (fun _ _ ↦ (0 : ℝ)) t ω = B t ω := by
  filter_upwards [ae_localItoIntegral_const_eq hB T hBmeas hBcont 1] with ω hω t ht
  simp [localItoProcess, AdaptedDrift.driftPath, hω t ht]

/-- **The twin is an Itô process**: `dY = (1 + σ² Y / 2) ds + σ Y dB`, `Y_0 = 0`, almost surely on
`[0, T]`. The product rule for `e^{σ B} · ∫ e^{-σ B} ds`, with `d e^{σ B} = (σ²/2) e^{σ B} ds
+ σ e^{σ B} dB` from Itô's formula. -/
theorem ae_localItoProcess_expIntTwin {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) (σ : ℝ)
    (hσYa : ∀ s, StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)]
      (fun ω ↦ σ * expIntTwin B σ s ω))
    (hσYc : ∀ ω, Continuous fun s ↦ σ * expIntTwin B σ s ω) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      localItoProcess (μ := μ) T hBmeas hσYa hσYc 0
        (fun s ω ↦ 1 + σ ^ 2 / 2 * expIntTwin B σ s ω) t ω = expIntTwin B σ t ω := by
  -- the exponential and its derivatives
  have hlin (x : ℝ) : HasDerivAt (fun y ↦ σ * y) σ x := by
    simpa using (hasDerivAt_id x).const_mul σ
  have hexp (x : ℝ) : HasDerivAt (fun y ↦ Real.exp (σ * y)) (σ * Real.exp (σ * x)) x := by
    rw [show σ * Real.exp (σ * x) = Real.exp (σ * x) * σ by ring]
    exact (hlin x).exp
  have hexp' (x : ℝ) :
      HasDerivAt (fun y ↦ σ * Real.exp (σ * y)) (σ ^ 2 * Real.exp (σ * x)) x := by
    rw [show σ ^ 2 * Real.exp (σ * x) = σ * (Real.exp (σ * x) * σ) by ring]
    exact ((hlin x).exp).const_mul σ
  have hexp''c : Continuous fun x : ℝ ↦ σ ^ 2 * Real.exp (σ * x) := by fun_prop
  -- the factors `Z = e^{σ B}`, `I = ∫ e^{-σ B}`
  have hBadap : ∀ s, StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)] (B s) :=
    stronglyAdapted_natFiltration hBmeas
  set Z : ℝ≥0 → Ω → ℝ := fun s ω ↦ Real.exp (σ * B s ω) with hZ
  have hZa : ∀ s, StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)] (Z s) :=
    fun s ↦ (show Continuous fun x : ℝ ↦ Real.exp (σ * x) by fun_prop).comp_stronglyMeasurable
      (hBadap s)
  have hZc : ∀ ω, Continuous fun s ↦ Z s ω := fun ω ↦
    Real.continuous_exp.comp (continuous_const.mul (hBcont ω))
  set e : ℝ≥0 → Ω → ℝ := fun s ω ↦ Real.exp (-σ * B s ω) with he
  have hea : ∀ s, StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)] (e s) :=
    fun s ↦ (show Continuous fun x : ℝ ↦ Real.exp (-σ * x) by fun_prop).comp_stronglyMeasurable
      (hBadap s)
  have hec : ∀ ω, Continuous fun s ↦ e s ω := fun ω ↦
    Real.continuous_exp.comp (continuous_const.mul (hBcont ω))
  set I : ℝ≥0 → Ω → ℝ := driftPath e with hI
  -- `dZ = (σ² Z / 2) ds + σ Z dB`
  set σZ : ℝ≥0 → Ω → ℝ := fun s ω ↦ σ * Z s ω with hσZ
  have hσZa : ∀ s, StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)] (σZ s) :=
    fun s ↦ (hZa s).const_mul σ
  have hσZc : ∀ ω, Continuous fun s ↦ σZ s ω := fun ω ↦ continuous_const.mul (hZc ω)
  set bZ : ℝ≥0 → Ω → ℝ := fun s ω ↦ σ ^ 2 / 2 * Z s ω with hbZ
  have hbZa : ∀ s, StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)] (bZ s) :=
    fun s ↦ (hZa s).const_mul (σ ^ 2 / 2)
  have hbZc : ∀ ω, Continuous fun s ↦ bZ s ω := fun ω ↦ continuous_const.mul (hZc ω)
  have hLZ : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      localItoProcess (μ := μ) T hBmeas hσZa hσZc 1 bZ t ω = Z t ω :=
    ae_localItoProcess_comp_of_version hB T hBmeas hBcont
      (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const)
      (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const)
      (ae_localItoProcess_one_eq hB T hBmeas hBcont)
      hexp hexp' hexp''c hσZa hσZc
      (fun s ω ↦ by simp only [σZ, Z, mul_one])
      (fun s ω ↦ by simp only [bZ, Z]; ring) (by simp)
  -- `dI = e^{-σ B} ds`
  have hLI : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, localItoProcess (μ := μ) T hBmeas
      (σ := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) 0
      e t ω = I t ω := by
    filter_upwards [ae_localItoIntegral_const_eq hB T hBmeas hBcont 0] with ω hω t ht
    simp only [localItoProcess, hω t ht, zero_mul, add_zero, zero_add, I]
  -- the product rule
  have hZe (s : ℝ≥0) (ω : Ω) : Z s ω * e s ω = 1 := by
    simp only [Z, e]
    rw [← Real.exp_add, show σ * B s ω + -σ * B s ω = 0 by ring, Real.exp_zero]
  have hYeq (s : ℝ≥0) (ω : Ω) : expIntTwin B σ s ω = Z s ω * I s ω := rfl
  exact ae_localItoProcess_mul_of_version hB T hBmeas hBcont hσZa hσZc hbZa hbZc
    (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) hea hec hLZ hLI hσYa hσYc
    (fun s ω ↦ by simp only [hYeq, σZ]; ring)
    (fun s ω ↦ by simp only [hYeq, bZ, σZ]; linear_combination -hZe s ω)
    (by simp)

/-- **Time reversal at a fixed horizon**: `(expIntTwin_s, B_s)` and `(∫₀ˢ e^{σ B_r} dr, B_s)` have
the same law, so they integrate every continuous function alike (paper (1.3)). -/
theorem integral_expIntTwin_eq {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) (σ : ℝ) (s : ℝ≥0)
    {g : ℝ → ℝ → ℝ} (hg : Continuous fun p : ℝ × ℝ ↦ g p.1 p.2) :
    ∫ ω, g (expIntTwin B σ s ω) (B s ω) ∂μ
      = ∫ ω, g (driftPath (fun r ω ↦ Real.exp (σ * B r ω)) s ω) (B s ω) ∂μ := by
  set φ₁ : Ω → (Fin 1 → ℝ) × ℝ :=
    fun ω ↦ (fun _ ↦ driftPath (fun r ω ↦ Real.exp (σ * B r ω)) s ω, B s ω) with hφ₁def
  set φ₂ : Ω → (Fin 1 → ℝ) × ℝ := fun ω ↦ (fun _ ↦ expIntTwin B σ s ω, B s ω) with hφ₂def
  have h₁ : (fun ω ↦ ((fun _ : Fin 1 ↦
      ∫ r in (0 : ℝ)..(s : ℝ), Real.exp (σ * B r.toNNReal ω)), B s ω)) = φ₁ := by
    funext ω
    refine Prod.ext (funext fun _ ↦ ?_) rfl
    exact (timeMeasure_Ioc_eq_interval (g := fun r ↦ Real.exp (σ * B r ω)) s).symm
  have h₂ : (fun ω ↦ ((fun _ : Fin 1 ↦
      ∫ r in (0 : ℝ)..(s : ℝ), Real.exp (σ * (B s ω - B r.toNNReal ω))), B s ω)) = φ₂ := by
    funext ω
    refine Prod.ext (funext fun _ ↦ ?_) rfl
    change _ = Real.exp (σ * B s ω) * driftPath (fun r ω ↦ Real.exp (-σ * B r ω)) s ω
    rw [driftPath, timeMeasure_Ioc_eq_interval (g := fun r ↦ Real.exp (-σ * B r ω)) s,
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun r _ ↦ ?_
    change Real.exp (σ * (B s ω - B r.toNNReal ω))
      = Real.exp (σ * B s ω) * Real.exp (-σ * B r.toNNReal ω)
    rw [← Real.exp_add]
    congr 1
    ring
  have htr : μ.map φ₁ = μ.map φ₂ := by
    rw [← h₁, ← h₂]
    exact time_reversal μ B hB 1 (fun _ _ w ↦ Real.exp (σ * w)) (fun _ ↦ by fun_prop) s
  have hφ₁ : Measurable φ₁ :=
    (measurable_pi_iff.2 fun _ ↦ measurable_driftPath_exp hBmeas hBcont σ s).prodMk (hBmeas s)
  have hφ₂ : Measurable φ₂ :=
    (measurable_pi_iff.2 fun _ ↦ measurable_expIntTwin hBmeas hBcont σ s).prodMk (hBmeas s)
  have hg' : Continuous fun p : (Fin 1 → ℝ) × ℝ ↦ g (p.1 0) p.2 :=
    hg.comp (f := fun p : (Fin 1 → ℝ) × ℝ ↦ (p.1 0, p.2))
      (((continuous_apply 0).comp continuous_fst).prodMk continuous_snd)
  calc ∫ ω, g (expIntTwin B σ s ω) (B s ω) ∂μ
      = ∫ p, g (p.1 0) p.2 ∂(μ.map φ₂) :=
        (integral_map hφ₂.aemeasurable hg'.aestronglyMeasurable).symm
    _ = ∫ p, g (p.1 0) p.2 ∂(μ.map φ₁) := by rw [htr]
    _ = ∫ ω, g (driftPath (fun r ω ↦ Real.exp (σ * B r ω)) s ω) (B s ω) ∂μ :=
        integral_map hφ₁.aemeasurable hg'.aestronglyMeasurable

/-- Itô's formula for a product test along `(expIntTwin, B)`, for a pre-Brownian motion with
every path continuous, with the time integral over `ℝ≥0`: the twin is an Itô process
(`dY = (1 + σ² Y / 2) ds + σ Y dB`, by the product rule for `e^{σ B} · ∫ e^{-σ B}`), then Itô's
formula for `u ∘ Y`, the product rule with `v ∘ B`, and the stochastic term is centered. -/
theorem ito_expIntTwin_product_of_continuous {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) (σ : ℝ) (T : ℝ≥0)
    (u v : ℝ → ℝ) (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (huC : HasCompactSupport u) (hvC : HasCompactSupport v) :
    (∫ ω, u (expIntTwin B σ T ω) * v (B T ω) ∂μ) - u 0 * v 0 =
      ∫ s in Ioc (0 : ℝ≥0) T,
        (∫ ω, twinGenerator σ u v (expIntTwin B σ s ω) (B s ω) ∂μ) ∂timeMeasure := by
  obtain ⟨Cu, hu_bdd, hu'_bdd, -⟩ := contDiff_top_compactSupport_bounds hu huC
  obtain ⟨Cv, hv_bdd, hv'_bdd, hv''_bdd⟩ := contDiff_top_compactSupport_bounds hv hvC
  have hCu : 0 ≤ Cu := (abs_nonneg _).trans (hu_bdd 0)
  have hCv : 0 ≤ Cv := (abs_nonneg _).trans (hv_bdd 0)
  -- regularity of the tests
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by decide)
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by decide)
  have hdu1 : ContDiff ℝ 1 (deriv u) := (contDiff_succ_iff_deriv (n := 1)).mp hu2 |>.2.2
  have huc : Continuous u := hu.continuous
  have hu'c : Continuous (deriv u) := ContDiff.continuous_deriv_one hu1
  have hu''c : Continuous (deriv (deriv u)) := ContDiff.continuous_deriv_one hdu1
  have hu' (x : ℝ) : HasDerivAt u (deriv u x) x :=
    (hu1.differentiable (by decide)).differentiableAt.hasDerivAt
  have hu'' (x : ℝ) : HasDerivAt (deriv u) (deriv (deriv u) x) x :=
    (hdu1.differentiable (by decide)).differentiableAt.hasDerivAt
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by decide)
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by decide)
  have hdv1 : ContDiff ℝ 1 (deriv v) := (contDiff_succ_iff_deriv (n := 1)).mp hv2 |>.2.2
  have hvc : Continuous v := hv.continuous
  have hv'c : Continuous (deriv v) := ContDiff.continuous_deriv_one hv1
  have hv''c : Continuous (deriv (deriv v)) := ContDiff.continuous_deriv_one hdv1
  have hv' (x : ℝ) : HasDerivAt v (deriv v x) x :=
    (hv1.differentiable (by decide)).differentiableAt.hasDerivAt
  have hv'' (x : ℝ) : HasDerivAt (deriv v) (deriv (deriv v) x) x :=
    (hdv1.differentiable (by decide)).differentiableAt.hasDerivAt
  -- `x u'(x)` and `x² u''(x)` are bounded: `u` has compact support
  obtain ⟨K₁, hK₁⟩ := (show Continuous ((fun x : ℝ ↦ x) * deriv u) from
    continuous_id.mul hu'c).bounded_above_of_compact_support huC.deriv.mul_left
  obtain ⟨K₂, hK₂⟩ := (show Continuous ((fun x : ℝ ↦ x ^ 2) * deriv (deriv u)) from
    (continuous_id.pow 2).mul hu''c).bounded_above_of_compact_support huC.deriv.deriv.mul_left
  have hK₁' (x : ℝ) : |x * deriv u x| ≤ K₁ := hK₁ x
  have hK₂' (x : ℝ) : |x ^ 2 * deriv (deriv u) x| ≤ K₂ := hK₂ x
  have hK₁0 : 0 ≤ K₁ := (abs_nonneg _).trans (hK₁' 0)
  have hK₂0 : 0 ≤ K₂ := (abs_nonneg _).trans (hK₂' 0)
  -- the twin `Y` and its Itô decomposition `dY = (1 + σ² Y / 2) ds + σ Y dB`
  have hBadap : ∀ s, StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)] (B s) :=
    stronglyAdapted_natFiltration hBmeas
  set Y : ℝ≥0 → Ω → ℝ := expIntTwin B σ with hY
  have hYa : ∀ s, StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)] (Y s) :=
    stronglyAdapted_expIntTwin hBmeas hBcont σ
  have hYc : ∀ ω, Continuous fun s ↦ Y s ω := continuous_expIntTwin hBcont σ
  have hYm : ∀ s, Measurable (Y s) := measurable_expIntTwin hBmeas hBcont σ
  set σY : ℝ≥0 → Ω → ℝ := fun s ω ↦ σ * Y s ω with hσY
  have hσYa : ∀ s, StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)] (σY s) :=
    fun s ↦ (hYa s).const_mul σ
  have hσYc : ∀ ω, Continuous fun s ↦ σY s ω := fun ω ↦ continuous_const.mul (hYc ω)
  set bY : ℝ≥0 → Ω → ℝ := fun s ω ↦ 1 + σ ^ 2 / 2 * Y s ω with hbY
  have hbYa : ∀ s, StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)] (bY s) :=
    fun s ↦ stronglyMeasurable_const.add ((hYa s).const_mul (σ ^ 2 / 2))
  have hbYc : ∀ ω, Continuous fun s ↦ bY s ω := fun ω ↦
    continuous_const.add (continuous_const.mul (hYc ω))
  have hLY : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      localItoProcess (μ := μ) T hBmeas hσYa hσYc 0 bY t ω = Y t ω :=
    ae_localItoProcess_expIntTwin hB T hBmeas hBcont σ hσYa hσYc
  -- Itô's formula for `u ∘ Y`
  set σU : ℝ≥0 → Ω → ℝ := fun s ω ↦ deriv u (Y s ω) * σY s ω with hσU
  have hσUa : ∀ s, StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)] (σU s) :=
    fun s ↦ (hu'c.comp_stronglyMeasurable (hYa s)).mul (hσYa s)
  have hσUc : ∀ ω, Continuous fun s ↦ σU s ω := fun ω ↦ (hu'c.comp (hYc ω)).mul (hσYc ω)
  set bU : ℝ≥0 → Ω → ℝ := fun s ω ↦
    deriv u (Y s ω) * bY s ω + 1 / 2 * (deriv (deriv u) (Y s ω) * σY s ω ^ 2) with hbU
  have hbUa : ∀ s, StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)] (bU s) :=
    fun s ↦ ((hu'c.comp_stronglyMeasurable (hYa s)).mul (hbYa s)).add
      (((hu''c.comp_stronglyMeasurable (hYa s)).mul ((hσYa s).pow 2)).const_mul (1 / 2))
  have hbUc : ∀ ω, Continuous fun s ↦ bU s ω := fun ω ↦
    ((hu'c.comp (hYc ω)).mul (hbYc ω)).add
      (continuous_const.mul ((hu''c.comp (hYc ω)).mul ((hσYc ω).pow 2)))
  have hLU : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      localItoProcess (μ := μ) T hBmeas hσUa hσUc (u 0) bU t ω = u (Y t ω) :=
    ae_localItoProcess_comp_of_version hB T hBmeas hBcont hσYa hσYc hbYa hbYc hLY
      hu' hu'' hu''c hσUa hσUc (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) rfl
  -- Itô's formula for `v ∘ B`
  set τ : ℝ≥0 → Ω → ℝ := fun s ω ↦ deriv v (B s ω) with hτ
  have hτa : ∀ s, StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)] (τ s) :=
    fun s ↦ hv'c.comp_stronglyMeasurable (hBadap s)
  have hτc : ∀ ω, Continuous fun s ↦ τ s ω := fun ω ↦ hv'c.comp (hBcont ω)
  set c : ℝ≥0 → Ω → ℝ := fun s ω ↦ 1 / 2 * deriv (deriv v) (B s ω) with hc
  have hca : ∀ s, StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)] (c s) :=
    fun s ↦ (hv''c.comp_stronglyMeasurable (hBadap s)).const_mul (1 / 2)
  have hcc : ∀ ω, Continuous fun s ↦ c s ω := fun ω ↦
    continuous_const.mul (hv''c.comp (hBcont ω))
  have hLV : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      localItoProcess (μ := μ) T hBmeas hτa hτc (v 0) c t ω = v (B t ω) :=
    ae_localItoProcess_comp_of_version hB T hBmeas hBcont
      (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const)
      (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const)
      (ae_localItoProcess_one_eq hB T hBmeas hBcont)
      hv' hv'' hv''c hτa hτc
      (fun s ω ↦ by simp only [τ, mul_one])
      (fun s ω ↦ by simp only [c]; ring) rfl
  -- the product rule for `(u ∘ Y) (v ∘ B)`
  set LU : ℝ≥0 → Ω → ℝ := localItoProcess (μ := μ) T hBmeas hσUa hσUc (u 0) bU with hLUdef
  set LV : ℝ≥0 → Ω → ℝ := localItoProcess (μ := μ) T hBmeas hτa hτc (v 0) c with hLVdef
  have hθ : IsStronglyPredictable (natFiltration hBmeas)
      fun s ω ↦ LU s ω * τ s ω + LV s ω * σU s ω :=
    productIntegrand_isStronglyPredictable hB T hBmeas hBcont hσUa hσUc hτa hτc hbUa hbUc
      hca hcc (u 0) (v 0)
  have hprod : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, LU t ω * LV t ω = u 0 * v 0
      + ∫ s in Ioc 0 t, (LU s ω * c s ω + LV s ω * bU s ω + σU s ω * τ s ω) ∂timeMeasure
      + predItoIntegral (μ := μ) T hBmeas hθ t ω :=
    ito_product_rule_process hB T hBmeas hBcont hσUa hσUc hτa hτc hbUa hbUc hca hcc
      (u 0) (v 0)
  -- the stochastic term is centered: its integrand is bounded
  have hσU_bdd (s : ℝ≥0) (ω : Ω) : |σU s ω| ≤ |σ| * K₁ := by
    have h : σU s ω = σ * (Y s ω * deriv u (Y s ω)) := by
      simp only [σU, σY]
      ring
    rw [h, abs_mul]
    exact mul_le_mul_of_nonneg_left (hK₁' _) (abs_nonneg _)
  have hθeq : ∀ᵐ ω ∂μ, ∀ s ∈ Icc 0 T,
      LU s ω * τ s ω + LV s ω * σU s ω
        = u (Y s ω) * deriv v (B s ω) + v (B s ω) * σU s ω := by
    filter_upwards [hLU, hLV] with ω h1 h2 s hs
    rw [h1 s hs, h2 s hs]
  have hθc : ∀ᵐ ω ∂μ,
      ContinuousOn (fun s ↦ LU s ω * τ s ω + LV s ω * σU s ω) (Icc 0 T) := by
    filter_upwards [hθeq] with ω h
    exact (((huc.comp (hYc ω)).mul (hv'c.comp (hBcont ω))).add
      ((hvc.comp (hBcont ω)).mul (hσUc ω))).continuousOn.congr h
  have hθbdd : ∀ᵐ ω ∂μ, ∀ s ∈ Icc 0 T,
      |LU s ω * τ s ω + LV s ω * σU s ω| ≤ (⌈Cu * Cv + Cv * (|σ| * K₁)⌉₊ : ℕ) := by
    filter_upwards [hθeq] with ω h s hs
    rw [h s hs]
    have h1 : |u (Y s ω) * deriv v (B s ω)| ≤ Cu * Cv := by
      rw [abs_mul]
      exact mul_le_mul (hu_bdd _) (hv'_bdd _) (abs_nonneg _) hCu
    have h2 : |v (B s ω) * σU s ω| ≤ Cv * (|σ| * K₁) := by
      rw [abs_mul]
      exact mul_le_mul (hv_bdd _) (hσU_bdd s ω) (abs_nonneg _) hCv
    exact ((abs_add_le _ _).trans (add_le_add h1 h2)).trans (Nat.le_ceil _)
  obtain ⟨hMint, hMzero⟩ :=
    integral_predItoIntegral_eq_zero_of_ae_bdd hB T hBmeas hBcont hθ hθc _ hθbdd
  -- the drift weight
  set w : ℝ≥0 → Ω → ℝ := fun s ω ↦ twinGenerator σ u v (Y s ω) (B s ω) with hw
  have hG : Continuous fun p : ℝ × ℝ ↦ twinGenerator σ u v p.1 p.2 :=
    continuous_twinGenerator σ hu hv
  have hw_meas : ∀ s, Measurable (w s) := by
    intro s
    have h := hG.measurable.comp ((hYm s).prodMk (hBmeas s))
    exact h
  have hw_cont : ∀ ω, Continuous fun s ↦ w s ω := by
    intro ω
    have h := hG.comp ((hYc ω).prodMk (hBcont ω))
    exact h
  have hC0 : 0 ≤ Cu * Cv + σ ^ 2 / 2 * K₁ * Cv + σ ^ 2 / 2 * K₂ * Cv + |σ| * K₁ * Cv
      + 1 / 2 * Cu * Cv := by positivity
  have hw_bdd : ∀ s ω, |w s ω| ≤ Cu * Cv + σ ^ 2 / 2 * K₁ * Cv + σ ^ 2 / 2 * K₂ * Cv
      + |σ| * K₁ * Cv + 1 / 2 * Cu * Cv := by
    intro s ω
    have hσ2 : (0 : ℝ) ≤ σ ^ 2 / 2 := by positivity
    have e1 : |1 * deriv u (Y s ω) * v (B s ω)| ≤ Cu * Cv := by
      rw [one_mul, abs_mul]
      exact mul_le_mul (hu'_bdd _) (hv_bdd _) (abs_nonneg _) hCu
    have e2 : |σ ^ 2 / 2 * Y s ω * deriv u (Y s ω) * v (B s ω)| ≤ σ ^ 2 / 2 * K₁ * Cv := by
      rw [mul_assoc (σ ^ 2 / 2), abs_mul, abs_mul, abs_of_nonneg hσ2]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hK₁' _) hσ2) (hv_bdd _) (abs_nonneg _)
        (by positivity)
    have e3 : |σ ^ 2 / 2 * Y s ω ^ 2 * deriv (deriv u) (Y s ω) * v (B s ω)|
        ≤ σ ^ 2 / 2 * K₂ * Cv := by
      rw [mul_assoc (σ ^ 2 / 2), abs_mul, abs_mul, abs_of_nonneg hσ2]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hK₂' _) hσ2) (hv_bdd _) (abs_nonneg _)
        (by positivity)
    have e4 : |σ * Y s ω * deriv u (Y s ω) * deriv v (B s ω)| ≤ |σ| * K₁ * Cv := by
      rw [mul_assoc σ, abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hK₁' _) (abs_nonneg _)) (hv'_bdd _)
        (abs_nonneg _) (by positivity)
    have e5 : |1 / 2 * u (Y s ω) * deriv (deriv v) (B s ω)| ≤ 1 / 2 * Cu * Cv := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hu_bdd _) (by norm_num)) (hv''_bdd _)
        (abs_nonneg _) (by positivity)
    simp only [w, twinGenerator]
    exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add e1 e2)) e3))
      e4)) e5)
  have hpathint : Integrable (fun ω ↦ ∫ s in Ioc 0 T, w s ω ∂timeMeasure) μ :=
    (memLp_pathIntegral_process hw_meas hw_cont hC0 hw_bdd T).integrable one_le_two
  -- the pathwise identity at the horizon
  have hid : ∀ᵐ ω ∂μ, u (Y T ω) * v (B T ω) = u 0 * v 0
      + ∫ s in Ioc 0 T, w s ω ∂timeMeasure + predItoIntegral (μ := μ) T hBmeas hθ T ω := by
    filter_upwards [hprod, hLU, hLV] with ω hp hU hV
    have hT : T ∈ Icc (0 : ℝ≥0) T := ⟨zero_le, le_rfl⟩
    have h1 := hp T hT
    rw [hU T hT, hV T hT] at h1
    have hint : ∫ s in Ioc 0 T, (LU s ω * c s ω + LV s ω * bU s ω + σU s ω * τ s ω)
        ∂timeMeasure = ∫ s in Ioc 0 T, w s ω ∂timeMeasure := by
      refine setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ ?_
      have hsT : s ∈ Icc (0 : ℝ≥0) T := ⟨zero_le, hs.2⟩
      simp only [hU s hsT, hV s hsT, w, twinGenerator, c, bU, σU, bY, σY, τ]
      ring
    rw [h1, hint]
  calc (∫ ω, u (Y T ω) * v (B T ω) ∂μ) - u 0 * v 0
      = (∫ ω, (u 0 * v 0 + ∫ s in Ioc 0 T, w s ω ∂timeMeasure
          + predItoIntegral (μ := μ) T hBmeas hθ T ω) ∂μ) - u 0 * v 0 := by
        rw [integral_congr_ae hid]
    _ = ∫ ω, (∫ s in Ioc 0 T, w s ω ∂timeMeasure) ∂μ := by
        have hsum : Integrable
            (fun ω ↦ u 0 * v 0 + ∫ s in Ioc 0 T, w s ω ∂timeMeasure) μ :=
          (integrable_const _).add hpathint
        rw [integral_add hsum hMint, integral_add (integrable_const _) hpathint, hMzero,
          integral_const]
        simp
    _ = ∫ s in Ioc 0 T, (∫ ω, w s ω ∂μ) ∂timeMeasure :=
        expectation_pathIntegral_eq hw_meas (ae_of_all _ hw_cont) hC0 hw_bdd T

/-- Paper (3.4b) after time-reversal, for product tests. -/
theorem ito_timeReversed_expInt_test_product (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (_ht : 0 < t)
    (u v : ℝ → ℝ) (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
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
  -- Work along the continuous modification `B` of `W`.
  set B : ℝ≥0 → Ω → ℝ := hW.toIsPreBrownianReal.mk W
  have hBmeas : ∀ s, Measurable (B s) := hW.toIsPreBrownianReal.measurable_mk
  have hBcont : ∀ ω, Continuous fun s : ℝ≥0 => B s ω := hW.toIsPreBrownianReal.continuous_mk
  have hBbm : IsBrownianReal B P := hW.toIsPreBrownianReal.isBrownianReal_mk
  have hBpre : IsPreBrownianReal B P := hBbm.toIsPreBrownianReal
  have hBae : ∀ s, B s =ᵐ[P] W s := fun s => hW.toIsPreBrownianReal.mk_ae_eq s
  have hpath : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, B s ω = W s ω :=
    indistinguishable_of_modification (ae_of_all _ hBcont) hW.cont hBae
  -- The drift path of `exp(σ B)` is `expInt W`, on almost every path at all times.
  have hdrift : ∀ᵐ ω ∂P, ∀ s : ℝ≥0,
      driftPath (fun r ω ↦ Real.exp (σ * B r ω)) s ω = expInt W σ 0 s ω := by
    filter_upwards [hpath] with ω hω s
    rw [driftPath, timeMeasure_Ioc_eq_interval (g := fun r ↦ Real.exp (σ * B r ω)) s]
    simp only [expInt, zero_mul, add_zero, hω]
  -- Itô along the time-reversed twin `Y_s = ∫₀ˢ exp(σ (B_s - B_r)) dr`
  -- (`dY = (1 + σ² Y / 2) ds + σ Y dB`).
  have key := ito_expIntTwin_product_of_continuous hBpre hBmeas hBcont σ t u v hu hv huC hvC
  -- `time_reversal` at each horizon replaces the twin by `expInt` in expectation.
  have hG : Continuous fun p : ℝ × ℝ ↦ twinGenerator σ u v p.1 p.2 :=
    continuous_twinGenerator σ hu hv
  have huv : Continuous fun p : ℝ × ℝ ↦ u p.1 * v p.2 :=
    (hu.continuous.comp continuous_fst).mul (hv.continuous.comp continuous_snd)
  have hterm : (∫ ω, u (expInt W σ 0 t ω) * v (W t ω) ∂P) =
      ∫ ω, u (expIntTwin B σ t ω) * v (B t ω) ∂P := by
    rw [integral_expIntTwin_eq hBbm hBmeas hBcont σ t (g := fun x y ↦ u x * v y) huv]
    refine integral_congr_ae ?_
    filter_upwards [hpath, hdrift] with ω h1 h2
    rw [h2 t, h1 t]
  rw [hterm, key, timeMeasure_Ioc_eq_interval t,
    intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]
  refine setIntegral_congr_fun measurableSet_Ioc fun s _ ↦ ?_
  refine (integral_expIntTwin_eq hBbm hBmeas hBcont σ s.toNNReal
    (g := twinGenerator σ u v) hG).trans (integral_congr_ae ?_)
  filter_upwards [hpath, hdrift] with ω h1 h2
  rw [h2 s.toNNReal, h1 s.toNNReal]
  rfl

end Lyasoff2016
