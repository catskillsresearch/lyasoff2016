/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Cameron–Martin–Girsanov for a constant drift, at the level of path functionals (p. 1066, (2.2)).

* `isBrownianReal_path_functional_two`: two Brownian motions, possibly under two different
  probability measures, give the same law to any measurable path functional.
* `isBrownianReal_drift_girsanov`: for a (measurable) Brownian motion `B` under `P`, the process
  `u ↦ B_u + θ (u ∧ T)` is a Brownian motion on all of `ℝ≥0` under
  `Q = exp(−θ B_T − θ² T / 2) · P`.  On `[0, T]` the exponential martingales come from MathFin's
  constant-θ Girsanov (`MathFin.expBtheta_isQMartingale`); past `T` the drift is frozen and the
  Wald exponential of `B` is pulled through the `𝓕_T`-measurable density.
* `cameronMartin_path_functional`: the resulting change of measure for path functionals.
* `jointLaw_girsanov`: the joint law `(∫₀ᵗ e^{σ W_s + σθ s} ds, W_t)`, tilted by
  `exp(−θ y − θ² t / 2)` and shifted by `y ↦ y + θ t`, is the zero-drift joint law.
* `jointDensity_girsanov_posPart`: the pointwise identity (2.2) between continuous densities,
  for their positive parts.
-/
module

public import Lyasoff2016.BrownianScaling
public import MathFin.Probability.Brownian.Girsanov.GirsanovConstantTheta
public import MathFin.Probability.Brownian.ExpMartingaleBrownian


@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-! ### Laws of path functionals under two measures -/

/-- The law of a measurable path functional is the same along any two Brownian motions, even
when they live under different probability measures (or on different spaces). -/
theorem isBrownianReal_path_functional_two {Ω' : Type*} [MeasurableSpace Ω']
    {E : Type*} [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (W : ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω' → ℝ) (hW : IsBrownianReal W P) (hB : IsBrownianReal B Q)
    (F : (ℝ≥0 → ℝ) → E) (hF : Measurable fun x : C(ℝ≥0, ℝ) => F (fun s => x s)) :
    P.map (fun ω => F (fun s => W s ω)) = Q.map (fun ω => F (fun s => B s ω)) := by
  let W' := (hW.toIsPreBrownianReal).mk W
  let B' := (hB.toIsPreBrownianReal).mk B
  let pW : Ω → C(ℝ≥0, ℝ) :=
    fun ω => ⟨(fun s => W' s ω), hW.toIsPreBrownianReal.continuous_mk ω⟩
  let pB : Ω' → C(ℝ≥0, ℝ) :=
    fun ω => ⟨(fun s => B' s ω), hB.toIsPreBrownianReal.continuous_mk ω⟩
  have hpW : Measurable pW := ContinuousMap.measurable_iff_eval.2 fun s =>
    by simpa [pW, W'] using hW.toIsPreBrownianReal.measurable_mk s
  have hpB : Measurable pB := ContinuousMap.measurable_iff_eval.2 fun s =>
    by simpa [pB, B'] using hB.toIsPreBrownianReal.measurable_mk s
  let e : C(ℝ≥0, ℝ) → (ℝ≥0 → ℝ) := fun x s => x s
  have he : Measurable e := measurable_pi_iff.2 fun s => ContinuousMap.measurable_eval s
  have he_comap : MeasurableSpace.comap e inferInstance =
      (inferInstance : MeasurableSpace C(ℝ≥0, ℝ)) := by
    apply le_antisymm
    · exact he.comap_le
    · rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval]
      refine iSup_le fun s => ?_
      rw [← measurable_iff_comap_le]
      exact (measurable_pi_apply s).comp (comap_measurable e)
  have hrawW : P.map (e ∘ pW) = gaussianLimit :=
    (hW.toIsPreBrownianReal.isBrownianReal_mk.toIsPreBrownianReal.hasLaw_gaussianLimit
      ((he.comp hpW).aemeasurable)).map_eq
  have hrawB : Q.map (e ∘ pB) = gaussianLimit :=
    (hB.toIsPreBrownianReal.isBrownianReal_mk.toIsPreBrownianReal.hasLaw_gaussianLimit
      ((he.comp hpB).aemeasurable)).map_eq
  have hpath : P.map pW = Q.map pB := by
    have hmap : (P.map pW).map e = (Q.map pB).map e := by
      calc
        (P.map pW).map e = P.map (e ∘ pW) := Measure.map_map he hpW
        _ = gaussianLimit := hrawW
        _ = Q.map (e ∘ pB) := hrawB.symm
        _ = (Q.map pB).map e := (Measure.map_map he hpB).symm
    ext A hA
    have hA' : MeasurableSet[MeasurableSpace.comap e inferInstance] A :=
      he_comap.symm ▸ hA
    rcases hA' with ⟨S, hS, rfl⟩
    rw [← Measure.map_apply he hS, hmap, Measure.map_apply he hS]
  let Φ : C(ℝ≥0, ℝ) → E := fun x => F (fun s => x s)
  have hWae : (fun ω => F (fun s => W s ω)) =ᵐ[P] Φ ∘ pW :=
    hW.mk_ae_forall_eq.mono fun ω hω => by
      simp only [Function.comp_apply, Φ, pW, ContinuousMap.coe_mk]
      congr 1
      funext s
      exact (hω s).symm
  have hBae : (fun ω => F (fun s => B s ω)) =ᵐ[Q] Φ ∘ pB :=
    hB.mk_ae_forall_eq.mono fun ω hω => by
      simp only [Function.comp_apply, Φ, pB, ContinuousMap.coe_mk]
      congr 1
      funext s
      exact (hω s).symm
  calc
    P.map (fun ω => F (fun s => W s ω)) = P.map (Φ ∘ pW) := Measure.map_congr hWae
    _ = (P.map pW).map Φ := (Measure.map_map hF hpW).symm
    _ = (Q.map pB).map Φ := by rw [hpath]
    _ = Q.map (Φ ∘ pB) := Measure.map_map hF hpB
    _ = Q.map (fun ω => F (fun s => B s ω)) := (Measure.map_congr hBae).symm

/-! ### Constant-drift Girsanov on the whole time axis -/

/-- Set integrals against `μ.withDensity (ofReal ∘ Z)` for a nonnegative real density `Z`. -/
theorem setIntegral_withDensity_ofReal_mul {μ : Measure Ω} {Z : Ω → ℝ} (hZ : Measurable Z)
    (hZpos : ∀ ω, 0 ≤ Z ω) (h : Ω → ℝ) {A : Set Ω} (hA : MeasurableSet A) :
    ∫ ω in A, h ω ∂(μ.withDensity fun ω => ENNReal.ofReal (Z ω)) = ∫ ω in A, h ω * Z ω ∂μ := by
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hZ.ennreal_ofReal.aemeasurable.restrict
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) h hA]
  refine setIntegral_congr_ae hA (ae_of_all _ fun ω _ => ?_)
  rw [ENNReal.toReal_ofReal (hZpos ω), smul_eq_mul, mul_comm]

/-- **Girsanov for a constant drift, frozen after the horizon.**  If `B` is a Brownian motion
under `P` with measurable marginals, then under `Q = exp(−θ B_T − θ² T / 2) · P` the process
`u ↦ B_u + θ (u ∧ T)` is a Brownian motion. -/
theorem isBrownianReal_drift_girsanov (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hBmeas : ∀ t, Measurable (B t))
    (θ : ℝ) (T : ℝ≥0) :
    IsProbabilityMeasure
        (P.withDensity fun ω => ENNReal.ofReal (Real.exp (-θ * B T ω - θ ^ 2 * (T : ℝ) / 2))) ∧
      IsBrownianReal (fun u ω => B u ω + θ * ((min u T : ℝ≥0) : ℝ))
        (P.withDensity fun ω => ENNReal.ofReal (Real.exp (-θ * B T ω - θ ^ 2 * (T : ℝ) / 2))) := by
  set 𝓕 : Filtration ℝ≥0 mΩ :=
    Filtration.natural B (fun t => (hBmeas t).stronglyMeasurable) with h𝓕
  have hFB : IsFilteredPreBrownian B 𝓕 P :=
    hB.toIsPreBrownianReal.isFilteredPreBrownian hBmeas
  set Z : Ω → ℝ := fun ω => Real.exp (-θ * B T ω - θ ^ 2 * (T : ℝ) / 2) with hZdef
  have hZmeas : Measurable Z := (((hBmeas T).const_mul (-θ)).sub_const _).exp
  have hZpos : ∀ ω, 0 ≤ Z ω := fun ω => (Real.exp_pos _).le
  have hQ : IsProbabilityMeasure (P.withDensity fun ω => ENNReal.ofReal (Z ω)) :=
    MathFin.girsanovMeasure_isProbabilityMeasure (X := B) (𝓕 := 𝓕) θ T
  have hQP : (P.withDensity fun ω => ENNReal.ofReal (Z ω)) ≪ P :=
    withDensity_absolutelyContinuous _ _
  refine ⟨hQ, ?_⟩
  -- The exponential martingale identity on `[0, T]`: MathFin's constant-θ Girsanov.
  have hlow : ∀ (a : ℝ) {s t : ℝ≥0}, s ≤ t → t ≤ T → ∀ {A : Set Ω},
      MeasurableSet[(𝓕 s : MeasurableSpace Ω)] A →
      ∫ ω in A, Real.exp (a * (B t ω + θ * ((min t T : ℝ≥0) : ℝ)) - a ^ 2 * (t : ℝ) / 2)
          ∂(P.withDensity fun ω => ENNReal.ofReal (Z ω)) =
        ∫ ω in A, Real.exp (a * (B s ω + θ * ((min s T : ℝ≥0) : ℝ)) - a ^ 2 * (s : ℝ) / 2)
          ∂(P.withDensity fun ω => ENNReal.ofReal (Z ω)) := by
    intro a s t hst htT A hA
    rw [min_eq_left htT, min_eq_left (hst.trans htT)]
    exact MathFin.expBtheta_isQMartingale (P := P) (𝓕 := 𝓕) (X := B) θ a T hst htT hA
  -- Past `T`: the drift is frozen and the Wald exponential of `B` is a `P`-martingale.
  have htail : ∀ (a : ℝ) {s t : ℝ≥0}, T ≤ s → s ≤ t → ∀ {A : Set Ω},
      MeasurableSet[(𝓕 s : MeasurableSpace Ω)] A →
      ∫ ω in A, Real.exp (a * (B t ω + θ * ((min t T : ℝ≥0) : ℝ)) - a ^ 2 * (t : ℝ) / 2)
          ∂(P.withDensity fun ω => ENNReal.ofReal (Z ω)) =
        ∫ ω in A, Real.exp (a * (B s ω + θ * ((min s T : ℝ≥0) : ℝ)) - a ^ 2 * (s : ℝ) / 2)
          ∂(P.withDensity fun ω => ENNReal.ofReal (Z ω)) := by
    intro a s t hTs hst A hA
    have hAm : MeasurableSet A := 𝓕.le s A hA
    rw [min_eq_right (hTs.trans hst), min_eq_right hTs,
      setIntegral_withDensity_ofReal_mul hZmeas hZpos _ hAm,
      setIntegral_withDensity_ofReal_mul hZmeas hZpos _ hAm]
    set K : Ω → ℝ := fun ω => Real.exp (a * θ * (T : ℝ)) * Z ω with hKdef
    set M : ℝ≥0 → Ω → ℝ := fun u ω => Real.exp (a * B u ω - a ^ 2 * (u : ℝ) / 2) with hMdef
    have hM : Martingale M 𝓕 P := IsFilteredPreBrownian.waldExponential_isMartingale a
    have hsplit : ∀ (u : ℝ≥0) (ω : Ω),
        Real.exp (a * (B u ω + θ * (T : ℝ)) - a ^ 2 * (u : ℝ) / 2) * Z ω = (K * M u) ω := by
      intro u ω
      simp only [Pi.mul_apply, hKdef, hMdef, hZdef]
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    simp only [hsplit]
    have hKsm : StronglyMeasurable[𝓕 s] K := by
      have hcont : Continuous fun x : ℝ =>
          Real.exp (a * θ * (T : ℝ)) * Real.exp (-θ * x - θ ^ 2 * (T : ℝ) / 2) := by fun_prop
      exact (hcont.comp_stronglyMeasurable (hFB.stronglyAdapted T)).mono (𝓕.mono hTs)
    have hKM : Integrable (K * M t) P := by
      have hcore : Integrable
          (fun ω => Real.exp (-θ * B T ω) * Real.exp (a * B t ω)) P := by
        refine MathFin.integrable_exp_mul_exp ((hBmeas T).const_mul (-θ))
          ((hBmeas t).const_mul a) ?_ ?_
        · refine ((hFB.hasLaw_eval T).integrable_fun_comp
            (integrable_exp_mul_gaussianReal (2 * -θ))).congr (ae_of_all _ fun ω => ?_)
          show Real.exp (2 * -θ * B T ω) = Real.exp (2 * (-θ * B T ω))
          rw [mul_assoc]
        · refine ((hFB.hasLaw_eval t).integrable_fun_comp
            (integrable_exp_mul_gaussianReal (2 * a))).congr (ae_of_all _ fun ω => ?_)
          show Real.exp (2 * a * B t ω) = Real.exp (2 * (a * B t ω))
          rw [mul_assoc]
      have hrw : K * M t = fun ω =>
          Real.exp (a * θ * (T : ℝ) - θ ^ 2 * (T : ℝ) / 2 - a ^ 2 * (t : ℝ) / 2) *
            (Real.exp (-θ * B T ω) * Real.exp (a * B t ω)) := by
        funext ω
        simp only [Pi.mul_apply, hKdef, hMdef, hZdef]
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [hrw]
      exact hcore.const_mul _
    have hce : P[K * M t | 𝓕 s] =ᵐ[P] K * M s :=
      (condExp_mul_of_stronglyMeasurable_left hKsm hKM (hM.integrable t)).trans
        ((hM.condExp_ae_eq hst).mono fun ω h => by simp only [Pi.mul_apply, h])
    calc ∫ ω in A, (K * M t) ω ∂P
        = ∫ ω in A, (P[K * M t | 𝓕 s]) ω ∂P := (setIntegral_condExp (𝓕.le s) hKM hA).symm
      _ = ∫ ω in A, (K * M s) ω ∂P := setIntegral_congr_ae hAm (hce.mono fun ω h _ => h)
  have hexp : ∀ T', MathFin.IsExpQMartingale
      (P.withDensity fun ω => ENNReal.ofReal (Z ω)) 𝓕
      (fun u ω => B u ω + θ * ((min u T : ℝ≥0) : ℝ)) T' := by
    intro T'
    refine ⟨fun u => (hFB.stronglyAdapted u).add_const _, ?_, ?_⟩
    · filter_upwards [hQP.ae_le hB.eval_zero_ae_eq_zero] with ω hω
      simp [hω]
    · intro a s t hst _ A hA
      by_cases hsT : T ≤ s
      · exact htail a hsT hst hA
      · rw [not_le] at hsT
        by_cases htT : t ≤ T
        · exact hlow a hst htT hA
        · rw [not_le] at htT
          exact (htail a le_rfl htT.le (𝓕.mono hsT.le A hA)).trans (hlow a hsT.le le_rfl hA)
  refine MathFin.isBrownianReal_of_expMartingale hexp (hQP.ae_le ?_)
  filter_upwards [hB.cont] with ω hω
  exact hω.add (by fun_prop)

/-! ### Cameron–Martin for path functionals -/

/-- **Cameron–Martin for a constant drift.**  For a Brownian motion `W` under `P` and a
measurable path functional `F`, the law of `F (W + θ (· ∧ T))` under
`exp(−θ W_T − θ² T / 2) · P` is the law of `F W` under `P`. -/
theorem cameronMartin_path_functional {E : Type*} [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P)
    (θ : ℝ) (T : ℝ≥0) (F : (ℝ≥0 → ℝ) → E)
    (hF : Measurable fun x : C(ℝ≥0, ℝ) => F (fun s => x s)) :
    (P.withDensity fun ω => ENNReal.ofReal (Real.exp (-θ * W T ω - θ ^ 2 * (T : ℝ) / 2))).map
        (fun ω => F (fun s => W s ω + θ * ((min s T : ℝ≥0) : ℝ))) =
      P.map (fun ω => F (fun s => W s ω)) := by
  let B : ℝ≥0 → Ω → ℝ := hW.toIsPreBrownianReal.mk W
  have hBmeas : ∀ s, Measurable (B s) := fun s => hW.toIsPreBrownianReal.measurable_mk s
  have hmod : ∀ᵐ ω ∂P, ∀ s, B s ω = W s ω := hW.mk_ae_forall_eq
  have hBbm : IsBrownianReal B P := hW.toIsPreBrownianReal.isBrownianReal_mk
  have hdens : (P.withDensity fun ω =>
        ENNReal.ofReal (Real.exp (-θ * W T ω - θ ^ 2 * (T : ℝ) / 2))) =
      P.withDensity fun ω => ENNReal.ofReal (Real.exp (-θ * B T ω - θ ^ 2 * (T : ℝ) / 2)) :=
    withDensity_congr_ae (hmod.mono fun ω h => by simp only [h])
  rw [hdens]
  obtain ⟨hQ, hY⟩ := isBrownianReal_drift_girsanov P B hBbm hBmeas θ T
  rw [← isBrownianReal_path_functional_two _ P _ W hY hW F hF]
  exact Measure.map_congr ((withDensity_absolutelyContinuous _ _).ae_le
    (hmod.mono fun ω h => by simp only [h]))

/-! ### The joint law of the exponential functional under a drift -/

/-- Pushing a density forward along the map that defines it. -/
theorem map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (H : α → β) (hH : AEMeasurable H μ) (d : β → ℝ≥0∞)
    (hd : Measurable d) :
    (μ.withDensity fun a => d (H a)).map H = (μ.map H).withDensity d := by
  have hHQ : AEMeasurable H (μ.withDensity fun a => d (H a)) :=
    hH.mono_ac (withDensity_absolutelyContinuous _ _)
  ext S hS
  rw [Measure.map_apply_of_aemeasurable hHQ hS, withDensity_apply' _ _, withDensity_apply _ hS,
    Measure.restrict_map_of_aemeasurable hH hS, lintegral_map' hd.aemeasurable hH.restrict]

/-- Paper p. 1066, (2.2) at the level of laws: the joint law with drift `σθ`, tilted by
`exp(−θ y − θ² t / 2)` and translated by `y ↦ y + θ t`, is the driftless joint law. -/
theorem jointLaw_girsanov (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ θ : ℝ) (t : ℝ≥0) :
    ((jointLaw P W σ (σ * θ) t).withDensity
        (fun p => ENNReal.ofReal (Real.exp (-θ * p.2 - θ ^ 2 * (t : ℝ) / 2)))).map
        (fun p : ℝ × ℝ => (p.1, p.2 + θ * (t : ℝ))) =
      jointLaw P W σ 0 t := by
  let F : ℝ → (ℝ≥0 → ℝ) → ℝ × ℝ := fun ν x =>
    (∫ s in (0 : ℝ)..(t : ℝ), Real.exp (σ * x s.toNNReal + ν * s), x t)
  have hF : ∀ ν, Measurable fun x : C(ℝ≥0, ℝ) => F ν (fun s => x s) := fun ν =>
    (measurable_path_intervalIntegral (fun s w => Real.exp (σ * w + ν * s))
      (show Continuous (fun p : ℝ × ℝ => Real.exp (σ * p.2 + ν * p.1)) by fun_prop)
      0 t).prodMk (ContinuousMap.measurable_eval t)
  let H : Ω → ℝ × ℝ := fun ω => (expInt W σ (σ * θ) t ω, W t ω)
  have hH : AEMeasurable H P :=
    (isBrownianReal_path_functional P W W hW hW (F (σ * θ)) (hF (σ * θ))).1
  let d : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (Real.exp (-θ * p.2 - θ ^ 2 * (t : ℝ) / 2))
  have hd : Measurable d := by fun_prop
  let sh : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, p.2 + θ * (t : ℝ))
  have hsh : Measurable sh := by fun_prop
  have hcm := cameronMartin_path_functional P W hW θ t (F 0) (hF 0)
  have hpath : ∀ ω, F 0 (fun s => W s ω + θ * ((min s t : ℝ≥0) : ℝ)) = sh (H ω) := by
    intro ω
    refine Prod.ext ?_ ?_
    · show ∫ s in (0 : ℝ)..(t : ℝ),
          Real.exp (σ * (W s.toNNReal ω + θ * ((min s.toNNReal t : ℝ≥0) : ℝ)) + 0 * s) =
        expInt W σ (σ * θ) t ω
      simp only [expInt]
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le (NNReal.coe_nonneg t)] at hs
      have hmin : ((min s.toNNReal t : ℝ≥0) : ℝ) = s := by
        rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hs.2), Real.coe_toNNReal _ hs.1]
      simp only [hmin]
      congr 1
      ring
    · show W t ω + θ * ((min t t : ℝ≥0) : ℝ) = W t ω + θ * (t : ℝ)
      rw [min_self]
  have hHQ : AEMeasurable H (P.withDensity fun ω => d (H ω)) :=
    hH.mono_ac (withDensity_absolutelyContinuous _ _)
  calc ((jointLaw P W σ (σ * θ) t).withDensity d).map sh
      = ((P.withDensity fun ω => d (H ω)).map H).map sh := by
        rw [map_withDensity_comp P H hH d hd]; rfl
    _ = (P.withDensity fun ω => d (H ω)).map (sh ∘ H) :=
        AEMeasurable.map_map_of_aemeasurable hsh.aemeasurable hHQ
    _ = (P.withDensity fun ω =>
          ENNReal.ofReal (Real.exp (-θ * W t ω - θ ^ 2 * (t : ℝ) / 2))).map
          (fun ω => F 0 (fun s => W s ω + θ * ((min s t : ℝ≥0) : ℝ))) := by
        congr 1
        funext ω
        exact (hpath ω).symm
    _ = P.map (fun ω => F 0 (fun s => W s ω)) := hcm
    _ = jointLaw P W σ 0 t := rfl

/-! ### The density identity (2.2) -/

/-- Translation in the second coordinate, as a measurable equivalence of the plane. -/
def shiftSnd (c : ℝ) : ℝ × ℝ ≃ᵐ ℝ × ℝ where
  toFun p := (p.1, p.2 + c)
  invFun p := (p.1, p.2 - c)
  left_inv p := by simp
  right_inv p := by simp
  measurable_toFun := measurable_fst.prodMk (measurable_snd.add_const c)
  measurable_invFun := measurable_fst.prodMk (measurable_snd.sub_const c)

theorem map_shiftSnd_volume (c : ℝ) :
    (volume : Measure (ℝ × ℝ)).map (shiftSnd c) = (1 : ℝ≥0∞) • volume := by
  have hcoe : (shiftSnd c : ℝ × ℝ → ℝ × ℝ) = Prod.map id (fun y => y + c) := rfl
  rw [hcoe, Measure.volume_eq_prod, ← Measure.map_prod_map _ _ measurable_id (by fun_prop),
    Measure.map_id, (measurePreserving_add_right volume c).map_eq, one_smul]

/-- Paper p. 1066, (2.2), for the positive parts of continuous densities:
`φ_{σθ}(x, y) = e^{θ y + θ² t / 2} φ_0(x, y + θ t)`. -/
theorem jointDensity_girsanov_posPart (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (σ θ : ℝ) (t : ℝ≥0)
    (φμ φ0 : ℝ → ℝ → ℝ) (h1 : IsJointDensity P W σ (σ * θ) t φμ)
    (h0 : IsJointDensity P W σ 0 t φ0)
    (hcμ : Continuous (Function.uncurry φμ)) (hc0 : Continuous (Function.uncurry φ0))
    (x y : ℝ) :
    max (φμ x y) 0 =
      Real.exp (θ * y + θ ^ 2 * (t : ℝ) / 2) * max (φ0 x (y + θ * (t : ℝ))) 0 := by
  have hmμ : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (φμ p.1 p.2) :=
    hcμ.measurable.ennreal_ofReal
  have hm0 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (φ0 p.1 p.2) :=
    hc0.measurable.ennreal_ofReal
  have hmd : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (Real.exp (-θ * p.2 - θ ^ 2 * (t : ℝ) / 2)) := by fun_prop
  have hlaw := jointLaw_girsanov P W hW σ θ t
  unfold IsJointDensity at h1 h0
  rw [h1, h0, ← withDensity_mul _ hmμ hmd] at hlaw
  have hmap := map_withDensity_eq_of_map_eq_smul volume (shiftSnd (θ * (t : ℝ))) 1
    (map_shiftSnd_volume _) _ (hmμ.mul hmd)
  have hlaw' : (volume : Measure (ℝ × ℝ)).withDensity (fun p =>
        1 * ((fun p : ℝ × ℝ => ENNReal.ofReal (φμ p.1 p.2)) *
          fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-θ * p.2 - θ ^ 2 * (t : ℝ) / 2)))
          ((shiftSnd (θ * (t : ℝ))).symm p)) =
      volume.withDensity fun p => ENNReal.ofReal (φ0 p.1 p.2) := hmap.symm.trans hlaw
  have hae := (withDensity_eq_iff_of_sigmaFinite
    ((((hmμ.mul hmd).comp (shiftSnd (θ * (t : ℝ))).symm.measurable).const_mul 1).aemeasurable)
    hm0.aemeasurable).1 hlaw'
  have hreal : (fun p : ℝ × ℝ => max (φμ p.1 (p.2 - θ * (t : ℝ))) 0 *
        Real.exp (-θ * (p.2 - θ * (t : ℝ)) - θ ^ 2 * (t : ℝ) / 2)) =ᵐ[volume]
      fun p => max (φ0 p.1 p.2) 0 := by
    filter_upwards [hae] with p hp
    have h := congrArg ENNReal.toReal hp
    have hsymm : (shiftSnd (θ * (t : ℝ))).symm p = (p.1, p.2 - θ * (t : ℝ)) := rfl
    simp only [one_mul, Function.comp_apply, Pi.mul_apply, hsymm, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal'] at h
    rw [max_eq_left (Real.exp_pos _).le] at h
    exact h
  have hcont1 : Continuous fun p : ℝ × ℝ => max (φμ p.1 (p.2 - θ * (t : ℝ))) 0 *
      Real.exp (-θ * (p.2 - θ * (t : ℝ)) - θ ^ 2 * (t : ℝ) / 2) := by
    have hcomp : Continuous fun p : ℝ × ℝ => φμ p.1 (p.2 - θ * (t : ℝ)) :=
      hcμ.comp (by fun_prop : Continuous fun p : ℝ × ℝ => (p.1, p.2 - θ * (t : ℝ)))
    exact (hcomp.max continuous_const).mul (by fun_prop)
  have hcont2 : Continuous fun p : ℝ × ℝ => max (φ0 p.1 p.2) 0 := hc0.max continuous_const
  have hpt := congrFun ((Continuous.ae_eq_iff_eq volume hcont1 hcont2).1 hreal)
    (x, y + θ * (t : ℝ))
  simp only [add_sub_cancel_right] at hpt
  rw [← hpt, mul_comm, mul_assoc, ← Real.exp_add]
  have hzero : -θ * y - θ ^ 2 * (t : ℝ) / 2 + (θ * y + θ ^ 2 * (t : ℝ) / 2) = 0 := by ring
  rw [hzero, Real.exp_zero, mul_one]

end Lyasoff2016
