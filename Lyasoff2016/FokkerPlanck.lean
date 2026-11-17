/-
# §3 Fokker–Planck characterization (pp. 1067–1071)
-/
module

public import Lyasoff2016.Auxiliary
public import Lyasoff2016.MomentUniqueness
public import Lyasoff2016.InverseGamma
public import Lyasoff2016.JointFokkerPlanckHelpers
public import Lyasoff2016.JointFokkerPlanckIto
public import Lyasoff2016.ExpectedIto
public import BrownianMotion.Gaussian.BrownianMotion
public import MathFin.Probability.Brownian.Ito.ItoFormulaTD
public import MathFin.Probability.Brownian.Ito.ItoFormulaProcess
public import MathFin.Probability.Brownian.BrownianExpMoment
public import MathFin.Probability.Brownian.BrownianMartingale
public import MathFin.Probability.Brownian.Ito.ItoIsometryAdapted
public import MathFin.Probability.Brownian.Ito.ItoFormulaGBM
public import MathFin.Probability.Brownian.Ito.ItoIntegralProcessGeneral
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.SpecificLimits.Basic


@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open MeasureTheory.Measure
open scoped ENNReal NNReal Real
open MathFin ItoIntegralL2

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

/- Paper: p. 1067, (3.1).
   Plain recap: the stationary process Z_t built from two independent BMs.
   PAPER NOTE: paper writes e^{σ(W_s+νs)} and e^{σ(νt−B_t)}; we use the equivalent
   e^{σ W_s + ν s} convention throughout, so the prefactor is e^{νt − σ B_t} and the
   B-integral is e^{−νs + σ B_s} (same drift ν in all three places). -/
def Zproc (W B : ℝ≥0 → Ω → ℝ) (σ ν : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (ν * (t : ℝ) - σ * B t ω) *
    ((∫ s in Ioi (0 : ℝ), Real.exp (σ * W s.toNNReal ω + ν * s)) +
     ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-ν * s + σ * B s.toNNReal ω))

/- Paper: p. 1067, (3.2).
   Plain recap: generator L = ½σ²x² ∂ₓₓ + (1 + (ν + σ²/2)x) ∂ₓ.
   PAPER NOTE: β = −2ν/σ² in our e^{σW+νs} convention. -/
def generator (σ ν : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  σ ^ 2 * x ^ 2 / 2 * deriv (deriv f) x + (1 + (ν + σ ^ 2 / 2) * x) * deriv f x

/- Paper: p. 1067, footnote 2 (integrable form).
   Plain recap: for σ > 0 and ν < 0, almost every path s ↦ e^{σ W_s + ν s} is Lebesgue
   integrable on (0, ∞), because W_s / s → 0 a.s. -/
theorem ae_integrableOn_exp_bm (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ ν : ℝ) (hσ : 0 < σ) (hν : ν < 0) :
    ∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => Real.exp (σ * W s.toNNReal ω + ν * s)) (Ioi 0) := by
  filter_upwards [hW.tendsto_div_id_atTop, hW.cont] with ω hlim hcont
  have hc : 0 < -ν / (2 * σ) := div_pos (neg_pos.mpr hν) (mul_pos two_pos hσ)
  have hev : ∀ᶠ t : ℝ≥0 in atTop, W t ω / (t : ℝ) < -ν / (2 * σ) :=
    (show Tendsto (fun t : ℝ≥0 => W t ω / (t : ℝ)) atTop (nhds 0) from hlim).eventually_lt_const hc
  obtain ⟨C, hC⟩ := eventually_atTop.1 hev
  let f : ℝ → ℝ := fun s => Real.exp (σ * W s.toNNReal ω + ν * s)
  have hfcont : Continuous f := by
    apply Real.continuous_exp.comp
    fun_prop
  have htail : ∀ s : ℝ, C < s → f s ≤ Real.exp ((ν / 2) * s) := by
    intro s hs
    have hs0 : 0 < s := lt_of_le_of_lt C.coe_nonneg hs
    have hb := hC s.toNNReal (by
      apply NNReal.coe_le_coe.mp
      simpa [Real.coe_toNNReal s hs0.le] using hs.le)
    have hcoe : (s.toNNReal : ℝ) = s := Real.coe_toNNReal s hs0.le
    rw [hcoe] at hb
    apply Real.exp_le_exp.mpr
    have : σ * W s.toNNReal ω < -(ν / 2) * s := by
      have := mul_lt_mul_of_pos_left hb hσ
      field_simp at this ⊢
      nlinarith
    linarith
  have hlocal : IntegrableOn f (Ioc 0 C) := hfcont.integrableOn_Ioc
  have hexp : IntegrableOn (fun s : ℝ => Real.exp ((ν / 2) * s)) (Ioi C) :=
    integrableOn_exp_mul_Ioi (by linarith) C
  have htail_int : IntegrableOn f (Ioi C) := by
    refine hexp.mono' hfcont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact htail s hs
  change IntegrableOn f (Ioi 0)
  rw [← Ioc_union_Ioi_eq_Ioi C.coe_nonneg]
  exact hlocal.union htail_int

/- Paper: p. 1067, footnote 2.
   Plain recap: for σ > 0 and ν < 0 the improper integral ∫₀^∞ e^{σW+νs} is a.s. finite. -/
theorem infinite_integral_finite (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ ν : ℝ) (hσ : 0 < σ) (hν : ν < 0) :
    ∀ᵐ ω ∂P, ∃ L : ℝ, Tendsto (fun T : ℝ≥0 => expInt W σ ν T ω) atTop (nhds L) := by
  filter_upwards [ae_integrableOn_exp_bm P W hW σ ν hσ hν] with ω hfi
  refine ⟨∫ s in Ioi (0 : ℝ), Real.exp (σ * W s.toNNReal ω + ν * s), ?_⟩
  simpa [expInt] using
    (intervalIntegral_tendsto_integral_Ioi
      (f := fun s : ℝ => Real.exp (σ * W s.toNNReal ω + ν * s)) 0 hfi
      (by
        apply tendsto_atTop.2
        intro b
        filter_upwards [eventually_ge_atTop b.toNNReal] with a ha
        exact (Real.le_coe_toNNReal b).trans (NNReal.coe_le_coe.mpr ha)))

/-! ### Path-space helpers

Any Brownian motion has a modification with values in `C(ℝ≥0, ℝ)` whose law is the Wiener
measure; laws of measurable path functionals therefore coincide for any two Brownian motions,
and independence of two processes transfers to their continuous-path versions. -/

/-- The Borel σ-algebra of `C(ℝ≥0, ℝ)` is generated by the coordinate map into `ℝ≥0 → ℝ`. -/
theorem comap_coeFn_path :
    MeasurableSpace.comap (fun (x : C(ℝ≥0, ℝ)) (s : ℝ≥0) => x s) inferInstance =
      (inferInstance : MeasurableSpace C(ℝ≥0, ℝ)) := by
  have he : Measurable (fun (x : C(ℝ≥0, ℝ)) (s : ℝ≥0) => x s) :=
    measurable_pi_iff.2 fun s => ContinuousMap.measurable_eval s
  apply le_antisymm
  · exact he.comap_le
  · rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval]
    refine iSup_le fun s => ?_
    rw [← measurable_iff_comap_le]
    exact (measurable_pi_apply s).comp (comap_measurable _)

/-- The continuous-path version of a Brownian motion, as a `C(ℝ≥0, ℝ)`-valued random variable. -/
def bmPath {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} (hW : IsBrownianReal W P) : Ω → C(ℝ≥0, ℝ) :=
  fun ω => ⟨fun s => hW.toIsPreBrownianReal.mk W s ω, hW.toIsPreBrownianReal.continuous_mk ω⟩

theorem measurable_bmPath {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} (hW : IsBrownianReal W P) :
    Measurable (bmPath hW) :=
  ContinuousMap.measurable_iff_eval.2 fun s => by
    simpa [bmPath] using hW.toIsPreBrownianReal.measurable_mk s

theorem bmPath_ae_eq {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} (hW : IsBrownianReal W P) :
    ∀ᵐ ω ∂P, ∀ s, bmPath hW ω s = W s ω :=
  hW.mk_ae_forall_eq

/-- Uniqueness of the Wiener measure: all Brownian motions have the same path law. -/
theorem map_bmPath_eq {P : Measure Ω} [IsProbabilityMeasure P] {W B : ℝ≥0 → Ω → ℝ}
    (hW : IsBrownianReal W P) (hB : IsBrownianReal B P) :
    P.map (bmPath hW) = P.map (bmPath hB) := by
  let e : C(ℝ≥0, ℝ) → (ℝ≥0 → ℝ) := fun x s => x s
  have he : Measurable e := measurable_pi_iff.2 fun s => ContinuousMap.measurable_eval s
  have hpW := measurable_bmPath hW
  have hpB := measurable_bmPath hB
  have hrawW : P.map (e ∘ bmPath hW) = gaussianLimit :=
    (hW.toIsPreBrownianReal.isBrownianReal_mk.toIsPreBrownianReal.hasLaw_gaussianLimit
      ((he.comp hpW).aemeasurable)).map_eq
  have hrawB : P.map (e ∘ bmPath hB) = gaussianLimit :=
    (hB.toIsPreBrownianReal.isBrownianReal_mk.toIsPreBrownianReal.hasLaw_gaussianLimit
      ((he.comp hpB).aemeasurable)).map_eq
  have hmap : (P.map (bmPath hW)).map e = (P.map (bmPath hB)).map e := by
    calc
      (P.map (bmPath hW)).map e = P.map (e ∘ bmPath hW) := Measure.map_map he hpW
      _ = gaussianLimit := hrawW
      _ = P.map (e ∘ bmPath hB) := hrawB.symm
      _ = (P.map (bmPath hB)).map e := (Measure.map_map he hpB).symm
  ext A hA
  have hA' : MeasurableSet[MeasurableSpace.comap e inferInstance] A :=
    comap_coeFn_path.symm ▸ hA
  rcases hA' with ⟨S, hS, rfl⟩
  rw [← Measure.map_apply he hS, hmap, Measure.map_apply he hS]

/-- Any two Brownian motions induce the same law for a measurable functional of the
continuous path. `F` and `G` are random variables that coincide (a.s.) with `Φ` evaluated
at any continuous path agreeing with `W`, resp. `B`. -/
theorem isBrownianReal_map_pathFunctional_eq (P : Measure Ω) [IsProbabilityMeasure P]
    (W B : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) (hB : IsBrownianReal B P)
    {E : Type*} [MeasurableSpace E] (Φ : C(ℝ≥0, ℝ) → E) (hΦ : Measurable Φ)
    (F G : Ω → E)
    (hF : ∀ᵐ ω ∂P, ∀ x : C(ℝ≥0, ℝ), (∀ s, x s = W s ω) → F ω = Φ x)
    (hG : ∀ᵐ ω ∂P, ∀ x : C(ℝ≥0, ℝ), (∀ s, x s = B s ω) → G ω = Φ x) :
    P.map F = P.map G := by
  calc
    P.map F = P.map (Φ ∘ bmPath hW) := Measure.map_congr <| by
      filter_upwards [bmPath_ae_eq hW, hF] with ω hω hFω
      exact hFω (bmPath hW ω) hω
    _ = (P.map (bmPath hW)).map Φ := (Measure.map_map hΦ (measurable_bmPath hW)).symm
    _ = (P.map (bmPath hB)).map Φ := by rw [map_bmPath_eq hW hB]
    _ = P.map (Φ ∘ bmPath hB) := Measure.map_map hΦ (measurable_bmPath hB)
    _ = P.map G := Measure.map_congr <| by
      filter_upwards [bmPath_ae_eq hB, hG] with ω hω hGω
      exact (hGω (bmPath hB ω) hω).symm

/-- Independence of two processes (in the product σ-algebra of `ℝ≥0 → ℝ`) transfers to any
`C(ℝ≥0, ℝ)`-valued versions of them. -/
theorem indepFun_path_of_ae_eq (P : Measure Ω) (p q : Ω → C(ℝ≥0, ℝ)) (X Y : Ω → ℝ≥0 → ℝ)
    (hXY : IndepFun X Y P) (hp : ∀ᵐ ω ∂P, ∀ s, p ω s = X ω s)
    (hq : ∀ᵐ ω ∂P, ∀ s, q ω s = Y ω s) : IndepFun p q P := by
  have h : IndepFun (fun ω (s : ℝ≥0) => p ω s) (fun ω (s : ℝ≥0) => q ω s) P :=
    hXY.congr (hp.mono fun ω h => (funext h).symm) (hq.mono fun ω h => (funext h).symm)
  rw [IndepFun_iff_Indep] at h ⊢
  have hc : ∀ r : Ω → C(ℝ≥0, ℝ),
      MeasurableSpace.comap (fun ω (s : ℝ≥0) => r ω s) inferInstance =
        MeasurableSpace.comap r inferInstance := by
    intro r
    conv_rhs => rw [← comap_coeFn_path, MeasurableSpace.comap_comp]
    rfl
  rwa [hc, hc] at h

/-- The path stopped at time `t`. -/
def stopPath (t : ℝ≥0) (x : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) :=
  ⟨fun s => x (min s t), x.continuous.comp (continuous_id.min continuous_const)⟩

theorem measurable_stopPath (t : ℝ≥0) : Measurable (stopPath t) :=
  ContinuousMap.measurable_iff_eval.2 fun s => ContinuousMap.measurable_eval (min s t)

/-- Set integrals `∫_S V s (x s) ds` are measurable functionals on path space. -/
theorem measurable_pathSetIntegral (V : ℝ → ℝ → ℝ) (hV : Continuous (Function.uncurry V))
    (S : Set ℝ) :
    Measurable (fun x : C(ℝ≥0, ℝ) => ∫ s in S, V s (x s.toNNReal)) := by
  have hev : Continuous (fun p : C(ℝ≥0, ℝ) × ℝ => p.1 p.2.toNNReal) :=
    continuous_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))
  have hc : Continuous (fun p : C(ℝ≥0, ℝ) × ℝ => V p.2 (p.1 p.2.toNNReal)) :=
    hV.comp (continuous_snd.prodMk hev)
  have hsm : StronglyMeasurable (Function.uncurry
      (fun x : C(ℝ≥0, ℝ) => fun s : ℝ => V s (x s.toNNReal))) :=
    hc.stronglyMeasurable
  exact (StronglyMeasurable.integral_prod_right (ν := volume.restrict S) hsm).measurable

/-- The running maximum over `[0, t]` is a measurable functional on path space. -/
theorem measurable_pathSup (t : ℝ≥0) :
    Measurable (fun x : C(ℝ≥0, ℝ) => ⨆ s : Icc (0 : ℝ≥0) t, x s) := by
  have : Nonempty (Icc (0 : ℝ≥0) t) := ⟨⟨0, by simp⟩⟩
  have hsup : Continuous (fun y : C(Icc (0 : ℝ≥0) t, ℝ) => ⨆ s, y s) := by
    refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_le_add_mul 1 fun y z => ?_)
    have hz : BddAbove (range fun s => z s) := (isCompact_range z.continuous).bddAbove
    refine ciSup_le fun s => ?_
    have h1 : y s - z s ≤ dist y z := by
      have := ContinuousMap.dist_apply_le_dist (f := y) (g := z) s
      rw [Real.dist_eq] at this
      exact (le_abs_self _).trans this
    have h2 : z s ≤ ⨆ s, z s := le_ciSup hz s
    simp only [NNReal.coe_one, one_mul]
    linarith
  exact (hsup.comp (ContinuousMap.continuous_restrict _)).measurable

/-- The time integral `∫₀ᵗ V s (x s) ds` is a measurable functional on path space. -/
theorem measurable_pathIntegral (V : ℝ → ℝ → ℝ) (hV : Continuous (Function.uncurry V))
    (t : ℝ≥0) :
    Measurable (fun x : C(ℝ≥0, ℝ) => ∫ s in (0 : ℝ)..(t : ℝ), V s (x s.toNNReal)) := by
  simp only [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  have hev : Continuous (fun p : C(ℝ≥0, ℝ) × ℝ => p.1 p.2.toNNReal) :=
    continuous_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))
  have hc : Continuous (fun p : C(ℝ≥0, ℝ) × ℝ => V p.2 (p.1 p.2.toNNReal)) :=
    hV.comp (continuous_snd.prodMk hev)
  have hsm : StronglyMeasurable (Function.uncurry
      (fun x : C(ℝ≥0, ℝ) => fun s : ℝ => V s (x s.toNNReal))) :=
    hc.stronglyMeasurable
  have hm := (StronglyMeasurable.measurable <|
    StronglyMeasurable.integral_prod_right
      (ν := volume.restrict (uIoc (0 : ℝ) (t : ℝ))) hsm).const_smul
        ((if (0 : ℝ) ≤ (t : ℝ) then 1 else -1) : ℝ)
  exact hm

/-! ### Stationarity of `Z` (consistent-drift form) -/

/-- Deterministic Markov-type decomposition of the perpetuity at time `t`:
`∫₀^∞ e^{σ w_s + ν s} ds = ∫₀ᵗ e^{σ w_s + ν s} ds + e^{σ w_t + ν t} ∫₀^∞ e^{σ (w_{t+s} − w_t) + ν s} ds`. -/
theorem integral_Ioi_exp_split (w : ℝ≥0 → ℝ) (σ ν : ℝ) (t : ℝ≥0)
    (hint : IntegrableOn (fun s : ℝ => Real.exp (σ * w s.toNNReal + ν * s)) (Ioi 0)) :
    ∫ s in Ioi (0 : ℝ), Real.exp (σ * w s.toNNReal + ν * s) =
      (∫ s in (0 : ℝ)..(t : ℝ), Real.exp (σ * w s.toNNReal + ν * s)) +
        Real.exp (σ * w t + ν * t) *
          ∫ s in Ioi (0 : ℝ), Real.exp (σ * (w (t + s.toNNReal) - w t) + ν * s) := by
  have h1 := intervalIntegral.integral_interval_add_Ioi (a := 0) (b := (t : ℝ)) hint
    (hint.mono_set (Ioi_subset_Ioi t.coe_nonneg))
  rw [← h1]
  congr 1
  rw [← integral_const_mul]
  have hmp := (measurePreserving_add_right volume (t : ℝ)).setIntegral_preimage_emb
    (measurableEmbedding_addRight (t : ℝ))
    (fun s : ℝ => Real.exp (σ * w s.toNNReal + ν * s)) (Ioi (t : ℝ))
  rw [← hmp]
  have hpre : (fun x : ℝ => x + (t : ℝ)) ⁻¹' Ioi (t : ℝ) = Ioi 0 := by
    ext x
    simp
  rw [hpre]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs0 : (0 : ℝ) ≤ s := (mem_Ioi.1 hs).le
  have hts : (s + (t : ℝ)).toNNReal = t + s.toNNReal := by
    rw [add_comm, Real.toNNReal_add t.coe_nonneg hs0, Real.toNNReal_coe]
  simp only [hts, ← Real.exp_add]
  congr 1
  ring

/-- On `[0, t]` the stopped path agrees with the path, so the time integral up to `t` of the
stopped path only sees the values `y` of the path. -/
theorem integral_stopPath_eq (σ ν : ℝ) (t : ℝ≥0) (x : C(ℝ≥0, ℝ)) (y : ℝ≥0 → ℝ)
    (hxy : ∀ s, x s = y s) :
    ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (σ * stopPath t x s.toNNReal + ν * s) =
      ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (σ * y s.toNNReal + ν * s) := by
  refine intervalIntegral.integral_congr fun s hs => ?_
  have hsI : s ∈ Icc (0 : ℝ) (t : ℝ) := by
    simpa [uIcc_of_le (NNReal.coe_nonneg t)] using hs
  have hle : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hsI.2
  simp [stopPath, min_eq_left hle, hxy]

/- Paper: p. 1067, stationarity of Z — consistent-drift form.
   Plain recap: with the *same* drift ν in the perpetuity and in the perturbation, i.e.
   Z_t = e^{νt − σB_t} (∫₀^∞ e^{σW_s+νs} ds + ∫₀ᵗ e^{−νs+σB_s} ds),
   Z_t has the law of ∫₀^∞ e^{σW_s+νs} ds for every t.
   Proof: `β_u = B_{t−u} − B_t` (negated time reversal of B) is a BM independent of W and
   Z_t = ∫₀ᵗ e^{σβ_u+νu} du + e^{σβ_t+νt} A_∞(W); by the weak Markov property the perpetuity
   of a single BM has the same decomposition with the same joint law of the ingredients. -/
theorem Z_stationary_consistent (P : Measure Ω) [IsProbabilityMeasure P] (W B : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (hB : IsBM P B)
    (hWB : IndepFun (fun ω => fun t : ℝ≥0 => W t ω) (fun ω => fun t : ℝ≥0 => B t ω) P)
    (σ ν : ℝ) (hσ : 0 < σ) (hν : ν < 0) (t : ℝ≥0) :
    P.map (fun ω => Real.exp (ν * (t : ℝ) - σ * B t ω) *
        ((∫ s in Ioi (0 : ℝ), Real.exp (σ * W s.toNNReal ω + ν * s)) +
          ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-ν * s + σ * B s.toNNReal ω))) =
      P.map (fun ω => ∫ s in Ioi (0 : ℝ), Real.exp (σ * W s.toNNReal ω + ν * s)) := by
  have hβ : IsBM P (-(timeReversed B t)) := (isBrownianReal_timeReversed P B hB t).neg
  have hS : IsBM P (fun s ω => W (t + s) ω - W t ω) := hW.shift t
  -- the path functional `Ψ(x, w) = ∫₀ᵗ e^{σ x_s + ν s} ds + e^{σ x_t + ν t} A_∞(w)`
  let V : ℝ → ℝ → ℝ := fun s b => Real.exp (σ * b + ν * s)
  have hV : Continuous (Function.uncurry V) := by
    simp only [V]
    fun_prop
  let Ψ : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) → ℝ := fun z =>
    (∫ s in (0 : ℝ)..(t : ℝ), Real.exp (σ * z.1 s.toNNReal + ν * s)) +
      Real.exp (σ * z.1 t + ν * t) *
        ∫ s in Ioi (0 : ℝ), Real.exp (σ * z.2 s.toNNReal + ν * s)
  have hΨ : Measurable Ψ := by
    have hI : Measurable (fun x : C(ℝ≥0, ℝ) =>
        ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (σ * x s.toNNReal + ν * s)) :=
      measurable_pathIntegral V hV t
    have hA : Measurable (fun x : C(ℝ≥0, ℝ) =>
        ∫ s in Ioi (0 : ℝ), Real.exp (σ * x s.toNNReal + ν * s)) :=
      measurable_pathSetIntegral V hV (Ioi 0)
    have hE : Measurable (fun x : C(ℝ≥0, ℝ) => Real.exp (σ * x t + ν * t)) :=
      Real.measurable_exp.comp (((ContinuousMap.measurable_eval t).const_mul σ).add_const _)
    exact (hI.comp measurable_fst).add ((hE.comp measurable_fst).mul (hA.comp measurable_snd))
  -- independence of the ingredients
  have hind1 : IndepFun (fun ω => stopPath t (bmPath hβ ω)) (bmPath hW) P := by
    refine indepFun_path_of_ae_eq P _ _ (fun ω s => -(B t ω - B (t - min s t) ω))
      (fun ω s => W s ω) ?_ ?_ (bmPath_ae_eq hW)
    · have hψ : Measurable (fun (y : ℝ≥0 → ℝ) (s : ℝ≥0) => -(y t - y (t - min s t))) :=
        measurable_pi_iff.2 fun s =>
          ((measurable_pi_apply t).sub (measurable_pi_apply (t - min s t))).neg
      exact (hWB.comp measurable_id hψ).symm
    · filter_upwards [bmPath_ae_eq hβ] with ω h s
      simp [stopPath, h, timeReversed_eq_on_Icc B t (min_le_right s t)]
  have hind2 : IndepFun (fun ω => stopPath t (bmPath hW ω)) (bmPath hS) P := by
    refine indepFun_path_of_ae_eq P _ _ (fun ω s => W (min s t) ω)
      (fun ω s => W (t + s) ω - W t ω) ?_ ?_ (bmPath_ae_eq hS)
    · have hψ : Measurable (fun (y : Iic t → ℝ) (s : ℝ≥0) => y ⟨min s t, min_le_right s t⟩) :=
        measurable_pi_iff.2 fun s => measurable_pi_apply _
      exact ((hW.toIsPreBrownianReal.indepFun_shift t).comp measurable_id hψ).symm
    · filter_upwards [bmPath_ae_eq hW] with ω h s
      simp [stopPath, h]
  have hm1 : Measurable (fun ω => stopPath t (bmPath hβ ω)) :=
    (measurable_stopPath t).comp (measurable_bmPath hβ)
  have hm2 : Measurable (fun ω => stopPath t (bmPath hW ω)) :=
    (measurable_stopPath t).comp (measurable_bmPath hW)
  have hL1 := (indepFun_iff_map_prod_eq_prod_map_map hm1.aemeasurable
    (measurable_bmPath hW).aemeasurable).1 hind1
  have hL2 := (indepFun_iff_map_prod_eq_prod_map_map hm2.aemeasurable
    (measurable_bmPath hS).aemeasurable).1 hind2
  have hstop : P.map (fun ω => stopPath t (bmPath hβ ω)) =
      P.map (fun ω => stopPath t (bmPath hW ω)) := by
    have e1 : P.map (fun ω => stopPath t (bmPath hβ ω)) =
        (P.map (bmPath hβ)).map (stopPath t) :=
      (Measure.map_map (measurable_stopPath t) (measurable_bmPath hβ)).symm
    have e2 : P.map (fun ω => stopPath t (bmPath hW ω)) =
        (P.map (bmPath hW)).map (stopPath t) :=
      (Measure.map_map (measurable_stopPath t) (measurable_bmPath hW)).symm
    rw [e1, e2, map_bmPath_eq hβ hW]
  have hlaw : P.map (fun ω => (stopPath t (bmPath hβ ω), bmPath hW ω)) =
      P.map (fun ω => (stopPath t (bmPath hW ω), bmPath hS ω)) := by
    rw [hL1, hL2, hstop, map_bmPath_eq hS hW]
  -- pathwise identities
  have hZ : ∀ᵐ ω ∂P, Real.exp (ν * (t : ℝ) - σ * B t ω) *
        ((∫ s in Ioi (0 : ℝ), Real.exp (σ * W s.toNNReal ω + ν * s)) +
          ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-ν * s + σ * B s.toNNReal ω)) =
      Ψ (stopPath t (bmPath hβ ω), bmPath hW ω) := by
    filter_upwards [bmPath_ae_eq hβ, bmPath_ae_eq hW, hB.eval_zero_ae_eq_zero] with ω hβω hWω h0
    have hI := integral_stopPath_eq σ ν t (bmPath hβ ω) (fun s => -(timeReversed B t s ω))
      (fun s => by rw [hβω]; rfl)
    have hrev := timeReversed_integral_eq B t ω (fun u b => Real.exp (σ * -b + ν * u))
    have hfin : ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (σ * -(timeReversed B t s.toNNReal ω) + ν * s)
        = Real.exp (ν * (t : ℝ) - σ * B t ω) *
          ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-ν * s + σ * B s.toNNReal ω) := by
      rw [← hrev, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [← Real.exp_add]
      congr 1
      ring
    have hend : stopPath t (bmPath hβ ω) t = -B t ω := by
      simp [stopPath, hβω, timeReversed_eq_on_Icc B t le_rfl, h0]
    simp only [Ψ, hI, hfin, hend, hWω]
    rw [mul_add, add_comm]
    congr 2
    congr 1
    ring
  have hA : ∀ᵐ ω ∂P, ∫ s in Ioi (0 : ℝ), Real.exp (σ * W s.toNNReal ω + ν * s) =
      Ψ (stopPath t (bmPath hW ω), bmPath hS ω) := by
    filter_upwards [bmPath_ae_eq hW, bmPath_ae_eq hS,
      ae_integrableOn_exp_bm P W hW σ ν hσ hν] with ω hWω hSω hint
    have hI := integral_stopPath_eq σ ν t (bmPath hW ω) (fun s => W s ω) hWω
    have hend : stopPath t (bmPath hW ω) t = W t ω := by
      simp [stopPath, hWω]
    simp only [Ψ, hI, hend, hSω]
    exact integral_Ioi_exp_split (fun s => W s ω) σ ν t hint
  calc
    P.map (fun ω => Real.exp (ν * (t : ℝ) - σ * B t ω) *
        ((∫ s in Ioi (0 : ℝ), Real.exp (σ * W s.toNNReal ω + ν * s)) +
          ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-ν * s + σ * B s.toNNReal ω)))
        = P.map (Ψ ∘ fun ω => (stopPath t (bmPath hβ ω), bmPath hW ω)) :=
          Measure.map_congr hZ
    _ = (P.map (fun ω => (stopPath t (bmPath hβ ω), bmPath hW ω))).map Ψ :=
          (Measure.map_map hΨ (hm1.prodMk (measurable_bmPath hW))).symm
    _ = (P.map (fun ω => (stopPath t (bmPath hW ω), bmPath hS ω))).map Ψ := by rw [hlaw]
    _ = P.map (Ψ ∘ fun ω => (stopPath t (bmPath hW ω), bmPath hS ω)) :=
          Measure.map_map hΨ (hm2.prodMk (measurable_bmPath hS))
    _ = P.map (fun ω => ∫ s in Ioi (0 : ℝ), Real.exp (σ * W s.toNNReal ω + ν * s)) :=
          (Measure.map_congr hA).symm

/- Paper: p. 1067, stationarity of Z — the case σ = 1 of `Z_stationary`, where the drift
   `σ ν` used in `Zproc` and the drift `ν` of the perpetuity coincide. -/
theorem Z_stationary_sigma_one (P : Measure Ω) [IsProbabilityMeasure P] (W B : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (hB : IsBM P B)
    (hWB : IndepFun (fun ω => fun t : ℝ≥0 => W t ω) (fun ω => fun t : ℝ≥0 => B t ω) P)
    (ν : ℝ) (hν : ν < 0) (t : ℝ≥0) :
    P.map (Zproc W B 1 ν t) =
      P.map (fun ω => ∫ s in Ioi (0 : ℝ), Real.exp (1 * W s.toNNReal ω + ν * s)) :=
  Z_stationary_consistent P W B hW hB hWB 1 ν one_pos hν t

/- Paper: p. 1067, stationarity of Z.
   Plain recap: Z_t has the same law as ∫₀^∞ e^{σW+νs} ds. -/
theorem Z_stationary (P : Measure Ω) [IsProbabilityMeasure P] (W B : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (hB : IsBM P B)
    (hWB : IndepFun (fun ω => fun t : ℝ≥0 => W t ω) (fun ω => fun t : ℝ≥0 => B t ω) P)
    (σ ν : ℝ) (hσ : 0 < σ) (hν : ν < 0) (t : ℝ≥0) :
    P.map (Zproc W B σ ν t) =
      P.map (fun ω => ∫ s in Ioi (0 : ℝ), Real.exp (σ * W s.toNNReal ω + ν * s)) :=
  Z_stationary_consistent P W B hW hB hWB σ ν hσ hν t

/- Paper: p. 1068, (3.3) Dufresne density.
   Plain recap: ψ(x) = (2/σ²)^β / Γ(β) · x^{-β-1} e^{-2/(σ² x)} with β = −2ν/σ² on x > 0
   (and 0 for x ≤ 0, since the infinite-horizon integral is a.s. positive). -/
def dufresne (σ ν x : ℝ) : ℝ :=
  if 0 < x then invGammaDensity (-2 * ν / σ ^ 2 + 1) (2 / σ ^ 2) x else 0

/- Paper: p. 1067–1068, stationary zero-flux ODE.
   Plain recap: Dufresne’s ψ satisfies (σ²/2)(x²ψ)' − (1+(ν+σ²/2)x)ψ = 0. -/
theorem dufresne_zero_flux (σ ν : ℝ) (hσ : 0 < σ) (x : ℝ) (hx : 0 < x) :
    σ ^ 2 / 2 * deriv (fun z => z ^ 2 * dufresne σ ν z) x
      - (1 + (ν + σ ^ 2 / 2) * x) * dufresne σ ν x = 0 := by
  have hx0 : x ≠ 0 := hx.ne'
  have hσ0 : σ ≠ 0 := hσ.ne'
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = -2 * ν / σ ^ 2 + 1 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 2 / σ ^ 2 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = a ^ (p - 1) / Real.Gamma (p - 1) := ⟨_, rfl⟩
  let ψ : ℝ → ℝ := fun z => C * z ^ (-p) * Real.exp (-a / z)
  have hloc : ∀ᶠ z in nhds x, dufresne σ ν z = ψ z := by
    filter_upwards [eventually_gt_nhds hx] with z hz
    simp [dufresne, ψ, invGammaDensity, hz, hp, ha, hC]
  have hψx : dufresne σ ν x = ψ x := by
    simp [dufresne, ψ, invGammaDensity, hx, hp, ha, hC]
  have h1 : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have h2 : HasDerivAt (fun z : ℝ => z ^ (-p)) (-p * x ^ (-p - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx0)
  have h3 : HasDerivAt (fun z : ℝ => -a / z) (a / x ^ 2) x := by
    have h : HasDerivAt (fun z : ℝ => -a / z) ((0 * x - -a * 1) / x ^ 2) x :=
      (hasDerivAt_const x (-a)).div (hasDerivAt_id x) hx0
    convert h using 1
    ring
  have h4 : HasDerivAt (fun z : ℝ => Real.exp (-a / z))
      (Real.exp (-a / x) * (a / x ^ 2)) x := h3.exp
  have key : HasDerivAt (fun z : ℝ => z ^ 2 * ψ z)
      (C * x ^ (-p) * Real.exp (-a / x) * ((2 - p) * x + a)) x := by
    have h := h1.mul ((h2.const_mul C).mul h4)
    convert h using 1
    simp only [Pi.mul_apply]
    rw [Real.rpow_sub_one hx0]
    field_simp
    ring
  have hderiv : deriv (fun z => z ^ 2 * dufresne σ ν z) x =
      C * x ^ (-p) * Real.exp (-a / x) * ((2 - p) * x + a) := by
    have heq : (fun z => z ^ 2 * dufresne σ ν z) =ᶠ[nhds x] fun z => z ^ 2 * ψ z :=
      hloc.mono fun z hz => by simp [hz]
    exact (key.congr_of_eventuallyEq heq).deriv
  rw [hderiv, hψx]
  simp only [ψ]
  rw [hp, ha]
  field_simp
  ring

/-- The logarithmic derivative implied by the zero-flux ODE:
`(x² ψ)' / (x² ψ) = (2/σ²)(x⁻² + (ν + σ²/2) x⁻¹)` wherever `ψ x ≠ 0`. -/
theorem zero_flux_logDeriv (σ ν : ℝ) (hσ : 0 < σ) (ψ : ℝ → ℝ) (x : ℝ) (hx : 0 < x)
    (hφ : x ^ 2 * ψ x ≠ 0)
    (hflux :
      σ ^ 2 / 2 * deriv (fun z => z ^ 2 * ψ z) x
        - (1 + (ν + σ ^ 2 / 2) * x) * ψ x = 0) :
    deriv (fun z => z ^ 2 * ψ z) x / (x ^ 2 * ψ x) =
      (2 / σ ^ 2) * (x⁻¹ ^ 2 + (ν + σ ^ 2 / 2) * x⁻¹) := by
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hx0 : x ≠ 0 := hx.ne'
  have hψ : ψ x ≠ 0 := by
    intro h; apply hφ; simp [h]
  have : deriv (fun z => z ^ 2 * ψ z) x =
      (2 / σ ^ 2) * (1 + (ν + σ ^ 2 / 2) * x) * ψ x := by
    have := hflux
    field_simp at this ⊢
    linarith
  rw [this]
  field_simp

/- Paper: p. 1068, nonnegativity of Dufresne's density. -/
theorem dufresne_nonneg (σ ν : ℝ) (hσ : 0 < σ) (hν : ν < 0) {x : ℝ} (hx : 0 < x) :
    0 ≤ dufresne σ ν x := by
  have hβ : 0 < -2 * ν / σ ^ 2 := div_pos (by linarith) (by positivity)
  have hΓ : 0 < Real.Gamma (-2 * ν / σ ^ 2 + 1 - 1) :=
    Real.Gamma_pos_of_pos (by simpa using hβ)
  have ha : (0 : ℝ) ≤ 2 / σ ^ 2 := by positivity
  simp only [dufresne, hx, ↓reduceIte]
  exact mul_nonneg (mul_nonneg (div_nonneg (Real.rpow_nonneg ha _) hΓ.le)
    (Real.rpow_nonneg hx.le _)) (Real.exp_pos _).le

/- Paper: p. 1067–1068, normalization constant c₂ in (3.3).
   Plain recap: Dufresne's ψ integrates to 1 over (0, ∞) (substitution u = 1/x reduces it
   to the Gamma integral). -/
theorem integral_dufresne_Ioi (σ ν : ℝ) (hσ : 0 < σ) (hν : ν < 0) :
    ∫ x in Ioi (0 : ℝ), dufresne σ ν x = 1 := by
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = -2 * ν / σ ^ 2 := ⟨_, rfl⟩
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = 2 / σ ^ 2 := ⟨_, rfl⟩
  have hβ : 0 < β := by
    rw [hβdef]
    exact div_pos (by linarith) (by positivity)
  have ha : 0 < a := by
    rw [hadef]
    positivity
  have hΓ := Real.Gamma_pos_of_pos hβ
  let g : ℝ → ℝ := fun y => a ^ β / Real.Gamma β * (y ^ (β - 1) * Real.exp (-(a * y)))
  have hsub := integral_comp_rpow_Ioi g (p := -1) (by norm_num)
  have hg : ∫ y in Ioi (0 : ℝ), g y = 1 := by
    simp only [g]
    rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hβ ha, one_div,
      Real.inv_rpow ha.le]
    have : a ^ β ≠ 0 := (Real.rpow_pos_of_pos ha β).ne'
    field_simp
  rw [← hg, ← hsub]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 < x := hx
  simp only [dufresne, hx0, ↓reduceIte, invGammaDensity, g, smul_eq_mul, ← hβdef, ← hadef]
  have h1 : β + 1 - 1 = β := by ring
  have h2 : (x ^ (-1 : ℝ)) ^ (β - 1) = x ^ (-(β - 1)) := by
    rw [← Real.rpow_mul hx0.le]
    congr 1
    ring
  have h3 : x ^ (-1 : ℝ) = x⁻¹ := Real.rpow_neg_one x
  have h4 : x ^ (-(β + 1)) = x ^ ((-1 : ℝ) - 1) * x ^ (-(β - 1)) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have h5 : -a / x = -(a * x⁻¹) := by
    field_simp
  rw [h1, h2, h3, h4, h5, abs_neg, abs_one]
  ring

/-- The inverse-gamma density has the Brownian-scaling covariance required by
`inftyLaw_scaling`. -/
theorem dufresne_scaling (σ ν x : ℝ) (hσ : 0 < σ) :
    σ⁻¹ ^ 2 * dufresne σ ν (x / σ ^ 2) = dufresne 1 (ν / σ ^ 2) x := by
  by_cases hx : 0 < x
  · have hσ2 : 0 < σ ^ 2 := sq_pos_of_pos hσ
    have hx' : 0 < x / σ ^ 2 := div_pos hx hσ2
    simp only [dufresne, hx, hx', ↓reduceIte, invGammaDensity, one_pow, div_one]
    have hβ : -2 * (ν / σ ^ 2) = -2 * ν / σ ^ 2 := by ring
    rw [hβ]
    have hβ' : -2 * ν / σ ^ 2 + 1 - 1 = -2 * ν / σ ^ 2 := by ring
    rw [hβ']
    have hpow : (2 / σ ^ 2) ^ (-2 * ν / σ ^ 2) =
        2 ^ (-2 * ν / σ ^ 2) / (σ ^ 2) ^ (-2 * ν / σ ^ 2) := by
      rw [Real.div_rpow (by positivity) (by positivity)]
    have hxpow : (x / σ ^ 2) ^ (-(-2 * ν / σ ^ 2 + 1)) =
        x ^ (-(-2 * ν / σ ^ 2 + 1)) /
          (σ ^ 2) ^ (-(-2 * ν / σ ^ 2 + 1)) := by
      rw [Real.div_rpow hx.le (sq_nonneg σ)]
    rw [hpow, hxpow]
    have hexp : -(2 / σ ^ 2) / (x / σ ^ 2) = -2 / x := by field_simp
    rw [hexp]
    have he : -(-2 * ν / σ ^ 2 + 1) = -(-2 * ν / σ ^ 2) - 1 := by ring
    have hscale : σ⁻¹ ^ 2 / (σ ^ 2) ^ (-2 * ν / σ ^ 2) /
        (σ ^ 2) ^ (-(-2 * ν / σ ^ 2 + 1)) = 1 := by
      rw [he, div_div, ← Real.rpow_add hσ2]
      have hexponents :
          -2 * ν / σ ^ 2 + (-(-2 * ν / σ ^ 2) - 1) = (-1 : ℝ) := by ring
      rw [hexponents, Real.rpow_neg_one]
      field_simp
    calc
      σ⁻¹ ^ 2 *
          (2 ^ (-2 * ν / σ ^ 2) / (σ ^ 2) ^ (-2 * ν / σ ^ 2) /
              Real.Gamma (-2 * ν / σ ^ 2) *
            (x ^ (-(-2 * ν / σ ^ 2 + 1)) /
              (σ ^ 2) ^ (-(-2 * ν / σ ^ 2 + 1))) *
            Real.exp (-2 / x)) =
          (σ⁻¹ ^ 2 / (σ ^ 2) ^ (-2 * ν / σ ^ 2) /
              (σ ^ 2) ^ (-(-2 * ν / σ ^ 2 + 1))) *
            (2 ^ (-2 * ν / σ ^ 2) / Real.Gamma (-2 * ν / σ ^ 2) *
              x ^ (-(-2 * ν / σ ^ 2 + 1)) * Real.exp (-2 / x)) := by ring
      _ = _ := by rw [hscale, one_mul]
  · have hx' : ¬ 0 < x / σ ^ 2 := not_lt.mpr (div_nonpos_of_nonpos_of_nonneg
      (not_lt.mp hx) (sq_nonneg σ))
    simp [dufresne, hx, hx']

/-- The nonnegative density used by `dufresne_theorem` is measurable. -/
theorem measurable_dufresne (σ ν : ℝ) :
    Measurable fun x => ENNReal.ofReal (dufresne σ ν x) := by
  apply Measurable.ennreal_ofReal
  unfold dufresne invGammaDensity
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  fun_prop

/-- Brownian scaling reduces Dufresne's theorem at arbitrary positive volatility to its
unit-volatility case. -/
theorem dufresne_theorem_of_sigma_one (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (σ ν : ℝ) (hσ : 0 < σ)
    (h1 : IsInftyDensity P W 1 (ν / σ ^ 2) (dufresne 1 (ν / σ ^ 2))) :
    IsInftyDensity P W σ ν (dufresne σ ν) := by
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hνscale : (ν / σ ^ 2) * σ ^ 2 = ν := by field_simp
  have hlaw := inftyLaw_scaling P W hW hσ (ν / σ ^ 2)
  rw [hνscale, h1] at hlaw
  unfold IsInftyDensity
  apply (MeasurableEquiv.mulLeft₀ (σ ^ 2)
    (pow_ne_zero 2 hσ0)).measurableEmbedding.map_injective
  change Measure.map (fun x : ℝ => σ ^ 2 * x) _ =
    Measure.map (fun x : ℝ => σ ^ 2 * x) _
  rw [← hlaw, map_mul_left_withDensity (pow_ne_zero 2 hσ0) _ (measurable_dufresne σ ν)]
  congr 1
  funext x
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simpa [abs_of_pos hσ, div_eq_inv_mul] using (dufresne_scaling σ ν x hσ).symm

/- Paper: p. 1068, Remark 3.1 / Dufresne’s theorem.
   Plain recap: the infinite-horizon integral has Dufresne’s density (supported on x > 0).
   Available pieces: `dufresne_zero_flux`, `dufresne_nonneg`, `integral_dufresne_Ioi`,
   `Z_stationary`. -/
theorem dufresne_eq_igDensity_one (ν : ℝ) :
    dufresne 1 ν = igDensity (-2 * ν) 2 := by
  funext x
  simp [dufresne, igDensity, one_pow, div_one]


/-! ### Product-space Brownian copies (for `perpetuity_inv_moment`) -/

theorem isBM_prod_fst {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → ℝ} (hW : IsBM P W) :
    IsBM (P.prod P) (fun t (p : Ω × Ω) => W t p.1) where
  hasLaw I :=
    (hW.hasLaw I).comp (measurePreserving_fst (μ := P) (ν := P)).hasLaw
  cont :=
    (measurePreserving_fst (μ := P) (ν := P)).quasiMeasurePreserving.ae hW.cont

theorem isBM_prod_snd {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → ℝ} (hW : IsBM P W) :
    IsBM (P.prod P) (fun t (p : Ω × Ω) => W t p.2) where
  hasLaw I :=
    (hW.hasLaw I).comp (measurePreserving_snd (μ := P) (ν := P)).hasLaw
  cont :=
    (measurePreserving_snd (μ := P) (ν := P)).quasiMeasurePreserving.ae hW.cont

theorem indepFun_prod_copies {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → ℝ} (hW : IsBM P W) :
    IndepFun (fun p : Ω × Ω => fun t : ℝ≥0 => W t p.1)
      (fun p => fun t : ℝ≥0 => W t p.2) (P.prod P) := by
  refine IndepFun.process_indepFun_process₀
    (fun t => (hW.toIsPreBrownianReal.aemeasurable t).comp_fst)
    (fun t => (hW.toIsPreBrownianReal.aemeasurable t).comp_snd)
    (fun I J => ?_)
  have hI : AEMeasurable (fun ω : Ω => fun i : I => W i.1 ω) P :=
    aemeasurable_pi_iff.mpr fun i => hW.toIsPreBrownianReal.aemeasurable i.1
  have hJ : AEMeasurable (fun ω : Ω => fun j : J => W j.1 ω) P :=
    aemeasurable_pi_iff.mpr fun j => hW.toIsPreBrownianReal.aemeasurable j.1
  exact indepFun_prod₀ hI hJ

/-! ### Reciprocal moment `E[A⁻¹] = -ν`

Pathwise calculus on continuous BM paths plus stationarity of `Z` (no Itô package for `Z`).
Consistency check: `dufresneGenerator_log` gives the same drift `ν + x⁻¹`. -/

/-- The Dufresne perpetuity is strictly positive a.s.: continuous paths make the integrand
bounded below by a positive constant on `[0,1]`, so the improper integral is positive. -/
theorem ae_perpetuity_pos (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (ν : ℝ) (hν : ν < 0) :
    ∀ᵐ ω ∂P, 0 < ∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s) := by
  filter_upwards [ae_integrableOn_exp_bm P W hW 1 ν one_pos hν, hW.cont] with ω hint hcont
  set f : ℝ → ℝ := fun s => Real.exp (W s.toNNReal ω + ν * s)
  have hfcont : Continuous f := by
    apply Real.continuous_exp.comp
    fun_prop
  have hintf : IntegrableOn f (Ioi 0) := by
    convert hint using 1
    funext s; simp [f]
  obtain ⟨x, _hx, hxmin⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (zero_le_one : (0 : ℝ) ≤ 1)) hfcont.continuousOn
  set m : ℝ := f x
  have hm0 : 0 < m := Real.exp_pos _
  have hIoc : m ≤ ∫ s in Ioc (0 : ℝ) 1, f s := by
    have hint' : IntegrableOn f (Ioc (0 : ℝ) 1) := hfcont.integrableOn_Ioc
    have hm_int : IntegrableOn (fun _ : ℝ => m) (Ioc (0 : ℝ) 1) volume :=
      integrableOn_const (by simp) (by simp)
    have hle : ∀ s ∈ Ioc (0 : ℝ) 1, m ≤ f s := fun s hs => hxmin ⟨hs.1.le, hs.2⟩
    calc m = ∫ _s in Ioc (0 : ℝ) 1, m := by
          rw [setIntegral_const, Measure.real, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal,
            one_smul]
          · exact zero_le_one
      _ ≤ ∫ s in Ioc (0 : ℝ) 1, f s :=
          setIntegral_mono_on hm_int hint' measurableSet_Ioc hle
  have hIoi : ∫ s in Ioc (0 : ℝ) 1, f s ≤ ∫ s in Ioi (0 : ℝ), f s :=
    setIntegral_mono_set hintf (Eventually.of_forall fun _ => (Real.exp_pos _).le)
      (Eventually.of_forall fun _ hs => (show _ ∈ Ioc (0 : ℝ) 1 from hs).1)
  exact hm0.trans_le (hIoc.trans hIoi)

/-- Path-space perpetuity functional. -/
def perpetuityPath (ν : ℝ) (x : C(ℝ≥0, ℝ)) : ℝ :=
  ∫ s in Ioi (0 : ℝ), Real.exp (x s.toNNReal + ν * s)

theorem measurable_perpetuityPath (ν : ℝ) : Measurable (perpetuityPath ν) :=
  measurable_pathSetIntegral (fun s w => Real.exp (w + ν * s)) (by fun_prop) (Ioi 0)

/-- The map `ω ↦ ∫₀^∞ e^{W_s+νs} ds` is a.e. equal to `perpetuityPath ν ∘ bmPath`. -/
theorem aemeasurable_perpetuity (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (ν : ℝ) :
    AEMeasurable (fun ω => ∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s)) P := by
  refine AEMeasurable.congr
    ((measurable_perpetuityPath ν).comp (measurable_bmPath hW)).aemeasurable ?_
  filter_upwards [bmPath_ae_eq hW] with ω hω
  simp only [Function.comp_apply, perpetuityPath]
  congr 1
  funext s
  rw [hω]

/-- Deterministic pathwise identity: writing `Y_t = A + ∫₀ᵗ e^{-νs+B_s}` and
`Z_t = e^{νt−B_t} Y_t`, one has `log Z_t − log A = νt − B_t + ∫₀ᵗ Z_s⁻¹` by ordinary calculus. -/
theorem pathwise_log_Z_identity (B : ℝ≥0 → ℝ) (hBcont : Continuous B) (_hB0 : B 0 = 0)
    (A : ℝ) (hA : 0 < A) (ν : ℝ) (t : ℝ≥0) :
    let Y : ℝ≥0 → ℝ := fun u =>
      A + ∫ s in (0 : ℝ)..(u : ℝ), Real.exp (-ν * s + B s.toNNReal)
    let Z : ℝ≥0 → ℝ := fun u => Real.exp (ν * (u : ℝ) - B u) * Y u
    Real.log (Z t) - Real.log A =
      ν * (t : ℝ) - B t + ∫ s in (0 : ℝ)..(t : ℝ), (Z s.toNNReal)⁻¹ := by
  intro Y Z
  set g : ℝ → ℝ := fun s => Real.exp (-ν * s + B s.toNNReal)
  have hgcont : Continuous g := by
    simp only [g]
    fun_prop
  have hgInt : ∀ a b, IntervalIntegrable g volume a b := fun _ _ => hgcont.intervalIntegrable _ _
  -- Define as a pointwise sum so `HasDerivAt.add` unifies directly with `YR`.
  set YR : ℝ → ℝ := (fun _ => A) + fun x => ∫ s in (0 : ℝ)..x, g s
  have hYR_apply : ∀ x, YR x = A + ∫ s in (0 : ℝ)..x, g s := fun x => rfl
  have hYRpos : ∀ x : ℝ≥0, 0 < YR x := fun x => by
    have : 0 ≤ ∫ s in (0 : ℝ)..(x : ℝ), g s :=
      intervalIntegral.integral_nonneg (NNReal.coe_nonneg x) fun _ _ => (Real.exp_pos _).le
    rw [hYR_apply]; linarith [hA]
  have hZ_eq : ∀ u : ℝ≥0, Z u = Real.exp (ν * (u : ℝ) - B u) * YR u := fun u => by
    simp only [Z, Y, hYR_apply, g]
  have hYRderiv : ∀ x : ℝ, 0 ≤ x → HasDerivAt YR (g x) x := by
    intro x _hx
    convert (hasDerivAt_const x A).add
      (intervalIntegral.integral_hasDerivAt_right (hgInt 0 x)
        (hgcont.stronglyMeasurableAtFilter volume (nhds x)) hgcont.continuousAt)
    simp
  have hprim : Continuous YR :=
    continuous_const.add (intervalIntegral.continuous_primitive hgInt 0)
  have hlogY : Real.log (YR t) - Real.log A =
      ∫ s in (0 : ℝ)..(t : ℝ), (YR s)⁻¹ * g s := by
    have h0 : YR 0 = A := by simp [YR]
    have hder : ∀ x ∈ Ioo (0 : ℝ) (t : ℝ), HasDerivAt (fun y => Real.log (YR y))
        ((YR x)⁻¹ * g x) x := by
      intro x hx
      have hx0 : 0 ≤ x := hx.1.le
      have hpos : YR x ≠ 0 := by
        have : 0 < YR x.toNNReal := hYRpos _
        simpa [Real.coe_toNNReal x hx0] using this.ne'
      have hd := (hYRderiv x hx0).log hpos
      convert hd using 1
      field_simp
    have hcontOn : ContinuousOn (fun y => Real.log (YR y)) (Icc (0 : ℝ) t) := by
      apply hprim.continuousOn.log
      intro y hy
      have : 0 < YR y.toNNReal := hYRpos _
      simpa [Real.coe_toNNReal y hy.1] using this.ne'
    have hinter : IntervalIntegrable (fun s => (YR s)⁻¹ * g s) volume 0 (t : ℝ) := by
      have hc : ContinuousOn (fun s => (YR s)⁻¹ * g s) (uIcc (0 : ℝ) t) := by
        rw [uIcc_of_le (NNReal.coe_nonneg t)]
        apply ContinuousOn.mul
        · exact (hprim.continuousOn.inv₀ fun y hy => by
            have : 0 < YR y.toNNReal := hYRpos _
            simpa [Real.coe_toNNReal y hy.1] using this.ne')
        · exact hgcont.continuousOn
      exact hc.intervalIntegrable
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (NNReal.coe_nonneg t) hcontOn hder hinter
    simpa [h0] using hFTC.symm
  have hintegrand : ∀ s ∈ uIcc (0 : ℝ) (t : ℝ),
      (YR s)⁻¹ * g s = (Z s.toNNReal)⁻¹ := by
    intro s hs
    have hsI : s ∈ Icc (0 : ℝ) t := by
      simpa [uIcc_of_le (NNReal.coe_nonneg t)] using hs
    have hs0 : 0 ≤ s := hsI.1
    have hZs : Z s.toNNReal = Real.exp (ν * s - B s.toNNReal) * YR s := by
      simp [hZ_eq, Real.coe_toNNReal s hs0]
    have hge : g s = Real.exp (-(ν * s - B s.toNNReal)) := by
      simp only [g]; congr 1; ring
    calc (YR s)⁻¹ * g s
        = (YR s)⁻¹ * Real.exp (-(ν * s - B s.toNNReal)) := by rw [hge]
      _ = (YR s * Real.exp (ν * s - B s.toNNReal))⁻¹ := by
            rw [Real.exp_neg, mul_comm (YR s)⁻¹, ← mul_inv_rev]
      _ = (Real.exp (ν * s - B s.toNNReal) * YR s)⁻¹ := by rw [mul_comm]
      _ = (Z s.toNNReal)⁻¹ := by rw [hZs]
  have hIntEq : ∫ s in (0 : ℝ)..(t : ℝ), (YR s)⁻¹ * g s =
      ∫ s in (0 : ℝ)..(t : ℝ), (Z s.toNNReal)⁻¹ :=
    intervalIntegral.integral_congr hintegrand
  have hlogZ : Real.log (Z t) = ν * (t : ℝ) - B t + Real.log (YR t) := by
    have hZt : Z t = Real.exp (ν * (t : ℝ) - B t) * YR t := hZ_eq t
    have hYpos' : 0 < YR t := hYRpos t
    rw [hZt, Real.log_mul (Real.exp_pos _).ne' hYpos'.ne', Real.log_exp]
  calc Real.log (Z t) - Real.log A
      = ν * (t : ℝ) - B t + Real.log (YR t) - Real.log A := by rw [hlogZ]
    _ = ν * (t : ℝ) - B t + (Real.log (YR t) - Real.log A) := by ring
    _ = ν * (t : ℝ) - B t + ∫ s in (0 : ℝ)..(t : ℝ), (YR s)⁻¹ * g s := by rw [hlogY]
    _ = ν * (t : ℝ) - B t + ∫ s in (0 : ℝ)..(t : ℝ), (Z s.toNNReal)⁻¹ := by rw [hIntEq]

/-- Truncated logarithm: bounded measurable approximation to `log` on `(0, ∞)`. -/
def truncLog (n : ℕ) (x : ℝ) : ℝ :=
  if 0 < x then max (-(n : ℝ)) (min (n : ℝ) (Real.log x)) else 0

theorem measurable_truncLog (n : ℕ) : Measurable (truncLog n) := by
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  exact Measurable.max measurable_const <|
    Measurable.min measurable_const Real.measurable_log

theorem abs_truncLog_le (n : ℕ) (x : ℝ) : |truncLog n x| ≤ n := by
  simp only [truncLog]
  split_ifs with hx
  · refine abs_le.2 ⟨le_max_left _ _, max_le (neg_le_self (Nat.cast_nonneg n)) (min_le_left _ _)⟩
  · simp

theorem tendsto_truncLog (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n : ℕ => truncLog n x) atTop (nhds (Real.log x)) := by
  have h : ∀ᶠ n : ℕ in atTop, truncLog n x = Real.log x := by
    filter_upwards [eventually_ge_atTop (Nat.ceil |Real.log x|)] with n hn
    have h1 : |Real.log x| ≤ n := (Nat.le_ceil _).trans (Nat.cast_le.2 hn)
    have hlo : -(n : ℝ) ≤ Real.log x := (abs_le.1 h1).1
    have hhi : Real.log x ≤ n := (abs_le.1 h1).2
    simp only [truncLog, hx, ite_true, min_eq_right hhi, max_eq_right hlo]
  exact tendsto_nhds_of_eventually_eq h

/-- Finite-horizon lower bound: `A ≥ e^ν ∫₀¹ e^{W_s} ds` a.s. when `ν < 0`. -/
theorem ae_perpetuity_ge_expInt (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (ν : ℝ) (hν : ν < 0) :
    ∀ᵐ ω ∂P,
      Real.exp ν * expInt W 1 0 1 ω ≤
        ∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s) := by
  filter_upwards [ae_integrableOn_exp_bm P W hW 1 ν one_pos hν, hW.cont] with ω hint _hcont
  set f : ℝ → ℝ := fun s => Real.exp (W s.toNNReal ω + ν * s)
  have hfcont : Continuous f := by
    apply Real.continuous_exp.comp
    fun_prop
  have hintf : IntegrableOn f (Ioi 0) := by
    convert hint using 1; funext s; simp [f]
  have hlow : ∀ s ∈ Ioc (0 : ℝ) 1, Real.exp ν * Real.exp (W s.toNNReal ω) ≤ f s := by
    intro s hs
    have : ν ≤ ν * s := by nlinarith [hν, hs.1.le, hs.2]
    simp only [f, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hInt : Real.exp ν * expInt W 1 0 1 ω =
      ∫ s in Ioc (0 : ℝ) 1, Real.exp ν * Real.exp (W s.toNNReal ω) := by
    simp only [expInt, zero_mul, add_zero, one_mul]
    have h01 : (0 : ℝ) ≤ (1 : ℝ) := zero_le_one
    rw [← intervalIntegral.integral_const_mul, show (1 : ℝ≥0) = (1 : ℝ) from rfl,
      intervalIntegral.integral_of_le h01]
  have hIoc : Real.exp ν * expInt W 1 0 1 ω ≤ ∫ s in Ioc (0 : ℝ) 1, f s := by
    rw [hInt]
    refine setIntegral_mono_on ?_ hfcont.integrableOn_Ioc measurableSet_Ioc hlow
    exact (continuous_const.mul (by fun_prop : Continuous fun s : ℝ =>
      Real.exp (W s.toNNReal ω))).integrableOn_Ioc
  have hIoi : ∫ s in Ioc (0 : ℝ) 1, f s ≤ ∫ s in Ioi (0 : ℝ), f s :=
    setIntegral_mono_set hintf (Eventually.of_forall fun _ => (Real.exp_pos _).le)
      (Eventually.of_forall fun _ hs => (show _ ∈ Ioc (0 : ℝ) 1 from hs).1)
  exact hIoc.trans hIoi

/-- Integrability of the reciprocal perpetuity: bound by the finite-horizon negative moment. -/
theorem integrable_inv_perpetuity (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (ν : ℝ) (hν : ν < 0) :
    Integrable (fun ω => (∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s))⁻¹) P := by
  have hfin := expInt_zpow_neg_integrable P W hW 1 1 one_pos one_pos 1
  have hge := ae_perpetuity_ge_expInt P W hW ν hν
  have hmeas := aemeasurable_perpetuity P W hW ν
  refine Integrable.mono' (hfin.const_mul (Real.exp (-ν))) hmeas.inv.aestronglyMeasurable ?_
  filter_upwards [hge, hW.cont] with ω hgeω _hcont
  set A := ∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s)
  set E1 := expInt W 1 0 1 ω
  have hEpos : 0 < E1 := by
    have hc : Continuous fun s : ℝ => Real.exp (W s.toNNReal ω) := by fun_prop
    have hInt := intervalIntegral.integral_pos (by norm_num : (0 : ℝ) < 1) hc.continuousOn
      (fun _ _ => (Real.exp_pos _).le)
      ⟨0, ⟨le_rfl, zero_le_one⟩, by simpa using Real.exp_pos (W 0 ω)⟩
    simpa [E1, expInt] using hInt
  have hApos : 0 < A := lt_of_lt_of_le (mul_pos (Real.exp_pos ν) hEpos) hgeω
  have hbound : A⁻¹ ≤ Real.exp (-ν) * E1⁻¹ := by
    have h1 : A⁻¹ ≤ (Real.exp ν * E1)⁻¹ :=
      inv_anti₀ (mul_pos (Real.exp_pos ν) hEpos) hgeω
    calc A⁻¹ ≤ (Real.exp ν)⁻¹ * E1⁻¹ := by rwa [mul_inv] at h1
      _ = Real.exp (-ν) * E1⁻¹ := by rw [Real.exp_neg]
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hApos)]
  simpa [zpow_neg, pow_one, E1] using hbound

/-- Brownian evaluation is integrable (Gaussian moments). -/
theorem integrable_BM_eval (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (t : ℝ≥0) : Integrable (W t) P :=
  (hW.toIsPreBrownianReal.hasLaw_eval t).integrable_comp (f := id)
    ((memLp_id_gaussianReal (μ := 0) (v := t) 2).integrable (by norm_num))

/-- Mean-zero property of Brownian motion. -/
theorem integral_BM_eval (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (t : ℝ≥0) : ∫ ω, W t ω ∂P = 0 := by
  have h := (hW.toIsPreBrownianReal.hasLaw_eval t).integral_comp
    (f := fun x : ℝ => x) continuous_id.aestronglyMeasurable
  simpa using h.trans integral_id_gaussianReal

/-- `Zproc` is a.e. measurable (path-integral construction). -/
theorem aemeasurable_Zproc (P : Measure Ω) [IsProbabilityMeasure P]
    (W B : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (hB : IsBM P B)
    (ν : ℝ) (_hν : ν < 0) (t : ℝ≥0) :
    AEMeasurable (Zproc W B 1 ν t) P := by
  have hAae := aemeasurable_perpetuity P W hW ν
  have hBt := hB.toIsPreBrownianReal.aemeasurable t
  have hIm : Measurable fun ω =>
      ∫ u in (0 : ℝ)..(t : ℝ), Real.exp (-ν * u + bmPath hB ω u.toNNReal) :=
    (measurable_pathIntegral (fun u b => Real.exp (-ν * u + b)) (by fun_prop) t).comp
      (measurable_bmPath hB)
  have hI : AEMeasurable
      (fun ω => ∫ u in (0 : ℝ)..(t : ℝ), Real.exp (-ν * u + B u.toNNReal ω)) P := by
    refine hIm.aemeasurable.congr ?_
    filter_upwards [bmPath_ae_eq hB] with ω hp
    refine intervalIntegral.integral_congr fun u hu => ?_
    have huI : u ∈ Icc (0 : ℝ) t := by
      simpa [uIcc_of_le (NNReal.coe_nonneg t)] using hu
    simp [hp u.toNNReal]
  have hexp : AEMeasurable (fun ω => Real.exp (ν * (t : ℝ) - B t ω)) P :=
    Real.measurable_exp.comp_aemeasurable <|
      ((measurable_const : Measurable fun _ => ν * (t : ℝ)).aemeasurable).sub hBt
  refine (hexp.mul (hAae.add hI)).congr ?_
  filter_upwards with ω
  simp [Zproc, one_mul]

/-- Reciprocal moments of `Z_t` and `A` agree by stationarity. -/
theorem integral_inv_Zproc_eq (P : Measure Ω) [IsProbabilityMeasure P]
    (W B : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (hB : IsBM P B)
    (hWB : IndepFun (fun ω => fun t : ℝ≥0 => W t ω) (fun ω => fun t : ℝ≥0 => B t ω) P)
    (ν : ℝ) (hν : ν < 0) (t : ℝ≥0) :
    ∫ ω, (Zproc W B 1 ν t ω)⁻¹ ∂P =
      ∫ ω, (∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s))⁻¹ ∂P := by
  set A : Ω → ℝ := fun ω => ∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s)
  have hAinv := integrable_inv_perpetuity P W hW ν hν
  have hApos := ae_perpetuity_pos P W hW ν hν
  have hZae := aemeasurable_Zproc P W B hW hB ν hν t
  have hmaps := Z_stationary_sigma_one P W B hW hB hWB ν hν t
  have hm0 : Measurable fun x : ℝ => ENNReal.ofReal x⁻¹ :=
    ENNReal.measurable_ofReal.comp measurable_inv
  have hAae := aemeasurable_perpetuity P W hW ν
  have hmomL : ∫⁻ ω, ENNReal.ofReal (Zproc W B 1 ν t ω)⁻¹ ∂P =
      ∫⁻ ω, ENNReal.ofReal (A ω)⁻¹ ∂P := by
    calc ∫⁻ ω, ENNReal.ofReal (Zproc W B 1 ν t ω)⁻¹ ∂P
        = ∫⁻ x, ENNReal.ofReal x⁻¹ ∂(P.map (Zproc W B 1 ν t)) :=
          (lintegral_map' hm0.aemeasurable hZae).symm
      _ = ∫⁻ x, ENNReal.ofReal x⁻¹ ∂(P.map A) := by
          simpa [A, one_mul] using congrArg (fun μ => ∫⁻ x, ENNReal.ofReal x⁻¹ ∂μ) hmaps
      _ = ∫⁻ ω, ENNReal.ofReal (A ω)⁻¹ ∂P := lintegral_map' hm0.aemeasurable hAae
  have hZpos : ∀ᵐ ω ∂P, 0 < Zproc W B 1 ν t ω := by
    filter_upwards [hApos] with ω hAp
    have hinter :
        0 ≤ ∫ u in (0 : ℝ)..(t : ℝ), Real.exp (-ν * u + B u.toNNReal ω) :=
      intervalIntegral.integral_nonneg (NNReal.coe_nonneg t) fun _ _ => (Real.exp_pos _).le
    have hY : 0 < A ω + ∫ u in (0 : ℝ)..(t : ℝ), Real.exp (-ν * u + B u.toNNReal ω) := by
      linarith [hAp]
    simpa [Zproc, A, one_mul] using mul_pos (Real.exp_pos _) hY
  have hnnZ : 0 ≤ᵐ[P] fun ω => (Zproc W B 1 ν t ω)⁻¹ := by
    filter_upwards [hZpos] with ω hp; exact (inv_pos.2 hp).le
  have hnnA : 0 ≤ᵐ[P] fun ω => (A ω)⁻¹ := by
    filter_upwards [hApos] with ω hp; exact (inv_pos.2 hp).le
  have hZinv : Integrable (fun ω => (Zproc W B 1 ν t ω)⁻¹) P := by
    refine ⟨hZae.inv.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnnZ, hmomL]
    exact (hasFiniteIntegral_iff_ofReal hnnA).1 hAinv.hasFiniteIntegral
  apply (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg_of_ae hnnZ)
    (integral_nonneg_of_ae hnnA)).1
  calc ENNReal.ofReal (∫ ω, (Zproc W B 1 ν t ω)⁻¹ ∂P)
      = ∫⁻ ω, ENNReal.ofReal (Zproc W B 1 ν t ω)⁻¹ ∂P :=
        ofReal_integral_eq_lintegral_ofReal hZinv hnnZ
    _ = ∫⁻ ω, ENNReal.ofReal (A ω)⁻¹ ∂P := hmomL
    _ = ENNReal.ofReal (∫ ω, (A ω)⁻¹ ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hAinv hnnA).symm

/-- Slice integrability of `Z_t⁻¹` (same L¹ norm as `A⁻¹` by stationarity). -/
theorem integrable_inv_Zproc (P : Measure Ω) [IsProbabilityMeasure P]
    (W B : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (hB : IsBM P B)
    (hWB : IndepFun (fun ω => fun t : ℝ≥0 => W t ω) (fun ω => fun t : ℝ≥0 => B t ω) P)
    (ν : ℝ) (hν : ν < 0) (t : ℝ≥0) :
    Integrable (fun ω => (Zproc W B 1 ν t ω)⁻¹) P := by
  have hAinv := integrable_inv_perpetuity P W hW ν hν
  have hApos := ae_perpetuity_pos P W hW ν hν
  have hZae := aemeasurable_Zproc P W B hW hB ν hν t
  have hmaps := Z_stationary_sigma_one P W B hW hB hWB ν hν t
  set A : Ω → ℝ := fun ω => ∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s)
  have hm0 : Measurable fun x : ℝ => ENNReal.ofReal x⁻¹ :=
    ENNReal.measurable_ofReal.comp measurable_inv
  have hAae := aemeasurable_perpetuity P W hW ν
  have hmomL : ∫⁻ ω, ENNReal.ofReal (Zproc W B 1 ν t ω)⁻¹ ∂P =
      ∫⁻ ω, ENNReal.ofReal (A ω)⁻¹ ∂P := by
    calc ∫⁻ ω, ENNReal.ofReal (Zproc W B 1 ν t ω)⁻¹ ∂P
        = ∫⁻ x, ENNReal.ofReal x⁻¹ ∂(P.map (Zproc W B 1 ν t)) :=
          (lintegral_map' hm0.aemeasurable hZae).symm
      _ = ∫⁻ x, ENNReal.ofReal x⁻¹ ∂(P.map A) := by
          simpa [A, one_mul] using congrArg (fun μ => ∫⁻ x, ENNReal.ofReal x⁻¹ ∂μ) hmaps
      _ = ∫⁻ ω, ENNReal.ofReal (A ω)⁻¹ ∂P := lintegral_map' hm0.aemeasurable hAae
  have hZpos : ∀ᵐ ω ∂P, 0 < Zproc W B 1 ν t ω := by
    filter_upwards [hApos] with ω hAp
    have hinter :
        0 ≤ ∫ u in (0 : ℝ)..(t : ℝ), Real.exp (-ν * u + B u.toNNReal ω) :=
      intervalIntegral.integral_nonneg (NNReal.coe_nonneg t) fun _ _ => (Real.exp_pos _).le
    have hY : 0 < A ω + ∫ u in (0 : ℝ)..(t : ℝ), Real.exp (-ν * u + B u.toNNReal ω) := by
      linarith [hAp]
    simpa [Zproc, A, one_mul] using mul_pos (Real.exp_pos _) hY
  have hnnZ : 0 ≤ᵐ[P] fun ω => (Zproc W B 1 ν t ω)⁻¹ := by
    filter_upwards [hZpos] with ω hp; exact (inv_pos.2 hp).le
  have hnnA : 0 ≤ᵐ[P] fun ω => (A ω)⁻¹ := by
    filter_upwards [hApos] with ω hp; exact (inv_pos.2 hp).le
  refine ⟨hZae.inv.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hnnZ, hmomL]
  exact (hasFiniteIntegral_iff_ofReal hnnA).1 hAinv.hasFiniteIntegral

/-- Path-space reciprocal used for joint measurability of `Z⁻¹`. -/
def invZFromPaths (ν : ℝ) (s : ℝ≥0) (w b : C(ℝ≥0, ℝ)) : ℝ :=
  let A := perpetuityPath ν w
  let Y := A + ∫ u in (0 : ℝ)..(s : ℝ), Real.exp (-ν * u + b u.toNNReal)
  let Zv := Real.exp (ν * (s : ℝ) - b s) * Y
  if 0 < A then Zv⁻¹ else 0

theorem continuous_invZFromPaths_time (ν : ℝ) (w b : C(ℝ≥0, ℝ)) :
    Continuous fun s : ℝ≥0 => invZFromPaths ν s w b := by
  classical
  simp only [invZFromPaths]
  by_cases hA : 0 < perpetuityPath ν w
  · simp only [hA, ite_true]
    have hYpos : ∀ s : ℝ≥0, 0 <
        perpetuityPath ν w +
          ∫ u in (0 : ℝ)..(s : ℝ), Real.exp (-ν * u + b u.toNNReal) := fun s => by
      have : 0 ≤ ∫ u in (0 : ℝ)..(s : ℝ), Real.exp (-ν * u + b u.toNNReal) :=
        intervalIntegral.integral_nonneg (NNReal.coe_nonneg s) fun _ _ => (Real.exp_pos _).le
      linarith [hA]
    refine Continuous.inv₀ ?_ fun s =>
      (mul_pos (Real.exp_pos _) (hYpos s)).ne'
    have hc : Continuous fun u : ℝ => Real.exp (-ν * u + b u.toNNReal) := by fun_prop
    have hprim :
        Continuous fun s : ℝ≥0 => ∫ u in (0 : ℝ)..(s : ℝ), Real.exp (-ν * u + b u.toNNReal) :=
      (intervalIntegral.continuous_primitive
          (μ := volume) (fun _ _ => hc.intervalIntegrable _ _) 0).comp continuous_subtype_val
    exact (by fun_prop : Continuous fun s : ℝ≥0 => Real.exp (ν * (s : ℝ) - b s)).mul <|
      continuous_const.add hprim
  · simp only [hA, ite_false]
    exact continuous_const

theorem measurable_invZFromPaths (ν : ℝ) (s : ℝ≥0) :
    Measurable fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => invZFromPaths ν s p.1 p.2 := by
  have hA : Measurable fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => perpetuityPath ν p.1 :=
    (measurable_perpetuityPath ν).comp measurable_fst
  have hI : Measurable fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) =>
      ∫ u in (0 : ℝ)..(s : ℝ), Real.exp (-ν * u + p.2 u.toNNReal) :=
    (measurable_pathIntegral (fun u b => Real.exp (-ν * u + b)) (by fun_prop) s).comp
      measurable_snd
  have hY := hA.add hI
  have hexp : Measurable fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) =>
      Real.exp (ν * (s : ℝ) - p.2 s) :=
    Real.measurable_exp.comp <|
      (measurable_const : Measurable fun _ => ν * (s : ℝ)).sub
        (ContinuousMap.measurable_eval s |>.comp measurable_snd)
  have hZv := hexp.mul hY
  refine Measurable.ite (measurableSet_lt measurable_const hA) hZv.inv measurable_const

/-- Joint integrability of `(s, ω) ↦ Z_s(ω)⁻¹` on `(0, t] × Ω`, for Fubini. -/
theorem integrable_uncurry_inv_Zproc (P : Measure Ω) [IsProbabilityMeasure P]
    (W B : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (hB : IsBM P B)
    (hWB : IndepFun (fun ω => fun t : ℝ≥0 => W t ω) (fun ω => fun t : ℝ≥0 => B t ω) P)
    (ν : ℝ) (hν : ν < 0) (t : ℝ≥0) :
    Integrable (Function.uncurry
      (fun s : ℝ => fun ω => (Zproc W B 1 ν s.toNNReal ω)⁻¹))
      ((volume.restrict (uIoc (0 : ℝ) (t : ℝ))).prod P) := by
  classical
  set fMeas : ℝ × Ω → ℝ := fun p =>
    invZFromPaths ν p.1.toNNReal (bmPath hW p.2) (bmPath hB p.2)
  have hfMeas' : Measurable fMeas :=
    measurable_uncurry_of_continuous_of_measurable
      (u := fun s : ℝ => fun ω : Ω =>
        invZFromPaths ν s.toNNReal (bmPath hW ω) (bmPath hB ω))
      (fun ω =>
        (continuous_invZFromPaths_time ν (bmPath hW ω) (bmPath hB ω)).comp
          continuous_real_toNNReal)
      (fun s =>
        (measurable_invZFromPaths ν s.toNNReal).comp
          ((measurable_bmPath hW).prodMk (measurable_bmPath hB)))
  have hae : fMeas =ᵐ[(volume.restrict (uIoc (0 : ℝ) (t : ℝ))).prod P]
      Function.uncurry (fun s : ℝ => fun ω => (Zproc W B 1 ν s.toNNReal ω)⁻¹) := by
    have hWae := bmPath_ae_eq hW
    have hBae := bmPath_ae_eq hB
    have hApos := ae_perpetuity_pos P W hW ν hν
    have hmod := (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (uIoc (0 : ℝ) (t : ℝ))) (ν := P)).ae
      ((hWae.and hBae).and hApos)
    filter_upwards [hmod] with p hp
    have hWw : ∀ u : ℝ≥0, bmPath hW p.2 u = W u p.2 := hp.1.1
    have hBb : ∀ u : ℝ≥0, bmPath hB p.2 u = B u p.2 := hp.1.2
    have hAp : 0 < ∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal p.2 + ν * s) := hp.2
    set τ : ℝ≥0 := p.1.toNNReal
    have hAeq : perpetuityPath ν (bmPath hW p.2) =
        ∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal p.2 + ν * s) := by
      simp only [perpetuityPath]
      congr 1; funext s; rw [hWw]
    have hIeq :
        ∫ u in (0 : ℝ)..(τ : ℝ), Real.exp (-ν * u + bmPath hB p.2 u.toNNReal) =
          ∫ u in (0 : ℝ)..(τ : ℝ), Real.exp (-ν * u + B u.toNNReal p.2) :=
      intervalIntegral.integral_congr fun u _ => by rw [hBb]
    have hBeq : bmPath hB p.2 τ = B τ p.2 := hBb _
    have hApos' : 0 < perpetuityPath ν (bmPath hW p.2) := by rwa [hAeq]
    change invZFromPaths ν τ (bmPath hW p.2) (bmPath hB p.2) =
      (Zproc W B 1 ν τ p.2)⁻¹
    unfold invZFromPaths
    rw [ite_eq_left hApos']
    simp only [Zproc, one_mul, hAeq, hIeq, hBeq]
  have hasm : AEStronglyMeasurable
      (Function.uncurry (fun s : ℝ => fun ω => (Zproc W B 1 ν s.toNNReal ω)⁻¹))
      ((volume.restrict (uIoc (0 : ℝ) (t : ℝ))).prod P) :=
    hfMeas'.aestronglyMeasurable.congr hae
  rw [integrable_prod_iff hasm]
  refine ⟨?_, ?_⟩
  · refine ae_restrict_of_forall_mem measurableSet_uIoc fun s hs => ?_
    have hs0 : 0 ≤ s := by
      rw [uIoc_of_le (NNReal.coe_nonneg t)] at hs
      exact hs.1.le
    simpa [Function.uncurry, Real.coe_toNNReal s hs0] using
      integrable_inv_Zproc P W B hW hB hWB ν hν s.toNNReal
  · have hvol : volume (uIoc (0 : ℝ) (t : ℝ)) < ∞ := by
      rw [uIoc_of_le (NNReal.coe_nonneg t), Real.volume_Ioc]
      simp
    have : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) (t : ℝ))) :=
      ⟨by simp [Measure.restrict_apply MeasurableSet.univ]⟩
    set c : ℝ := ∫ ω, (∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s))⁻¹ ∂P
    have hc : Integrable (fun _ : ℝ => c) (volume.restrict (uIoc (0 : ℝ) (t : ℝ))) :=
      integrable_const c
    refine hc.congr ?_
    refine ae_restrict_of_forall_mem measurableSet_uIoc fun s hs => ?_
    have hs0 : 0 ≤ s := by
      rw [uIoc_of_le (NNReal.coe_nonneg t)] at hs
      exact hs.1.le
    have hnn : 0 ≤ᵐ[P] fun ω => (Zproc W B 1 ν s.toNNReal ω)⁻¹ := by
      have hApos := ae_perpetuity_pos P W hW ν hν
      filter_upwards [hApos] with ω hAp
      have hinter :
          0 ≤ ∫ u in (0 : ℝ)..(s.toNNReal : ℝ), Real.exp (-ν * u + B u.toNNReal ω) :=
        intervalIntegral.integral_nonneg (NNReal.coe_nonneg _) fun _ _ => (Real.exp_pos _).le
      have hY : 0 <
          (∫ u in Ioi (0 : ℝ), Real.exp (W u.toNNReal ω + ν * u)) +
            ∫ u in (0 : ℝ)..(s.toNNReal : ℝ), Real.exp (-ν * u + B u.toNNReal ω) := by
        linarith [hAp]
      exact (inv_pos.2 (by simpa [Zproc, one_mul] using mul_pos (Real.exp_pos _) hY)).le
    simp only [Function.uncurry, Real.norm_eq_abs, c]
    have habs : ∫ ω, |(Zproc W B 1 ν s.toNNReal ω)⁻¹| ∂P =
        ∫ ω, (Zproc W B 1 ν s.toNNReal ω)⁻¹ ∂P :=
      integral_congr_ae <| by
        filter_upwards [hnn] with ω hω; exact abs_of_nonneg hω
    rw [habs]
    exact (integral_inv_Zproc_eq P W B hW hB hWB ν hν s.toNNReal).symm

/-- Stationarity of `Z` plus the pathwise log identity give `E[A⁻¹] = -ν`.

Uses truncated logs + DCT so that only `Integrable A⁻¹` (not `Integrable log A`) is required. -/
theorem perpetuity_inv_moment (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (ν : ℝ) (hν : ν < 0) :
    ∫⁻ ω, ENNReal.ofReal
        ((∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s))⁻¹) ∂P =
      ENNReal.ofReal (-ν) := by
  classical
  set Q : Measure (Ω × Ω) := P.prod P
  set W1 : ℝ≥0 → Ω × Ω → ℝ := fun t p => W t p.1
  set Bproc : ℝ≥0 → Ω × Ω → ℝ := fun t p => W t p.2
  have hW1 : IsBM Q W1 := isBM_prod_fst hW
  have hB : IsBM Q Bproc := isBM_prod_snd hW
  have hWB := indepFun_prod_copies (W := W) hW
  set A : Ω × Ω → ℝ := fun p =>
    ∫ s in Ioi (0 : ℝ), Real.exp (W1 s.toNNReal p + ν * s)
  set A0 : Ω → ℝ := fun ω =>
    ∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s)
  have hA_fst : A = A0 ∘ Prod.fst := by
    funext p; simp [A, A0, W1, Function.comp]
  have hAinv : Integrable (fun p => (A p)⁻¹) Q := by
    simpa [A, W1] using integrable_inv_perpetuity Q W1 hW1 ν hν
  have hApos : ∀ᵐ p ∂Q, 0 < A p := by
    simpa [A, W1] using ae_perpetuity_pos Q W1 hW1 ν hν
  set Z1 : Ω × Ω → ℝ := Zproc W1 Bproc 1 ν 1
  have hstat : Q.map Z1 = Q.map A := by
    simpa [Z1, A, W1, Bproc, one_mul] using
      Z_stationary_sigma_one Q W1 Bproc hW1 hB hWB ν hν 1
  have htransfer :
      (∫⁻ p, ENNReal.ofReal (A p)⁻¹ ∂Q) = ∫⁻ ω, ENNReal.ofReal (A0 ω)⁻¹ ∂P := by
    have hfst : MeasurePreserving Prod.fst Q P := measurePreserving_fst (μ := P) (ν := P)
    set A0m : Ω → ℝ := fun ω => perpetuityPath ν (bmPath hW ω)
    have hm : Measurable fun ω => ENNReal.ofReal (A0m ω)⁻¹ :=
      ENNReal.measurable_ofReal.comp
        ((measurable_perpetuityPath ν).comp (measurable_bmPath hW)).inv
    have hAe : A0 =ᵐ[P] A0m := by
      filter_upwards [bmPath_ae_eq hW] with ω hω
      simp [A0, A0m, perpetuityPath, hω]
    have hQe : (fun p => ENNReal.ofReal (A p)⁻¹) =ᵐ[Q]
        fun p => ENNReal.ofReal (A0m p.1)⁻¹ := by
      rw [hA_fst]
      filter_upwards [hfst.quasiMeasurePreserving.ae hAe] with p hp
      simp [Function.comp, hp]
    rw [lintegral_congr_ae hQe, hfst.lintegral_comp hm]
    exact lintegral_congr_ae <| by
      filter_upwards [hAe] with ω hω; simp [hω]
  have hid : ∀ᵐ p ∂Q,
      Real.log (Z1 p) - Real.log (A p) =
        ν * (1 : ℝ) - Bproc 1 p +
          ∫ s in (0 : ℝ)..(1 : ℝ), (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ := by
    filter_upwards [hApos, hB.cont, hB.eval_zero_ae_eq_zero] with p hAp hBcont hB0
    simpa [Z1, Zproc, A, W1, Bproc, one_mul] using
      pathwise_log_Z_identity (fun t => Bproc t p) hBcont hB0 (A p) hAp ν 1
  have hmain : ∫ p, (A p)⁻¹ ∂Q = -ν := by
    have hEB := integral_BM_eval Q Bproc hB 1
    have hBint := integrable_BM_eval Q Bproc hB 1
    have hmomR : ∀ s : ℝ≥0, ∫ p, (Zproc W1 Bproc 1 ν s p)⁻¹ ∂Q = ∫ p, (A p)⁻¹ ∂Q :=
      fun s => by simpa [A, W1] using integral_inv_Zproc_eq Q W1 Bproc hW1 hB hWB ν hν s
    have hZae := aemeasurable_Zproc Q W1 Bproc hW1 hB ν hν
    have hid' : ∀ᵐ p ∂Q,
        ∫ s in (0 : ℝ)..(1 : ℝ), (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ =
          Real.log (Z1 p) - Real.log (A p) - ν + Bproc 1 p := by
      filter_upwards [hid] with p hp; linarith [hp]
    have hZpos : ∀ᵐ p ∂Q, ∀ s : ℝ≥0, 0 < Zproc W1 Bproc 1 ν s p := by
      filter_upwards [hApos] with p hAp s
      have hinter :
          0 ≤ ∫ u in (0 : ℝ)..(s : ℝ), Real.exp (-ν * u + Bproc u.toNNReal p) :=
        intervalIntegral.integral_nonneg (NNReal.coe_nonneg s) fun _ _ => (Real.exp_pos _).le
      have hY : 0 < A p + ∫ u in (0 : ℝ)..(s : ℝ), Real.exp (-ν * u + Bproc u.toNNReal p) := by
        linarith [hAp]
      simpa [Zproc, one_mul] using mul_pos (Real.exp_pos _) hY
    have hint :
        Integrable (Function.uncurry
          (fun s : ℝ => fun p => (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹))
          ((volume.restrict (uIoc (0 : ℝ) (1 : ℝ))).prod Q) :=
      integrable_uncurry_inv_Zproc Q W1 Bproc hW1 hB hWB ν hν 1
    have hIntZ : Integrable
        (fun p => ∫ s in (0 : ℝ)..(1 : ℝ), (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹) Q := by
      have hset : Integrable
          (fun p => ∫ s in uIoc (0 : ℝ) (1 : ℝ),
            (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹) Q := by
        simpa [Function.uncurry] using hint.integral_prod_right
      convert hset using 1
      funext p
      simp [intervalIntegral.intervalIntegral_eq_integral_uIoc]
    have hFub :
        ∫ p, (∫ s in (0 : ℝ)..(1 : ℝ), (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹) ∂Q =
          ∫ p, (A p)⁻¹ ∂Q := by
      have hswap :=
        intervalIntegral_integral_swap
          (f := fun s p => (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹) hint
      -- hswap : ∫s ∫p = ∫p (∫s)
      rw [← hswap]
      have hpoint : ∀ s ∈ uIcc (0 : ℝ) (1 : ℝ),
          ∫ p, (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ∂Q = ∫ p, (A p)⁻¹ ∂Q := by
        intro s hs
        have hsI : s ∈ Icc (0 : ℝ) 1 := by
          simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using hs
        simpa [Real.coe_toNNReal s hsI.1] using hmomR s.toNNReal
      calc ∫ s in (0 : ℝ)..(1 : ℝ), ∫ p, (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ∂Q
          = ∫ s in (0 : ℝ)..(1 : ℝ), ∫ p, (A p)⁻¹ ∂Q :=
            intervalIntegral.integral_congr hpoint
        _ = ∫ p, (A p)⁻¹ ∂Q := by
            rw [intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1),
              setIntegral_const, Measure.real, Real.volume_Ioc, sub_zero,
              ENNReal.toReal_ofReal zero_le_one, one_smul]
    have hlogdiff : Integrable (fun p => Real.log (Z1 p) - Real.log (A p)) Q := by
      refine ((hIntZ.add (integrable_const ν)).sub hBint).congr ?_
      filter_upwards [hid'] with p hp
      have h :
          (∫ s in (0 : ℝ)..(1 : ℝ), (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹) + ν - Bproc 1 p =
            Real.log (Z1 p) - Real.log (A p) := by linarith [hp]
      exact h
    have hElog : ∫ p, Real.log (Z1 p) - Real.log (A p) ∂Q = 0 := by
      have hZi : ∀ n, Integrable (fun p => truncLog n (Z1 p)) Q := fun n =>
        Integrable.of_bound
          ((measurable_truncLog n).comp_aemeasurable (hZae 1)).aestronglyMeasurable n
          (Eventually.of_forall fun p => abs_truncLog_le n _)
      have hAi : ∀ n, Integrable (fun p => truncLog n (A p)) Q := fun n =>
        Integrable.of_bound
          ((measurable_truncLog n).comp_aemeasurable
            (aemeasurable_perpetuity Q W1 hW1 ν)).aestronglyMeasurable n
          (Eventually.of_forall fun p => abs_truncLog_le n _)
      have htrunc : ∀ n, ∫ p, truncLog n (Z1 p) ∂Q = ∫ p, truncLog n (A p) ∂Q := by
        intro n
        have hm := measurable_truncLog n
        calc ∫ p, truncLog n (Z1 p) ∂Q
            = ∫ x, truncLog n x ∂(Q.map Z1) :=
              (integral_map (hZae 1) hm.aestronglyMeasurable).symm
          _ = ∫ x, truncLog n x ∂(Q.map A) := by rw [hstat]
          _ = ∫ p, truncLog n (A p) ∂Q :=
              integral_map (aemeasurable_perpetuity Q W1 hW1 ν) hm.aestronglyMeasurable
      have htend :
          Tendsto (fun n => ∫ p, truncLog n (Z1 p) - truncLog n (A p) ∂Q) atTop
            (nhds (∫ p, Real.log (Z1 p) - Real.log (A p) ∂Q)) := by
        refine tendsto_integral_of_dominated_convergence
          (fun p => |Real.log (Z1 p) - Real.log (A p)|)
          (fun n =>
            (((measurable_truncLog n).comp_aemeasurable (hZae 1)).sub
              ((measurable_truncLog n).comp_aemeasurable
                (aemeasurable_perpetuity Q W1 hW1 ν))).aestronglyMeasurable)
          hlogdiff.abs ?_ ?_
        · intro n
          filter_upwards [hZpos, hApos] with p hpZ hpA
          have hx : 0 < Z1 p := hpZ 1
          have hy : 0 < A p := hpA
          change |truncLog n (Z1 p) - truncLog n (A p)| ≤ |Real.log (Z1 p) - Real.log (A p)|
          simp only [truncLog, hx, hy, ite_true]
          have hLip : LipschitzWith 1
              (fun t : ℝ => max (-(n : ℝ)) (min (n : ℝ) t)) :=
            (LipschitzWith.id (α := ℝ)).const_min (n : ℝ) |>.const_max (-(n : ℝ))
          have := hLip.dist_le_mul (Real.log (Z1 p)) (Real.log (A p))
          simpa [Real.dist_eq, NNReal.coe_one, one_mul] using this
        · filter_upwards [hZpos, hApos] with p hpZ hpA
          exact (tendsto_truncLog _ (hpZ 1)).sub (tendsto_truncLog _ hpA)
      have hzero : ∀ n, ∫ p, truncLog n (Z1 p) - truncLog n (A p) ∂Q = 0 := fun n => by
        rw [integral_sub (hZi n) (hAi n), htrunc n, sub_self]
      exact tendsto_nhds_unique htend (tendsto_const_nhds.congr fun n => (hzero n).symm)
    have hsplit :
        ∫ p, Real.log (Z1 p) - Real.log (A p) - ν + Bproc 1 p ∂Q = -ν := by
      have h1 : Integrable (fun p => Real.log (Z1 p) - Real.log (A p) + (-ν)) Q :=
        hlogdiff.add (integrable_const _)
      have heq :
          (fun p => Real.log (Z1 p) - Real.log (A p) - ν + Bproc 1 p) =ᵐ[Q]
            fun p => (Real.log (Z1 p) - Real.log (A p) + (-ν)) + Bproc 1 p :=
        Eventually.of_forall fun p => by ring
      rw [integral_congr_ae heq, integral_add h1 hBint, hEB, add_zero,
        integral_add hlogdiff (integrable_const (-ν)), hElog, zero_add,
        MeasureTheory.integral_const]
      simp [Measure.real]
    calc ∫ p, (A p)⁻¹ ∂Q
        = ∫ p, (∫ s in (0 : ℝ)..(1 : ℝ), (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹) ∂Q :=
          hFub.symm
      _ = ∫ p, Real.log (Z1 p) - Real.log (A p) - ν + Bproc 1 p ∂Q :=
          integral_congr_ae hid'
      _ = -ν := hsplit
  have hnn : 0 ≤ᵐ[Q] fun p => (A p)⁻¹ := by
    filter_upwards [hApos] with p hp; exact (inv_pos.2 hp).le
  have hlin : ∫⁻ p, ENNReal.ofReal (A p)⁻¹ ∂Q = ENNReal.ofReal (∫ p, (A p)⁻¹ ∂Q) :=
    (ofReal_integral_eq_lintegral_ofReal hAinv hnn).symm
  calc ∫⁻ ω, ENNReal.ofReal (A0 ω)⁻¹ ∂P
      = ∫⁻ p, ENNReal.ofReal (A p)⁻¹ ∂Q := htransfer.symm
    _ = ENNReal.ofReal (∫ p, (A p)⁻¹ ∂Q) := hlin
    _ = ENNReal.ofReal (-ν) := by rw [hmain]

/-- Unit-volatility generator: `generator 1 ν`. -/
abbrev dufresneGenerator (ν : ℝ) : (ℝ → ℝ) → ℝ → ℝ := generator 1 ν

/-- Formal computation: `L(log)(x) = ν + x⁻¹` for `x > 0`. -/
theorem dufresneGenerator_log (ν x : ℝ) (hx : 0 < x) :
    dufresneGenerator ν Real.log x = ν + x⁻¹ := by
  have h1 : deriv Real.log x = x⁻¹ := Real.deriv_log x
  have hnhd : (fun y => deriv Real.log y) =ᶠ[nhds x] fun y => y⁻¹ :=
    Filter.Eventually.of_forall fun y => Real.deriv_log y
  have h2' : deriv (fun y : ℝ => y⁻¹) x = -(x⁻¹) ^ 2 := by
    simp [pow_two, (hasDerivAt_inv hx.ne').deriv]
  have h2 : deriv (deriv Real.log) x = -(x⁻¹) ^ 2 :=
    (Filter.EventuallyEq.deriv_eq hnhd).trans h2'
  simp only [dufresneGenerator, generator, one_pow, one_mul, h1, h2]
  field_simp
  ring

/-- Formal computation: `L(y ↦ (y^k)⁻¹)(x) = (k²/2 - k ν)(x^k)⁻¹ - k (x^{k+1})⁻¹` for `x > 0`. -/
theorem dufresneGenerator_zpow (ν : ℝ) (k : ℕ) (_hk : 0 < k) (x : ℝ) (hx : 0 < x) :
    dufresneGenerator ν (fun y => (y ^ k)⁻¹) x =
      ((k : ℝ) ^ 2 / 2 - (k : ℝ) * ν) * (x ^ k)⁻¹ - (k : ℝ) * (x ^ (k + 1))⁻¹ := by
  have hx0 : x ≠ 0 := hx.ne'
  -- Identify `(· ^ k)⁻¹` with the zpow `· ^ (-k)` on a neighbourhood of `x > 0`.
  have hfun : (fun y : ℝ => (y ^ k)⁻¹) =ᶠ[nhds x] fun y => y ^ (-(k : ℤ)) := by
    filter_upwards [eventually_ne_nhds hx0] with y hy
    rw [zpow_neg, zpow_natCast]
  have h1 : deriv (fun y : ℝ => (y ^ k)⁻¹) x = -(k : ℝ) * x ^ (-(k : ℤ) - 1) := by
    rw [Filter.EventuallyEq.deriv_eq hfun, deriv_zpow]
    simp [Int.cast_neg]
  have hnhd : (fun y => deriv (fun z : ℝ => (z ^ k)⁻¹) y) =ᶠ[nhds x]
      fun y => (-(k : ℝ)) * y ^ (-(k : ℤ) - 1) := by
    filter_upwards [eventually_ne_nhds hx0] with y hy
    have hfy : (fun z : ℝ => (z ^ k)⁻¹) =ᶠ[nhds y] fun z => z ^ (-(k : ℤ)) := by
      filter_upwards [eventually_ne_nhds hy] with z hz
      rw [zpow_neg, zpow_natCast]
    rw [Filter.EventuallyEq.deriv_eq hfy, deriv_zpow]
    simp [Int.cast_neg]
  have h2 : deriv (deriv (fun y : ℝ => (y ^ k)⁻¹)) x =
      (k : ℝ) * (k + 1 : ℝ) * x ^ (-(k : ℤ) - 2) := by
    rw [Filter.EventuallyEq.deriv_eq hnhd, deriv_const_mul_field']
    -- (-k) * ((-k) - 1) * x^(-k-2) = k(k+1) x^(-k-2)
    simp only [deriv_zpow, Int.cast_neg, Int.cast_sub, Int.cast_natCast]
    ring_nf
  -- Rewrite negative zpowers as reciprocal nat-powers for the algebra
  have hz1 : x ^ (-(k : ℤ) - 1) = (x ^ (k + 1))⁻¹ := by
    rw [show -(k : ℤ) - 1 = -((k + 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
  have hz2 : x ^ (-(k : ℤ) - 2) = (x ^ (k + 2))⁻¹ := by
    rw [show -(k : ℤ) - 2 = -((k + 2 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
  simp only [dufresneGenerator, generator, one_pow, one_mul, h1, h2, hz1, hz2]
  have hxpow : (x : ℝ) ^ 2 * (x ^ (k + 2))⁻¹ = (x ^ k)⁻¹ := by
    calc
      x ^ 2 * (x ^ (k + 2))⁻¹
          = x ^ 2 * (x ^ k * x ^ 2)⁻¹ := by rw [pow_add]
      _ = x ^ 2 * ((x ^ k)⁻¹ * (x ^ 2)⁻¹) := by rw [mul_inv]
      _ = (x ^ 2 * (x ^ 2)⁻¹) * (x ^ k)⁻¹ := by ring
      _ = (x ^ k)⁻¹ := by rw [mul_inv_cancel₀ (pow_ne_zero 2 hx0), one_mul]
  have hxpow' : x * (x ^ (k + 1))⁻¹ = (x ^ k)⁻¹ := by
    calc
      x * (x ^ (k + 1))⁻¹ = x * (x * x ^ k)⁻¹ := by rw [pow_succ']
      _ = x * (x⁻¹ * (x ^ k)⁻¹) := by rw [mul_inv]
      _ = (x * x⁻¹) * (x ^ k)⁻¹ := by ring
      _ = (x ^ k)⁻¹ := by rw [mul_inv_cancel₀ hx0, one_mul]
  calc
    x ^ 2 / 2 * ((k : ℝ) * (k + 1) * (x ^ (k + 2))⁻¹) +
          (1 + (ν + (1 : ℝ) / 2) * x) * (-(k : ℝ) * (x ^ (k + 1))⁻¹)
        = (k : ℝ) * (k + 1) / 2 * (x ^ 2 * (x ^ (k + 2))⁻¹) +
            (-(k : ℝ)) * (x ^ (k + 1))⁻¹ +
            (-(k : ℝ)) * (ν + 1 / 2) * (x * (x ^ (k + 1))⁻¹) := by ring
    _ = (k : ℝ) * (k + 1) / 2 * (x ^ k)⁻¹ +
            (-(k : ℝ)) * (x ^ (k + 1))⁻¹ +
            (-(k : ℝ)) * (ν + 1 / 2) * (x ^ k)⁻¹ := by
          rw [hxpow, hxpow']
    _ = ((k : ℝ) ^ 2 / 2 - (k : ℝ) * ν) * (x ^ k)⁻¹ -
          (k : ℝ) * (x ^ (k + 1))⁻¹ := by ring

/-- Integrability of all negative integer moments of the perpetuity. -/
theorem integrable_pow_inv_perpetuity (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (ν : ℝ) (hν : ν < 0) (k : ℕ) :
    Integrable
      (fun ω => (∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s))⁻¹ ^ k) P := by
  cases k with
  | zero =>
    simp
  | succ k =>
    have hfin := expInt_zpow_neg_integrable P W hW 1 1 one_pos one_pos (k + 1)
    have hge := ae_perpetuity_ge_expInt P W hW ν hν
    have hmeas := aemeasurable_perpetuity P W hW ν
    have hfin' : Integrable (fun ω => Real.exp (-ν * (k + 1 : ℝ)) *
        (expInt W 1 0 1 ω)⁻¹ ^ (k + 1)) P := by
      refine (hfin.const_mul (Real.exp (-ν * (k + 1 : ℝ)))).congr ?_
      filter_upwards with ω
      simp only [zpow_neg, zpow_natCast]
      ring
    refine Integrable.mono' hfin' (hmeas.inv.pow_const (k + 1)).aestronglyMeasurable ?_
    filter_upwards [hge, hW.cont] with ω hgeω _hcont
    set A := ∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s)
    set E1 := expInt W 1 0 1 ω
    have hEpos : 0 < E1 := by
      have hc : Continuous fun s : ℝ => Real.exp (W s.toNNReal ω) := by fun_prop
      have hInt := intervalIntegral.integral_pos (by norm_num : (0 : ℝ) < 1) hc.continuousOn
        (fun _ _ => (Real.exp_pos _).le)
        ⟨0, ⟨le_rfl, zero_le_one⟩, by simpa using Real.exp_pos (W 0 ω)⟩
      simpa [E1, expInt] using hInt
    have hApos : 0 < A := lt_of_lt_of_le (mul_pos (Real.exp_pos ν) hEpos) hgeω
    have hbound : A⁻¹ ^ (k + 1) ≤ Real.exp (-ν * (k + 1 : ℝ)) * (E1⁻¹ ^ (k + 1)) := by
      have h1 : A⁻¹ ≤ (Real.exp ν * E1)⁻¹ :=
        inv_anti₀ (mul_pos (Real.exp_pos ν) hEpos) hgeω
      have h2 : A⁻¹ ≤ Real.exp (-ν) * E1⁻¹ := by
        calc A⁻¹ ≤ (Real.exp ν)⁻¹ * E1⁻¹ := by rwa [mul_inv] at h1
          _ = Real.exp (-ν) * E1⁻¹ := by rw [Real.exp_neg]
      have := pow_le_pow_left₀ (inv_nonneg.2 hApos.le) h2 (k + 1)
      calc A⁻¹ ^ (k + 1) ≤ (Real.exp (-ν) * E1⁻¹) ^ (k + 1) := this
        _ = Real.exp (-ν) ^ (k + 1) * E1⁻¹ ^ (k + 1) := mul_pow _ _ _
        _ = Real.exp (-ν * (k + 1 : ℝ)) * E1⁻¹ ^ (k + 1) := by
              rw [← Real.exp_nat_mul, Nat.cast_succ]
              congr 2
              ring
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (inv_nonneg.2 hApos.le) _)]
    exact hbound

/-- Reciprocal power moments of `Z_t` and `A` agree by stationarity. -/
theorem integral_pow_inv_Zproc_eq (P : Measure Ω) [IsProbabilityMeasure P]
    (W B : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (hB : IsBM P B)
    (hWB : IndepFun (fun ω => fun t : ℝ≥0 => W t ω) (fun ω => fun t : ℝ≥0 => B t ω) P)
    (ν : ℝ) (hν : ν < 0) (t : ℝ≥0) (k : ℕ) :
    ∫ ω, (Zproc W B 1 ν t ω)⁻¹ ^ k ∂P =
      ∫ ω, (∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s))⁻¹ ^ k ∂P := by
  set A : Ω → ℝ := fun ω => ∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s)
  have hAinv := integrable_pow_inv_perpetuity P W hW ν hν k
  have hApos := ae_perpetuity_pos P W hW ν hν
  have hZae := aemeasurable_Zproc P W B hW hB ν hν t
  have hmaps := Z_stationary_sigma_one P W B hW hB hWB ν hν t
  have hm0 : Measurable fun x : ℝ => ENNReal.ofReal (x⁻¹ ^ k) :=
    ENNReal.measurable_ofReal.comp (measurable_inv.pow_const k)
  have hAae := aemeasurable_perpetuity P W hW ν
  have hmomL : ∫⁻ ω, ENNReal.ofReal ((Zproc W B 1 ν t ω)⁻¹ ^ k) ∂P =
      ∫⁻ ω, ENNReal.ofReal ((A ω)⁻¹ ^ k) ∂P := by
    calc ∫⁻ ω, ENNReal.ofReal ((Zproc W B 1 ν t ω)⁻¹ ^ k) ∂P
        = ∫⁻ x, ENNReal.ofReal (x⁻¹ ^ k) ∂(P.map (Zproc W B 1 ν t)) :=
          (lintegral_map' hm0.aemeasurable hZae).symm
      _ = ∫⁻ x, ENNReal.ofReal (x⁻¹ ^ k) ∂(P.map A) := by
          simpa [A, one_mul] using congrArg (fun μ => ∫⁻ x, ENNReal.ofReal (x⁻¹ ^ k) ∂μ) hmaps
      _ = ∫⁻ ω, ENNReal.ofReal ((A ω)⁻¹ ^ k) ∂P := lintegral_map' hm0.aemeasurable hAae
  have hZpos : ∀ᵐ ω ∂P, 0 < Zproc W B 1 ν t ω := by
    filter_upwards [hApos] with ω hAp
    have hinter :
        0 ≤ ∫ u in (0 : ℝ)..(t : ℝ), Real.exp (-ν * u + B u.toNNReal ω) :=
      intervalIntegral.integral_nonneg (NNReal.coe_nonneg t) fun _ _ => (Real.exp_pos _).le
    have hY : 0 < A ω + ∫ u in (0 : ℝ)..(t : ℝ), Real.exp (-ν * u + B u.toNNReal ω) := by
      linarith [hAp]
    simpa [Zproc, A, one_mul] using mul_pos (Real.exp_pos _) hY
  have hnnZ : 0 ≤ᵐ[P] fun ω => (Zproc W B 1 ν t ω)⁻¹ ^ k := by
    filter_upwards [hZpos] with ω hp
    exact pow_nonneg (inv_pos.2 hp).le _
  have hnnA : 0 ≤ᵐ[P] fun ω => (A ω)⁻¹ ^ k := by
    filter_upwards [hApos] with ω hp
    exact pow_nonneg (inv_pos.2 hp).le _
  have hZinv : Integrable (fun ω => (Zproc W B 1 ν t ω)⁻¹ ^ k) P := by
    refine ⟨(hZae.inv.pow_const k).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnnZ, hmomL]
    exact (hasFiniteIntegral_iff_ofReal hnnA).1 hAinv.hasFiniteIntegral
  apply (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg_of_ae hnnZ)
    (integral_nonneg_of_ae hnnA)).1
  calc ENNReal.ofReal (∫ ω, (Zproc W B 1 ν t ω)⁻¹ ^ k ∂P)
      = ∫⁻ ω, ENNReal.ofReal ((Zproc W B 1 ν t ω)⁻¹ ^ k) ∂P :=
        ofReal_integral_eq_lintegral_ofReal hZinv hnnZ
    _ = ∫⁻ ω, ENNReal.ofReal ((A ω)⁻¹ ^ k) ∂P := hmomL
    _ = ENNReal.ofReal (∫ ω, (A ω)⁻¹ ^ k ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hAinv hnnA).symm

/-- Pathwise FTC: derivative of `Y ↦ Y⁻ᵏ` along the finite-variation factor of `Z`. -/
theorem pathwise_pow_inv_Y_identity (B : ℝ≥0 → ℝ) (_hBcont : Continuous B)
    (A : ℝ) (hA : 0 < A) (ν : ℝ) (k : ℕ) (hk : 0 < k) (t : ℝ≥0) :
    let Y : ℝ≥0 → ℝ := fun u =>
      A + ∫ s in (0 : ℝ)..(u : ℝ), Real.exp (-ν * s + B s.toNNReal)
    (Y t)⁻¹ ^ k - A⁻¹ ^ k =
      -(k : ℝ) * ∫ s in (0 : ℝ)..(t : ℝ),
        (Y s.toNNReal)⁻¹ ^ (k + 1) * Real.exp (-ν * s + B s.toNNReal) := by
  intro Y
  set g : ℝ → ℝ := fun s => Real.exp (-ν * s + B s.toNNReal)
  have hgcont : Continuous g := by simp only [g]; fun_prop
  have hgInt : ∀ a b, IntervalIntegrable g volume a b := fun _ _ => hgcont.intervalIntegrable _ _
  set YR : ℝ → ℝ := (fun _ => A) + fun x => ∫ s in (0 : ℝ)..x, g s
  have hYRpos : ∀ x : ℝ≥0, 0 < YR x := fun x => by
    have : 0 ≤ ∫ s in (0 : ℝ)..(x : ℝ), g s :=
      intervalIntegral.integral_nonneg (NNReal.coe_nonneg x) fun _ _ => (Real.exp_pos _).le
    change 0 < A + ∫ s in (0 : ℝ)..(x : ℝ), g s; linarith [hA]
  have hY_eq : ∀ u : ℝ≥0, Y u = YR u := fun u => rfl
  have hYRderiv : ∀ x : ℝ, 0 ≤ x → HasDerivAt YR (g x) x := by
    intro x _hx
    convert (hasDerivAt_const x A).add
      (intervalIntegral.integral_hasDerivAt_right (hgInt 0 x)
        (hgcont.stronglyMeasurableAtFilter volume (nhds x)) hgcont.continuousAt)
    simp
  have hprim : Continuous YR :=
    continuous_const.add (intervalIntegral.continuous_primitive hgInt 0)
  have hpow : ContinuousOn (fun y => (YR y)⁻¹ ^ k) (Icc (0 : ℝ) t) := by
    refine (hprim.continuousOn.inv₀ ?_).pow k
    intro y hy
    have : 0 < YR y.toNNReal := hYRpos _
    simpa [Real.coe_toNNReal y hy.1] using this.ne'
  have hder : ∀ x ∈ Ioo (0 : ℝ) (t : ℝ),
      HasDerivAt (fun y => (YR y)⁻¹ ^ k)
        (-(k : ℝ) * (YR x)⁻¹ ^ (k + 1) * g x) x := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1.le
    have hpos : YR x ≠ 0 := by
      have : 0 < YR x.toNNReal := hYRpos _
      simpa [Real.coe_toNNReal x hx0] using this.ne'
    have hd : HasDerivAt (fun y => (YR y)⁻¹) (-(YR x)⁻¹ ^ 2 * g x) x := by
      convert (hYRderiv x hx0).inv hpos using 1
      field_simp [hpos, pow_two]
    have hinvpow := hd.pow k
    convert hinvpow using 1
    cases k with
    | zero => cases hk
    | succ m =>
      simp [pow_succ]
      field_simp [hpos]
      ring
  have hinter : IntervalIntegrable
      (fun s => -(k : ℝ) * (YR s)⁻¹ ^ (k + 1) * g s) volume 0 (t : ℝ) := by
    have hc : ContinuousOn (fun s => -(k : ℝ) * (YR s)⁻¹ ^ (k + 1) * g s)
        (uIcc (0 : ℝ) t) := by
      rw [uIcc_of_le (NNReal.coe_nonneg t)]
      refine ContinuousOn.mul (ContinuousOn.mul continuousOn_const ?_) hgcont.continuousOn
      exact (hprim.continuousOn.inv₀ fun y hy => by
          have : 0 < YR y.toNNReal := hYRpos _
          simpa [Real.coe_toNNReal y hy.1] using this.ne').pow _
    exact hc.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (NNReal.coe_nonneg t) hpow hder hinter
  have h0 : YR 0 = A := by simp [YR]
  -- Rewrite the integral against `Y` and pull out the constant `-(k)`.
  have hInt :
      ∫ s in (0 : ℝ)..(t : ℝ), -(k : ℝ) * (YR s)⁻¹ ^ (k + 1) * g s =
        -(k : ℝ) * ∫ s in (0 : ℝ)..(t : ℝ),
          (Y s.toNNReal)⁻¹ ^ (k + 1) * Real.exp (-ν * s + B s.toNNReal) := by
    have h1 : ∫ s in (0 : ℝ)..(t : ℝ), -(k : ℝ) * (YR s)⁻¹ ^ (k + 1) * g s =
        -(k : ℝ) * ∫ s in (0 : ℝ)..(t : ℝ), (YR s)⁻¹ ^ (k + 1) * g s := by
      simp_rw [mul_assoc]
      rw [intervalIntegral.integral_const_mul]
    rw [h1]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hsI : s ∈ Icc (0 : ℝ) t := by
      simpa [uIcc_of_le (NNReal.coe_nonneg t)] using hs
    simp [hY_eq, g, Real.coe_toNNReal s hsI.1]
  calc (Y t)⁻¹ ^ k - A⁻¹ ^ k
      = (YR t)⁻¹ ^ k - A⁻¹ ^ k := by rw [hY_eq]
    _ = ∫ s in (0 : ℝ)..(t : ℝ), -(k : ℝ) * (YR s)⁻¹ ^ (k + 1) * g s := by
          simpa [h0] using hFTC.symm
    _ = -(k : ℝ) * ∫ s in (0 : ℝ)..(t : ℝ),
          (Y s.toNNReal)⁻¹ ^ (k + 1) * Real.exp (-ν * s + B s.toNNReal) := hInt

/-- Wald exponential for Brownian motion: `E[exp(α B_t − α² t / 2)] = 1`. -/
theorem integral_wald_exp_eq_one (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBM P B) (α : ℝ) (t : ℝ≥0) :
    ∫ ω, Real.exp (α * B t ω - α ^ 2 * (t : ℝ) / 2) ∂P = 1 := by
  have hpre : IsPreBrownianReal B P := hB.toIsPreBrownianReal
  have h := MathFin.integral_exp_mul_eval hpre t α
  have hcongr : (fun ω => Real.exp (α * B t ω - α ^ 2 * (t : ℝ) / 2)) =
      fun ω => Real.exp (-(α ^ 2 * (t : ℝ) / 2)) * Real.exp (α * B t ω) := by
    funext ω
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hcongr, integral_const_mul, h, ← Real.exp_add]
  ring_nf
  simp

/-- Joint integrability of `(s, ω) ↦ Z_s(ω)⁻ᵏ` on `(0, t] × Ω`. -/
theorem integrable_uncurry_pow_inv_Zproc (P : Measure Ω) [IsProbabilityMeasure P]
    (W B : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (hB : IsBM P B)
    (hWB : IndepFun (fun ω => fun t : ℝ≥0 => W t ω) (fun ω => fun t : ℝ≥0 => B t ω) P)
    (ν : ℝ) (hν : ν < 0) (t : ℝ≥0) (k : ℕ) :
    Integrable (Function.uncurry
      (fun s : ℝ => fun ω => (Zproc W B 1 ν s.toNNReal ω)⁻¹ ^ k))
      ((volume.restrict (uIoc (0 : ℝ) (t : ℝ))).prod P) := by
  classical
  have hasm : AEStronglyMeasurable
      (Function.uncurry (fun s : ℝ => fun ω => (Zproc W B 1 ν s.toNNReal ω)⁻¹ ^ k))
      ((volume.restrict (uIoc (0 : ℝ) (t : ℝ))).prod P) := by
    have h := (integrable_uncurry_inv_Zproc P W B hW hB hWB ν hν t).aestronglyMeasurable
    exact h.pow k
  rw [integrable_prod_iff hasm]
  refine ⟨?_, ?_⟩
  · refine ae_restrict_of_forall_mem measurableSet_uIoc fun s hs => ?_
    have hs0 : 0 ≤ s := by
      rw [uIoc_of_le (NNReal.coe_nonneg t)] at hs
      exact hs.1.le
    -- Integrability of Z_s^{-k} via stationarity = integrability of A^{-k}
    have hZ : Integrable (fun ω => (Zproc W B 1 ν s.toNNReal ω)⁻¹ ^ k) P := by
      have hA := integrable_pow_inv_perpetuity P W hW ν hν k
      have heq := integral_pow_inv_Zproc_eq P W B hW hB hWB ν hν s.toNNReal k
      -- reuse the integrability proof pattern from integral_pow_inv_Zproc_eq
      have hZae := aemeasurable_Zproc P W B hW hB ν hν s.toNNReal
      have hApos := ae_perpetuity_pos P W hW ν hν
      have hZpos : ∀ᵐ ω ∂P, 0 < Zproc W B 1 ν s.toNNReal ω := by
        filter_upwards [hApos] with ω hAp
        have hinter :
            0 ≤ ∫ u in (0 : ℝ)..(s.toNNReal : ℝ), Real.exp (-ν * u + B u.toNNReal ω) :=
          intervalIntegral.integral_nonneg (NNReal.coe_nonneg _) fun _ _ => (Real.exp_pos _).le
        have hY : 0 <
            (∫ u in Ioi (0 : ℝ), Real.exp (W u.toNNReal ω + ν * u)) +
              ∫ u in (0 : ℝ)..(s.toNNReal : ℝ), Real.exp (-ν * u + B u.toNNReal ω) := by
          linarith [hAp]
        simpa [Zproc, one_mul] using mul_pos (Real.exp_pos _) hY
      have hnnZ : 0 ≤ᵐ[P] fun ω => (Zproc W B 1 ν s.toNNReal ω)⁻¹ ^ k := by
        filter_upwards [hZpos] with ω hp; exact pow_nonneg (inv_pos.2 hp).le _
      have hnnA : 0 ≤ᵐ[P] fun ω =>
          (∫ u in Ioi (0 : ℝ), Real.exp (W u.toNNReal ω + ν * u))⁻¹ ^ k := by
        filter_upwards [hApos] with ω hp; exact pow_nonneg (inv_pos.2 hp).le _
      have hm0 : Measurable fun x : ℝ => ENNReal.ofReal (x⁻¹ ^ k) :=
        ENNReal.measurable_ofReal.comp (measurable_inv.pow_const k)
      have hmaps := Z_stationary_sigma_one P W B hW hB hWB ν hν s.toNNReal
      have hmomL : ∫⁻ ω, ENNReal.ofReal ((Zproc W B 1 ν s.toNNReal ω)⁻¹ ^ k) ∂P =
          ∫⁻ ω, ENNReal.ofReal
            ((∫ u in Ioi (0 : ℝ), Real.exp (W u.toNNReal ω + ν * u))⁻¹ ^ k) ∂P := by
        calc ∫⁻ ω, ENNReal.ofReal ((Zproc W B 1 ν s.toNNReal ω)⁻¹ ^ k) ∂P
            = ∫⁻ x, ENNReal.ofReal (x⁻¹ ^ k) ∂(P.map (Zproc W B 1 ν s.toNNReal)) :=
              (lintegral_map' hm0.aemeasurable hZae).symm
          _ = ∫⁻ x, ENNReal.ofReal (x⁻¹ ^ k) ∂(P.map
                (fun ω => ∫ u in Ioi (0 : ℝ), Real.exp (W u.toNNReal ω + ν * u))) := by
              simpa [one_mul] using congrArg (fun μ => ∫⁻ x, ENNReal.ofReal (x⁻¹ ^ k) ∂μ) hmaps
          _ = ∫⁻ ω, ENNReal.ofReal
                ((∫ u in Ioi (0 : ℝ), Real.exp (W u.toNNReal ω + ν * u))⁻¹ ^ k) ∂P :=
              lintegral_map' hm0.aemeasurable (aemeasurable_perpetuity P W hW ν)
      refine ⟨(hZae.inv.pow_const k).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal hnnZ, hmomL]
      exact (hasFiniteIntegral_iff_ofReal hnnA).1 hA.hasFiniteIntegral
    simpa [Function.uncurry, Real.coe_toNNReal s hs0] using hZ
  · have hvol : volume (uIoc (0 : ℝ) (t : ℝ)) < ∞ := by
      rw [uIoc_of_le (NNReal.coe_nonneg t), Real.volume_Ioc]; simp
    have : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) (t : ℝ))) :=
      ⟨by simp [Measure.restrict_apply MeasurableSet.univ]⟩
    set c : ℝ :=
      ∫ ω, (∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s))⁻¹ ^ k ∂P
    have hc : Integrable (fun _ : ℝ => c) (volume.restrict (uIoc (0 : ℝ) (t : ℝ))) :=
      integrable_const c
    refine hc.congr ?_
    refine ae_restrict_of_forall_mem measurableSet_uIoc fun s hs => ?_
    have hs0 : 0 ≤ s := by
      rw [uIoc_of_le (NNReal.coe_nonneg t)] at hs; exact hs.1.le
    have hnn : 0 ≤ᵐ[P] fun ω => (Zproc W B 1 ν s.toNNReal ω)⁻¹ ^ k := by
      have hApos := ae_perpetuity_pos P W hW ν hν
      filter_upwards [hApos] with ω hAp
      have hinter :
          0 ≤ ∫ u in (0 : ℝ)..(s.toNNReal : ℝ), Real.exp (-ν * u + B u.toNNReal ω) :=
        intervalIntegral.integral_nonneg (NNReal.coe_nonneg _) fun _ _ => (Real.exp_pos _).le
      have hY : 0 <
          (∫ u in Ioi (0 : ℝ), Real.exp (W u.toNNReal ω + ν * u)) +
            ∫ u in (0 : ℝ)..(s.toNNReal : ℝ), Real.exp (-ν * u + B u.toNNReal ω) := by
        linarith [hAp]
      exact pow_nonneg (inv_pos.2
        (by simpa [Zproc, one_mul] using mul_pos (Real.exp_pos _) hY)).le _
    simp only [Function.uncurry, Real.norm_eq_abs, c]
    have habs : ∫ ω, |(Zproc W B 1 ν s.toNNReal ω)⁻¹ ^ k| ∂P =
        ∫ ω, (Zproc W B 1 ν s.toNNReal ω)⁻¹ ^ k ∂P :=
      integral_congr_ae <| by
        filter_upwards [hnn] with ω hω; exact abs_of_nonneg hω
    rw [habs]
    exact (integral_pow_inv_Zproc_eq P W B hW hB hWB ν hν s.toNNReal k).symm

/-- Algebraic identity: `Z_u^{-k} = M_u · G_u` with Wald factor `M` and FV factor `G`. -/
theorem pathwise_Zpow_eq_wald_mul (B : ℝ≥0 → ℝ) (A : ℝ) (hA : 0 < A)
    (ν : ℝ) (k : ℕ) (u : ℝ≥0) :
    let Y : ℝ := A + ∫ s in (0 : ℝ)..(u : ℝ), Real.exp (-ν * s + B s.toNNReal)
    let Z : ℝ := Real.exp (ν * (u : ℝ) - B u) * Y
    let M : ℝ := Real.exp ((k : ℝ) * B u - (k : ℝ) ^ 2 * (u : ℝ) / 2)
    let G : ℝ := Real.exp (((k : ℝ) ^ 2 / 2 - (k : ℝ) * ν) * (u : ℝ)) * Y⁻¹ ^ k
    Z⁻¹ ^ k = M * G := by
  intro Y Z M G
  have hYpos : 0 < Y := by
    have : 0 ≤ ∫ s in (0 : ℝ)..(u : ℝ), Real.exp (-ν * s + B s.toNNReal) :=
      intervalIntegral.integral_nonneg (NNReal.coe_nonneg u) fun _ _ => (Real.exp_pos _).le
    linarith [hA]
  simp only [Z, M, G]
  have hYne : Y ≠ 0 := hYpos.ne'
  calc (Real.exp (ν * (u : ℝ) - B u) * Y)⁻¹ ^ k
      = (Real.exp (ν * (u : ℝ) - B u))⁻¹ ^ k * Y⁻¹ ^ k := by
          rw [mul_inv, mul_pow]
    _ = Real.exp (-(k : ℝ) * (ν * (u : ℝ) - B u)) * Y⁻¹ ^ k := by
          rw [← Real.exp_neg, ← Real.exp_nat_mul]
          congr 2; ring
    _ = Real.exp ((k : ℝ) * B u - (k : ℝ) ^ 2 * (u : ℝ) / 2) *
          (Real.exp (((k : ℝ) ^ 2 / 2 - (k : ℝ) * ν) * (u : ℝ)) * Y⁻¹ ^ k) := by
          rw [← mul_assoc, ← Real.exp_add]
          congr 1
          ring_nf

/-- Pathwise Wald–log factorization: `Z_t^{-k} = A^{-k} N_t H_t` with
`N` the Wald exponential and `H_t = exp(c t - k ∫₀ᵗ Z^{-1})`. -/
theorem pathwise_Zpow_eq_wald_H (B : ℝ≥0 → ℝ) (hBcont : Continuous B) (hB0 : B 0 = 0)
    (A : ℝ) (hA : 0 < A) (ν : ℝ) (k : ℕ) (t : ℝ≥0) :
    let Y : ℝ≥0 → ℝ := fun u =>
      A + ∫ s in (0 : ℝ)..(u : ℝ), Real.exp (-ν * s + B s.toNNReal)
    let Z : ℝ≥0 → ℝ := fun u => Real.exp (ν * (u : ℝ) - B u) * Y u
    let N : ℝ≥0 → ℝ := fun u => Real.exp ((k : ℝ) * B u - (k : ℝ) ^ 2 * (u : ℝ) / 2)
    let c : ℝ := (k : ℝ) ^ 2 / 2 - (k : ℝ) * ν
    let H : ℝ≥0 → ℝ := fun u =>
      Real.exp (c * (u : ℝ) - (k : ℝ) * ∫ s in (0 : ℝ)..(u : ℝ), (Z s.toNNReal)⁻¹)
    (Z t)⁻¹ ^ k = A⁻¹ ^ k * N t * H t := by
  intro Y Z N c H
  have hlog := pathwise_log_Z_identity B hBcont hB0 A hA ν t
  -- hlog: log(Z t) - log A = ν t - B t + ∫ (Z)^{-1}
  have hZpos : 0 < Z t := by
    have hYpos : 0 < Y t := by
      have : 0 ≤ ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-ν * s + B s.toNNReal) :=
        intervalIntegral.integral_nonneg (NNReal.coe_nonneg t) fun _ _ => (Real.exp_pos _).le
      simp only [Y]; linarith [hA]
    simp only [Z]; exact mul_pos (Real.exp_pos _) hYpos
  have hform :
      Real.log (Z t) - Real.log A =
        ν * (t : ℝ) - B t + ∫ s in (0 : ℝ)..(t : ℝ), (Z s.toNNReal)⁻¹ := hlog
  have hZexp : (Z t)⁻¹ ^ k = Real.exp (-(k : ℝ) * Real.log (Z t)) := by
    rw [← Real.rpow_natCast, Real.inv_rpow hZpos.le, Real.rpow_def_of_pos hZpos,
      ← Real.exp_neg]
    congr 1; ring
  have hAexp : A⁻¹ ^ k = Real.exp (-(k : ℝ) * Real.log A) := by
    rw [← Real.rpow_natCast, Real.inv_rpow hA.le, Real.rpow_def_of_pos hA,
      ← Real.exp_neg]
    congr 1; ring
  have hexp : (Z t)⁻¹ ^ k = A⁻¹ ^ k *
      Real.exp (-(k : ℝ) * (Real.log (Z t) - Real.log A)) := by
    rw [hZexp, hAexp, ← Real.exp_add]
    congr 1; ring
  rw [hexp, hform]
  simp only [N, H, c]
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  ring_nf

/-- Pathwise FTC for the finite-variation factor `H` in `pathwise_Zpow_eq_wald_H`. -/
theorem pathwise_H_ftc (B : ℝ≥0 → ℝ) (hBcont : Continuous B) (_hB0 : B 0 = 0)
    (A : ℝ) (hA : 0 < A) (ν : ℝ) (k : ℕ) (t : ℝ≥0) :
    let Y : ℝ≥0 → ℝ := fun u =>
      A + ∫ s in (0 : ℝ)..(u : ℝ), Real.exp (-ν * s + B s.toNNReal)
    let Z : ℝ≥0 → ℝ := fun u => Real.exp (ν * (u : ℝ) - B u) * Y u
    let c : ℝ := (k : ℝ) ^ 2 / 2 - (k : ℝ) * ν
    let H : ℝ≥0 → ℝ := fun u =>
      Real.exp (c * (u : ℝ) - (k : ℝ) * ∫ s in (0 : ℝ)..(u : ℝ), (Z s.toNNReal)⁻¹)
    H t - 1 =
      ∫ s in (0 : ℝ)..(t : ℝ), (c - (k : ℝ) * (Z s.toNNReal)⁻¹) * H s.toNNReal := by
  intro Y Z c H
  set invZ : ℝ → ℝ := fun s => (Z s.toNNReal)⁻¹
  have hZpos : ∀ u : ℝ≥0, 0 < Z u := fun u => by
    have hYpos : 0 < Y u := by
      have : 0 ≤ ∫ s in (0 : ℝ)..(u : ℝ), Real.exp (-ν * s + B s.toNNReal) :=
        intervalIntegral.integral_nonneg (NNReal.coe_nonneg u) fun _ _ => (Real.exp_pos _).le
      simp only [Y]; linarith [hA]
    simp only [Z]; exact mul_pos (Real.exp_pos _) hYpos
  have hg : Continuous fun s : ℝ => Real.exp (-ν * s + B s.toNNReal) := by fun_prop
  have hZcont : Continuous Z := by
    refine (Real.continuous_exp.comp ?_).mul ?_
    · exact (continuous_const.mul continuous_subtype_val).sub hBcont
    · exact continuous_const.add <|
        (intervalIntegral.continuous_primitive (fun _ _ => hg.intervalIntegrable _ _) 0).comp
          continuous_subtype_val
  have hinvCont : Continuous invZ := by
    simp only [invZ]
    exact (hZcont.comp continuous_real_toNNReal).inv₀ fun x => (hZpos x.toNNReal).ne'
  set φR : ℝ → ℝ := fun x => c * x - (k : ℝ) * ∫ s in (0 : ℝ)..x, invZ s
  have hφderiv : ∀ x : ℝ, 0 ≤ x → HasDerivAt φR (c - (k : ℝ) * invZ x) x := by
    intro x _hx
    have hinter0x : IntervalIntegrable invZ volume 0 x := hinvCont.intervalIntegrable _ _
    have hInt :=
      (intervalIntegral.integral_hasDerivAt_right hinter0x
        (hinvCont.stronglyMeasurableAtFilter volume (nhds x)) hinvCont.continuousAt).const_mul
        (k : ℝ)
    have hid : HasDerivAt (fun y : ℝ => c * y) c x := by
      convert (hasDerivAt_id x).const_mul c using 1
      · rfl
      · ring
    exact hid.sub hInt
  have hH0 : φR 0 = 0 := by simp [φR, intervalIntegral.integral_same]
  have hHR : ∀ u : ℝ≥0, H u = Real.exp (φR u) := fun u => by simp only [H, φR, invZ]
  have hder : ∀ x ∈ Ioo (0 : ℝ) (t : ℝ),
      HasDerivAt (fun y => Real.exp (φR y))
        ((c - (k : ℝ) * invZ x) * Real.exp (φR x)) x := by
    intro x hx
    have h := (hφderiv x hx.1.le).exp
    convert h using 1
    ring
  have hφcont : Continuous φR :=
    (continuous_const.mul continuous_id).sub
      (continuous_const.mul (intervalIntegral.continuous_primitive
        (fun _ _ => hinvCont.intervalIntegrable _ _) 0))
  have hcontOn : ContinuousOn (fun y => Real.exp (φR y)) (Icc (0 : ℝ) t) :=
    Real.continuous_exp.comp hφcont |>.continuousOn
  have hinter : IntervalIntegrable
      (fun s => (c - (k : ℝ) * invZ s) * Real.exp (φR s)) volume 0 (t : ℝ) := by
    have hc : ContinuousOn
        (fun s => (c - (k : ℝ) * invZ s) * Real.exp (φR s)) (uIcc (0 : ℝ) t) := by
      rw [uIcc_of_le (NNReal.coe_nonneg t)]
      exact (continuousOn_const.sub (continuousOn_const.mul hinvCont.continuousOn)).mul
        (Real.continuous_exp.comp hφcont).continuousOn
    exact hc.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (NNReal.coe_nonneg t) hcontOn hder hinter
  have hcongr : ∫ s in (0 : ℝ)..(t : ℝ),
      (c - (k : ℝ) * invZ s) * Real.exp (φR s) =
      ∫ s in (0 : ℝ)..(t : ℝ), (c - (k : ℝ) * (Z s.toNNReal)⁻¹) * H s.toNNReal := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hsI : s ∈ Icc (0 : ℝ) t := by
      simpa [uIcc_of_le (NNReal.coe_nonneg t)] using hs
    simp only [invZ, hHR, Real.coe_toNNReal s hsI.1]
  calc H t - 1
      = Real.exp (φR t) - Real.exp (φR 0) := by rw [hHR, hH0, Real.exp_zero]
    _ = ∫ s in (0 : ℝ)..(t : ℝ), (c - (k : ℝ) * invZ s) * Real.exp (φR s) := by
          simpa using hFTC.symm
    _ = ∫ s in (0 : ℝ)..(t : ℝ), (c - (k : ℝ) * (Z s.toNNReal)⁻¹) * H s.toNNReal := hcongr

/-- On the product space, `A⁻ᵏ` (from the first BM) is independent of the Wald factor
`N_t = exp(k B_t − k² t/2)` (from the second BM), and `E[A⁻ᵏ N_t] = E[A⁻ᵏ]`. -/
theorem integral_Ainv_mul_wald_eq (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (ν : ℝ) (hν : ν < 0) (k : ℕ) (t : ℝ≥0) :
    let Q : Measure (Ω × Ω) := P.prod P
    let W1 : ℝ≥0 → Ω × Ω → ℝ := fun u p => W u p.1
    let Bproc : ℝ≥0 → Ω × Ω → ℝ := fun u p => W u p.2
    let A : Ω × Ω → ℝ := fun p =>
      ∫ s in Ioi (0 : ℝ), Real.exp (W1 s.toNNReal p + ν * s)
    let N : Ω × Ω → ℝ := fun p =>
      Real.exp ((k : ℝ) * Bproc t p - (k : ℝ) ^ 2 * (t : ℝ) / 2)
    ∫ p, (A p)⁻¹ ^ k * N p ∂Q = ∫ p, (A p)⁻¹ ^ k ∂Q := by
  intro Q W1 Bproc A N
  set f : Ω → ℝ := fun ω =>
    (∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s))⁻¹ ^ k
  set g : Ω → ℝ := fun ω =>
    Real.exp ((k : ℝ) * W t ω - (k : ℝ) ^ 2 * (t : ℝ) / 2)
  have hf : Integrable f P := integrable_pow_inv_perpetuity P W hW ν hν k
  have hg : Integrable g P := by
    have hcongr : g = fun ω =>
        Real.exp (-((k : ℝ) ^ 2 * (t : ℝ) / 2)) * Real.exp ((k : ℝ) * W t ω) := by
      funext ω; simp only [g]; rw [← Real.exp_add]; congr 1; ring
    rw [hcongr]
    exact (hW.toIsPreBrownianReal.hasLaw_eval t).integrable_comp
      (f := fun x : ℝ => Real.exp ((k : ℝ) * x)) (integrable_exp_mul_gaussianReal (k : ℝ))
      |>.const_mul _
  have hAe : (fun p => (A p)⁻¹ ^ k) = fun p => f p.1 := by
    funext p; simp [A, W1, f]
  have hNe : N = fun p => g p.2 := by
    funext p; simp [N, Bproc, g]
  have hprod : ∫ p, (A p)⁻¹ ^ k * N p ∂Q = (∫ ω, f ω ∂P) * ∫ ω, g ω ∂P := by
    have hpt : (fun p => (A p)⁻¹ ^ k * N p) = fun p => f p.1 * g p.2 := by
      funext p; rw [show (A p)⁻¹ ^ k = f p.1 from congrFun hAe p,
        show N p = g p.2 from congrFun hNe p]
    rw [hpt]
    simpa [Q] using integral_prod_mul (μ := P) (ν := P) f g
  have hN1 : ∫ ω, g ω ∂P = 1 := by
    simpa [g] using integral_wald_exp_eq_one P W hW (k : ℝ) t
  have hA : ∫ p, (A p)⁻¹ ^ k ∂Q = ∫ ω, f ω ∂P := by
    rw [hAe]
    simpa [Q, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] using
      integral_fun_fst (μ := P) (ν := P) f
  rw [hprod, hN1, mul_one, hA]

/-- Path functional: reciprocal power of the finite-horizon `Z` built from a continuous path
with fixed initial capital `A`. -/
def zpowPath (ν A : ℝ) (s : ℝ≥0) (m : ℕ) (x : C(ℝ≥0, ℝ)) : ℝ :=
  (Real.exp (ν * (s : ℝ) - x s) *
    (A + ∫ v in (0 : ℝ)..(s : ℝ), Real.exp (-ν * v + x v.toNNReal)))⁻¹ ^ m

theorem measurable_zpowPath (ν A : ℝ) (s : ℝ≥0) (m : ℕ) :
    Measurable (zpowPath ν A s m) := by
  have hI : Measurable fun x : C(ℝ≥0, ℝ) =>
      ∫ v in (0 : ℝ)..(s : ℝ), Real.exp (-ν * v + x v.toNNReal) :=
    measurable_pathIntegral (fun v b => Real.exp (-ν * v + b)) (by fun_prop) s
  have hE : Measurable fun x : C(ℝ≥0, ℝ) => Real.exp (ν * (s : ℝ) - x s) :=
    Real.measurable_exp.comp
      ((measurable_const.sub (ContinuousMap.measurable_eval s)))
  exact (((hE.mul (measurable_const.add hI)).inv).pow_const m)

/-- For fixed initial capital `A > 0`, the Wald increment after time `s` is independent of
`Z_s` (which depends on `B` only through `[0, s]`), hence
`E[D_{s,t} Z_s^{-m}] = E[Z_s^{-m}]`. -/
theorem integral_waldIncrement_mul_Zpow_fixedA (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBM P B) (A : ℝ) (hA : 0 < A) (ν : ℝ)
    (s t : ℝ≥0) (hst : s ≤ t) (k m : ℕ) :
    let Z : ℝ≥0 → Ω → ℝ := fun u ω =>
      Real.exp (ν * (u : ℝ) - B u ω) *
        (A + ∫ v in (0 : ℝ)..(u : ℝ), Real.exp (-ν * v + B v.toNNReal ω))
    let D : Ω → ℝ := fun ω =>
      Real.exp ((k : ℝ) * (B t ω - B s ω) - (k : ℝ) ^ 2 * ((t : ℝ) - (s : ℝ)) / 2)
    ∫ ω, D ω * (Z s ω)⁻¹ ^ m ∂P = ∫ ω, (Z s ω)⁻¹ ^ m ∂P := by
  intro Z D
  have hS : IsBM P (fun u ω => B (s + u) ω - B s ω) := hB.shift s
  have hind : IndepFun (fun ω => stopPath s (bmPath hB ω)) (bmPath hS) P := by
    refine indepFun_path_of_ae_eq P _ _
      (fun ω u => B (min u s) ω) (fun ω u => B (s + u) ω - B s ω) ?_ ?_ (bmPath_ae_eq hS)
    · have hψ : Measurable (fun (y : Set.Iic s → ℝ) (u : ℝ≥0) => y ⟨min u s, min_le_right u s⟩) :=
        measurable_pi_iff.2 fun _ => measurable_pi_apply _
      exact ((hB.toIsPreBrownianReal.indepFun_shift s).comp measurable_id hψ).symm
    · filter_upwards [bmPath_ae_eq hB] with ω h u
      simp [stopPath, h]
  have hZae : (fun ω => (Z s ω)⁻¹ ^ m) =ᵐ[P]
      fun ω => zpowPath ν A s m (stopPath s (bmPath hB ω)) := by
    filter_upwards [bmPath_ae_eq hB] with ω h
    have hsTop : stopPath s (bmPath hB ω) s = B s ω := by
      simp [stopPath, h]
    have hInt : ∫ v in (0 : ℝ)..(s : ℝ),
          Real.exp (-ν * v + stopPath s (bmPath hB ω) v.toNNReal) =
        ∫ v in (0 : ℝ)..(s : ℝ), Real.exp (-ν * v + B v.toNNReal ω) := by
      refine intervalIntegral.integral_congr fun v hv => ?_
      have hvI : v ∈ Icc (0 : ℝ) s := by
        simpa [uIcc_of_le (NNReal.coe_nonneg s)] using hv
      have hle : v.toNNReal ≤ s := Real.toNNReal_le_iff_le_coe.mpr hvI.2
      simp [stopPath, min_eq_left hle, h]
    simp only [zpowPath, Z, hsTop, hInt]
  have hDae : D =ᵐ[P] fun ω =>
      Real.exp ((k : ℝ) * bmPath hS ω (t - s) -
        (k : ℝ) ^ 2 * ((t : ℝ) - (s : ℝ)) / 2) := by
    filter_upwards [bmPath_ae_eq hS] with ω h
    simp only [D, h, add_tsub_cancel_of_le hst]
  have hWald : Measurable fun x : C(ℝ≥0, ℝ) =>
      Real.exp ((k : ℝ) * x (t - s) - (k : ℝ) ^ 2 * ((t : ℝ) - (s : ℝ)) / 2) :=
    Real.measurable_exp.comp
      (((ContinuousMap.measurable_eval (t - s)).const_mul (k : ℝ)).sub measurable_const)
  have hmStop : Measurable (fun ω => stopPath s (bmPath hB ω)) :=
    (measurable_stopPath s).comp (measurable_bmPath hB)
  have hZpath : Measurable fun ω => zpowPath ν A s m (stopPath s (bmPath hB ω)) :=
    (measurable_zpowPath ν A s m).comp hmStop
  have hDpath : Measurable fun ω =>
      Real.exp ((k : ℝ) * bmPath hS ω (t - s) -
        (k : ℝ) ^ 2 * ((t : ℝ) - (s : ℝ)) / 2) :=
    hWald.comp (measurable_bmPath hS)
  have hind' : IndepFun
      (fun ω => zpowPath ν A s m (stopPath s (bmPath hB ω)))
      (fun ω => Real.exp ((k : ℝ) * bmPath hS ω (t - s) -
        (k : ℝ) ^ 2 * ((t : ℝ) - (s : ℝ)) / 2)) P :=
    hind.comp (measurable_zpowPath ν A s m) hWald
  have hZint : Integrable (fun ω => (Z s ω)⁻¹ ^ m) P := by
    set C : ℝ := A⁻¹ ^ m * Real.exp (-(m : ℝ) * ν * (s : ℝ))
    have hexp : Integrable (fun ω => Real.exp ((m : ℝ) * B s ω)) P :=
      (hB.toIsPreBrownianReal.hasLaw_eval s).integrable_comp
        (f := fun x => Real.exp ((m : ℝ) * x)) (integrable_exp_mul_gaussianReal (m : ℝ))
    have hbound : Integrable (fun ω => C * Real.exp ((m : ℝ) * B s ω)) P :=
      hexp.const_mul C
    refine hbound.mono' ?_ ?_
    · exact (hZpath.aemeasurable.congr hZae.symm).aestronglyMeasurable
    · filter_upwards with ω
      have hY : 0 ≤ ∫ v in (0 : ℝ)..(s : ℝ), Real.exp (-ν * v + B v.toNNReal ω) :=
        intervalIntegral.integral_nonneg (NNReal.coe_nonneg s) fun _ _ => (Real.exp_pos _).le
      have hZge : Real.exp (ν * (s : ℝ) - B s ω) * A ≤ Z s ω := by
        simp only [Z]; exact mul_le_mul_of_nonneg_left (by linarith [hA]) (Real.exp_pos _).le
      have hZpos : 0 < Z s ω := lt_of_lt_of_le (mul_pos (Real.exp_pos _) hA) hZge
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (inv_pos.2 hZpos).le _)]
      have hle : (Z s ω)⁻¹ ^ m ≤ (Real.exp (ν * (s : ℝ) - B s ω) * A)⁻¹ ^ m :=
        pow_le_pow_left₀ (inv_nonneg.2 hZpos.le)
          (inv_anti₀ (mul_pos (Real.exp_pos _) hA) hZge) m
      refine hle.trans (le_of_eq ?_)
      simp only [C]
      rw [mul_inv, mul_pow]
      have hexp' : (Real.exp (ν * (s : ℝ) - B s ω))⁻¹ ^ m =
          Real.exp (-(m : ℝ) * (ν * (s : ℝ) - B s ω)) := by
        rw [← Real.exp_neg, ← Real.exp_nat_mul]
        congr 1; ring
      have hmul : -(m : ℝ) * (ν * (s : ℝ) - B s ω) =
          -(m : ℝ) * ν * (s : ℝ) + (m : ℝ) * B s ω := by ring
      rw [hexp', hmul, Real.exp_add]
      ring
  have hDint : Integrable D P := by
    set cD : ℝ := Real.exp (-((k : ℝ) ^ 2 * ((t : ℝ) - (s : ℝ)) / 2))
    have hcongr : D = fun ω =>
        cD * Real.exp ((k : ℝ) * (B (s + (t - s)) ω - B s ω)) := by
      funext ω; simp only [D, cD, add_tsub_cancel_of_le hst]; rw [← Real.exp_add]; congr 1; ring
    rw [hcongr]
    exact ((hS.toIsPreBrownianReal.hasLaw_eval (t - s)).integrable_comp
      (f := fun x => Real.exp ((k : ℝ) * x))
      (integrable_exp_mul_gaussianReal (k : ℝ))).const_mul cD
  have hts : ((t - s : ℝ≥0) : ℝ) = (t : ℝ) - (s : ℝ) := NNReal.coe_sub hst
  have hD1 : ∫ ω, D ω ∂P = 1 := by
    have h := integral_wald_exp_eq_one P (fun u ω => B (s + u) ω - B s ω) hS (k : ℝ) (t - s)
    refine Eq.trans ?_ h
    refine integral_congr_ae ?_
    filter_upwards with ω
    simp only [D, add_tsub_cancel_of_le hst, hts]
  have hmul :
      ∫ ω, Real.exp ((k : ℝ) * bmPath hS ω (t - s) -
            (k : ℝ) ^ 2 * ((t : ℝ) - (s : ℝ)) / 2) *
          zpowPath ν A s m (stopPath s (bmPath hB ω)) ∂P =
        (∫ ω, Real.exp ((k : ℝ) * bmPath hS ω (t - s) -
            (k : ℝ) ^ 2 * ((t : ℝ) - (s : ℝ)) / 2) ∂P) *
          ∫ ω, zpowPath ν A s m (stopPath s (bmPath hB ω)) ∂P := by
    simpa [Pi.mul_apply] using
      hind'.symm.integral_mul_eq_mul_integral hDpath.aestronglyMeasurable
        hZpath.aestronglyMeasurable
  have hD1' : ∫ ω, Real.exp ((k : ℝ) * bmPath hS ω (t - s) -
      (k : ℝ) ^ 2 * ((t : ℝ) - (s : ℝ)) / 2) ∂P = 1 :=
    (integral_congr_ae hDae).symm.trans hD1
  have hleft : ∫ ω, D ω * (Z s ω)⁻¹ ^ m ∂P =
      ∫ ω, Real.exp ((k : ℝ) * bmPath hS ω (t - s) -
          (k : ℝ) ^ 2 * ((t : ℝ) - (s : ℝ)) / 2) *
        zpowPath ν A s m (stopPath s (bmPath hB ω)) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hDae, hZae] with ω hDω hZω
    rw [hDω, hZω, mul_comm]
  have hright : ∫ ω, (Z s ω)⁻¹ ^ m ∂P =
      ∫ ω, zpowPath ν A s m (stopPath s (bmPath hB ω)) ∂P :=
    integral_congr_ae hZae
  rw [hleft, hmul, hD1', one_mul, hright]

/-- Integrability of the Wald-increment times `Z_s^{-m}` on the product space. -/
theorem integrable_waldIncrement_mul_Zpow (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (ν : ℝ) (hν : ν < 0)
    (s t : ℝ≥0) (hst : s ≤ t) (k m : ℕ) :
    let Q : Measure (Ω × Ω) := P.prod P
    let W1 : ℝ≥0 → Ω × Ω → ℝ := fun u p => W u p.1
    let Bproc : ℝ≥0 → Ω × Ω → ℝ := fun u p => W u p.2
    let D : Ω × Ω → ℝ := fun p =>
      Real.exp ((k : ℝ) * (Bproc t p - Bproc s p) - (k : ℝ) ^ 2 * ((t : ℝ) - (s : ℝ)) / 2)
    Integrable (fun p => D p * (Zproc W1 Bproc 1 ν s p)⁻¹ ^ m) Q := by
  intro Q W1 Bproc D
  have hW1 : IsBM Q W1 := isBM_prod_fst hW
  have hB : IsBM Q Bproc := isBM_prod_snd hW
  set A0 : Ω → ℝ := fun ω => ∫ u in Ioi (0 : ℝ), Real.exp (W u.toNNReal ω + ν * u)
  set f : Ω → ℝ := fun ω => (A0 ω)⁻¹ ^ m
  set g : Ω → ℝ := fun ω =>
    Real.exp (-(m : ℝ) * ν * (s : ℝ)) *
      Real.exp ((k : ℝ) * (W t ω - W s ω) - (k : ℝ) ^ 2 * ((t : ℝ) - (s : ℝ)) / 2) *
        Real.exp ((m : ℝ) * W s ω)
  have hf : Integrable f P := integrable_pow_inv_perpetuity P W hW ν hν m
  have hg : Integrable g P := by
    set c0 : ℝ :=
      Real.exp (-(m : ℝ) * ν * (s : ℝ) - (k : ℝ) ^ 2 * ((t : ℝ) - (s : ℝ)) / 2)
    have hS : IsBM P (fun u ω => W (s + u) ω - W s ω) := hW.shift s
    have hInc : Integrable (fun ω => Real.exp ((k : ℝ) * (W (s + (t - s)) ω - W s ω))) P :=
      (hS.toIsPreBrownianReal.hasLaw_eval (t - s)).integrable_comp
        (f := fun x => Real.exp ((k : ℝ) * x)) (integrable_exp_mul_gaussianReal (k : ℝ))
    have hBs : Integrable (fun ω => Real.exp ((m : ℝ) * W s ω)) P :=
      (hW.toIsPreBrownianReal.hasLaw_eval s).integrable_comp
        (f := fun x => Real.exp ((m : ℝ) * x)) (integrable_exp_mul_gaussianReal (m : ℝ))
    have hind : IndepFun (fun ω => Real.exp ((k : ℝ) * (W (s + (t - s)) ω - W s ω)))
        (fun ω => Real.exp ((m : ℝ) * W s ω)) P := by
      have hsh := hW.toIsPreBrownianReal.indepFun_shift s
      have hψ1 : Measurable fun y : ℝ≥0 → ℝ => Real.exp ((k : ℝ) * y (t - s)) := by fun_prop
      have hψ2 : Measurable fun x : Set.Iic s → ℝ =>
          Real.exp ((m : ℝ) * x ⟨s, (mem_Iic.mpr le_rfl)⟩) := by fun_prop
      exact (hsh.comp hψ1 hψ2).congr
        (Eventually.of_forall fun ω => by simp [add_tsub_cancel_of_le hst])
        (Eventually.of_forall fun ω => rfl)
    have hprod := hind.integrable_mul hInc hBs
    refine (hprod.const_mul c0).congr (Eventually.of_forall fun ω => ?_)
    simp only [g, c0, Pi.mul_apply, add_tsub_cancel_of_le hst]
    have h1 : c0 * Real.exp ((k : ℝ) * (W t ω - W s ω)) =
        Real.exp (-(m : ℝ) * ν * (s : ℝ)) *
          Real.exp ((k : ℝ) * (W t ω - W s ω) - (k : ℝ) ^ 2 * ((t : ℝ) - (s : ℝ)) / 2) := by
      simp only [c0]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    calc c0 * (Real.exp ((k : ℝ) * (W t ω - W s ω)) * Real.exp ((m : ℝ) * W s ω))
        = (c0 * Real.exp ((k : ℝ) * (W t ω - W s ω))) * Real.exp ((m : ℝ) * W s ω) :=
            (mul_assoc _ _ _).symm
      _ = Real.exp (-(m : ℝ) * ν * (s : ℝ)) *
            Real.exp ((k : ℝ) * (W t ω - W s ω) - (k : ℝ) ^ 2 * ((t : ℝ) - (s : ℝ)) / 2) *
            Real.exp ((m : ℝ) * W s ω) := by
            rw [h1]
  have hindfg : IndepFun (fun p : Ω × Ω => f p.1) (fun p => g p.2) Q :=
    indepFun_prod₀ hf.aemeasurable hg.aemeasurable
  have hfg : Integrable (fun p : Ω × Ω => f p.1 * g p.2) Q :=
    hindfg.integrable_mul (hf.comp_fst P) (hg.comp_snd P)
  have hD_ae : AEMeasurable D Q :=
    Real.measurable_exp.comp_aemeasurable
      ((((hB.toIsPreBrownianReal.aemeasurable t).sub
          (hB.toIsPreBrownianReal.aemeasurable s)).const_mul (k : ℝ)).sub
        (aemeasurable_const (μ := Q)))
  have hasm : AEStronglyMeasurable
      (fun p => D p * (Zproc W1 Bproc 1 ν s p)⁻¹ ^ m) Q :=
    (hD_ae.mul ((aemeasurable_Zproc Q W1 Bproc hW1 hB ν hν s).inv.pow_const m)).aestronglyMeasurable
  refine hfg.mono' hasm ?_
  filter_upwards [ae_perpetuity_pos Q W1 hW1 ν hν] with p hAp
  have hinter :
      0 ≤ ∫ u in (0 : ℝ)..(s : ℝ), Real.exp (-ν * u + Bproc u.toNNReal p) :=
    intervalIntegral.integral_nonneg (NNReal.coe_nonneg s) fun _ _ => (Real.exp_pos _).le
  have hY : 0 <
      (∫ u in Ioi (0 : ℝ), Real.exp (W1 u.toNNReal p + ν * u)) +
        ∫ u in (0 : ℝ)..(s : ℝ), Real.exp (-ν * u + Bproc u.toNNReal p) := by
    linarith [hAp]
  have hZpos : 0 < Zproc W1 Bproc 1 ν s p := by
    simpa [Zproc, one_mul] using mul_pos (Real.exp_pos _) hY
  have hZge : Real.exp (ν * (s : ℝ) - Bproc s p) *
      (∫ u in Ioi (0 : ℝ), Real.exp (W1 u.toNNReal p + ν * u)) ≤
      Zproc W1 Bproc 1 ν s p := by
    simp only [Zproc, one_mul]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  have hle : (Zproc W1 Bproc 1 ν s p)⁻¹ ^ m ≤
      ((∫ u in Ioi (0 : ℝ), Real.exp (W1 u.toNNReal p + ν * u))⁻¹ ^ m) *
        Real.exp (-(m : ℝ) * (ν * (s : ℝ) - Bproc s p)) := by
    have hpow := pow_le_pow_left₀ (inv_nonneg.2 hZpos.le)
      (inv_anti₀ (mul_pos (Real.exp_pos _) hAp) hZge) m
    refine hpow.trans (le_of_eq ?_)
    set A := ∫ u in Ioi (0 : ℝ), Real.exp (W1 u.toNNReal p + ν * u)
    set e := Real.exp (ν * (s : ℝ) - Bproc s p)
    have he : e⁻¹ ^ m = Real.exp (-(m : ℝ) * (ν * (s : ℝ) - Bproc s p)) := by
      simp only [e]
      calc (Real.exp (ν * (s : ℝ) - Bproc s p))⁻¹ ^ m
          = Real.exp (-(ν * (s : ℝ) - Bproc s p)) ^ m := by rw [← Real.exp_neg]
        _ = Real.exp ((m : ℝ) * -(ν * (s : ℝ) - Bproc s p)) := by rw [← Real.exp_nat_mul]
        _ = Real.exp (-(m : ℝ) * (ν * (s : ℝ) - Bproc s p)) := by congr 1; ring
    calc (e * A)⁻¹ ^ m
        = (e⁻¹ * A⁻¹) ^ m := by rw [mul_inv]
      _ = e⁻¹ ^ m * A⁻¹ ^ m := by rw [mul_pow]
      _ = Real.exp (-(m : ℝ) * (ν * (s : ℝ) - Bproc s p)) * A⁻¹ ^ m := by rw [he]
      _ = A⁻¹ ^ m * Real.exp (-(m : ℝ) * (ν * (s : ℝ) - Bproc s p)) := mul_comm _ _
  have hDpos : 0 ≤ D p := (Real.exp_pos _).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hDpos (pow_nonneg (inv_pos.2 hZpos).le _))]
  calc D p * (Zproc W1 Bproc 1 ν s p)⁻¹ ^ m
      ≤ D p * (((∫ u in Ioi (0 : ℝ), Real.exp (W1 u.toNNReal p + ν * u))⁻¹ ^ m) *
          Real.exp (-(m : ℝ) * (ν * (s : ℝ) - Bproc s p))) :=
        mul_le_mul_of_nonneg_left hle hDpos
    _ = f p.1 * g p.2 := by
        simp only [f, g, A0, W1]
        have hexp : Real.exp (-(m : ℝ) * (ν * (s : ℝ) - Bproc s p)) =
            Real.exp (-(m : ℝ) * ν * (s : ℝ)) * Real.exp ((m : ℝ) * Bproc s p) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [hexp]
        simp only [D, Bproc, mul_assoc]
        ac_rfl

/-- Product-space lift: Wald increment after `s` is mean-one against `Z_s^{-m}`. -/
theorem integral_waldIncrement_mul_Zpow (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (ν : ℝ) (hν : ν < 0)
    (s t : ℝ≥0) (hst : s ≤ t) (k m : ℕ) :
    let Q : Measure (Ω × Ω) := P.prod P
    let W1 : ℝ≥0 → Ω × Ω → ℝ := fun u p => W u p.1
    let Bproc : ℝ≥0 → Ω × Ω → ℝ := fun u p => W u p.2
    let D : Ω × Ω → ℝ := fun p =>
      Real.exp ((k : ℝ) * (Bproc t p - Bproc s p) - (k : ℝ) ^ 2 * ((t : ℝ) - (s : ℝ)) / 2)
    ∫ p, D p * (Zproc W1 Bproc 1 ν s p)⁻¹ ^ m ∂Q =
      ∫ p, (Zproc W1 Bproc 1 ν s p)⁻¹ ^ m ∂Q := by
  intro Q W1 Bproc D
  have hW1 : IsBM Q W1 := isBM_prod_fst hW
  have hB : IsBM Q Bproc := isBM_prod_snd hW
  have hWB := indepFun_prod_copies (W := W) hW
  have hAposP := ae_perpetuity_pos P W hW ν hν
  set A0 : Ω → ℝ := fun ω => ∫ u in Ioi (0 : ℝ), Real.exp (W u.toNNReal ω + ν * u)
  have hZint : Integrable (fun p => (Zproc W1 Bproc 1 ν s p)⁻¹ ^ m) Q := by
    have hA := integrable_pow_inv_perpetuity Q W1 hW1 ν hν m
    have hZae := aemeasurable_Zproc Q W1 Bproc hW1 hB ν hν s
    have hApos := ae_perpetuity_pos Q W1 hW1 ν hν
    have hZpos : ∀ᵐ p ∂Q, 0 < Zproc W1 Bproc 1 ν s p := by
      filter_upwards [hApos] with p hAp
      have hinter :
          0 ≤ ∫ u in (0 : ℝ)..(s : ℝ), Real.exp (-ν * u + Bproc u.toNNReal p) :=
        intervalIntegral.integral_nonneg (NNReal.coe_nonneg s) fun _ _ => (Real.exp_pos _).le
      have hY : 0 <
          (∫ u in Ioi (0 : ℝ), Real.exp (W1 u.toNNReal p + ν * u)) +
            ∫ u in (0 : ℝ)..(s : ℝ), Real.exp (-ν * u + Bproc u.toNNReal p) := by
        linarith [hAp]
      simpa [Zproc, one_mul] using mul_pos (Real.exp_pos _) hY
    have hnnZ : 0 ≤ᵐ[Q] fun p => (Zproc W1 Bproc 1 ν s p)⁻¹ ^ m := by
      filter_upwards [hZpos] with p hp; exact pow_nonneg (inv_pos.2 hp).le _
    have hnnA : 0 ≤ᵐ[Q] fun p =>
        (∫ u in Ioi (0 : ℝ), Real.exp (W1 u.toNNReal p + ν * u))⁻¹ ^ m := by
      filter_upwards [hApos] with p hp; exact pow_nonneg (inv_pos.2 hp).le _
    have hm0 : Measurable fun x : ℝ => ENNReal.ofReal (x⁻¹ ^ m) :=
      ENNReal.measurable_ofReal.comp (measurable_inv.pow_const m)
    have hmaps := Z_stationary_sigma_one Q W1 Bproc hW1 hB hWB ν hν s
    have hmomL : ∫⁻ p, ENNReal.ofReal ((Zproc W1 Bproc 1 ν s p)⁻¹ ^ m) ∂Q =
        ∫⁻ p, ENNReal.ofReal
          ((∫ u in Ioi (0 : ℝ), Real.exp (W1 u.toNNReal p + ν * u))⁻¹ ^ m) ∂Q := by
      calc ∫⁻ p, ENNReal.ofReal ((Zproc W1 Bproc 1 ν s p)⁻¹ ^ m) ∂Q
          = ∫⁻ x, ENNReal.ofReal (x⁻¹ ^ m) ∂(Q.map (Zproc W1 Bproc 1 ν s)) :=
            (lintegral_map' hm0.aemeasurable hZae).symm
        _ = ∫⁻ x, ENNReal.ofReal (x⁻¹ ^ m) ∂(Q.map
              (fun p => ∫ u in Ioi (0 : ℝ), Real.exp (W1 u.toNNReal p + ν * u))) := by
            simpa [one_mul] using congrArg (fun μ => ∫⁻ x, ENNReal.ofReal (x⁻¹ ^ m) ∂μ) hmaps
        _ = ∫⁻ p, ENNReal.ofReal
              ((∫ u in Ioi (0 : ℝ), Real.exp (W1 u.toNNReal p + ν * u))⁻¹ ^ m) ∂Q :=
            lintegral_map' hm0.aemeasurable (aemeasurable_perpetuity Q W1 hW1 ν)
    refine ⟨(hZae.inv.pow_const m).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnnZ, hmomL]
    exact (hasFiniteIntegral_iff_ofReal hnnA).1 hA.hasFiniteIntegral
  have hpoint : ∀ᵐ ω1 ∂P,
      ∫ ω2, D (ω1, ω2) * (Zproc W1 Bproc 1 ν s (ω1, ω2))⁻¹ ^ m ∂P =
        ∫ ω2, (Zproc W1 Bproc 1 ν s (ω1, ω2))⁻¹ ^ m ∂P := by
    filter_upwards [hAposP] with ω1 hA
    set A1 : ℝ := ∫ u in Ioi (0 : ℝ), Real.exp (W u.toNNReal ω1 + ν * u)
    simpa [Zproc, W1, Bproc, A1, one_mul, D] using
      integral_waldIncrement_mul_Zpow_fixedA P W hW A1 hA ν s t hst k m
  -- Dominant: `D · Z^{-m} ≤ (A₀^{-m} ∘ fst) · (D · e^{m B_s} · e^{-m ν s} ∘ snd)`.
  have hDZint : Integrable (fun p => D p * (Zproc W1 Bproc 1 ν s p)⁻¹ ^ m) Q :=
    integrable_waldIncrement_mul_Zpow P W hW ν hν s t hst k m
  have hL := MeasureTheory.integral_prod
    (f := fun p => D p * (Zproc W1 Bproc 1 ν s p)⁻¹ ^ m) hDZint
  have hR := MeasureTheory.integral_prod
    (f := fun p => (Zproc W1 Bproc 1 ν s p)⁻¹ ^ m) hZint
  rw [hL, hR]
  exact integral_congr_ae hpoint

/-- Integrability of reciprocal powers of the stationary process `Z`. -/
theorem integrable_pow_inv_Zproc (P : Measure Ω) [IsProbabilityMeasure P]
    (W B : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (hB : IsBM P B)
    (hWB : IndepFun (fun ω => fun t : ℝ≥0 => W t ω) (fun ω => fun t : ℝ≥0 => B t ω) P)
    (ν : ℝ) (hν : ν < 0) (t : ℝ≥0) (k : ℕ) :
    Integrable (fun ω => (Zproc W B 1 ν t ω)⁻¹ ^ k) P := by
  set A : Ω → ℝ := fun ω => ∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s)
  have hAinv := integrable_pow_inv_perpetuity P W hW ν hν k
  have hApos := ae_perpetuity_pos P W hW ν hν
  have hZae := aemeasurable_Zproc P W B hW hB ν hν t
  have hmaps := Z_stationary_sigma_one P W B hW hB hWB ν hν t
  have hm0 : Measurable fun x : ℝ => ENNReal.ofReal (x⁻¹ ^ k) :=
    ENNReal.measurable_ofReal.comp (measurable_inv.pow_const k)
  have hAae := aemeasurable_perpetuity P W hW ν
  have hmomL : ∫⁻ ω, ENNReal.ofReal ((Zproc W B 1 ν t ω)⁻¹ ^ k) ∂P =
      ∫⁻ ω, ENNReal.ofReal ((A ω)⁻¹ ^ k) ∂P := by
    calc ∫⁻ ω, ENNReal.ofReal ((Zproc W B 1 ν t ω)⁻¹ ^ k) ∂P
        = ∫⁻ x, ENNReal.ofReal (x⁻¹ ^ k) ∂(P.map (Zproc W B 1 ν t)) :=
          (lintegral_map' hm0.aemeasurable hZae).symm
      _ = ∫⁻ x, ENNReal.ofReal (x⁻¹ ^ k) ∂(P.map A) := by
          simpa [A, one_mul] using congrArg (fun μ => ∫⁻ x, ENNReal.ofReal (x⁻¹ ^ k) ∂μ) hmaps
      _ = ∫⁻ ω, ENNReal.ofReal ((A ω)⁻¹ ^ k) ∂P := lintegral_map' hm0.aemeasurable hAae
  have hZpos : ∀ᵐ ω ∂P, 0 < Zproc W B 1 ν t ω := by
    filter_upwards [hApos] with ω hAp
    have hinter :
        0 ≤ ∫ u in (0 : ℝ)..(t : ℝ), Real.exp (-ν * u + B u.toNNReal ω) :=
      intervalIntegral.integral_nonneg (NNReal.coe_nonneg t) fun _ _ => (Real.exp_pos _).le
    have hY : 0 < A ω + ∫ u in (0 : ℝ)..(t : ℝ), Real.exp (-ν * u + B u.toNNReal ω) := by
      linarith [hAp]
    simpa [Zproc, A, one_mul] using mul_pos (Real.exp_pos _) hY
  have hnnZ : 0 ≤ᵐ[P] fun ω => (Zproc W B 1 ν t ω)⁻¹ ^ k := by
    filter_upwards [hZpos] with ω hp; exact pow_nonneg (inv_pos.2 hp).le _
  have hnnA : 0 ≤ᵐ[P] fun ω => (A ω)⁻¹ ^ k := by
    filter_upwards [hApos] with ω hp; exact pow_nonneg (inv_pos.2 hp).le _
  refine ⟨(hZae.inv.pow_const k).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hnnZ, hmomL]
  exact (hasFiniteIntegral_iff_ofReal hnnA).1 hAinv.hasFiniteIntegral

/-- Pathwise Dynkin identity: expand `Z_t^{-k} - A^{-k}` via Wald–H and the FTC for `H`. -/
theorem pathwise_Zpow_drift_identity (B : ℝ≥0 → ℝ) (hBcont : Continuous B) (hB0 : B 0 = 0)
    (A : ℝ) (hA : 0 < A) (ν : ℝ) (k : ℕ) (t : ℝ≥0) :
    let Y : ℝ≥0 → ℝ := fun u =>
      A + ∫ s in (0 : ℝ)..(u : ℝ), Real.exp (-ν * s + B s.toNNReal)
    let Z : ℝ≥0 → ℝ := fun u => Real.exp (ν * (u : ℝ) - B u) * Y u
    let N : ℝ≥0 → ℝ := fun u => Real.exp ((k : ℝ) * B u - (k : ℝ) ^ 2 * (u : ℝ) / 2)
    let c : ℝ := (k : ℝ) ^ 2 / 2 - (k : ℝ) * ν
    (Z t)⁻¹ ^ k - A⁻¹ ^ k =
      A⁻¹ ^ k * (N t - 1) +
        ∫ s in (0 : ℝ)..(t : ℝ),
          Real.exp ((k : ℝ) * (B t - B s.toNNReal) - (k : ℝ) ^ 2 * ((t : ℝ) - s) / 2) *
            (c * (Z s.toNNReal)⁻¹ ^ k - (k : ℝ) * (Z s.toNNReal)⁻¹ ^ (k + 1)) := by
  intro Y Z N c
  let H : ℝ≥0 → ℝ := fun u =>
    Real.exp (c * (u : ℝ) - (k : ℝ) * ∫ s in (0 : ℝ)..(u : ℝ), (Z s.toNNReal)⁻¹)
  have hfact := pathwise_Zpow_eq_wald_H B hBcont hB0 A hA ν k t
  have hH := pathwise_H_ftc B hBcont hB0 A hA ν k t
  have hZeq : ∀ u : ℝ≥0, (Z u)⁻¹ ^ k = A⁻¹ ^ k * N u * H u := fun u =>
    pathwise_Zpow_eq_wald_H B hBcont hB0 A hA ν k u
  have hsplit : (Z t)⁻¹ ^ k - A⁻¹ ^ k =
      A⁻¹ ^ k * (N t - 1) + A⁻¹ ^ k * N t * (H t - 1) := by
    have := hfact
    -- this: (Z t)⁻¹^k = A⁻¹^k * N t * H t
    calc (Z t)⁻¹ ^ k - A⁻¹ ^ k
        = A⁻¹ ^ k * N t * H t - A⁻¹ ^ k := by rw [this]
      _ = A⁻¹ ^ k * (N t - 1) + A⁻¹ ^ k * N t * (H t - 1) := by ring
  have hinter :
      A⁻¹ ^ k * N t * (H t - 1) =
        ∫ s in (0 : ℝ)..(t : ℝ),
          Real.exp ((k : ℝ) * (B t - B s.toNNReal) - (k : ℝ) ^ 2 * ((t : ℝ) - s) / 2) *
            (c * (Z s.toNNReal)⁻¹ ^ k - (k : ℝ) * (Z s.toNNReal)⁻¹ ^ (k + 1)) := by
    have hH' : H t - 1 =
        ∫ s in (0 : ℝ)..(t : ℝ), (c - (k : ℝ) * (Z s.toNNReal)⁻¹) * H s.toNNReal := hH
    have hmul :
        A⁻¹ ^ k * N t * (H t - 1) =
          ∫ s in (0 : ℝ)..(t : ℝ),
            A⁻¹ ^ k * N t * ((c - (k : ℝ) * (Z s.toNNReal)⁻¹) * H s.toNNReal) := by
      rw [hH', ← intervalIntegral.integral_const_mul]
    refine hmul.trans ?_
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hs0 : 0 ≤ s :=
      (show s ∈ Icc (0 : ℝ) t by
        simpa [uIcc_of_le (NNReal.coe_nonneg t)] using hs).1
    have hsNN : (s.toNNReal : ℝ) = s := Real.coe_toNNReal s hs0
    have hZs := hZeq s.toNNReal
    have hNratio :
        N t / N s.toNNReal =
          Real.exp ((k : ℝ) * (B t - B s.toNNReal) - (k : ℝ) ^ 2 * ((t : ℝ) - s) / 2) := by
      simp only [N]
      have hNpos : Real.exp ((k : ℝ) * B s.toNNReal - (k : ℝ) ^ 2 * (s.toNNReal : ℝ) / 2) ≠ 0 :=
        (Real.exp_pos _).ne'
      field_simp [hNpos]
      rw [← Real.exp_add]
      congr 1
      simp only [hsNN]
      ring
    have hD :
        A⁻¹ ^ k * N t * ((c - (k : ℝ) * (Z s.toNNReal)⁻¹) * H s.toNNReal) =
          (N t / N s.toNNReal) *
            (c * (Z s.toNNReal)⁻¹ ^ k - (k : ℝ) * (Z s.toNNReal)⁻¹ ^ (k + 1)) := by
      have hNne : N s.toNNReal ≠ 0 := (Real.exp_pos _).ne'
      have hrew :
          A⁻¹ ^ k * N s.toNNReal * H s.toNNReal = (Z s.toNNReal)⁻¹ ^ k := by
        simpa [mul_assoc] using hZs.symm
      calc A⁻¹ ^ k * N t * ((c - (k : ℝ) * (Z s.toNNReal)⁻¹) * H s.toNNReal)
          = (N t / N s.toNNReal) *
              (A⁻¹ ^ k * N s.toNNReal * H s.toNNReal) *
              (c - (k : ℝ) * (Z s.toNNReal)⁻¹) := by
                field_simp [hNne]
        _ = (N t / N s.toNNReal) * (Z s.toNNReal)⁻¹ ^ k *
              (c - (k : ℝ) * (Z s.toNNReal)⁻¹) := by rw [hrew]
        _ = (N t / N s.toNNReal) *
              (c * (Z s.toNNReal)⁻¹ ^ k - (k : ℝ) * (Z s.toNNReal)⁻¹ ^ (k + 1)) := by
              ring
    rw [hD, hNratio]
  rw [hsplit, hinter]

/-- Wald increment as a continuous-path functional. -/
def waldIncrementFromPaths (k : ℕ) (t : ℝ≥0) (s : ℝ) (b : C(ℝ≥0, ℝ)) : ℝ :=
  Real.exp ((k : ℝ) * (b t - b s.toNNReal) - (k : ℝ) ^ 2 * ((t : ℝ) - s) / 2)

theorem continuous_waldIncrementFromPaths_time (k : ℕ) (t : ℝ≥0) (b : C(ℝ≥0, ℝ)) :
    Continuous fun s : ℝ => waldIncrementFromPaths k t s b := by
  unfold waldIncrementFromPaths; fun_prop

theorem measurable_waldIncrementFromPaths (k : ℕ) (t : ℝ≥0) (s : ℝ) :
    Measurable fun b : C(ℝ≥0, ℝ) => waldIncrementFromPaths k t s b := by
  unfold waldIncrementFromPaths; fun_prop

/-- Joint integrability of Wald-increment × `Z_s^{-m}` on `(0,1] × Q`. -/
theorem integrable_uncurry_waldIncrement_mul_Zpow (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (ν : ℝ) (hν : ν < 0) (k m : ℕ) :
    let Q : Measure (Ω × Ω) := P.prod P
    let W1 : ℝ≥0 → Ω × Ω → ℝ := fun u p => W u p.1
    let Bproc : ℝ≥0 → Ω × Ω → ℝ := fun u p => W u p.2
    Integrable (Function.uncurry fun s : ℝ => fun p =>
      Real.exp ((k : ℝ) * (Bproc 1 p - Bproc s.toNNReal p) -
          (k : ℝ) ^ 2 * ((1 : ℝ) - s) / 2) *
        (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ^ m)
      ((volume.restrict (uIoc (0 : ℝ) (1 : ℝ))).prod Q) := by
  intro Q W1 Bproc
  classical
  have hW1 : IsBM Q W1 := isBM_prod_fst hW
  have hB : IsBM Q Bproc := isBM_prod_snd hW
  have hWB := indepFun_prod_copies (W := W) hW
  set fPath : ℝ → Ω × Ω → ℝ := fun s p =>
    waldIncrementFromPaths k 1 s (bmPath hB p) *
      (invZFromPaths ν s.toNNReal (bmPath hW1 p) (bmPath hB p)) ^ m
  have hfMeas : Measurable (Function.uncurry fPath) :=
    measurable_uncurry_of_continuous_of_measurable
      (u := fPath)
      (fun p =>
        (continuous_waldIncrementFromPaths_time k 1 (bmPath hB p)).mul <|
          ((continuous_invZFromPaths_time ν (bmPath hW1 p) (bmPath hB p)).comp
              continuous_real_toNNReal).pow m)
      (fun s =>
        ((measurable_waldIncrementFromPaths k 1 s).comp (measurable_bmPath hB)).mul <|
          (((measurable_invZFromPaths ν s.toNNReal).comp
              ((measurable_bmPath hW1).prodMk (measurable_bmPath hB))).pow_const m))
  have hae : Function.uncurry fPath =ᵐ[(volume.restrict (uIoc (0 : ℝ) (1 : ℝ))).prod Q]
      Function.uncurry fun s : ℝ => fun p =>
        Real.exp ((k : ℝ) * (Bproc 1 p - Bproc s.toNNReal p) -
            (k : ℝ) ^ 2 * ((1 : ℝ) - s) / 2) *
          (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ^ m := by
    have hWae := bmPath_ae_eq hW1
    have hBae := bmPath_ae_eq hB
    have hApos := ae_perpetuity_pos Q W1 hW1 ν hν
    have hmod := (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (uIoc (0 : ℝ) (1 : ℝ))) (ν := Q)).ae
      ((hWae.and hBae).and hApos)
    filter_upwards [hmod] with p hp
    have hWw : ∀ u : ℝ≥0, bmPath hW1 p.2 u = W1 u p.2 := hp.1.1
    have hBb : ∀ u : ℝ≥0, bmPath hB p.2 u = Bproc u p.2 := hp.1.2
    have hAp : 0 < ∫ s in Ioi (0 : ℝ), Real.exp (W1 s.toNNReal p.2 + ν * s) := hp.2
    set τ : ℝ≥0 := p.1.toNNReal
    have hAeq : perpetuityPath ν (bmPath hW1 p.2) =
        ∫ s in Ioi (0 : ℝ), Real.exp (W1 s.toNNReal p.2 + ν * s) := by
      simp only [perpetuityPath]; congr 1; funext s; rw [hWw]
    have hIeq :
        ∫ u in (0 : ℝ)..(τ : ℝ), Real.exp (-ν * u + bmPath hB p.2 u.toNNReal) =
          ∫ u in (0 : ℝ)..(τ : ℝ), Real.exp (-ν * u + Bproc u.toNNReal p.2) :=
      intervalIntegral.integral_congr fun u _ => by rw [hBb]
    have hBeqτ : bmPath hB p.2 τ = Bproc τ p.2 := hBb _
    have hApos' : 0 < perpetuityPath ν (bmPath hW1 p.2) := by rwa [hAeq]
    have hinv :
        invZFromPaths ν τ (bmPath hW1 p.2) (bmPath hB p.2) =
          (Zproc W1 Bproc 1 ν τ p.2)⁻¹ := by
      simp only [invZFromPaths, Zproc, one_mul]
      rw [ite_eq_left hApos', hAeq, hIeq, hBeqτ]
    simp only [Function.uncurry, fPath, waldIncrementFromPaths]
    rw [hBb 1, hBb τ, hinv]
    simp [τ]
  have hasm :
      AEStronglyMeasurable
        (Function.uncurry fun s : ℝ => fun p =>
          Real.exp ((k : ℝ) * (Bproc 1 p - Bproc s.toNNReal p) -
              (k : ℝ) ^ 2 * ((1 : ℝ) - s) / 2) *
            (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ^ m)
        ((volume.restrict (uIoc (0 : ℝ) (1 : ℝ))).prod Q) :=
    hfMeas.aestronglyMeasurable.congr hae
  rw [integrable_prod_iff hasm]
  refine ⟨?_, ?_⟩
  · refine ae_restrict_of_forall_mem measurableSet_uIoc fun s hs => ?_
    have hsI : s ∈ Ioc (0 : ℝ) 1 := by
      simpa [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
    have hst : s.toNNReal ≤ (1 : ℝ≥0) := Real.toNNReal_le_iff_le_coe.2 hsI.2
    simpa [Function.uncurry, Real.coe_toNNReal s hsI.1.le, Q, W1, Bproc] using
      integrable_waldIncrement_mul_Zpow P W hW ν hν s.toNNReal 1 hst k m
  · have hvol : volume (uIoc (0 : ℝ) (1 : ℝ)) < ∞ := by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), Real.volume_Ioc]; simp
    have : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) (1 : ℝ))) :=
      ⟨by simp [Measure.restrict_apply MeasurableSet.univ]⟩
    set cA : ℝ :=
      ∫ p, (∫ u in Ioi (0 : ℝ), Real.exp (W1 u.toNNReal p + ν * u))⁻¹ ^ m ∂Q
    refine (integrable_const (μ := volume.restrict (uIoc (0 : ℝ) (1 : ℝ))) cA).congr ?_
    refine ae_restrict_of_forall_mem measurableSet_uIoc fun s hs => ?_
    have hsI : s ∈ Ioc (0 : ℝ) 1 := by
      simpa [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
    have hst : s.toNNReal ≤ (1 : ℝ≥0) := Real.toNNReal_le_iff_le_coe.2 hsI.2
    have hlift := integral_waldIncrement_mul_Zpow P W hW ν hν s.toNNReal 1 hst k m
    have hZeq := integral_pow_inv_Zproc_eq Q W1 Bproc hW1 hB hWB ν hν s.toNNReal m
    simp only [Function.uncurry, Real.norm_eq_abs, cA]
    have habs :
        ∫ p, |Real.exp ((k : ℝ) * (Bproc 1 p - Bproc s.toNNReal p) -
              (k : ℝ) ^ 2 * ((1 : ℝ) - s) / 2) *
            (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ^ m| ∂Q =
          ∫ p, Real.exp ((k : ℝ) * (Bproc 1 p - Bproc s.toNNReal p) -
              (k : ℝ) ^ 2 * ((1 : ℝ) - (s.toNNReal : ℝ)) / 2) *
            (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ^ m ∂Q := by
      refine integral_congr_ae ?_
      filter_upwards [ae_perpetuity_pos Q W1 hW1 ν hν] with p hAp
      have hinter :
          0 ≤ ∫ u in (0 : ℝ)..(s.toNNReal : ℝ), Real.exp (-ν * u + Bproc u.toNNReal p) :=
        intervalIntegral.integral_nonneg (NNReal.coe_nonneg _) fun _ _ => (Real.exp_pos _).le
      have hY : 0 <
          (∫ u in Ioi (0 : ℝ), Real.exp (W1 u.toNNReal p + ν * u)) +
            ∫ u in (0 : ℝ)..(s.toNNReal : ℝ), Real.exp (-ν * u + Bproc u.toNNReal p) := by
        linarith [hAp]
      have hZpos : 0 < Zproc W1 Bproc 1 ν s.toNNReal p := by
        simpa [Zproc, one_mul] using mul_pos (Real.exp_pos _) hY
      rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg (inv_pos.2 hZpos).le _)),
        Real.coe_toNNReal s hsI.1.le]
    rw [habs]
    simpa [Q, W1, Bproc, Real.coe_toNNReal s hsI.1.le] using (hlift.trans hZeq).symm

/-- Generator recurrence for reciprocal moments of the unit-volatility perpetuity. -/
theorem perpetuity_neg_moment_succ (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (ν : ℝ) (hν : ν < 0) (k : ℕ) (hk : 0 < k) :
    ∫ ω, (∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s))⁻¹ ^ (k + 1) ∂P =
      ((k : ℝ) / 2 - ν) *
        ∫ ω, (∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s))⁻¹ ^ k ∂P := by
  classical
  set Q : Measure (Ω × Ω) := P.prod P
  set W1 : ℝ≥0 → Ω × Ω → ℝ := fun t p => W t p.1
  set Bproc : ℝ≥0 → Ω × Ω → ℝ := fun t p => W t p.2
  have hW1 : IsBM Q W1 := isBM_prod_fst hW
  have hB : IsBM Q Bproc := isBM_prod_snd hW
  have hWB := indepFun_prod_copies (W := W) hW
  set A : Ω × Ω → ℝ := fun p =>
    ∫ s in Ioi (0 : ℝ), Real.exp (W1 s.toNNReal p + ν * s)
  set A0 : Ω → ℝ := fun ω =>
    ∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s)
  have hAinvk : Integrable (fun p => (A p)⁻¹ ^ k) Q := by
    simpa [A, W1] using integrable_pow_inv_perpetuity Q W1 hW1 ν hν k
  have hAinvk1 : Integrable (fun p => (A p)⁻¹ ^ (k + 1)) Q := by
    simpa [A, W1] using integrable_pow_inv_perpetuity Q W1 hW1 ν hν (k + 1)
  have htransfer (m : ℕ) :
      ∫ p, (A p)⁻¹ ^ m ∂Q = ∫ ω, (A0 ω)⁻¹ ^ m ∂P := by
    have hAe : (fun p => (A p)⁻¹ ^ m) = fun p => (A0 p.1)⁻¹ ^ m := by
      funext p; simp [A, A0, W1]
    rw [hAe]
    have h := integral_fun_fst (μ := P) (ν := P) (f := fun ω => (A0 ω)⁻¹ ^ m)
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at h
    exact h
  have hstat (s : ℝ≥0) (m : ℕ) :
      ∫ p, (Zproc W1 Bproc 1 ν s p)⁻¹ ^ m ∂Q = ∫ p, (A p)⁻¹ ^ m ∂Q := by
    simpa [A, W1] using integral_pow_inv_Zproc_eq Q W1 Bproc hW1 hB hWB ν hν s m
  set c : ℝ := (k : ℝ) ^ 2 / 2 - (k : ℝ) * ν
  -- Core Dynkin identity from Wald × pathwise FTC (see plan).
  -- Coefficient identity from Dynkin: c E[A^{-k}] = k E[A^{-(k+1)}].
  have hcoef : c * ∫ p, (A p)⁻¹ ^ k ∂Q = (k : ℝ) * ∫ p, (A p)⁻¹ ^ (k + 1) ∂Q := by
    have hZ1int : Integrable (fun p => (Zproc W1 Bproc 1 ν 1 p)⁻¹ ^ k) Q :=
      integrable_pow_inv_Zproc Q W1 Bproc hW1 hB hWB ν hν 1 k
    set N : ℝ≥0 → Ω × Ω → ℝ := fun u p =>
      Real.exp ((k : ℝ) * Bproc u p - (k : ℝ) ^ 2 * (u : ℝ) / 2)
    set η : ℝ≥0 → Ω × Ω → ℝ := fun u p =>
      c * (Zproc W1 Bproc 1 ν u p)⁻¹ ^ k -
        (k : ℝ) * (Zproc W1 Bproc 1 ν u p)⁻¹ ^ (k + 1)
    set Dfun : ℝ → Ω × Ω → ℝ := fun s p =>
      Real.exp ((k : ℝ) * (Bproc 1 p - Bproc s.toNNReal p) -
        (k : ℝ) ^ 2 * ((1 : ℝ) - s) / 2)
    have hApos : ∀ᵐ p ∂Q, 0 < A p := by
      simpa [A, W1] using ae_perpetuity_pos Q W1 hW1 ν hν
    have hpath : ∀ᵐ p ∂Q,
        (Zproc W1 Bproc 1 ν 1 p)⁻¹ ^ k - (A p)⁻¹ ^ k =
          (A p)⁻¹ ^ k * (N 1 p - 1) +
            ∫ s in (0 : ℝ)..(1 : ℝ), Dfun s p * η s.toNNReal p := by
      filter_upwards [hApos, hB.cont, hB.eval_zero_ae_eq_zero] with p hAp hBcont hB0
      have hid :=
        pathwise_Zpow_drift_identity (fun u => Bproc u p) hBcont hB0 (A p) hAp ν k 1
      convert hid using 1 <;>
        simp [Zproc, A, W1, Bproc, one_mul, N, Dfun, η, c]
    set fA : Ω → ℝ := fun ω =>
      (∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s))⁻¹ ^ k
    set gN : Ω → ℝ := fun ω =>
      Real.exp ((k : ℝ) * W 1 ω - (k : ℝ) ^ 2 * (1 : ℝ) / 2)
    have hfA : Integrable fA P := integrable_pow_inv_perpetuity P W hW ν hν k
    have hgN : Integrable gN P := by
      have hcongr : gN = fun ω =>
          Real.exp (-((k : ℝ) ^ 2 * (1 : ℝ) / 2)) * Real.exp ((k : ℝ) * W 1 ω) := by
        funext ω; simp only [gN]; rw [← Real.exp_add]; congr 1; ring
      rw [hcongr]
      exact (hW.toIsPreBrownianReal.hasLaw_eval 1).integrable_comp
        (f := fun x : ℝ => Real.exp ((k : ℝ) * x))
        (integrable_exp_mul_gaussianReal (k : ℝ)) |>.const_mul _
    have hintAN : Integrable (fun p => (A p)⁻¹ ^ k * N 1 p) Q := by
      have hpt : (fun p => (A p)⁻¹ ^ k * N 1 p) = fun p => fA p.1 * gN p.2 := by
        funext p; simp [A, W1, N, Bproc, fA, gN]
      rw [hpt]
      exact (indepFun_prod₀ hfA.aemeasurable hgN.aemeasurable).integrable_mul
        (hfA.comp_fst P) (hgN.comp_snd P)
    have hintNterm : Integrable (fun p => (A p)⁻¹ ^ k * (N 1 p - 1)) Q :=
      (hintAN.sub hAinvk).congr (Eventually.of_forall fun p => by
        change ((A p)⁻¹ ^ k * N 1 p - (A p)⁻¹ ^ k) = (A p)⁻¹ ^ k * (N 1 p - 1); ring)
    have hN0 : ∫ p, (A p)⁻¹ ^ k * (N 1 p - 1) ∂Q = 0 := by
      have hEq : ∫ p, (A p)⁻¹ ^ k * N 1 p ∂Q = ∫ p, (A p)⁻¹ ^ k ∂Q := by
        simpa [Q, W1, Bproc, A, N] using integral_Ainv_mul_wald_eq P W hW ν hν k 1
      have h1 : ∫ p, (A p)⁻¹ ^ k * (N 1 p - 1) ∂Q =
          ∫ p, ((A p)⁻¹ ^ k * N 1 p - (A p)⁻¹ ^ k) ∂Q :=
        integral_congr_ae (Eventually.of_forall fun p => by ring)
      rw [h1, integral_sub hintAN hAinvk, hEq, sub_self]
    have huncurry_k := integrable_uncurry_waldIncrement_mul_Zpow P W hW ν hν k k
    have huncurry_k1 := integrable_uncurry_waldIncrement_mul_Zpow P W hW ν hν k (k + 1)
    have hkI : Integrable
        (fun p => ∫ s in (0 : ℝ)..(1 : ℝ),
          Dfun s p * (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ^ k) Q := by
      have h :=
        (show Integrable (Function.uncurry fun s : ℝ => fun p =>
            Dfun s p * (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ^ k)
            ((volume.restrict (uIoc (0 : ℝ) (1 : ℝ))).prod Q) from by
          simpa [Dfun, Q, W1, Bproc] using huncurry_k).integral_prod_right
      refine h.congr (Eventually.of_forall fun p => ?_)
      simp [Dfun, intervalIntegral.intervalIntegral_eq_integral_uIoc]
    have hk1I : Integrable
        (fun p => ∫ s in (0 : ℝ)..(1 : ℝ),
          Dfun s p * (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ^ (k + 1)) Q := by
      have h :=
        (show Integrable (Function.uncurry fun s : ℝ => fun p =>
            Dfun s p * (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ^ (k + 1))
            ((volume.restrict (uIoc (0 : ℝ) (1 : ℝ))).prod Q) from by
          simpa [Dfun, Q, W1, Bproc] using huncurry_k1).integral_prod_right
      refine h.congr (Eventually.of_forall fun p => ?_)
      simp [Dfun, intervalIntegral.intervalIntegral_eq_integral_uIoc]
    have hpath_lin : ∀ᵐ p ∂Q,
        ∫ s in (0 : ℝ)..(1 : ℝ), Dfun s p * η s.toNNReal p =
          c * (∫ s in (0 : ℝ)..(1 : ℝ),
              Dfun s p * (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ^ k) -
            (k : ℝ) * (∫ s in (0 : ℝ)..(1 : ℝ),
              Dfun s p * (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ^ (k + 1)) := by
      filter_upwards [hB.cont, hApos] with p hBcont hAp
      have hg : Continuous fun s : ℝ => Real.exp (-ν * s + Bproc s.toNNReal p) := by fun_prop
      have hZcont : Continuous fun u : ℝ≥0 => Zproc W1 Bproc 1 ν u p := by
        simp only [Zproc, one_mul]
        refine (Real.continuous_exp.comp ?_).mul ?_
        · exact (continuous_const.mul continuous_subtype_val).sub hBcont
        · exact continuous_const.add <|
            (intervalIntegral.continuous_primitive (μ := volume)
                (fun _ _ => hg.intervalIntegrable _ _) 0).comp continuous_subtype_val
      have hDcont : Continuous fun s : ℝ => Dfun s p := by simp only [Dfun]; fun_prop
      have hpos : ∀ u : ℝ≥0, 0 < Zproc W1 Bproc 1 ν u p := fun u => by
        have hinter :
            0 ≤ ∫ v in (0 : ℝ)..(u : ℝ), Real.exp (-ν * v + Bproc v.toNNReal p) :=
          intervalIntegral.integral_nonneg (NNReal.coe_nonneg u) fun _ _ => (Real.exp_pos _).le
        have hY : 0 < A p + ∫ v in (0 : ℝ)..(u : ℝ), Real.exp (-ν * v + Bproc v.toNNReal p) := by
          linarith [hAp]
        simpa [Zproc, one_mul, A, W1] using mul_pos (Real.exp_pos _) hY
      have hZinvcont (m : ℕ) : Continuous fun s : ℝ =>
          (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ^ m :=
        (((hZcont.comp continuous_real_toNNReal).inv₀ fun s => (hpos _).ne').pow m)
      have hinter_k :
          IntervalIntegrable (fun s => Dfun s p * (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ^ k)
            volume 0 1 :=
        (hDcont.mul (hZinvcont k)).intervalIntegrable _ _
      have hinter_k1 :
          IntervalIntegrable (fun s =>
              Dfun s p * (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ^ (k + 1)) volume 0 1 :=
        (hDcont.mul (hZinvcont (k + 1))).intervalIntegrable _ _
      have h1 :
          ∫ s in (0 : ℝ)..(1 : ℝ), Dfun s p * η s.toNNReal p =
            ∫ s in (0 : ℝ)..(1 : ℝ),
              c * (Dfun s p * (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ^ k) -
                (k : ℝ) * (Dfun s p * (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ^ (k + 1)) := by
        refine intervalIntegral.integral_congr fun s _ => by simp only [η]; ring
      rw [h1, intervalIntegral.integral_sub (hinter_k.const_mul c) (hinter_k1.const_mul (k : ℝ)),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hintDrift : Integrable
        (fun p => ∫ s in (0 : ℝ)..(1 : ℝ), Dfun s p * η s.toNNReal p) Q :=
      ((hkI.const_mul c).sub (hk1I.const_mul (k : ℝ))).congr
        (hpath_lin.mono fun _ h => h.symm)
    have hE :
        ∫ p, (Zproc W1 Bproc 1 ν 1 p)⁻¹ ^ k ∂Q - ∫ p, (A p)⁻¹ ^ k ∂Q =
          c * (∫ p, (∫ s in (0 : ℝ)..(1 : ℝ),
              Dfun s p * (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ^ k) ∂Q) -
            (k : ℝ) * (∫ p, (∫ s in (0 : ℝ)..(1 : ℝ),
              Dfun s p * (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ^ (k + 1)) ∂Q) := by
      have hsub := (integral_sub hZ1int hAinvk).symm
      rw [hsub, integral_congr_ae hpath, integral_add hintNterm hintDrift, hN0, zero_add]
      refine (integral_congr_ae hpath_lin).trans ?_
      rw [integral_sub (hkI.const_mul c) (hk1I.const_mul (k : ℝ)),
        integral_const_mul, integral_const_mul]
    have hFub (m : ℕ) (huncurry : Integrable (Function.uncurry fun s : ℝ => fun p =>
          Dfun s p * (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ^ m)
          ((volume.restrict (uIoc (0 : ℝ) (1 : ℝ))).prod Q)) :
        ∫ p, (∫ s in (0 : ℝ)..(1 : ℝ),
            Dfun s p * (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ^ m) ∂Q =
          ∫ p, (A p)⁻¹ ^ m ∂Q := by
      have hswap :=
        intervalIntegral_integral_swap
          (f := fun s p => Dfun s p * (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ^ m) huncurry
      rw [← hswap]
      have hpoint : ∀ s ∈ uIcc (0 : ℝ) 1,
          ∫ p, Dfun s p * (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ^ m ∂Q =
            ∫ p, (A p)⁻¹ ^ m ∂Q := by
        intro s hs
        have hsI : s ∈ Icc (0 : ℝ) 1 := by
          simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
        have hst : s.toNNReal ≤ (1 : ℝ≥0) := Real.toNNReal_le_iff_le_coe.2 hsI.2
        have hl := integral_waldIncrement_mul_Zpow P W hW ν hν s.toNNReal 1 hst k m
        have hz := integral_pow_inv_Zproc_eq Q W1 Bproc hW1 hB hWB ν hν s.toNNReal m
        simpa [Dfun, Q, W1, Bproc, A, Real.coe_toNNReal s hsI.1] using hl.trans hz
      have hcongr := intervalIntegral.integral_congr (μ := volume) hpoint
      rw [hcongr, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        setIntegral_const, Measure.real, Real.volume_Ioc, sub_zero,
        ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1), one_smul]
    have hEk := hFub k (by simpa [Dfun, Q, W1, Bproc] using huncurry_k)
    have hEk1 := hFub (k + 1) (by simpa [Dfun, Q, W1, Bproc] using huncurry_k1)
    -- LHS of hE is 0 by stationarity.
    have hL0 : ∫ p, (Zproc W1 Bproc 1 ν 1 p)⁻¹ ^ k ∂Q - ∫ p, (A p)⁻¹ ^ k ∂Q = 0 := by
      rw [hstat 1 k, sub_self]
    rw [hL0, hEk, hEk1] at hE
    linarith [hE]
  have hdrift :
      ∫ p, (Zproc W1 Bproc 1 ν 1 p)⁻¹ ^ k ∂Q - ∫ p, (A p)⁻¹ ^ k ∂Q =
        ∫ s in (0 : ℝ)..(1 : ℝ),
          c * ∫ p, (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ^ k ∂Q -
            (k : ℝ) * ∫ p, (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ^ (k + 1) ∂Q := by
    have hL : ∫ p, (Zproc W1 Bproc 1 ν 1 p)⁻¹ ^ k ∂Q - ∫ p, (A p)⁻¹ ^ k ∂Q = 0 := by
      rw [hstat 1 k, sub_self]
    have hR :
        ∫ s in (0 : ℝ)..(1 : ℝ),
            c * ∫ p, (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ^ k ∂Q -
              (k : ℝ) * ∫ p, (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ^ (k + 1) ∂Q =
          c * ∫ p, (A p)⁻¹ ^ k ∂Q - (k : ℝ) * ∫ p, (A p)⁻¹ ^ (k + 1) ∂Q := by
      have hcongr :
          ∫ s in (0 : ℝ)..(1 : ℝ),
              c * ∫ p, (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ^ k ∂Q -
                (k : ℝ) * ∫ p, (Zproc W1 Bproc 1 ν s.toNNReal p)⁻¹ ^ (k + 1) ∂Q =
            ∫ s in (0 : ℝ)..(1 : ℝ),
              c * ∫ p, (A p)⁻¹ ^ k ∂Q - (k : ℝ) * ∫ p, (A p)⁻¹ ^ (k + 1) ∂Q := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        have hs0 : 0 ≤ s :=
          (show s ∈ Icc (0 : ℝ) 1 by
            simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs).1
        rw [hstat s.toNNReal k, hstat s.toNNReal (k + 1)]
      rw [hcongr, intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _),
        intervalIntegral.integral_const, intervalIntegral.integral_const]
      simp [sub_eq_add_neg]
    have hcoef0 : c * ∫ p, (A p)⁻¹ ^ k ∂Q - (k : ℝ) * ∫ p, (A p)⁻¹ ^ (k + 1) ∂Q = 0 := by
      linarith [hcoef]
    rw [hL, hR, hcoef0]
  have hzero :
      (0 : ℝ) = c * ∫ p, (A p)⁻¹ ^ k ∂Q - (k : ℝ) * ∫ p, (A p)⁻¹ ^ (k + 1) ∂Q := by
    linarith [hcoef]
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.pos_iff_ne_zero.1 hk)
  have hQ : ∫ p, (A p)⁻¹ ^ (k + 1) ∂Q =
      ((k : ℝ) / 2 - ν) * ∫ p, (A p)⁻¹ ^ k ∂Q := by
    have hmul : (k : ℝ) * ∫ p, (A p)⁻¹ ^ (k + 1) ∂Q =
        c * ∫ p, (A p)⁻¹ ^ k ∂Q := by linarith [hzero]
    have : ∫ p, (A p)⁻¹ ^ (k + 1) ∂Q =
        (c / (k : ℝ)) * ∫ p, (A p)⁻¹ ^ k ∂Q := by
      field_simp [hk0] at hmul ⊢
      linarith
    convert this using 2
    simp only [c]
    field_simp [hk0]
  rw [← htransfer (k + 1), ← htransfer k, hQ]

/-- Classical reciprocal-Gamma moments of the unit-volatility perpetuity:
`E[A^{-n}] = gammaMoment (-2ν) 2 n` for `A = ∫₀^∞ e^{W_s+νs} ds`.
Together with `measure_eq_of_moments` and `lintegral_inv_pow_igMeasure` this identifies
`law(A)` with `igMeasure (-2ν) 2` (= `dufresne 1 ν`). -/
theorem perpetuity_neg_moments (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (ν : ℝ) (hν : ν < 0) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal
        ((∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s))⁻¹ ^ n) ∂P =
      ENNReal.ofReal (gammaMoment (-2 * ν) 2 n) := by
  induction n with
  | zero =>
    simp only [pow_zero, gammaMoment, ENNReal.ofReal_one, lintegral_const, measure_univ,
      mul_one]
  | succ n ih =>
    cases n with
    | zero =>
      -- First reciprocal moment: `gammaMoment (-2ν) 2 1 = -ν`.
      have hγ : gammaMoment (-2 * ν) 2 1 = -ν := by
        simp [gammaMoment]; ring
      rw [hγ]
      simpa using perpetuity_inv_moment P W hW ν hν
    | succ n =>
      -- Target power `n+2`; recurrence at `k = n+1 ≥ 1`, using IH at `n+1`.
      have hk : 0 < n + 1 := Nat.succ_pos _
      have hrec := perpetuity_neg_moment_succ P W hW ν hν (n + 1) hk
      have hγ : gammaMoment (-2 * ν) 2 (n + 2) =
          ((n + 1 : ℝ) / 2 - ν) * gammaMoment (-2 * ν) 2 (n + 1) := by
        -- gammaMoment β a (n+2) = (β+(n+1))/a * gammaMoment β a (n+1)
        -- with β=-2ν, a=2: (-2ν+n+1)/2 = (n+1)/2 - ν
        simp only [gammaMoment, Nat.cast_add, Nat.cast_one]
        ring_nf
      have hAk : Integrable
          (fun ω => (∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s))⁻¹ ^ (n + 1)) P :=
        integrable_pow_inv_perpetuity P W hW ν hν (n + 1)
      have hAk1 : Integrable
          (fun ω => (∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s))⁻¹ ^ (n + 2)) P :=
        integrable_pow_inv_perpetuity P W hW ν hν (n + 2)
      have hnnk : 0 ≤ᵐ[P]
          fun ω => (∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s))⁻¹ ^ (n + 1) := by
        filter_upwards [ae_perpetuity_pos P W hW ν hν] with ω hp
        exact pow_nonneg (inv_pos.2 hp).le _
      have hnnk1 : 0 ≤ᵐ[P]
          fun ω => (∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s))⁻¹ ^ (n + 2) := by
        filter_upwards [ae_perpetuity_pos P W hW ν hν] with ω hp
        exact pow_nonneg (inv_pos.2 hp).le _
      have hposγ : 0 ≤ gammaMoment (-2 * ν) 2 (n + 1) :=
        gammaMoment_nonneg (by linarith : 0 < -2 * ν) (by norm_num : (0 : ℝ) < 2) (n + 1)
      have hihB : ∫ ω,
            (∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s))⁻¹ ^ (n + 1) ∂P =
          gammaMoment (-2 * ν) 2 (n + 1) := by
        apply (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg_of_ae hnnk) hposγ).1
        rw [ofReal_integral_eq_lintegral_ofReal hAk hnnk, ih]
      have hcoef : 0 ≤ (n + 1 : ℝ) / 2 - ν := by
        have : 0 ≤ (n + 1 : ℝ) / 2 := by positivity
        linarith [hν]
      have hReal :
          ∫ ω, (∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s))⁻¹ ^ (n + 2) ∂P =
            ((n + 1 : ℝ) / 2 - ν) * gammaMoment (-2 * ν) 2 (n + 1) := by
        calc ∫ ω, (∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s))⁻¹ ^ (n + 2) ∂P
            = ∫ ω, (∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s))⁻¹ ^ (n + 1 + 1) ∂P := by
                rfl
          _ = (↑(n + 1) / 2 - ν) *
                ∫ ω, (∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s))⁻¹ ^ (n + 1) ∂P :=
                hrec
          _ = ((n + 1 : ℝ) / 2 - ν) * gammaMoment (-2 * ν) 2 (n + 1) := by
                rw [hihB]; simp [Nat.cast_succ]
      rw [hγ, ← ofReal_integral_eq_lintegral_ofReal hAk1 hnnk1, hReal,
        ENNReal.ofReal_mul hcoef]


/-- The unit-volatility form of Dufresne's identity.  This is the sole probabilistic
identification needed after Brownian scaling: equivalently, the reciprocal of the integral
has the Gamma law with shape `-2 * ν` and rate `2`.

From `perpetuity_neg_moments`, compare the law of `A⁻¹` to the Gamma law via
`measure_eq_of_moments`, then invert to conclude `P.map A = igMeasure (-2ν) 2`. -/
theorem dufresne_theorem_sigma_one (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (ν : ℝ) (hν : ν < 0) :
    IsInftyDensity P W 1 ν (dufresne 1 ν) := by
  set β : ℝ := -2 * ν
  set a : ℝ := 2
  have hβ : 0 < β := by simp [β]; linarith
  have ha : 0 < a := by norm_num [a]
  -- Measurable representative of the perpetuity (ae-equal to the BM-path integral)
  let A : Ω → ℝ := perpetuityPath ν ∘ bmPath hW
  have hAmeas : Measurable A := (measurable_perpetuityPath ν).comp (measurable_bmPath hW)
  have hAeq : (fun ω => ∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s)) =ᵐ[P] A := by
    filter_upwards [bmPath_ae_eq hW] with ω hω
    simp only [A, Function.comp_apply, perpetuityPath]
    congr 1
    funext s
    rw [hω]
  have hApos : ∀ᵐ ω ∂P, 0 < A ω := by
    filter_upwards [ae_perpetuity_pos P W hW ν hν, hAeq] with ω hpos heq
    rwa [← heq]
  have hAne : ∀ᵐ ω ∂P, A ω ≠ 0 := hApos.mono fun _ h => h.ne'
  let Ainv : Ω → ℝ := fun ω => (A ω)⁻¹
  have hAinvMeas : Measurable Ainv := hAmeas.inv
  let ρ₁ : Measure ℝ := P.map Ainv
  let ρ₂ : Measure ℝ := (igMeasure β a).map Inv.inv
  have : IsProbabilityMeasure (igMeasure β a) := isProbabilityMeasure_igMeasure hβ ha
  have : IsProbabilityMeasure ρ₁ :=
    (inferInstance : AEMeasurable Ainv P → IsProbabilityMeasure ρ₁) hAinvMeas.aemeasurable
  have : IsProbabilityMeasure ρ₂ := inferInstance
  have hpos₁ : ∀ᵐ y ∂ρ₁, 0 ≤ y := by
    dsimp [ρ₁]
    rw [ae_map_iff hAinvMeas.aemeasurable measurableSet_Ici]
    filter_upwards [hApos] with ω hω
    exact (inv_pos.2 hω).le
  have hpos₂ : ∀ᵐ y ∂ρ₂, 0 ≤ y := ae_nonneg_map_inv_igMeasure β a
  have hmom : ∀ n : ℕ,
      ∫⁻ y, ENNReal.ofReal (y ^ n) ∂ρ₁ = ∫⁻ y, ENNReal.ofReal (y ^ n) ∂ρ₂ := by
    intro n
    have hL : ∫⁻ y, ENNReal.ofReal (y ^ n) ∂ρ₁ =
        ∫⁻ ω, ENNReal.ofReal (Ainv ω ^ n) ∂P := by
      dsimp [ρ₁]
      exact lintegral_map (by fun_prop) hAinvMeas
    have hR : ∫⁻ y, ENNReal.ofReal (y ^ n) ∂ρ₂ =
        ENNReal.ofReal (gammaMoment β a n) :=
      lintegral_inv_pow_igMeasure hβ ha n
    have hL' : ∫⁻ ω, ENNReal.ofReal (Ainv ω ^ n) ∂P =
        ∫⁻ ω, ENNReal.ofReal
          ((∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s))⁻¹ ^ n) ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [hAeq] with ω heq
      simp only [Ainv, heq]
    rw [hL, hL', hR]
    simpa [β, a] using perpetuity_neg_moments P W hW ν hν n
  have hfin : ∀ s ∈ Ico (0 : ℝ) a,
      ∫⁻ y, ENNReal.ofReal (Real.exp (s * y)) ∂ρ₂ ≠ ∞ := by
    intro s hs
    have hs' : s < a := hs.2
    dsimp [ρ₂]
    rw [lintegral_exp_inv_igMeasure hβ ha hs']
    exact ENNReal.ofReal_ne_top
  have hρ : ρ₁ = ρ₂ :=
    measure_eq_of_moments hpos₁ hpos₂ ha hmom hfin
  have hρ₁' : ρ₁ = (P.map A).map Inv.inv := by
    dsimp only [ρ₁]
    show P.map Ainv = (P.map A).map Inv.inv
    rw [show Ainv = Inv.inv ∘ A from rfl]
    exact (Measure.map_map measurable_inv hAmeas).symm
  have hinv_comp : Inv.inv ∘ Inv.inv = (id : ℝ → ℝ) := funext fun _ => inv_inv _
  have hA_inv_inv : ((P.map A).map Inv.inv).map Inv.inv = P.map A := by
    rw [Measure.map_map measurable_inv measurable_inv, hinv_comp, Measure.map_id]
  have hig_inv_inv : ((igMeasure β a).map Inv.inv).map Inv.inv = igMeasure β a := by
    rw [Measure.map_map measurable_inv measurable_inv, hinv_comp, Measure.map_id]
  have hlaw : P.map A = igMeasure β a := by
    calc P.map A
        = ((P.map A).map Inv.inv).map Inv.inv := hA_inv_inv.symm
      _ = ρ₁.map Inv.inv := by rw [← hρ₁']
      _ = ρ₂.map Inv.inv := by rw [hρ]
      _ = ((igMeasure β a).map Inv.inv).map Inv.inv := rfl
      _ = igMeasure β a := hig_inv_inv
  unfold IsInftyDensity
  have hone :
      (fun ω => ∫ s in Ioi (0 : ℝ), Real.exp (1 * W s.toNNReal ω + ν * s)) =ᵐ[P]
        (fun ω => ∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s)) :=
    Eventually.of_forall fun ω => by
      simp only [one_mul]
  have h1mul :
      (fun ω => ∫ s in Ioi (0 : ℝ), Real.exp (1 * W s.toNNReal ω + ν * s)) =ᵐ[P] A :=
    hone.trans hAeq
  rw [Measure.map_congr h1mul, hlaw, dufresne_eq_igDensity_one ν]
  rfl

theorem dufresne_theorem (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ ν : ℝ) (hσ : 0 < σ) (hν : ν < 0) :
    IsInftyDensity P W σ ν (dufresne σ ν) := by
  apply dufresne_theorem_of_sigma_one P W hW σ ν hσ
  exact dufresne_theorem_sigma_one P W hW (ν / σ ^ 2)
    (div_neg_of_neg_of_pos hν (sq_pos_of_pos hσ))

/- Paper: p. 1069, operator A_t.
   Plain recap: the second-order operator appearing in the Fokker–Planck argument. -/
def Aop (V0 : ℝ) (V : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (x y u v : ℝ) : ℝ :=
  u ^ 2 / 2 * iteratedDeriv 2 (fun x' => f x' y) x
    + u * deriv (fun y' => deriv (fun x' => f x' y') x) y
    + (v / 2 + V0 - V y) * deriv (fun x' => f x' y) x

/-- The probability flux in the `x` direction in (3.6b). -/
def jointFlux (σ : ℝ) (φ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  σ ^ 2 * x ^ 2 / 2 * deriv (fun z => φ z y) x
    + σ * x * deriv (fun y' => φ x y') y
    + (Real.exp (σ * y) + σ ^ 2 * x / 2 - 1) * φ x y

/-- The expanded formal adjoint in (3.6a).  This is the derivative in `x` of
`jointFlux`; keeping it named separates the analytic integration-by-parts calculation from the
stochastic weak-forward-equation argument. -/
def jointFokkerPlanckAdjoint (σ : ℝ) (φ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  σ ^ 2 * x ^ 2 / 2 * deriv (deriv fun z => φ z y) x
    + σ * x * deriv (fun z => deriv (fun y' => φ z y') y) x
    + (Real.exp (σ * y) + 3 * σ ^ 2 * x / 2 - 1) * deriv (fun z => φ z y) x
    + σ * deriv (fun y' => φ x y') y
    + σ ^ 2 / 2 * φ x y

/-- Deterministic divergence/adjoint calculation underlying (3.6a)–(3.6b). -/
theorem hasDerivAt_jointFlux (σ : ℝ) (φ : ℝ → ℝ → ℝ) (x y : ℝ)
    (hφx : HasDerivAt (fun z => φ z y) (deriv (fun z => φ z y) x) x)
    (hφxx : HasDerivAt (deriv fun z => φ z y)
      (deriv (deriv fun z => φ z y) x) x)
    (hφxy : HasDerivAt (fun z => deriv (fun y' => φ z y') y)
      (deriv (fun z => deriv (fun y' => φ z y') y) x) x) :
    HasDerivAt (fun z => jointFlux σ φ z y) (jointFokkerPlanckAdjoint σ φ x y) x := by
  have hsq : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hfirst := (((hsq.const_mul (σ ^ 2)).div_const 2).mul hφxx)
  have hmixed : HasDerivAt
      (fun z => σ * z * deriv (fun y' => φ z y') y)
      (σ * deriv (fun y' => φ x y') y
        + σ * x * deriv (fun z => deriv (fun y' => φ z y') y) x) x := by
    convert ((hasDerivAt_id x).const_mul σ).mul hφxy using 1
    · ext z
      rfl
    · simp [id]
  have hcoefficient : HasDerivAt
      (fun z : ℝ => Real.exp (σ * y) + σ ^ 2 * z / 2 - 1) (σ ^ 2 / 2) x := by
    convert (hasDerivAt_const x (Real.exp (σ * y) - 1)).add
      (((hasDerivAt_id x).const_mul (σ ^ 2)).div_const 2) using 1
    · ext z
      simp [id]
      ring
    · ring
  have hlast := hcoefficient.mul hφx
  convert (hfirst.add hmixed).add hlast using 1
  · ext z
    simp only [jointFlux, Pi.add_apply, Pi.mul_apply]
  · simp only [jointFokkerPlanckAdjoint]
    ring

/-- Pointwise equality between the derivative-of-flux and expanded-adjoint formulations. -/
theorem deriv_jointFlux (σ : ℝ) (φ : ℝ → ℝ → ℝ) (x y : ℝ)
    (hφx : HasDerivAt (fun z => φ z y) (deriv (fun z => φ z y) x) x)
    (hφxx : HasDerivAt (deriv fun z => φ z y)
      (deriv (deriv fun z => φ z y) x) x)
    (hφxy : HasDerivAt (fun z => deriv (fun y' => φ z y') y)
      (deriv (fun z => deriv (fun y' => φ z y') y) x) x) :
    deriv (fun z => jointFlux σ φ z y) x = jointFokkerPlanckAdjoint σ φ x y :=
  (hasDerivAt_jointFlux σ φ x y hφx hφxx hφxy).deriv

/-- Paper (3.5) operator at exponential-BM coefficients, acting on a test function. -/
def jointA (σ : ℝ) (ϕ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  σ ^ 2 * x ^ 2 / 2 * iteratedDeriv 2 (fun x' => ϕ x' y) x
    + σ * x * deriv (fun y' => deriv (fun x' => ϕ x' y') x) y
    + (σ ^ 2 * x / 2 + 1 - Real.exp (σ * y)) * deriv (fun x' => ϕ x' y) x

theorem jointA_eq_Aop (σ : ℝ) (ϕ : ℝ → ℝ → ℝ) (x y : ℝ) :
    jointA σ ϕ x y =
      Aop 1 (fun z => Real.exp (σ * z)) ϕ x y (σ * x) (σ ^ 2 * x) := by
  simp only [jointA, Aop]; ring

/-- The (3.4b)−(3.4a) drift difference is `jointA` on product tests. -/
theorem jointA_eq_drift_diff (σ : ℝ) (u v : ℝ → ℝ)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (x y : ℝ) :
    jointA σ (fun x y => u x * v y) x y =
      ((1 : ℝ) * deriv u x * v y
        + (σ ^ 2 / 2) * x * deriv u x * v y
        + (σ ^ 2 / 2) * x ^ 2 * deriv (deriv u) x * v y
        + σ * x * deriv u x * deriv v y
        + (1 / 2) * u x * deriv (deriv v) y)
      - (deriv u x * Real.exp (σ * y) * v y
          + u x * ((1 : ℝ) / 2) * deriv (deriv v) y) := by
  have hu_diff : Differentiable ℝ u := hu.differentiable (by decide)
  have hv_diff : Differentiable ℝ v := hv.differentiable (by decide)
  have huder : Differentiable ℝ (deriv u) :=
    ((contDiff_succ_iff_deriv (n := 1)).mp hu).2.2.differentiable (by decide)
  have hx : deriv (fun x' => u x' * v y) x = deriv u x * v y :=
    deriv_mul_const (hu_diff.differentiableAt) (v y)
  have hxx : iteratedDeriv 2 (fun x' => u x' * v y) x = deriv (deriv u) x * v y := by
    have heq : deriv (fun x' => u x' * v y) = fun x' => deriv u x' * v y := by
      funext x'
      exact deriv_mul_const (hu_diff.differentiableAt) (v y)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, heq]
    exact deriv_mul_const (huder.differentiableAt) (v y)
  have hxy : deriv (fun y' => deriv (fun x' => u x' * v y') x) y =
      deriv u x * deriv v y := by
    have h1 : (fun y' => deriv (fun x' => u x' * v y') x) =
        fun y' => deriv u x * v y' := by
      funext y'
      exact deriv_mul_const (hu_diff.differentiableAt) (v y')
    rw [h1]
    exact deriv_const_mul (deriv u x) (hv_diff.differentiableAt)
  simp only [jointA, hxx, hxy, hx]
  ring

/-- Pointwise: `jointA(u⊗v) = twinGenerator − (3.4a drift)`. -/
theorem jointA_eq_twinGenerator_sub (σ : ℝ) (u v : ℝ → ℝ)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (x y : ℝ) :
    jointA σ (fun x y => u x * v y) x y =
      twinGenerator σ u v x y -
        (deriv u x * Real.exp (σ * y) * v y +
          u x * ((1 : ℝ) / 2) * deriv (deriv v) y) := by
  simpa [twinGenerator] using jointA_eq_drift_diff σ u v hu hv x y

/-- Continuity of the product-test generator. -/
theorem continuous_jointA_product (σ : ℝ) {u v : ℝ → ℝ}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v) :
    Continuous fun p : ℝ × ℝ => jointA σ (fun x y => u x * v y) p.1 p.2 := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by decide)
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by decide)
  have htw := continuous_twinGenerator σ hu hv
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by decide)
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by decide)
  have hdv1 : ContDiff ℝ 1 (deriv v) := (contDiff_succ_iff_deriv (n := 1)).mp hv2 |>.2.2
  have hu'c : Continuous (deriv u) := ContDiff.continuous_deriv_one hu1
  have hv''c : Continuous (deriv (deriv v)) := ContDiff.continuous_deriv_one hdv1
  have hdrift : Continuous fun p : ℝ × ℝ =>
      deriv u p.1 * Real.exp (σ * p.2) * v p.2 +
        u p.1 * ((1 : ℝ) / 2) * deriv (deriv v) p.2 :=
    (((hu'c.comp continuous_fst).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_snd))).mul
        (hv.continuous.comp continuous_snd)).add
      (((hu.continuous.comp continuous_fst).mul continuous_const).mul
        (hv''c.comp continuous_snd))
  refine (htw.sub hdrift).congr fun p => ?_
  exact (jointA_eq_twinGenerator_sub σ u v hu2 hv2 p.1 p.2).symm

/-- Compactly supported product tests make `jointA(u⊗v)`, `twinGenerator`, and the
(3.4a) drift globally bounded. -/
theorem jointA_product_bounds (σ : ℝ) {u v : ℝ → ℝ}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (huC : HasCompactSupport u) (hvC : HasCompactSupport v) :
    ∃ M : ℝ,
      (∀ x y, |jointA σ (fun x y => u x * v y) x y| ≤ M) ∧
      (∀ x y, |twinGenerator σ u v x y| ≤ M) ∧
      (∀ x y,
        |deriv u x * Real.exp (σ * y) * v y +
            u x * ((1 : ℝ) / 2) * deriv (deriv v) y| ≤ M) := by
  obtain ⟨Cu, hu_bdd, hu'_bdd, hu''_bdd⟩ := contDiff_top_compactSupport_bounds hu huC
  obtain ⟨Cv, hv_bdd, hv'_bdd, hv''_bdd⟩ := contDiff_top_compactSupport_bounds hv hvC
  have hCu : 0 ≤ Cu := (abs_nonneg _).trans (hu_bdd 0)
  have hCv : 0 ≤ Cv := (abs_nonneg _).trans (hv_bdd 0)
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by decide)
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by decide)
  have hdu1 : ContDiff ℝ 1 (deriv u) := (contDiff_succ_iff_deriv (n := 1)).mp hu2 |>.2.2
  have hu'c : Continuous (deriv u) := ContDiff.continuous_deriv_one hu1
  have hu''c : Continuous (deriv (deriv u)) := ContDiff.continuous_deriv_one hdu1
  have hvc : Continuous v := hv.continuous
  obtain ⟨K₁, hK₁⟩ := (show Continuous ((fun x : ℝ => x) * deriv u) from
    continuous_id.mul hu'c).bounded_above_of_compact_support huC.deriv.mul_left
  obtain ⟨K₂, hK₂⟩ := (show Continuous ((fun x : ℝ => x ^ 2) * deriv (deriv u)) from
    (continuous_id.pow 2).mul hu''c).bounded_above_of_compact_support
      huC.deriv.deriv.mul_left
  obtain ⟨Kexp, hKexp⟩ :=
    (show Continuous ((fun y : ℝ => Real.exp (σ * y)) * v) from
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hvc
      ).bounded_above_of_compact_support hvC.mul_left
  have hK₁0 : 0 ≤ K₁ := (abs_nonneg _).trans (hK₁ 0)
  have hK₂0 : 0 ≤ K₂ := (abs_nonneg _).trans (hK₂ 0)
  have hKexp0 : 0 ≤ Kexp := (abs_nonneg _).trans (by simpa [Real.norm_eq_abs] using hKexp 0)
  set Mtw : ℝ :=
    Cu * Cv + |σ ^ 2 / 2| * K₁ * Cv + |σ ^ 2 / 2| * K₂ * Cv +
      |σ| * K₁ * Cv + (1 / 2) * Cu * Cv
  set Mdr : ℝ := Cu * Kexp + Cu * (1 / 2) * Cv
  set M : ℝ := Mtw + Mdr
  have htw (x y : ℝ) : |twinGenerator σ u v x y| ≤ Mtw := by
    simp only [twinGenerator]
    have h1 : |(1 : ℝ) * deriv u x * v y| ≤ Cu * Cv := by
      simp only [one_mul, abs_mul]
      exact mul_le_mul (hu'_bdd x) (hv_bdd y) (abs_nonneg _) hCu
    have h2 : |(σ ^ 2 / 2) * x * deriv u x * v y| ≤ |σ ^ 2 / 2| * K₁ * Cv := by
      have : |(σ ^ 2 / 2) * (x * deriv u x) * v y| =
          |σ ^ 2 / 2| * |x * deriv u x| * |v y| := by
        simp [abs_mul, mul_assoc]
      rw [show (σ ^ 2 / 2) * x * deriv u x * v y =
          (σ ^ 2 / 2) * (x * deriv u x) * v y by ring, this]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hK₁ x) (abs_nonneg _))
        (hv_bdd y) (abs_nonneg _) (by positivity)
    have h3 : |(σ ^ 2 / 2) * x ^ 2 * deriv (deriv u) x * v y| ≤ |σ ^ 2 / 2| * K₂ * Cv := by
      have : |(σ ^ 2 / 2) * (x ^ 2 * deriv (deriv u) x) * v y| =
          |σ ^ 2 / 2| * |x ^ 2 * deriv (deriv u) x| * |v y| := by
        simp [abs_mul, mul_assoc]
      rw [show (σ ^ 2 / 2) * x ^ 2 * deriv (deriv u) x * v y =
          (σ ^ 2 / 2) * (x ^ 2 * deriv (deriv u) x) * v y by ring, this]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hK₂ x) (abs_nonneg _))
        (hv_bdd y) (abs_nonneg _) (by positivity)
    have h4 : |σ * x * deriv u x * deriv v y| ≤ |σ| * K₁ * Cv := by
      have : |σ * (x * deriv u x) * deriv v y| = |σ| * |x * deriv u x| * |deriv v y| := by
        simp [abs_mul, mul_assoc]
      rw [show σ * x * deriv u x * deriv v y = σ * (x * deriv u x) * deriv v y by ring, this]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hK₁ x) (abs_nonneg _))
        (hv'_bdd y) (abs_nonneg _) (by positivity)
    have h5 : |(1 / 2) * u x * deriv (deriv v) y| ≤ (1 / 2) * Cu * Cv := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hu_bdd x) (by norm_num))
        (hv''_bdd y) (abs_nonneg _) (by positivity)
    refine (abs_add_le _ _).trans ?_
    refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
    refine (add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl).trans ?_
    refine (add_le_add (add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl) le_rfl).trans ?_
    have := add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5
    simpa [Mtw] using this
  have hdr (x y : ℝ) :
      |deriv u x * Real.exp (σ * y) * v y +
          u x * ((1 : ℝ) / 2) * deriv (deriv v) y| ≤ Mdr := by
    have h1 : |deriv u x * Real.exp (σ * y) * v y| ≤ Cu * Kexp := by
      rw [mul_assoc, abs_mul]
      refine mul_le_mul (hu'_bdd x) ?_ (abs_nonneg _) hCu
      simpa [Real.norm_eq_abs] using hKexp y
    have h2 : |u x * ((1 : ℝ) / 2) * deriv (deriv v) y| ≤ Cu * (1 / 2) * Cv := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact mul_le_mul (mul_le_mul_of_nonneg_right (hu_bdd x) (by norm_num))
        (hv''_bdd y) (abs_nonneg _) (by positivity)
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  refine ⟨M, ?_, ?_, ?_⟩
  · intro x y
    have hu2' : ContDiff ℝ 2 u := hu.of_le (by decide)
    have hv2' : ContDiff ℝ 2 v := hv.of_le (by decide)
    rw [jointA_eq_twinGenerator_sub σ u v hu2' hv2' x y]
    exact (abs_sub _ _).trans (add_le_add (htw x y) (hdr x y))
  · intro x y
    exact (htw x y).trans (le_add_of_nonneg_right (by
      have : 0 ≤ Mdr := (abs_nonneg _).trans (hdr 0 0)
      exact this))
  · intro x y
    exact (hdr x y).trans (le_add_of_nonneg_left (by
      have : 0 ≤ Mtw := (abs_nonneg _).trans (htw 0 0)
      exact this))

omit [MeasurableSpace Ω] in
private lemma continuous_expInt_of_continuous_path
    {B : ℝ≥0 → Ω → ℝ} (hBcont : ∀ ω, Continuous fun s : ℝ≥0 => B s ω) (σ : ℝ) (ω : Ω) :
    Continuous fun r : ℝ => expInt B σ 0 r.toNNReal ω := by
  have heq : (fun r : ℝ => expInt B σ 0 r.toNNReal ω) =
      fun r : ℝ => ∫ s in (0 : ℝ)..(r.toNNReal : ℝ), Real.exp (σ * B s.toNNReal ω) := by
    funext r; simp [expInt]
  rw [heq]
  exact (continuous_pathIntegral_nnreal (Real.continuous_exp.comp
    (continuous_const.mul (hBcont ω)))).comp continuous_real_toNNReal

private lemma measurable_expInt_of_continuous_path
    {B : ℝ≥0 → Ω → ℝ} (hBmeas : ∀ s, Measurable (B s))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 => B s ω) (σ : ℝ) (s : ℝ≥0) :
    Measurable (expInt B σ 0 s) := by
  have heq : expInt B σ 0 s =
      fun ω => ∫ r in (0 : ℝ)..(s : ℝ), Real.exp (σ * B r.toNNReal ω) := by
    funext ω; simp [expInt]
  rw [heq]
  exact (measurable_pathIntegral_natFiltration hBmeas hBcont
    (by fun_prop : Continuous fun y => Real.exp (σ * y)) s).mono
    ((natFiltration hBmeas).le s) le_rfl

/-- Expectation of a continuous bounded functional of `(expInt, B_s)` is continuous in time. -/
private lemma continuous_expectation_jointA_path
    {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (hBmeas : ∀ s, Measurable (B s))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 => B s ω) (σ : ℝ)
    (H : ℝ → ℝ → ℝ) (hH : Continuous fun p : ℝ × ℝ => H p.1 p.2)
    {M : ℝ} (hM : ∀ (r : ℝ) (ω : Ω), |H (expInt B σ 0 r.toNNReal ω) (B r.toNNReal ω)| ≤ M) :
    Continuous fun r : ℝ => ∫ ω, H (expInt B σ 0 r.toNNReal ω) (B r.toNNReal ω) ∂P := by
  rw [continuous_iff_seqContinuous]
  intro rn r₀ hrn
  refine tendsto_integral_of_dominated_convergence (fun _ => M) ?_ (integrable_const M) ?_ ?_
  · intro k
    exact (hH.measurable.comp ((measurable_expInt_of_continuous_path hBmeas hBcont σ
      (rn k).toNNReal).prodMk (hBmeas _))).aestronglyMeasurable
  · intro k
    filter_upwards with ω
    simpa [Real.norm_eq_abs] using hM (rn k) ω
  · filter_upwards with ω
    have hcont : Continuous fun r : ℝ =>
        H (expInt B σ 0 r.toNNReal ω) (B r.toNNReal ω) :=
      hH.comp ((continuous_expInt_of_continuous_path hBcont σ ω).prodMk
        ((hBcont ω).comp continuous_real_toNNReal))
    exact hcont.continuousAt.tendsto.comp hrn

/-- Dynkin identity (3.5) for product test functions.

Proof outline (paper (3.5)): the product-test Itô identities (3.4a)/(3.4b) share the same
LHS, so their drift-integrand difference integrates to zero on every horizon `τ ∈ (0,t]`.
Pointwise that difference is `jointA` (`jointA_eq_twinGenerator_sub`). The resulting
cumulative integral of `g(τ) := E[jointA(expInt_τ, W_τ)]` vanishes; continuity of `g`
and FTC recover `g(t) = 0`. -/
theorem joint_dynkin_Aop_product (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (ht : 0 < t)
    (u v : ℝ → ℝ) (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (huC : HasCompactSupport u) (hvC : HasCompactSupport v) :
    ∫ ω, jointA σ (fun x y => u x * v y) (expInt W σ 0 t ω) (W t ω) ∂P = 0 := by
  classical
  set B : ℝ≥0 → Ω → ℝ := hW.toIsPreBrownianReal.mk W
  have hBmeas : ∀ s, Measurable (B s) := hW.toIsPreBrownianReal.measurable_mk
  have hBcont : ∀ ω, Continuous fun s : ℝ≥0 => B s ω := hW.toIsPreBrownianReal.continuous_mk
  have hBW : ∀ᵐ ω ∂P, ∀ s, B s ω = W s ω := hW.mk_ae_forall_eq
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by decide)
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by decide)
  obtain ⟨M, hJA_bdd, hTw_bdd, hDr_bdd⟩ := jointA_product_bounds σ hu hv huC hvC
  have hJA_cont := continuous_jointA_product σ hu hv
  -- Continuous-in-time expectation along the continuous modification.
  set g : ℝ → ℝ := fun r =>
    ∫ ω, jointA σ (fun x y => u x * v y) (expInt B σ 0 r.toNNReal ω) (B r.toNNReal ω) ∂P
  have hg_cont : Continuous g :=
    continuous_expectation_jointA_path hBmeas hBcont σ
      (fun x y => jointA σ (fun x y => u x * v y) x y) hJA_cont
      (fun r ω => hJA_bdd _ _)
  -- Goal equals `g t` after transporting `W` to `B`.
  have hm_eq : (∫ ω, jointA σ (fun x y => u x * v y) (expInt W σ 0 t ω) (W t ω) ∂P) =
      g (t : ℝ) := by
    have htNN : (t : ℝ).toNNReal = t := Real.toNNReal_coe
    simp only [g, htNN]
    refine integral_congr_ae ?_
    filter_upwards [hBW] with ω hω
    have hX : expInt W σ 0 t ω = expInt B σ 0 t ω := by
      simp only [expInt]
      refine intervalIntegral.integral_congr fun r _ => ?_
      rw [hω r.toNNReal]
    rw [hX, hω t]
  -- Continuous expectations of the (3.4a)/(3.4b) integrands along `B`.
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by decide)
  have hv2' : ContDiff ℝ 2 v := hv.of_le (by decide)
  have hdv1 : ContDiff ℝ 1 (deriv v) := (contDiff_succ_iff_deriv (n := 1)).mp hv2' |>.2.2
  have hu'c : Continuous (deriv u) := ContDiff.continuous_deriv_one hu1
  have hv''c : Continuous (deriv (deriv v)) := ContDiff.continuous_deriv_one hdv1
  have hdrift_cont : Continuous fun p : ℝ × ℝ =>
      deriv u p.1 * Real.exp (σ * p.2) * v p.2 +
        u p.1 * ((1 : ℝ) / 2) * deriv (deriv v) p.2 :=
    (((hu'c.comp continuous_fst).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_snd))).mul
        (hv.continuous.comp continuous_snd)).add
      (((hu.continuous.comp continuous_fst).mul continuous_const).mul
        (hv''c.comp continuous_snd))
  set gTw : ℝ → ℝ := fun r =>
    ∫ ω, twinGenerator σ u v (expInt B σ 0 r.toNNReal ω) (B r.toNNReal ω) ∂P
  set gDr : ℝ → ℝ := fun r =>
    ∫ ω,
      deriv u (expInt B σ 0 r.toNNReal ω) * Real.exp (σ * B r.toNNReal ω) *
          v (B r.toNNReal ω)
        + u (expInt B σ 0 r.toNNReal ω) * ((1 : ℝ) / 2) *
            deriv (deriv v) (B r.toNNReal ω) ∂P
  have hgTw_cont : Continuous gTw :=
    continuous_expectation_jointA_path hBmeas hBcont σ
      (fun x y => twinGenerator σ u v x y) (continuous_twinGenerator σ hu hv)
      (fun r ω => hTw_bdd _ _)
  have hgDr_cont : Continuous gDr :=
    continuous_expectation_jointA_path hBmeas hBcont σ
      (fun x y =>
        deriv u x * Real.exp (σ * y) * v y +
          u x * ((1 : ℝ) / 2) * deriv (deriv v) y)
      hdrift_cont (fun r ω => hDr_bdd _ _)
  have hg_eq : g = fun r => gTw r - gDr r := by
    funext r
    have hintTw : Integrable
        (fun ω => twinGenerator σ u v (expInt B σ 0 r.toNNReal ω) (B r.toNNReal ω)) P :=
      Integrable.of_bound
        ((continuous_twinGenerator σ hu hv).measurable.comp
          ((measurable_expInt_of_continuous_path hBmeas hBcont σ r.toNNReal).prodMk
            (hBmeas _))).aestronglyMeasurable
        M (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hTw_bdd _ _)
    have hintDr : Integrable
        (fun ω =>
          deriv u (expInt B σ 0 r.toNNReal ω) * Real.exp (σ * B r.toNNReal ω) *
              v (B r.toNNReal ω)
            + u (expInt B σ 0 r.toNNReal ω) * ((1 : ℝ) / 2) *
                deriv (deriv v) (B r.toNNReal ω)) P :=
      Integrable.of_bound
        (hdrift_cont.measurable.comp
          ((measurable_expInt_of_continuous_path hBmeas hBcont σ r.toNNReal).prodMk
            (hBmeas _))).aestronglyMeasurable
        M (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hDr_bdd _ _)
    simp only [g, gTw, gDr]
    rw [← integral_sub hintTw hintDr]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simpa using jointA_eq_twinGenerator_sub σ u v hu2 hv2
      (expInt B σ 0 r.toNNReal ω) (B r.toNNReal ω)
  -- Cumulative vanishing + FTC.
  have hcum : ∀ τ : ℝ≥0, 0 < τ → τ ≤ t → (∫ s in (0 : ℝ)..τ, g s) = 0 := by
    intro τ hτpos _hτle
    have h34a := ito_expInt_test_product P W hW σ τ u v hu hv huC hvC
    have h34b := ito_timeReversed_expInt_test_product P W hW σ τ hτpos u v hu hv huC hvC
    -- Transport Itô RHSs from `W` to the continuous modification `B`.
    have h34aB :
        (∫ ω, u (expInt W σ 0 τ ω) * v (W τ ω) ∂P) - u 0 * v 0 =
          ∫ s in Ioc (0 : ℝ) τ, gDr s := by
      refine h34a.trans ?_
      refine setIntegral_congr_fun measurableSet_Ioc fun s _hs => ?_
      change _ = ∫ ω,
          deriv u (expInt B σ 0 s.toNNReal ω) * Real.exp (σ * B s.toNNReal ω) *
              v (B s.toNNReal ω)
            + u (expInt B σ 0 s.toNNReal ω) * ((1 : ℝ) / 2) *
                deriv (deriv v) (B s.toNNReal ω) ∂P
      refine integral_congr_ae ?_
      filter_upwards [hBW] with ω hω
      have hX : expInt W σ 0 s.toNNReal ω = expInt B σ 0 s.toNNReal ω := by
        simp only [expInt]
        refine intervalIntegral.integral_congr fun r _ => ?_
        rw [hω r.toNNReal]
      simp only [hX, hω]
    have h34bB :
        (∫ ω, u (expInt W σ 0 τ ω) * v (W τ ω) ∂P) - u 0 * v 0 =
          ∫ s in Ioc (0 : ℝ) τ, gTw s := by
      refine h34b.trans ?_
      refine setIntegral_congr_fun measurableSet_Ioc fun s _hs => ?_
      change _ = ∫ ω, twinGenerator σ u v (expInt B σ 0 s.toNNReal ω) (B s.toNNReal ω) ∂P
      refine integral_congr_ae ?_
      filter_upwards [hBW] with ω hω
      have hX : expInt W σ 0 s.toNNReal ω = expInt B σ 0 s.toNNReal ω := by
        simp only [expInt]
        refine intervalIntegral.integral_congr fun r _ => ?_
        rw [hω r.toNNReal]
      simp only [twinGenerator, hX, hω]
    have hrhs : (∫ s in Ioc (0 : ℝ) τ, gTw s) = ∫ s in Ioc (0 : ℝ) τ, gDr s :=
      h34bB.symm.trans h34aB
    have hIoc_g : (∫ s in Ioc (0 : ℝ) τ, g s) = 0 := by
      have hcongr : (fun s => g s) = fun s => gTw s - gDr s := hg_eq
      simp only [hcongr]
      rw [integral_sub hgTw_cont.integrableOn_Ioc hgDr_cont.integrableOn_Ioc, hrhs, sub_self]
    have hτ0 : (0 : ℝ) ≤ τ := NNReal.coe_nonneg τ
    calc
      (∫ s in (0 : ℝ)..τ, g s) = ∫ s in Ioc (0 : ℝ) τ, g s :=
        intervalIntegral.integral_of_le hτ0
      _ = 0 := hIoc_g
  have hF : ∀ τ : ℝ, τ ∈ Icc (0 : ℝ) t → (∫ s in (0 : ℝ)..τ, g s) = 0 := by
    intro τ ⟨hτ0, hτt⟩
    rcases eq_or_lt_of_le hτ0 with h0 | h0
    · subst h0; simp
    · exact hcum ⟨τ, hτ0⟩ (by exact_mod_cast h0) (by exact_mod_cast hτt)
  have hg_zero_oo : ∀ τ ∈ Ioo (0 : ℝ) t, g τ = 0 := by
    intro τ ⟨hτ0, hτt⟩
    have hder : HasDerivAt (fun υ => ∫ s in (0 : ℝ)..υ, g s) (g τ) τ :=
      intervalIntegral.integral_hasDerivAt_right
        (hg_cont.intervalIntegrable _ _)
        (hg_cont.stronglyMeasurableAtFilter _ _)
        hg_cont.continuousAt
    have hF0 : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 τ] (fun υ => ∫ s in (0 : ℝ)..υ, g s) := by
      filter_upwards [Ioo_mem_nhds hτ0 hτt] with υ hυ
      exact (hF υ ⟨hυ.1.le, hυ.2.le⟩).symm
    exact HasDerivAt.unique (hder.congr_of_eventuallyEq hF0) (hasDerivAt_const _ _)
  have hg_t : g (t : ℝ) = 0 := by
    have hseq' : Tendsto (fun n : ℕ => (t : ℝ) * ((n : ℝ) / (n + 1))) atTop (𝓝 (t : ℝ)) := by
      have h := tendsto_const_nhds (x := (t : ℝ)) |>.mul (tendsto_natCast_div_add_atTop (1 : ℝ))
      simpa using h
    have hpos : ∀ᶠ n : ℕ in atTop, (t : ℝ) * ((n : ℝ) / (n + 1)) ∈ Ioo (0 : ℝ) t := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      have hden : (0 : ℝ) < n + 1 := by positivity
      have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
      refine ⟨mul_pos ht0 (div_pos hn0 hden), ?_⟩
      have : (t : ℝ) * (n / (n + 1)) < t * 1 :=
        mul_lt_mul_of_pos_left (div_lt_one hden |>.mpr (by linarith)) ht0
      simpa using this
    have heq : ∀ᶠ n : ℕ in atTop, g ((t : ℝ) * ((n : ℝ) / (n + 1))) = 0 := by
      filter_upwards [hpos] with n hn
      exact hg_zero_oo _ hn
    exact tendsto_nhds_unique (hg_cont.continuousAt.tendsto.comp hseq')
      (tendsto_nhds_of_eventually_eq heq)
  exact hm_eq.trans hg_t

/-- Weak adjoint identity against product test functions, via `IsJointDensity`. -/
theorem weak_joint_fokker_planck_product (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (ht : 0 < t)
    (φ : ℝ → ℝ → ℝ) (hφ : IsJointDensity P W σ 0 t φ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry φ) jointDomain)
    (u v : ℝ → ℝ) (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (huC : HasCompactSupport u) (hvC : HasCompactSupport v)
    (hsupp : tsupport (fun p : ℝ × ℝ => u p.1 * v p.2) ⊆ jointDomain) :
    ∫ p : ℝ × ℝ, u p.1 * v p.2 * jointFokkerPlanckAdjoint σ φ p.1 p.2 = 0 := by
  have hdyn := joint_dynkin_Aop_product P W hW σ t ht u v hu hv huC hvC
  -- E[jointA] = ∫∫ jointA · φ via `IsJointDensity`; IBP on jointDomain (boundary vanishes by
  -- `hsupp`) yields the adjoint pairing.
  sorry

/-- Pointwise vanishing of the adjoint from product weak identities. -/
theorem jointFokkerPlanckAdjoint_eq_zero (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (ht : 0 < t)
    (φ : ℝ → ℝ → ℝ) (hφ : IsJointDensity P W σ 0 t φ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry φ) jointDomain)
    (x y : ℝ) (hx : 0 < x) :
    jointFokkerPlanckAdjoint σ φ x y = 0 := by
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => jointFokkerPlanckAdjoint σ φ p.1 p.2) jointDomain := by
    -- C³ on the open joint domain ⇒ continuous second partials ⇒ continuous adjoint.
    have h3 := hsm 3
    -- Each term of `jointFokkerPlanckAdjoint` is continuous on `jointDomain`.
    sorry
  refine eq_zero_of_integral_product_eq_zero hcont ?_ hx
  intro u v hu hv huC hvC hts
  exact weak_joint_fokker_planck_product P W hW σ t ht φ hφ hsm u v hu hv huC hvC hts

/- Paper: p. 1070, (3.6b).
   Plain recap: the joint density φ satisfies the divergence-form PDE
   ∂ₓ[(σ²x²/2)∂ₓφ + σx ∂ᵧφ + (e^{σy} + σ²x/2 − 1)φ] = 0.
   PAPER NOTE: the skeleton placed the zeroth-order term outside ∂ₓ; restored to the
   paper's bracketed form (what §4 integrates in x). -/
theorem fokker_planck_joint (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (_hσ : 0 < σ) (ht : 0 < t)
    (φ : ℝ → ℝ → ℝ) (hφ : IsJointDensity P W σ 0 t φ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry φ) (Ioi (0 : ℝ) ×ˢ univ))
    (x y : ℝ) (hx : 0 < x) :
    deriv (fun x' =>
        σ ^ 2 * x' ^ 2 / 2 * deriv (fun z => φ z y) x'
          + σ * x' * deriv (fun y' => φ x' y') y
          + (Real.exp (σ * y) + σ ^ 2 * x' / 2 - 1) * φ x' y) x = 0 := by
  have hsm' : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry φ) jointDomain := by
    simpa [jointDomain] using hsm
  have hadj := jointFokkerPlanckAdjoint_eq_zero P W hW σ t ht φ hφ hsm' x y hx
  have hxmem : (x, y) ∈ jointDomain := mem_jointDomain hx
  have hnhds := isOpen_jointDomain.mem_nhds hxmem
  have hinner1 : ContDiffAt ℝ 1 (fun z : ℝ => (z, y)) x :=
    ContDiffAt.prodMk contDiffAt_id contDiffAt_const
  have hinner2 : ContDiffAt ℝ 2 (fun z : ℝ => (z, y)) x :=
    ContDiffAt.prodMk contDiffAt_id contDiffAt_const
  have hslice1 : ContDiffAt ℝ 1 (fun z : ℝ => φ z y) x := by
    have hAt : ContDiffAt ℝ 1 (Function.uncurry φ) (x, y) :=
      ((hsm' 1).contDiffWithinAt hxmem).contDiffAt hnhds
    exact ContDiffAt.comp x hAt hinner1
  have hslice2 : ContDiffAt ℝ 2 (fun z : ℝ => φ z y) x := by
    have hAt : ContDiffAt ℝ 2 (Function.uncurry φ) (x, y) :=
      ((hsm' 2).contDiffWithinAt hxmem).contDiffAt hnhds
    exact ContDiffAt.comp x hAt hinner2
  have hφx : HasDerivAt (fun z => φ z y) (deriv (fun z => φ z y) x) x :=
    (hasDerivAt_deriv_iff).2 (hslice1.differentiableAt (by decide))
  have hφxx : HasDerivAt (deriv fun z => φ z y)
      (deriv (deriv fun z => φ z y) x) x :=
    (hasDerivAt_deriv_iff).2
      ((hslice2.derivWithin (m := 1) (by decide)).differentiableAt (by decide))
  have hφxy : HasDerivAt (fun z => deriv (fun y' => φ z y') y)
      (deriv (fun z => deriv (fun y' => φ z y') y) x) x := by
    have hAt : ContDiffAt ℝ 2 (Function.uncurry φ) (x, y) :=
      ((hsm' 2).contDiffWithinAt hxmem).contDiffAt hnhds
    -- `z ↦ fderiv (φ z ·) y` is C¹, apply to `1` to recover `∂ᵧ`
    have hf : ContDiffAt ℝ 1 (fun z => fderiv ℝ (fun y' => φ z y') y) x :=
      ContDiffAt.fderiv (f := fun z y' => φ z y') (g := fun _ => y) hAt
        (by fun_prop) (by decide)
    have happly : ContDiffAt ℝ 1
        (fun z => fderiv ℝ (fun y' => φ z y') y (1 : ℝ)) x :=
      ContDiffAt.clm_apply hf contDiffAt_const
    have hident : (fun z => deriv (fun y' => φ z y') y) =
        fun z => fderiv ℝ (fun y' => φ z y') y (1 : ℝ) := by
      funext z; rfl
    rw [hident]
    exact (hasDerivAt_deriv_iff).2 (happly.differentiableAt (by decide))
  have hder := deriv_jointFlux σ φ x y hφx hφxx hφxy
  change deriv (fun x' => jointFlux σ φ x' y) x = 0
  rw [hder, hadj]

/- Paper: p. 1070, Remark 3.2.
   Plain recap: identity in law relating (X_t, M_t−W_t, M_t) to a reflected version. -/
theorem remark_3_2 (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (t : ℝ≥0) (_ht : 0 < t) :
    P.map (fun ω =>
      (expInt W 1 0 t ω,
        (⨆ s : Icc (0 : ℝ≥0) t, W s ω) - W t ω,
        ⨆ s : Icc (0 : ℝ≥0) t, W s ω)) =
    P.map (fun ω =>
      (Real.exp (-W t ω) * expInt W 1 0 t ω,
        ⨆ s : Icc (0 : ℝ≥0) t, W s ω,
        (⨆ s : Icc (0 : ℝ≥0) t, W s ω) - W t ω)) := by
  -- `B_s = W_{t-s} - W_t` (the negated time reversal of `W` on `[0, t]`) is again a BM,
  -- and the left-hand functional evaluated on `B` is the right-hand functional of `W`.
  have hB : IsBM P (-(timeReversed W t)) := (isBrownianReal_timeReversed P W hW t).neg
  let Φ : C(ℝ≥0, ℝ) → ℝ × ℝ × ℝ := fun x =>
    (∫ s in (0 : ℝ)..(t : ℝ), Real.exp (1 * x s.toNNReal + 0 * s),
      (⨆ s : Icc (0 : ℝ≥0) t, x s) - x t, ⨆ s : Icc (0 : ℝ≥0) t, x s)
  have hΦ : Measurable Φ := by
    refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
    · exact measurable_pathIntegral (fun s b => Real.exp (1 * b + 0 * s)) (by fun_prop) t
    · exact (measurable_pathSup t).sub (ContinuousMap.measurable_eval t)
    · exact measurable_pathSup t
  refine isBrownianReal_map_pathFunctional_eq P W (-(timeReversed W t)) hW hB Φ hΦ _ _ ?_ ?_
  · refine Eventually.of_forall fun ω x hx => ?_
    simp only [Φ, expInt, hx]
  · filter_upwards [hW.cont, hW.eval_zero_ae_eq_zero] with ω hcont h0 x hx
    have hBt : x t = -W t ω := by
      rw [hx]
      simp [timeReversed_eq_on_Icc W t le_rfl, h0]
    have hBs : ∀ s : Icc (0 : ℝ≥0) t, x s = W (t - s) ω - W t ω := by
      intro s
      rw [hx]
      simp [timeReversed_eq_on_Icc W t s.2.2]
    have hint : ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (1 * x s.toNNReal + 0 * s) =
        Real.exp (-W t ω) * expInt W 1 0 t ω := by
      have h := timeReversed_integral_eq W t ω (fun _ b => Real.exp (-b))
      simp only [expInt]
      rw [← intervalIntegral.integral_const_mul]
      calc ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (1 * x s.toNNReal + 0 * s)
          = ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-(timeReversed W t s.toNNReal ω)) := by
              refine intervalIntegral.integral_congr fun s _ => ?_
              simp [hx]
        _ = ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-(W t ω - W s.toNNReal ω)) := h.symm
        _ = _ := by
              refine intervalIntegral.integral_congr fun s _ => ?_
              simp only [← Real.exp_add]
              congr 1
              ring
    have hsup : (⨆ s : Icc (0 : ℝ≥0) t, x s) = (⨆ s : Icc (0 : ℝ≥0) t, W s ω) - W t ω := by
      have : Nonempty (Icc (0 : ℝ≥0) t) := ⟨⟨0, by simp⟩⟩
      let r : Icc (0 : ℝ≥0) t → Icc (0 : ℝ≥0) t := fun s => ⟨t - s, ⟨zero_le, tsub_le_self⟩⟩
      have hr : Function.Surjective r := fun y =>
        ⟨⟨t - y, ⟨zero_le, tsub_le_self⟩⟩, Subtype.ext (tsub_tsub_cancel_of_le y.2.2)⟩
      have hbdd : BddAbove (range fun s : Icc (0 : ℝ≥0) t => W (r s) ω) :=
        (isCompact_range (hcont.comp (continuous_subtype_val.comp
          (show Continuous r by fun_prop)))).bddAbove
      calc (⨆ s : Icc (0 : ℝ≥0) t, x s)
          = ⨆ s : Icc (0 : ℝ≥0) t, (W (r s) ω - W t ω) := iSup_congr hBs
        _ = (⨆ s : Icc (0 : ℝ≥0) t, W (r s) ω) - W t ω := (ciSup_sub hbdd _).symm
        _ = (⨆ s : Icc (0 : ℝ≥0) t, W s ω) - W t ω := by
              rw [hr.iSup_comp (fun s : Icc (0 : ℝ≥0) t => W s ω)]
    simp only [Φ, hint, hsup, hBt, sub_neg_eq_add, sub_add_cancel]

end Lyasoff2016
