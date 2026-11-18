/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Equality of laws of continuous path functionals of Brownian motions,
and the pathwise time-reversal change of variables for (1.3).
-/
module

public import BrownianMotion.Gaussian.BrownianMotion
public import Lyasoff2016.TimeReversal


@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

/- The cylinder functional of the integral against continuous V, evaluated on a path. -/
private def pathIntegralFun (n : ℕ) (V : Fin n → ℝ → ℝ → ℝ) (t : ℝ≥0)
    (path : ℝ≥0 → ℝ) : (Fin n → ℝ) × ℝ :=
  (fun i => ∫ s in (0 : ℝ)..(t : ℝ), V i s (path s.toNNReal), path t)

/- Paper: p. 1063, underlying uniqueness for (1.3).
   Plain recap: any two Brownian motions share the law of
   (∫₀ᵗ Vᵢ(s, ·_s) ds)_i paired with the terminal value, because both induce
   the same projective limit `gaussianLimit` on path space. -/
theorem isBrownianReal_integral_functional_law_eq
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W B : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) (hB : IsBrownianReal B P)
    (n : ℕ) (V : Fin n → ℝ → ℝ → ℝ)
    (hV : ∀ i, Continuous (Function.uncurry (V i))) (t : ℝ≥0) :
    P.map (fun ω => (fun i : Fin n =>
        ∫ s in (0 : ℝ)..(t : ℝ), V i s (W s.toNNReal ω), W t ω)) =
    P.map (fun ω => (fun i : Fin n =>
        ∫ s in (0 : ℝ)..(t : ℝ), V i s (B s.toNNReal ω), B t ω)) := by
  let W' := (hW.toIsPreBrownianReal).mk W
  let B' := (hB.toIsPreBrownianReal).mk B
  let pW : Ω → C(ℝ≥0, ℝ) :=
    fun ω => ⟨(fun s => W' s ω), hW.toIsPreBrownianReal.continuous_mk ω⟩
  let pB : Ω → C(ℝ≥0, ℝ) :=
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
  have hrawB : P.map (e ∘ pB) = gaussianLimit :=
    (hB.toIsPreBrownianReal.isBrownianReal_mk.toIsPreBrownianReal.hasLaw_gaussianLimit
      ((he.comp hpB).aemeasurable)).map_eq
  have hpath : P.map pW = P.map pB := by
    have hmap : (P.map pW).map e = (P.map pB).map e := by
      calc
        (P.map pW).map e = P.map (e ∘ pW) := Measure.map_map he hpW
        _ = gaussianLimit := hrawW
        _ = P.map (e ∘ pB) := hrawB.symm
        _ = (P.map pB).map e := (Measure.map_map he hpB).symm
    ext A hA
    have hA' : MeasurableSet[MeasurableSpace.comap e inferInstance] A :=
      he_comap.symm ▸ hA
    rcases hA' with ⟨S, hS, rfl⟩
    rw [← Measure.map_apply he hS, hmap, Measure.map_apply he hS]
  let Φ : C(ℝ≥0, ℝ) → (Fin n → ℝ) × ℝ := fun x =>
    (fun i => ∫ s in (0 : ℝ)..(t : ℝ), V i s (x s.toNNReal), x t)
  have hΦ : Measurable Φ := by
    apply Measurable.prodMk
    · rw [measurable_pi_iff]
      intro i
      simp only [intervalIntegral.intervalIntegral_eq_integral_uIoc]
      have hev : Continuous (fun p : C(ℝ≥0, ℝ) × ℝ => p.1 p.2.toNNReal) :=
        continuous_eval.comp
          (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))
      have hc : Continuous (fun p : C(ℝ≥0, ℝ) × ℝ =>
          V i p.2 (p.1 p.2.toNNReal)) :=
        (hV i).comp (continuous_snd.prodMk hev)
      have hsm : StronglyMeasurable (Function.uncurry
          (fun x : C(ℝ≥0, ℝ) => fun s : ℝ => V i s (x s.toNNReal))) :=
        hc.stronglyMeasurable
      have hm := (StronglyMeasurable.measurable <|
        StronglyMeasurable.integral_prod_right
          (ν := volume.restrict (uIoc (0 : ℝ) (t : ℝ))) hsm).const_smul
            ((if (0 : ℝ) ≤ (t : ℝ) then 1 else -1) : ℝ)
      change Measurable ((if (0 : ℝ) ≤ (t : ℝ) then 1 else -1 : ℝ) •
        (fun x : C(ℝ≥0, ℝ) =>
          ∫ s : ℝ, V i s (x s.toNNReal) ∂(volume.restrict (uIoc 0 (t : ℝ)))))
      exact hm
    · exact ContinuousMap.measurable_eval t
  have hmodW : ∀ᵐ ω ∂P, ∀ s, W' s ω = W s ω := hW.mk_ae_forall_eq
  have hmodB : ∀ᵐ ω ∂P, ∀ s, B' s ω = B s ω := hB.mk_ae_forall_eq
  calc
    P.map (fun ω => (fun i : Fin n =>
        ∫ s in (0 : ℝ)..(t : ℝ), V i s (W s.toNNReal ω), W t ω))
        = P.map (Φ ∘ pW) := Measure.map_congr <| hmodW.mono fun ω hω => by
            simp only [Function.comp_apply, Φ, pW]
            congr 1
            · funext i
              apply intervalIntegral.integral_congr
              intro s _
              change V i s (W s.toNNReal ω) = V i s (W' s.toNNReal ω)
              rw [hω]
            · change W t ω = W' t ω
              exact (hω t).symm
    _ = (P.map pW).map Φ := (Measure.map_map hΦ hpW).symm
    _ = (P.map pB).map Φ := by rw [hpath]
    _ = P.map (Φ ∘ pB) := Measure.map_map hΦ hpB
    _ = P.map (fun ω => (fun i : Fin n =>
        ∫ s in (0 : ℝ)..(t : ℝ), V i s (B s.toNNReal ω), B t ω)) :=
      Measure.map_congr <| hmodB.mono fun ω hω => by
        simp only [Function.comp_apply, Φ, pB]
        congr 1
        · funext i
          apply intervalIntegral.integral_congr
          intro s _
          change V i s (B' s.toNNReal ω) = V i s (B s.toNNReal ω)
          rw [hω]
        · change B' t ω = B t ω
          exact hω t

private theorem toNNReal_sub_of_mem_Icc {t : ℝ≥0} {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (t : ℝ)) :
    ((t : ℝ) - u).toNNReal = t - u.toNNReal := by
  have hu0 : 0 ≤ u := hu.1
  have hut : u ≤ (t : ℝ) := hu.2
  apply NNReal.coe_injective
  rw [Real.coe_toNNReal _ (sub_nonneg.mpr hut), NNReal.coe_sub
    (Real.toNNReal_le_iff_le_coe.mpr hut), Real.coe_toNNReal _ hu0]

private theorem toNNReal_of_mem_Icc {t : ℝ≥0} {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (t : ℝ)) :
    u.toNNReal ≤ t :=
  Real.toNNReal_le_iff_le_coe.mpr hu.2

namespace timeReversed

/- Pathwise change of variables: Ψ(W)(ω) = Φ(timeReversed W t)(ω) for each coordinate. -/
omit [MeasurableSpace Ω] in
theorem integral_eq
    (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) (V : ℝ → ℝ → ℝ) :
    (∫ s in (0 : ℝ)..(t : ℝ), V ((t : ℝ) - s) (W t ω - W s.toNNReal ω)) =
    (∫ s in (0 : ℝ)..(t : ℝ), V s (timeReversed W t s.toNNReal ω)) := by
  have hrewrite :
      (∫ s in (0 : ℝ)..(t : ℝ), V ((t : ℝ) - s) (W t ω - W s.toNNReal ω)) =
      ∫ s in (0 : ℝ)..(t : ℝ),
        V ((t : ℝ) - s) (W t ω - W ((t : ℝ) - ((t : ℝ) - s)).toNNReal ω) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hsI : s ∈ Icc (0 : ℝ) (t : ℝ) := by
      simpa [uIcc_of_le (NNReal.coe_nonneg t)] using hs
    congr 2
    have : ((t : ℝ) - ((t : ℝ) - s)).toNNReal = s.toNNReal := by
      simp [sub_sub_cancel]
    rw [this]
  rw [hrewrite]
  let f : ℝ → ℝ := fun u => V u (W t ω - W ((t : ℝ) - u).toNNReal ω)
  have hsub :
      (∫ s in (0 : ℝ)..(t : ℝ), f ((t : ℝ) - s)) =
      ∫ u in (0 : ℝ)..(t : ℝ), f u := by
    simp [sub_self, sub_zero,
      intervalIntegral.integral_comp_sub_left (f := f) (a := (0 : ℝ)) (b := (t : ℝ)) (t : ℝ)]
  change (∫ s in (0 : ℝ)..(t : ℝ), f ((t : ℝ) - s)) =
    ∫ s in (0 : ℝ)..(t : ℝ), V s (timeReversed W t s.toNNReal ω) at *
  rw [hsub]
  refine intervalIntegral.integral_congr fun u hu => ?_
  have huI : u ∈ Icc (0 : ℝ) (t : ℝ) := by
    simpa [uIcc_of_le (NNReal.coe_nonneg t)] using hu
  have hle := toNNReal_of_mem_Icc (t := t) huI
  have htr : timeReversed W t u.toNNReal ω = W t ω - W (t - u.toNNReal) ω :=
    timeReversed.eq_on_Icc W t hle ω
  change V u (W t ω - W ((t : ℝ) - u).toNNReal ω) = V u (timeReversed W t u.toNNReal ω)
  rw [htr, toNNReal_sub_of_mem_Icc huI]

/- Bundle the pathwise identity for the Fin n-valued functional used in (1.3). -/
omit [MeasurableSpace Ω] in
theorem functional_eq
    (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) (n : ℕ) (V : Fin n → ℝ → ℝ → ℝ)
    (hW0 : W 0 ω = 0) :
    (fun i : Fin n => ∫ s in (0 : ℝ)..(t : ℝ),
        V i ((t : ℝ) - s) (W t ω - W s.toNNReal ω), W t ω) =
    (fun i : Fin n => ∫ s in (0 : ℝ)..(t : ℝ),
        V i s (timeReversed W t s.toNNReal ω), timeReversed W t t ω) := by
  have hterm : timeReversed W t t ω = W t ω := by
    rw [timeReversed.eq_on_Icc W t le_rfl, tsub_self, hW0, sub_zero]
  refine Prod.ext ?_ hterm.symm
  funext i
  exact timeReversed.integral_eq W t ω (V i)

end timeReversed

end Lyasoff2016
