/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Joint integrability of `(s, ω) ↦ exp (σ W_s ω + ν s)` on `(0, t] × Ω` for a Brownian motion `W`.

Used to justify the Fubini swap in the `K = 0` benchmark of Remark 6.1 (p. 1092).
`IsBrownianReal` only gives a.s. continuous paths, so joint measurability is obtained from the
continuous modification `IsPreBrownianReal.mk`, which agrees with `W` off a `P`-null set.
-/
module

public import Lyasoff2016.Setting


@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Gaussian mgf along a Brownian motion: `E[exp (σ W_s + ν s)] = exp ((ν + σ²/2) s)`. -/
theorem integral_exp_bm (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ ν : ℝ) (s : ℝ≥0) :
    ∫ ω, Real.exp (σ * W s ω + ν * s) ∂P = Real.exp ((ν + σ ^ 2 / 2) * s) := by
  have hlaw : HasLaw (W s) (gaussianReal 0 s) P := hW.hasLaw_eval _
  have hmgf := mgf_gaussianReal (X := W s) (μ := 0) (v := s) hlaw σ
  unfold mgf at hmgf
  have hfactor : ∫ ω, Real.exp (σ * W s ω + ν * s) ∂P =
      Real.exp (ν * s) * ∫ ω, Real.exp (σ * W s ω) ∂P := by
    rw [← integral_const_mul]
    congr 1
    funext ω
    rw [Real.exp_add, mul_comm]
  rw [hfactor, hmgf, ← Real.exp_add]
  congr 1
  ring

/-- `ω ↦ exp (σ W_s ω + ν s)` is integrable for a Brownian motion `W`. -/
theorem integrable_exp_bm (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ ν : ℝ) (s : ℝ≥0) :
    Integrable (fun ω => Real.exp (σ * W s ω + ν * s)) P := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_exp_bm P W hW σ ν s]
  exact (Real.exp_pos _).ne'

/-- Joint integrability of `(s, ω) ↦ exp (σ W_s ω + ν s)` on `(0, t] × Ω`: the Fubini hypothesis
for exchanging `E` and `∫₀ᵗ ds` in the `K = 0` benchmark. -/
theorem integrable_uncurry_exp_bm (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ ν : ℝ) (t : ℝ≥0) :
    Integrable (Function.uncurry
      (fun s : ℝ => fun ω => Real.exp (σ * W s.toNNReal ω + ν * s)))
      ((volume.restrict (uIoc (0 : ℝ) (t : ℝ))).prod P) := by
  -- Continuous modification: jointly measurable and indistinguishable from `W`.
  let B : ℝ≥0 → Ω → ℝ := hW.toIsPreBrownianReal.mk W
  have hBmeas : ∀ s, Measurable (B s) := fun s => hW.toIsPreBrownianReal.measurable_mk s
  have hBcont : ∀ ω, Continuous (B · ω) := fun ω => hW.toIsPreBrownianReal.continuous_mk ω
  have hmod : ∀ᵐ ω ∂P, ∀ s, B s ω = W s ω := hW.mk_ae_forall_eq
  have hBjoint : Measurable (Function.uncurry (fun s : ℝ => fun ω => B s.toNNReal ω)) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun ω => (hBcont ω).comp continuous_real_toNNReal) (fun s => hBmeas s.toNNReal)
  have hgB : Measurable (fun p : ℝ × Ω => Real.exp (σ * B p.1.toNNReal p.2 + ν * p.1)) :=
    Real.measurable_exp.comp ((hBjoint.const_mul σ).add (measurable_fst.const_mul ν))
  have hae : (fun p : ℝ × Ω => Real.exp (σ * B p.1.toNNReal p.2 + ν * p.1)) =ᵐ[
      (volume.restrict (uIoc (0 : ℝ) (t : ℝ))).prod P]
      Function.uncurry (fun s : ℝ => fun ω => Real.exp (σ * W s.toNNReal ω + ν * s)) := by
    have h := (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (uIoc (0 : ℝ) (t : ℝ))) (ν := P)).ae hmod
    filter_upwards [h] with p hp
    simp only [Function.uncurry]
    rw [hp]
  have hasm : AEStronglyMeasurable (Function.uncurry
      (fun s : ℝ => fun ω => Real.exp (σ * W s.toNNReal ω + ν * s)))
      ((volume.restrict (uIoc (0 : ℝ) (t : ℝ))).prod P) :=
    hgB.aestronglyMeasurable.congr hae
  rw [integrable_prod_iff hasm]
  refine ⟨?_, ?_⟩
  · -- each time slice is integrable (Gaussian mgf)
    refine ae_restrict_of_forall_mem measurableSet_uIoc fun s hs => ?_
    have hs0 : 0 ≤ s := by
      rw [uIoc_of_le (NNReal.coe_nonneg t)] at hs
      exact hs.1.le
    have h := integrable_exp_bm P W hW σ ν s.toNNReal
    simpa only [Function.uncurry, Real.coe_toNNReal s hs0] using h
  · -- the slice norms integrate to the continuous function `s ↦ exp ((ν + σ²/2) s)`
    have hcont : Continuous fun s : ℝ => Real.exp ((ν + σ ^ 2 / 2) * s) := by fun_prop
    have hI : Integrable (fun s : ℝ => Real.exp ((ν + σ ^ 2 / 2) * s))
        (volume.restrict (uIoc (0 : ℝ) (t : ℝ))) :=
      (hcont.intervalIntegrable 0 (t : ℝ)).def'
    refine hI.congr ?_
    refine ae_restrict_of_forall_mem measurableSet_uIoc fun s hs => ?_
    have hs0 : 0 ≤ s := by
      rw [uIoc_of_le (NNReal.coe_nonneg t)] at hs
      exact hs.1.le
    have h := integral_exp_bm P W hW σ ν s.toNNReal
    rw [Real.coe_toNNReal s hs0] at h
    simp only [Function.uncurry, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact h.symm

end Lyasoff2016
