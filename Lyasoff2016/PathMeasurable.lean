/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Measurability of path-space integral and running-supremum functionals.
-/
module

public import Lyasoff2016.Setting


@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/-- The time-set integral `∫_S V s (x s) ds` is a measurable functional on path space. -/
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

end Lyasoff2016
