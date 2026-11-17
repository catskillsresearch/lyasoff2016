/-
Path-space reciprocal of the finite-horizon `Z` process.
-/
module

public import Lyasoff2016.PerpetuityPath


@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal Real

noncomputable section
namespace Lyasoff2016

/-- Path-space reciprocal used for joint measurability of `Z⁻¹`. -/
def invZFromPaths (ν : ℝ) (s : ℝ≥0) (w b : C(ℝ≥0, ℝ)) : ℝ :=
  let A := perpetuityPath ν w
  let Y := A + ∫ u in (0 : ℝ)..(s : ℝ), Real.exp (-ν * u + b u.toNNReal)
  let Zv := Real.exp (ν * (s : ℝ) - b s) * Y
  if 0 < A then Zv⁻¹ else 0

namespace invZFromPaths

theorem continuous_time (ν : ℝ) (w b : C(ℝ≥0, ℝ)) :
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

theorem measurable (ν : ℝ) (s : ℝ≥0) :
    Measurable fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => invZFromPaths ν s p.1 p.2 := by
  have hA : Measurable fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => perpetuityPath ν p.1 :=
    (perpetuityPath.measurable ν).comp measurable_fst
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

end invZFromPaths

end Lyasoff2016
