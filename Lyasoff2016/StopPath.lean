/-
Path stopped at a fixed time (`stopPath`).
-/
module

public import Lyasoff2016.Setting


@[expose] public section

open MeasureTheory Set
open scoped NNReal Real

noncomputable section
namespace Lyasoff2016

/-- The path stopped at time `t`. -/
def stopPath (t : ℝ≥0) (x : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) :=
  ⟨fun s => x (min s t), x.continuous.comp (continuous_id.min continuous_const)⟩

namespace stopPath

theorem measurable (t : ℝ≥0) : Measurable (stopPath t) :=
  ContinuousMap.measurable_iff_eval.2 fun s => ContinuousMap.measurable_eval (min s t)

/-- On `[0, t]` the stopped path agrees with the path, so the time integral up to `t` of the
stopped path only sees the values `y` of the path. -/
theorem integral_eq (σ ν : ℝ) (t : ℝ≥0) (x : C(ℝ≥0, ℝ)) (y : ℝ≥0 → ℝ)
    (hxy : ∀ s, x s = y s) :
    ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (σ * stopPath t x s.toNNReal + ν * s) =
      ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (σ * y s.toNNReal + ν * s) := by
  refine intervalIntegral.integral_congr fun s hs => ?_
  have hsI : s ∈ Icc (0 : ℝ) (t : ℝ) := by
    simpa [uIcc_of_le (NNReal.coe_nonneg t)] using hs
  have hle : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hsI.2
  simp [stopPath, min_eq_left hle, hxy]

end stopPath

end Lyasoff2016

