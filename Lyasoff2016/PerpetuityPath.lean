/-
Path-space perpetuity functional.
-/
module

public import Lyasoff2016.PathMeasurable


@[expose] public section

open MeasureTheory Set
open scoped NNReal Real

noncomputable section
namespace Lyasoff2016

/-- Path-space perpetuity functional. -/
def perpetuityPath (ν : ℝ) (x : C(ℝ≥0, ℝ)) : ℝ :=
  ∫ s in Ioi (0 : ℝ), Real.exp (x s.toNNReal + ν * s)

namespace perpetuityPath

theorem measurable (ν : ℝ) : Measurable (perpetuityPath ν) :=
  measurable_pathSetIntegral (fun s w => Real.exp (w + ν * s)) (by fun_prop) (Ioi 0)

end perpetuityPath

end Lyasoff2016
