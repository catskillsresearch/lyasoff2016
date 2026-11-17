/-
Path functional: reciprocal power of the finite-horizon `Z`.
-/
module

public import Lyasoff2016.PathMeasurable


@[expose] public section

open MeasureTheory Set
open scoped NNReal Real

noncomputable section
namespace Lyasoff2016

/-- Path functional: reciprocal power of the finite-horizon `Z` built from a continuous path
with fixed initial capital `A`. -/
def zpowPath (ν A : ℝ) (s : ℝ≥0) (m : ℕ) (x : C(ℝ≥0, ℝ)) : ℝ :=
  (Real.exp (ν * (s : ℝ) - x s) *
    (A + ∫ v in (0 : ℝ)..(s : ℝ), Real.exp (-ν * v + x v.toNNReal)))⁻¹ ^ m

namespace zpowPath

theorem measurable (ν A : ℝ) (s : ℝ≥0) (m : ℕ) :
    Measurable (zpowPath ν A s m) := by
  have hI : Measurable fun x : C(ℝ≥0, ℝ) =>
      ∫ v in (0 : ℝ)..(s : ℝ), Real.exp (-ν * v + x v.toNNReal) :=
    measurable_pathIntegral (fun v b => Real.exp (-ν * v + b)) (by fun_prop) s
  have hE : Measurable fun x : C(ℝ≥0, ℝ) => Real.exp (ν * (s : ℝ) - x s) :=
    Real.measurable_exp.comp
      ((measurable_const.sub (ContinuousMap.measurable_eval s)))
  exact (((hE.mul (measurable_const.add hI)).inv).pow_const m)

end zpowPath

end Lyasoff2016
