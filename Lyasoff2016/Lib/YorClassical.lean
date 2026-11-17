/-
Classical citation of Yor’s joint density formula (Yor 1992, (6.c)), used by
`yor_formula_classical` as an external analytic input independent of the §5 contour route.
-/
module

public import Lyasoff2016.Setting


@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Classical theorem: for Brownian motion, the law of
`(∫₀ᵗ exp(2 W_s) ds, W_t)` admits the Yor density (1.1) / [33, (6.c)].

This is taken as a classical analytic input (Yor, *Some Aspects of Brownian Motion*,
Part I, (6.c)); the project’s contour analysis recovers it as a special case via
`remark_5_1`, but the direct density identification is not re-derived here. -/
axiom yor_joint_density_classical (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (t : ℝ≥0) (ht : 0 < t) :
    IsJointDensity P W 2 0 t (fun x y => yorDensity t x y)

end Lyasoff2016
