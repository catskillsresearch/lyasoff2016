/-
Hartman–Watson-type kernel θ(r, t) in Yor's joint density formula.
-/
module

public import Lyasoff2016.Setting


@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/- Paper: p. 1062, θ(r,t) in Yor’s formula.
   Plain recap: the Hartman–Watson-type kernel appearing in Yor’s density. -/
def theta (r t : ℝ) : ℝ :=
  r / Real.sqrt (2 * Real.pi ^ 3 * t) * Real.exp (Real.pi ^ 2 / (2 * t)) *
    ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * t)) * Real.exp (-r * Real.cosh u) *
      Real.sinh u * Real.sin (Real.pi * u / t)

end Lyasoff2016