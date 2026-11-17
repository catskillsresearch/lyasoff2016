/-
Yor candidate joint density for σ = 2 (Lyasoff (1.1)).
-/
module

public import Lyasoff2016.Theta


@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/- Paper: p. 1061, (1.1).
   Plain recap: Yor’s candidate joint density for σ = 2. -/
def yorDensity (t x y : ℝ) : ℝ :=
  (1 / x) * Real.exp (-(1 + Real.exp (2 * y)) / (2 * x)) * theta (Real.exp y / x) t

end Lyasoff2016