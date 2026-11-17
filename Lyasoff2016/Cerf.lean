/-
Complex error function `cerf` used in integral representations (p. 1082–1083).
-/
module

public import Lyasoff2016.Setting


@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/- Paper: p. 1082–1083, complex error function used to build g_{t,p} for p = 3,4.
   Plain recap: entire function erf on ℂ, defined via the Gaussian integral. -/
def cerf (z : ℂ) : ℂ :=
  (2 / Real.sqrt Real.pi : ℂ) * ∫ t in (0 : ℝ)..1, Complex.exp (-(t * z) ^ 2) * z

end Lyasoff2016