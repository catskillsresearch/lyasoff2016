/-
Contour-equation integrand (5.3) on the lower edge u ↦ u − ia.
-/
module

public import Lyasoff2016.GFun


@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/- Paper: p. 1080, (5.3), the integrand of the contour equation on the lower edge
   u ↦ u − ia of the contour ζ_a (p. 1082):
     g_{t,p}(u − ia) sinh(u − ia) / (cosh(u − ia) − cosh y)^{p−1}. -/
def contourIntegrand (p : ℕ) (t a y u : ℝ) : ℂ :=
  gFun p t (u - I * a) * Complex.sinh (u - I * a) /
    (Complex.cosh (u - I * a) - Complex.cosh y) ^ (p - 1)

end Lyasoff2016