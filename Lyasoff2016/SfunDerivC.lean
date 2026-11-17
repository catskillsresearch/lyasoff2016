/-
Strike-derivative kernel `S'_{k,p}(A)` for complex rate `A` (p. 1091).
-/
module

public import Lyasoff2016.Setting


@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/- Paper: p. 1091, S'_{k(α),p} := ∂_α S_{k(α),p} = −k'(α) ∫_{k(α)}^∞ e^{−A/x} x^{−p} dx,
   taken here with the strike itself as parameter (k(α) = α, k' = 1). -/
def SfunDerivC (k : ℝ) (p : ℕ) (A : ℂ) : ℂ :=
  -∫ x in Ioi k, ((x ^ (-(p : ℤ)) : ℝ) : ℂ) * Complex.exp (-A / x)

end Lyasoff2016