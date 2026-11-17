/-
Residue recipe R_{t,p}[g] from (5.7).
-/
module

public import Lyasoff2016.Setting


@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/- Paper: p. 1081, (5.7), the residue recipe g ↦ R_{t,p}[g]:
     R_{t,2}(y) = g(y),   R_{t,p}(y) = (1 / ((p−2) sinh y)) (d/dy) R_{t,p−1}(y)   (p ≥ 3).
   Plain recap: R_{t,p}[g](y) is the residue at z = y of g(z) sinh z / (cosh z − cosh y)^{p−1}
   (display (5.6)), produced recursively from the generic symbol g.
   The recursion divides by sinh y, so for p ≥ 3 the value at y = 0 is Lean's `x / 0 = 0`
   rather than the limit in (5.6); only y ≠ 0 is meaningful there. -/
def Rrecipe (g : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => g
  | 1 => g
  | 2 => g
  | (p + 3) => fun y => deriv (Rrecipe g (p + 2)) y / (((p + 1 : ℕ) : ℂ) * Real.sinh y)

end Lyasoff2016