/-
π/2-formula for the conditional density (5.9a)/(5.10a).
-/
module

public import Lyasoff2016.GFun


@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/- Paper: (5.9a)/(5.10a), π/2-formula (same normalisation). -/
def piHalfFormula (p : ℕ) (σ t x y : ℝ) : ℝ :=
  σ ^ 4 * (16 / x ^ p) *
    Real.exp (y * (p - 1) / 2 + y ^ 2 / (2 * (t * σ ^ 2)) - 2 * (Real.exp y + 1) / x) *
    ∫ u in Ioi (0 : ℝ), Real.sinh u *
      (((Real.exp (-(4 / x) * Real.exp (y / 2) * Real.cosh u) : ℝ) : ℂ) *
        gFun p (t * σ ^ 2) (u - I * (Real.pi / 2))).re

end Lyasoff2016