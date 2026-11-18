/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
π-formula for the conditional density (5.9b)/(5.10b).
-/
module

public import Lyasoff2016.GFun


@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/- Paper: (5.9b)/(5.10b), π-formula for the conditional density, normalised so that
   `gaussianPDFReal 0 t y * (σ²)⁻¹ * piFormula p σ t (x σ²) (y σ)` is the joint density.
   PAPER NOTE: includes the Jacobian/scaling factor σ⁴ and the paper's sinh-integral
   form; the skeleton's stub `∫ (gFun …).re` omitted these and made Remark 5.1 false. -/
def piFormula (p : ℕ) (σ t x y : ℝ) : ℝ :=
  if 0 < x then
    σ ^ 4 * (16 / x ^ p) *
      Real.exp (y * (p - 1) / 2 + y ^ 2 / (2 * (t * σ ^ 2)) - 2 * (Real.exp y + 1) / x) *
      ∫ u in Ioi (0 : ℝ), Real.sinh u *
        (((Real.exp (-(4 / x) * Real.exp (y / 2) * Real.cosh u) : ℝ) : ℂ) *
          gFun p (t * σ ^ 2) (u - I * π)).re
  else 0

end Lyasoff2016