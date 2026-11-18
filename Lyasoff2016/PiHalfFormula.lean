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

/- Paper: (5.9a)/(5.10a), π/2-formula, normalised so that
   `gaussianPDFReal 0 t y * (σ²)⁻¹ * piHalfFormula p σ t (x σ²) (y σ)` is the joint density
   (same scaled-coordinate convention as `piFormula`).
   Outside weight is `cosh u`; the oscillatory kernel is
   `ℜ(i exp(-i (4/x) e^{y/2} sinh u) g_{σ²t,p}(u − iπ/2))` — not the π-kernel. -/
def piHalfFormula (p : ℕ) (σ t x y : ℝ) : ℝ :=
  if 0 < x then
    σ ^ 4 * (16 / x ^ p) *
      Real.exp (y * (p - 1) / 2 + y ^ 2 / (2 * (t * σ ^ 2)) - 2 * (Real.exp y + 1) / x) *
      ∫ u in Ioi (0 : ℝ), Real.cosh u *
        (I * cexp (-I * ((4 / x : ℂ) * Real.exp (y / 2) * Real.sinh u)) *
          gFun p (t * σ ^ 2) (u - I * (Real.pi / 2))).re
  else 0

end Lyasoff2016
