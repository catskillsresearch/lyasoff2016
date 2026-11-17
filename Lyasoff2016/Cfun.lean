/-
Contour prefactor `C(u,w)` of the π/2-formula (p. 1090).
-/
module

public import Lyasoff2016.Setting


@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/- Paper: p. 1090, display defining C(u,w):
     C(u,w) := 8 i √2 σ^{−2p+2} w^{p−1} cosh u e^{μpt/2 − μt/2} / √(πt). -/
def Cfun (p : ℕ) (σ ν t : ℝ) (u w : ℝ) : ℂ :=
  ((8 * √2 * σ ^ (-2 * (p : ℤ) + 2) * w ^ ((p : ℤ) - 1) * Real.cosh u *
      Real.exp (ν * p * t / 2 - ν * t / 2) / √(π * t) : ℝ) : ℂ) * Complex.I

end Lyasoff2016