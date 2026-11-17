/-
Strike-derivative Asian integrand `F'_{t,σ,μ,k}(u,w)` (p. 1091).
-/
module

public import Lyasoff2016.Ffun
public import Lyasoff2016.SfunDerivC


@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/- Paper: p. 1091, display before (6.1):
     F'_{t,σ,μ,k(α)}(u,w) := B(w) C(u,w) g_{σ²t,4}(u − iπ/2) S'_{k(α),4}(u,w),
   here with k(α) = α. -/
def FfunDeriv (σ ν t k : ℝ) (u w : ℝ) : ℂ :=
  (Bfun σ ν t w : ℂ) * Cfun 4 σ ν t u w * gFour (σ ^ 2 * t) (u - Complex.I * (π / 2)) *
    SfunDerivC k 4 (Afun σ ν t u w)

end Lyasoff2016