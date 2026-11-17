/-
Asian complex integrand `F_{t,σ,μ,k}(u,w)` (p. 1091).
-/
module

public import Lyasoff2016.Afun
public import Lyasoff2016.Bfun
public import Lyasoff2016.Cfun
public import Lyasoff2016.SfunC
public import Lyasoff2016.GFun


@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/- Paper: p. 1082, (5.8), the case p = 4 — alias of `gFun 4`. -/
abbrev gFour (t : ℝ) (z : ℂ) : ℂ := gFun 4 t z

/- Paper: p. 1091, display before (6.1):
     F_{t,σ,μ,k}(u,w) := B(w) C(u,w) g_{σ²t,4}(u − iπ/2) S_{k,4}(u,w). -/
def Ffun (σ ν t k : ℝ) (u w : ℝ) : ℂ :=
  (Bfun σ ν t w : ℂ) * Cfun 4 σ ν t u w * gFour (σ ^ 2 * t) (u - Complex.I * (π / 2)) *
    SfunC k 4 (Afun σ ν t u w)

end Lyasoff2016