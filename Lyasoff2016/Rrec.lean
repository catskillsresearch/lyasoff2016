/-
Concrete residues R_{t,p} for g = g_{t,p} of (5.8).
-/
module

public import Lyasoff2016.Rrecipe
public import Lyasoff2016.GFun


@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/- Paper: (5.6)/(5.7), R_{t,p}(y) for the concrete choice g = g_{t,p} of (5.8).
   PAPER NOTE: the skeleton's `Rrec p t y a := gFun p t (a i)` was not the paper's recipe
   (R_{t,p} is a function of y and does not involve the contour parameter a). -/
def Rrec (p : ℕ) (t : ℝ) (y : ℝ) : ℂ :=
  Rrecipe (fun s : ℝ => gFun p t s) p y

namespace Rrec

/-- (5.7) for p = 2: `R_{t,2} = g_{t,2}`. -/
lemma two (t y : ℝ) : Rrec 2 t y = gFun 2 t y := rfl

end Rrec

end Lyasoff2016