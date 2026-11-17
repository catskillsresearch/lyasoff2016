/-
Contour equation (5.3) on ζ_a and analytic input that g_{t,p} solves it.
-/
module

public import Lyasoff2016.ContourIntegrand


@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/- Paper: p. 1080, (5.3), on the contour ζ = ζ_a of p. 1082, in the form of the display
   on p. 1083 ("With a completely analogous calculation, (5.3) can be cast as"):
     2 ∫_{−∞}^{∞} ℜ( g_{t,p}(u − ia) / (cosh(u − ia) − cosh y)^{p−1} · sinh(u − ia) ) du
       = ((−4)^{p−2} / (p−2)!) e^{−2y²/t}.
   Plain recap: ζ_a is the boundary of the strip {|ℑ z| < a}; since g_{t,p}(z̄) = −conj g_{t,p}(z)
   the upper edge contributes the conjugate of the lower one, leaving twice the real part.
   This is the only condition imposed on g_{t,p} (footnote 9).  The integrand is also
   required to be integrable (pp. 1084–1085).
   PAPER NOTE: earlier versions of `contourEq` took a density `φc` and equated
   `laplaceCond φc y ξ` with `0`, resp. with `∫ ℜ((−4/ξ)^{p−1} · contourIntegrand)`.  Neither
   is in the paper, and both are false for a genuine conditional density (at ξ = 0 they give
   `∫ φc(x|y) dx = 0`).  (5.3) involves no density: it is a statement about g_{t,p}, the
   contour ζ_a and y only. -/
def contourEq (p : ℕ) (t : ℝ) (y : ℝ) (a : ℝ) : Prop :=
  Integrable (fun u : ℝ => contourIntegrand p t a y u) ∧
  2 * ∫ u : ℝ, (contourIntegrand p t a y u).re =
    (-4 : ℝ) ^ (p - 2) / ((p - 2).factorial : ℝ) * Real.exp (-2 * y ^ 2 / t)

/- Paper: p. 1082–1085.
   Plain recap: g_{t,p} of (5.8) solves the contour equation (5.3) on ζ_a for every opening
   a ∈ [π/2, 3π/2] and every y ∈ ℝ (residues at z = ±y via (5.5)–(5.7); the vertical sides
   cancel because g_{t,p} is even).
   STATUS: not proved in Lean; the residue computation is taken as analytic input. -/
/-- Contour/residue identity (Lyasoff pp. 1082–1085); hole pending residue analysis. -/
theorem g_solves_contour_equation (p : ℕ) (hp : p = 2 ∨ p = 3 ∨ p = 4)
    (t : ℝ) (ht : 0 < t) (y : ℝ) (a : ℝ) (ha : Real.pi / 2 ≤ a ∧ a ≤ 3 * Real.pi / 2) :
    contourEq p t y a := by
  sorry

end Lyasoff2016