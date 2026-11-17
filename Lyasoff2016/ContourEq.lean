/-
Contour equation (5.3) on ζ_a and proof that g_{t,p} solves it.
-/
module

public import Lyasoff2016.ContourIntegrand
public import Lyasoff2016.ContourTwo
public import Lyasoff2016.ContourRec


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

namespace contourEq

/-- The integral of the real part is the real part of the integral. -/
lemma integral_re_eq {f : ℝ → ℂ} (hf : Integrable f) :
    ∫ u : ℝ, (f u).re = (∫ u : ℝ, f u).re :=
  Complex.reCLM.integral_comp_comm hf

lemma integrand_two (t a y : ℝ) :
    (fun u : ℝ => contourIntegrand 2 t a y u) = fun u : ℝ =>
      gFun 2 t (u - I * a) * Complex.sinh (u - I * a) /
        (Complex.cosh (u - I * a) - Complex.cosh y) := by
  funext u
  simp only [contourIntegrand, Nat.reduceSub, pow_one]

lemma integrand_three (t a y : ℝ) :
    (fun u : ℝ => contourIntegrand 3 t a y u) = fun u : ℝ =>
      gFun 3 t (u - I * a) * Complex.sinh (u - I * a) /
        (Complex.cosh (u - I * a) - Complex.cosh y) ^ 2 := by
  funext u
  simp only [contourIntegrand, Nat.reduceSub]

lemma integrand_four (t a y : ℝ) :
    (fun u : ℝ => contourIntegrand 4 t a y u) = fun u : ℝ =>
      gFun 4 t (u - I * a) * Complex.sinh (u - I * a) /
        (Complex.cosh (u - I * a) - Complex.cosh y) ^ 3 := by
  funext u
  simp only [contourIntegrand, Nat.reduceSub]

/- Paper: p. 1082–1083, (5.3) with (5.5) for p = 2.
   Plain recap: residues of g_{t,2}(z) sinh z / (cosh z − cosh y) at z = ±y inside the strip;
   the vertical sides vanish (Gaussian decay) and the upper edge is the conjugate of the lower
   one.  Proved in `ContourTwo.contour_two` for every opening 0 < a < 2π. -/
/-- Contour equation for `p = 2`. -/
theorem two {t : ℝ} (ht : 0 < t) (y : ℝ) {a : ℝ}
    (ha : Real.pi / 2 ≤ a ∧ a ≤ 3 * Real.pi / 2) : contourEq 2 t y a := by
  have ha0 : 0 < a := by linarith [Real.pi_pos]
  have ha2 : a < 2 * Real.pi := by linarith [Real.pi_pos]
  obtain ⟨hInt, hid⟩ := ContourTwo.contour_two ht y ha0 ha2
  have hInt' : Integrable (fun u : ℝ => contourIntegrand 2 t a y u) := by
    rw [integrand_two]; exact hInt
  refine ⟨hInt', ?_⟩
  rw [integral_re_eq hInt', integrand_two, hid]
  norm_num

/- Paper: p. 1081, (5.7), and p. 1084, (5.8): g_{t,3}' = −4 sinh · g_{t,2}.
   Plain recap: integrating d/du [g_{t,3}(z)/(cosh z − cosh y)] over the lower edge gives
   ∫ (integrand for p = 3) = −4 ∫ (integrand for p = 2) (`ContourRec.integral_three`). -/
/-- Contour equation for `p = 3`. -/
theorem three {t : ℝ} (ht : 0 < t) (y : ℝ) {a : ℝ}
    (ha : Real.pi / 2 ≤ a ∧ a ≤ 3 * Real.pi / 2) : contourEq 3 t y a := by
  have ha0 : 0 < a := by linarith [Real.pi_pos]
  have ha2 : a < 2 * Real.pi := by linarith [Real.pi_pos]
  have hc : Real.cos a ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le ha.1 (by linarith [Real.pi_pos])
  obtain ⟨hInt2, hid⟩ := ContourTwo.contour_two ht y ha0 ha2
  have hInt' : Integrable (fun u : ℝ => contourIntegrand 3 t a y u) := by
    rw [integrand_three]; exact ContourRec.integrable_three t y hc
  refine ⟨hInt', ?_⟩
  rw [integral_re_eq hInt', integrand_three, ContourRec.integral_three ht y hc hInt2]
  have hre : ∀ J : ℂ, (-4 * J).re = -4 * J.re := fun J => by simp
  have hfac : (-4 : ℝ) ^ (3 - 2) / ((3 - 2).factorial : ℝ) = -4 := by norm_num
  rw [hre, hfac]
  -- 2 * (-4 * (∫₂).re) = -4 * (2 * (∫₂).re) = -4 * exp
  calc 2 * (-4 * _) = -4 * (2 * _) := by ring
    _ = -4 * Real.exp (-2 * y ^ 2 / t) := by rw [hid]

/- Paper: p. 1081, (5.7), and p. 1084, (5.8): g_{t,4}' = −4 sinh · g_{t,3}.
   Plain recap: integrating d/du [g_{t,4}(z)/(cosh z − cosh y)²] over the lower edge gives
   ∫ (integrand for p = 4) = −2 ∫ (integrand for p = 3) (`ContourRec.integral_four`). -/
/-- Contour equation for `p = 4`. -/
theorem four {t : ℝ} (ht : 0 < t) (y : ℝ) {a : ℝ}
    (ha : Real.pi / 2 ≤ a ∧ a ≤ 3 * Real.pi / 2) : contourEq 4 t y a := by
  have ha0 : 0 < a := by linarith [Real.pi_pos]
  have ha2 : a < 2 * Real.pi := by linarith [Real.pi_pos]
  have hc : Real.cos a ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le ha.1 (by linarith [Real.pi_pos])
  obtain ⟨hInt2, hid⟩ := ContourTwo.contour_two ht y ha0 ha2
  have hInt' : Integrable (fun u : ℝ => contourIntegrand 4 t a y u) := by
    rw [integrand_four]; exact ContourRec.integrable_four t y hc
  refine ⟨hInt', ?_⟩
  rw [integral_re_eq hInt', integrand_four, ContourRec.integral_four ht y hc,
    ContourRec.integral_three ht y hc hInt2]
  have hre : ∀ J : ℂ, (-2 * (-4 * J)).re = 8 * J.re := fun J => by
    simp; ring
  have hfac : (-4 : ℝ) ^ (4 - 2) / ((4 - 2).factorial : ℝ) = 8 := by
    norm_num [Nat.factorial]
  rw [hre, hfac]
  -- 2 * (8 * (∫₂).re) = 8 * (2 * (∫₂).re) = 8 * exp
  calc 2 * (8 * _) = 8 * (2 * _) := by ring
    _ = 8 * Real.exp (-2 * y ^ 2 / t) := by rw [hid]


end contourEq

/- Paper: p. 1082–1085.
   Plain recap: g_{t,p} of (5.8) solves the contour equation (5.3) on ζ_a for every opening
   a ∈ [π/2, 3π/2] and every y ∈ ℝ.  For p = 2 this is the residue computation at z = ±y
   (the vertical sides vanish and the upper edge is the conjugate of the lower one); for
   p = 3, 4 the relations g_{t,p}' = −4 sinh · g_{t,p−1} behind the recipe (5.7) reduce the
   edge integral to the one for p − 1 by integration by parts, with factor −4/(p−2). -/
/-- Contour/residue identity (Lyasoff pp. 1082–1085). -/
theorem g_solves_contour_equation (p : ℕ) (hp : p = 2 ∨ p = 3 ∨ p = 4)
    (t : ℝ) (ht : 0 < t) (y : ℝ) (a : ℝ) (ha : Real.pi / 2 ≤ a ∧ a ≤ 3 * Real.pi / 2) :
    contourEq p t y a := by
  rcases hp with rfl | rfl | rfl
  · exact contourEq.two ht y ha
  · exact contourEq.three ht y ha
  · exact contourEq.four ht y ha

end Lyasoff2016
