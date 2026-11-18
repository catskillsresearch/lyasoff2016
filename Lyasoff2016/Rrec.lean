/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
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

/-- Explicit formula for `R_{t,2}`. -/
lemma two_apply (t y : ℝ) :
    Rrec 2 t y = cexp (-2 * (y : ℂ) ^ 2 / t) / (4 * π * I) := by
  rw [two, gFun.two_apply]

/-- `R_{t,2}` is even. -/
lemma two_even (t y : ℝ) : Rrec 2 t (-y) = Rrec 2 t y := by
  rw [two, two, ← gFun.two_even t (y : ℂ)]
  simp

/- Paper: (5.5) for p = 2.
   `R_{t,2}(y) + R_{t,2}(-y) = e^{-2y²/t} / (2πi)`. -/
theorem two_sum (t y : ℝ) :
    Rrec 2 t y + Rrec 2 t (-y) =
      cexp (-2 * (y : ℂ) ^ 2 / t) / (2 * π * I) := by
  rw [two_even, two_apply, ← two_mul, div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- (5.5) scaled by `2πi`: the contour RHS for `p = 2`. -/
theorem two_sum_mul_two_pi_I (t y : ℝ) :
    (2 * π * I) * (Rrec 2 t y + Rrec 2 t (-y)) =
      cexp (-2 * (y : ℂ) ^ 2 / t) := by
  rw [two_sum, ← mul_div_assoc, mul_div_cancel_left₀]
  exact mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)) I_ne_zero

/-- Real form of (5.5) for `p = 2` matching `contourEq`'s RHS. -/
theorem two_sum_re (t y : ℝ) :
    ((2 * π * I) * (Rrec 2 t y + Rrec 2 t (-y))).re =
      Real.exp (-2 * y ^ 2 / t) := by
  rw [two_sum_mul_two_pi_I]
  have h : (-2 * (y : ℂ) ^ 2 / t : ℂ) = ↑(-2 * y ^ 2 / t : ℝ) := by
    push_cast; ring
  rw [h, Complex.exp_ofReal_re]

private lemma sinh_ne_zero {y : ℝ} (hy : y ≠ 0) : Complex.sinh (y : ℂ) ≠ 0 := by
  rw [← Complex.ofReal_sinh]
  exact_mod_cast fun h => hy (Real.sinh_eq_zero.mp h)

/-- Explicit `R_{t,3}(y) = −e^{−2y²/t}/(πi)` for `y ≠ 0`. -/
theorem three_apply {t : ℝ} (ht : 0 < t) {y : ℝ} (hy : y ≠ 0) :
    Rrec 3 t y = -cexp (-2 * (y : ℂ) ^ 2 / t) / (π * I) := by
  have hd : deriv (fun s : ℝ => gFun 3 t s) y =
      -(Complex.sinh y * cexp (-2 * (y : ℂ) ^ 2 / t)) / (π * I) :=
    (gFun.three_hasDerivAt ht y).comp_ofReal.deriv
  have hs := sinh_ne_zero hy
  rw [Rrec, Rrecipe.three, hd, Complex.ofReal_sinh]
  field_simp

/-- Explicit `R_{t,4}(y) = 2e^{−2y²/t}/(πi)` for `y ≠ 0`. -/
theorem four_apply {t : ℝ} (ht : 0 < t) {y : ℝ} (hy : y ≠ 0) :
    Rrec 4 t y = 2 * cexp (-2 * (y : ℂ) ^ 2 / t) / (π * I) := by
  have hev : (fun s : ℝ => deriv (fun s : ℝ => gFun 4 t s) s / Real.sinh s) =ᶠ[𝓝 y]
      fun s : ℝ => -4 * gFun 3 t s := by
    filter_upwards [isOpen_ne.mem_nhds hy] with s hs
    have hs' := sinh_ne_zero hs
    rw [(gFun.four_hasDerivAt ht s).comp_ofReal.deriv, Complex.ofReal_sinh]
    field_simp
  have hd : deriv (fun s : ℝ => -4 * gFun 3 t s) y =
      -4 * (-(Complex.sinh y * cexp (-2 * (y : ℂ) ^ 2 / t)) / (π * I)) :=
    ((gFun.three_hasDerivAt ht y).comp_ofReal.const_mul (-4 : ℂ)).deriv
  have hs := sinh_ne_zero hy
  rw [Rrec, Rrecipe.four, hev.deriv_eq, hd, Complex.ofReal_sinh]
  field_simp
  ring

/-- With Lean's `x / 0 = 0`, the recipe value at `y = 0` is `0` for `p = 3` (not the limit). -/
lemma three_zero (t : ℝ) : Rrec 3 t 0 = 0 := by
  simp [Rrec, Rrecipe.three]

/-- With Lean's `x / 0 = 0`, the recipe value at `y = 0` is `0` for `p = 4` (not the limit). -/
lemma four_zero (t : ℝ) : Rrec 4 t 0 = 0 := by
  simp [Rrec, Rrecipe.four]

/-- (5.5) for `p = 3`. -/
theorem three_sum {t : ℝ} (ht : 0 < t) {y : ℝ} (hy : y ≠ 0) :
    Rrec 3 t y + Rrec 3 t (-y) = -4 / (2 * π * I) * cexp (-2 * (y : ℂ) ^ 2 / t) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [three_apply ht hy, three_apply ht (neg_ne_zero.mpr hy)]
  push_cast
  rw [neg_sq]
  field_simp
  ring

/-- (5.5) for `p = 4`. -/
theorem four_sum {t : ℝ} (ht : 0 < t) {y : ℝ} (hy : y ≠ 0) :
    Rrec 4 t y + Rrec 4 t (-y) = 8 / (2 * π * I) * cexp (-2 * (y : ℂ) ^ 2 / t) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [four_apply ht hy, four_apply ht (neg_ne_zero.mpr hy)]
  push_cast
  rw [neg_sq]
  field_simp
  ring

/- Paper: (5.5), with (5.7)–(5.8).  For the concrete `g = g_{t,p}`, `p ∈ {2,3,4}`:
     R_{t,p}(y) + R_{t,p}(−y) = ((−4)^{p−2} / (p−2)!) · e^{−2y²/t} / (2πi).
   For `p = 3, 4` this needs `y ≠ 0`: `Rrecipe` divides by `sinh y`, so `Rrec p t 0 = 0`
   (`three_zero`, `four_zero`) and the identity is false at `y = 0` (`three_sum_zero_ne`). -/
theorem sum_eq {p : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 4) {t : ℝ} (ht : 0 < t) {y : ℝ}
    (hy : p = 2 ∨ y ≠ 0) :
    Rrec p t y + Rrec p t (-y) =
      ((-4 : ℂ) ^ (p - 2) / ((p - 2).factorial : ℂ) / (2 * π * I)) *
        cexp (-2 * (y : ℂ) ^ 2 / t) := by
  rcases hp with rfl | rfl | rfl
  · have h2 : ∀ s : ℝ, Rrec 2 t s = cexp (-2 * (s : ℂ) ^ 2 / t) / (4 * π * I) := fun _ => rfl
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [h2, h2]
    push_cast
    rw [neg_sq]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    field_simp
    ring
  · rw [three_sum ht (hy.resolve_left (by norm_num))]
    norm_num
  · rw [four_sum ht (hy.resolve_left (by norm_num))]
    norm_num [Nat.factorial]

/-- (5.5) scaled by `2πi`, in the real form of the right-hand side of `contourEq`. -/
theorem two_pi_I_mul_sum {p : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 4) {t : ℝ} (ht : 0 < t) {y : ℝ}
    (hy : p = 2 ∨ y ≠ 0) :
    (2 * π * I) * (Rrec p t y + Rrec p t (-y)) =
      (((-4 : ℝ) ^ (p - 2) / ((p - 2).factorial : ℝ) * Real.exp (-2 * y ^ 2 / t) : ℝ) : ℂ) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [sum_eq hp ht hy]
  push_cast
  field_simp

/-- The unrestricted form of (5.5) fails at `y = 0` for `p = 3` under Lean's `x / 0 = 0`. -/
lemma three_sum_zero_ne (t : ℝ) :
    Rrec 3 t 0 + Rrec 3 t (-0) ≠
      ((-4 : ℂ) ^ (3 - 2) / ((3 - 2).factorial : ℂ) / (2 * π * I)) *
        cexp (-2 * ((0 : ℝ) : ℂ) ^ 2 / t) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hne : (-4 : ℂ) / (2 * π * I) ≠ 0 :=
    div_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero two_ne_zero hπ) I_ne_zero)
  simpa [three_zero] using hne.symm

end Rrec


end Lyasoff2016