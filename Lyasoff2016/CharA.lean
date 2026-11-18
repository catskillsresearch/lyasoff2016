/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Characteristic invariant `A(v, y) = cosh y + v * exp(-y)`.
-/
module

public import Lyasoff2016.YCrit
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Calculus.ContDiff.Basic


@[expose] public section

open Set Filter Topology
open scoped Real

noncomputable section
namespace Lyasoff2016

/-- Characteristic invariant `A(v, y) = cosh y + v * exp(-y)`. -/
def charA (v y : ℝ) : ℝ := Real.cosh y + v * Real.exp (-y)

namespace charA

theorem eq (v y : ℝ) :
    charA v y = (Real.exp y + (1 + 2 * v) * Real.exp (-y)) / 2 := by
  simp only [charA, Real.cosh_eq]; ring

theorem deriv_y_eq (v y : ℝ) :
    Real.sinh y - v * Real.exp (-y) = (Real.exp y - (1 + 2 * v) * Real.exp (-y)) / 2 := by
  simp only [Real.sinh_eq]; ring

theorem hasDerivAt_y (v y : ℝ) :
    HasDerivAt (charA v) (Real.sinh y - v * Real.exp (-y)) y := by
  have h1 := Real.hasDerivAt_cosh y
  have h2 := ((hasDerivAt_id' y).neg.exp).const_mul v
  unfold charA
  convert h1.fun_add h2 using 1
  simp [sub_eq_add_neg, mul_neg]

theorem hasDerivAt_v (v y : ℝ) :
    HasDerivAt (fun v' => charA v' y) (Real.exp (-y)) v := by
  have h := ((hasDerivAt_id' v).mul_const (Real.exp (-y))).const_add (Real.cosh y)
  simpa [charA] using h

theorem sq_sub (v y : ℝ) :
    charA v y ^ 2 - (1 + 2 * v) = (Real.sinh y - v * Real.exp (-y)) ^ 2 := by
  rw [eq, deriv_y_eq]
  have hmul : Real.exp y * Real.exp (-y) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc ((Real.exp y + (1 + 2 * v) * Real.exp (-y)) / 2) ^ 2 - (1 + 2 * v)
      = ((Real.exp y - (1 + 2 * v) * Real.exp (-y)) / 2) ^ 2 +
          (1 + 2 * v) * (Real.exp y * Real.exp (-y) - 1) := by ring
    _ = ((Real.exp y - (1 + 2 * v) * Real.exp (-y)) / 2) ^ 2 := by rw [hmul]; ring

theorem yCrit {v : ℝ} (hv : 0 ≤ v) :
    charA v (Lyasoff2016.yCrit v) = Real.sqrt (1 + 2 * v) := by
  have h12v : 0 < 1 + 2 * v := by linarith
  have hsq : Real.exp (Lyasoff2016.yCrit v) ^ 2 = 1 + 2 * v := by
    rw [← Real.exp_nat_mul]; simpa [Nat.cast_ofNat] using Lyasoff2016.yCrit.exp_two_mul hv
  have hexp_pos : 0 < Real.exp (Lyasoff2016.yCrit v) := Real.exp_pos _
  have he : Real.exp (Lyasoff2016.yCrit v) = Real.sqrt (1 + 2 * v) := by
    rw [← Real.sqrt_sq hexp_pos.le, hsq]
  have he_neg : (1 + 2 * v) * Real.exp (-Lyasoff2016.yCrit v) = Real.sqrt (1 + 2 * v) := by
    calc (1 + 2 * v) * Real.exp (-Lyasoff2016.yCrit v)
        = (Real.exp (Lyasoff2016.yCrit v) * Real.exp (Lyasoff2016.yCrit v)) *
            (Real.exp (Lyasoff2016.yCrit v))⁻¹ := by
            rw [← hsq, sq, Real.exp_neg]
      _ = Real.exp (Lyasoff2016.yCrit v) := mul_inv_cancel_right₀ hexp_pos.ne' _
      _ = Real.sqrt (1 + 2 * v) := he
  rw [eq, he, he_neg]
  ring

theorem ge_sqrt {v : ℝ} (hv : 0 ≤ v) (y : ℝ) :
    Real.sqrt (1 + 2 * v) ≤ charA v y := by
  have hpos : 0 < charA v y := by
    unfold charA
    exact add_pos_of_pos_of_nonneg (Real.cosh_pos y) (mul_nonneg hv (Real.exp_pos _).le)
  have hsq : 1 + 2 * v ≤ charA v y ^ 2 := by
    have := sq_sub v y
    nlinarith [sq_nonneg (Real.sinh y - v * Real.exp (-y))]
  rw [← Real.sqrt_sq hpos.le]
  exact Real.sqrt_le_sqrt hsq

theorem deriv_pos_iff {v : ℝ} (hv : 0 ≤ v) (y : ℝ) :
    0 < Real.sinh y - v * Real.exp (-y) ↔ Lyasoff2016.yCrit v < y := by
  rw [deriv_y_eq]
  have hexp : 0 < Real.exp (-y) := Real.exp_pos (-y)
  have hfactor : (Real.exp y - (1 + 2 * v) * Real.exp (-y)) / 2 =
      Real.exp (-y) * (Real.exp (2 * y) - (1 + 2 * v)) / 2 := by
    have hmul : Real.exp (-y) * Real.exp (2 * y) = Real.exp y := by
      rw [← Real.exp_add]; congr 1; ring
    linarith [mul_sub (Real.exp (-y)) (Real.exp (2 * y)) (1 + 2 * v)]
  rw [hfactor]
  constructor
  · intro h
    have h2 : 0 < Real.exp (2 * y) - (1 + 2 * v) := by nlinarith
    have h3 : Real.exp (2 * Lyasoff2016.yCrit v) < Real.exp (2 * y) := by
      rw [Lyasoff2016.yCrit.exp_two_mul hv]; linarith
    linarith [Real.exp_lt_exp.mp h3]
  · intro h
    have h3 : 1 + 2 * v < Real.exp (2 * y) := by
      rw [← Lyasoff2016.yCrit.exp_two_mul hv]; exact Real.exp_lt_exp.mpr (by linarith)
    have h2 : 0 < Real.exp (2 * y) - (1 + 2 * v) := by linarith
    positivity

theorem deriv_neg_iff {v : ℝ} (hv : 0 ≤ v) (y : ℝ) :
    Real.sinh y - v * Real.exp (-y) < 0 ↔ y < Lyasoff2016.yCrit v := by
  rw [deriv_y_eq]
  have hexp : 0 < Real.exp (-y) := Real.exp_pos (-y)
  have hfactor : (Real.exp y - (1 + 2 * v) * Real.exp (-y)) / 2 =
      Real.exp (-y) * (Real.exp (2 * y) - (1 + 2 * v)) / 2 := by
    have hmul : Real.exp (-y) * Real.exp (2 * y) = Real.exp y := by
      rw [← Real.exp_add]; congr 1; ring
    linarith [mul_sub (Real.exp (-y)) (Real.exp (2 * y)) (1 + 2 * v)]
  rw [hfactor]
  constructor
  · intro h
    have h2 : Real.exp (2 * y) - (1 + 2 * v) < 0 := by
      by_contra hge
      push Not at hge
      have : 0 ≤ Real.exp (-y) * (Real.exp (2 * y) - (1 + 2 * v)) / 2 := by positivity
      linarith
    have h3 : Real.exp (2 * y) < Real.exp (2 * Lyasoff2016.yCrit v) := by
      rw [Lyasoff2016.yCrit.exp_two_mul hv]; linarith
    linarith [Real.exp_lt_exp.mp h3]
  · intro h
    have h3 : Real.exp (2 * y) < 1 + 2 * v := by
      rw [← Lyasoff2016.yCrit.exp_two_mul hv]; exact Real.exp_lt_exp.mpr (by linarith)
    have h2 : Real.exp (2 * y) - (1 + 2 * v) < 0 := by linarith
    have : Real.exp (-y) * (Real.exp (2 * y) - (1 + 2 * v)) < 0 :=
      mul_neg_of_pos_of_neg hexp h2
    linarith

theorem strictMonoOn {v : ℝ} (hv : 0 ≤ v) :
    StrictMonoOn (charA v) (Ici (Lyasoff2016.yCrit v)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici _) (by unfold charA; fun_prop) fun y hy => ?_
  have hd := (hasDerivAt_y v y).deriv
  rw [hd]
  exact (deriv_pos_iff hv y).mpr (by simpa using hy)

theorem strictAntiOn {v : ℝ} (hv : 0 ≤ v) :
    StrictAntiOn (charA v) (Iic (Lyasoff2016.yCrit v)) := by
  refine strictAntiOn_of_deriv_neg (convex_Iic _) (by unfold charA; fun_prop) fun y hy => ?_
  have hd := (hasDerivAt_y v y).deriv
  rw [hd]
  exact (deriv_neg_iff hv y).mpr (by simpa using hy)

theorem lower_bound {v y : ℝ} (hv : 0 ≤ v) :
    Real.exp |y| / 2 ≤ charA v y := by
  unfold charA
  have h1 : Real.exp |y| / 2 ≤ Real.cosh y := by
    rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hy, Real.cosh_eq]
      linarith [Real.exp_pos (-y)]
    · rw [abs_of_nonpos hy, Real.cosh_eq]
      linarith [Real.exp_pos y]
  linarith [mul_nonneg hv (Real.exp_pos (-y)).le]

end charA

end Lyasoff2016
