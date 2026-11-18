/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Critical point `y₀(v)` of the characteristic `A(v, ·)`.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp


@[expose] public section

open scoped Real

noncomputable section
namespace Lyasoff2016

/-- Critical point `y₀(v) = (1/2) * log(1 + 2v)` where `∂_y A(v, y) = 0`. -/
def yCrit (v : ℝ) : ℝ := (1 / 2 : ℝ) * Real.log (1 + 2 * v)

namespace yCrit

theorem exp_two_mul {v : ℝ} (hv : 0 ≤ v) :
    Real.exp (2 * yCrit v) = 1 + 2 * v := by
  simp only [yCrit]
  rw [show 2 * ((1 / 2 : ℝ) * Real.log (1 + 2 * v)) = Real.log (1 + 2 * v) by ring]
  exact Real.exp_log (by linarith)

end yCrit

end Lyasoff2016
