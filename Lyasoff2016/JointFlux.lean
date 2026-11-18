/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Probability flux in the `x` direction (paper (3.6b)).
-/
module

public import Lyasoff2016.Setting


@[expose] public section

open scoped Real

noncomputable section
namespace Lyasoff2016

/-- The probability flux in the `x` direction in (3.6b). -/
def jointFlux (σ : ℝ) (φ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  σ ^ 2 * x ^ 2 / 2 * deriv (fun z => φ z y) x
    + σ * x * deriv (fun y' => φ x y') y
    + (Real.exp (σ * y) + σ ^ 2 * x / 2 - 1) * φ x y

end Lyasoff2016
