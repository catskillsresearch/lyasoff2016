/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Diffusion generator L = ½σ²x² ∂ₓₓ + (1 + (ν + σ²/2)x) ∂ₓ (paper (3.2)).
-/
module

public import Lyasoff2016.Setting


@[expose] public section

open scoped Real

noncomputable section
namespace Lyasoff2016

/- Paper: p. 1067, (3.2).
   Plain recap: generator L = ½σ²x² ∂ₓₓ + (1 + (ν + σ²/2)x) ∂ₓ.
   PAPER NOTE: β = −2ν/σ² in our e^{σW+νs} convention. -/
def generator (σ ν : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  σ ^ 2 * x ^ 2 / 2 * deriv (deriv f) x + (1 + (ν + σ ^ 2 / 2) * x) * deriv f x

end Lyasoff2016
