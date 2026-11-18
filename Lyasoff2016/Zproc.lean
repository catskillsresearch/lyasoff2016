/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Stationary process Z_t from two independent BMs (paper (3.1)).
-/
module

public import Lyasoff2016.Setting


@[expose] public section

open MeasureTheory Set
open scoped NNReal Real

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

/- Paper: p. 1067, (3.1).
   Plain recap: the stationary process Z_t built from two independent BMs.
   PAPER NOTE: paper writes e^{σ(W_s+νs)} and e^{σ(νt−B_t)}; we use the equivalent
   e^{σ W_s + ν s} convention throughout, so the prefactor is e^{νt − σ B_t} and the
   B-integral is e^{−νs + σ B_s} (same drift ν in all three places). -/
def Zproc (W B : ℝ≥0 → Ω → ℝ) (σ ν : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (ν * (t : ℝ) - σ * B t ω) *
    ((∫ s in Ioi (0 : ℝ), Real.exp (σ * W s.toNNReal ω + ν * s)) +
     ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-ν * s + σ * B s.toNNReal ω))

end Lyasoff2016
