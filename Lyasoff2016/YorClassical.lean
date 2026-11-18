/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Yor’s joint density formula (Yor 1992, (6.c) / Lyasoff (1.1)), wired to the
constructive Laplace/FP proof in `YorJointDensity`.
-/
module

public import Lyasoff2016.YorJointDensity


@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Yor’s joint density: the law of `(∫₀ᵗ exp(2 W_s) ds, W_t)` admits the density (1.1).

Proved constructively as `yor_joint_density` (Laplace transform of the joint law via
the Fokker–Planck stack); kept under this name as the classical citation point. -/
theorem yor_joint_density_classical (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (t : ℝ≥0) (ht : 0 < t) :
    IsJointDensity P W 2 0 t (fun x y => yorDensity t x y) :=
  yor_joint_density P W hW t ht

end Lyasoff2016
