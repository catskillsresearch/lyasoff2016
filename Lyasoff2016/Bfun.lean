/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Jacobian–Girsanov factor `B(w)` in the Asian integrand (p. 1090).
-/
module

public import Lyasoff2016.Setting


@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/- Paper: p. 1090, display defining B(w):
     B(w) := 2 w^{2μ/σ² − 1} e^{μ² t/(2σ²)} / σ. -/
def Bfun (σ ν t : ℝ) (w : ℝ) : ℝ :=
  2 * w ^ (2 * ν / σ ^ 2 - 1) * Real.exp (ν ^ 2 * t / (2 * σ ^ 2)) / σ

end Lyasoff2016