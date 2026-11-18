/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Upper incomplete Gamma `Γ(s, x)` used in Asian inner integrals (p. 1091).
-/
module

public import Lyasoff2016.Setting


@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/- Paper: p. 1091, incomplete Gamma and S_{k,p}.
   Plain recap: upper incomplete Gamma and the Asian inner integral S. -/
def upperGamma (s x : ℝ) : ℝ :=
  ∫ u in Ioi x, u ^ (s - 1) * Real.exp (-u)

end Lyasoff2016