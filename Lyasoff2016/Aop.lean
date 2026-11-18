/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Second-order operator A_t from the Fokker–Planck argument (p. 1069).
-/
module

public import Lyasoff2016.Setting


@[expose] public section

open scoped Real

noncomputable section
namespace Lyasoff2016

/- Paper: p. 1069, operator A_t.
   Plain recap: the second-order operator appearing in the Fokker–Planck argument. -/
def Aop (V0 : ℝ) (V : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (x y u v : ℝ) : ℝ :=
  u ^ 2 / 2 * iteratedDeriv 2 (fun x' => f x' y) x
    + u * deriv (fun y' => deriv (fun x' => f x' y') x) y
    + (v / 2 + V0 - V y) * deriv (fun x' => f x' y) x

end Lyasoff2016
