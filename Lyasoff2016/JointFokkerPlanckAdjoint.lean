/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Expanded formal Fokker–Planck adjoint (paper (3.6a)).
-/
module

public import Lyasoff2016.JointFlux


@[expose] public section

open scoped Real

noncomputable section
namespace Lyasoff2016

/-- The expanded formal adjoint in (3.6a).  This is the derivative in `x` of
`jointFlux`; keeping it named separates the analytic integration-by-parts calculation from the
stochastic weak-forward-equation argument. -/
def jointFokkerPlanckAdjoint (σ : ℝ) (φ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  σ ^ 2 * x ^ 2 / 2 * deriv (deriv fun z => φ z y) x
    + σ * x * deriv (fun z => deriv (fun y' => φ z y') y) x
    + (Real.exp (σ * y) + 3 * σ ^ 2 * x / 2 - 1) * deriv (fun z => φ z y) x
    + σ * deriv (fun y' => φ x y') y
    + σ ^ 2 / 2 * φ x y

namespace jointFlux

/-- Deterministic divergence/adjoint calculation underlying (3.6a)–(3.6b). -/
theorem hasDerivAt (σ : ℝ) (φ : ℝ → ℝ → ℝ) (x y : ℝ)
    (hφx : HasDerivAt (fun z => φ z y) (deriv (fun z => φ z y) x) x)
    (hφxx : HasDerivAt (deriv fun z => φ z y)
      (deriv (deriv fun z => φ z y) x) x)
    (hφxy : HasDerivAt (fun z => deriv (fun y' => φ z y') y)
      (deriv (fun z => deriv (fun y' => φ z y') y) x) x) :
    HasDerivAt (fun z => jointFlux σ φ z y) (jointFokkerPlanckAdjoint σ φ x y) x := by
  have hsq : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hfirst := (((hsq.const_mul (σ ^ 2)).div_const 2).mul hφxx)
  have hmixed : HasDerivAt
      (fun z => σ * z * deriv (fun y' => φ z y') y)
      (σ * deriv (fun y' => φ x y') y
        + σ * x * deriv (fun z => deriv (fun y' => φ z y') y) x) x := by
    convert ((hasDerivAt_id x).const_mul σ).mul hφxy using 1
    · ext z
      rfl
    · simp [id]
  have hcoefficient : HasDerivAt
      (fun z : ℝ => Real.exp (σ * y) + σ ^ 2 * z / 2 - 1) (σ ^ 2 / 2) x := by
    convert (hasDerivAt_const x (Real.exp (σ * y) - 1)).add
      (((hasDerivAt_id x).const_mul (σ ^ 2)).div_const 2) using 1
    · ext z
      simp [id]
      ring
    · ring
  have hlast := hcoefficient.mul hφx
  convert (hfirst.add hmixed).add hlast using 1
  · ext z
    simp only [jointFlux, Pi.add_apply, Pi.mul_apply]
  · simp only [jointFokkerPlanckAdjoint]
    ring

/-- Pointwise equality between the derivative-of-flux and expanded-adjoint formulations. -/
theorem deriv_eq (σ : ℝ) (φ : ℝ → ℝ → ℝ) (x y : ℝ)
    (hφx : HasDerivAt (fun z => φ z y) (deriv (fun z => φ z y) x) x)
    (hφxx : HasDerivAt (deriv fun z => φ z y)
      (deriv (deriv fun z => φ z y) x) x)
    (hφxy : HasDerivAt (fun z => deriv (fun y' => φ z y') y)
      (deriv (fun z => deriv (fun y' => φ z y') y) x) x) :
    deriv (fun z => jointFlux σ φ z y) x = jointFokkerPlanckAdjoint σ φ x y :=
  (hasDerivAt σ φ x y hφx hφxx hφxy).deriv

end jointFlux

end Lyasoff2016
