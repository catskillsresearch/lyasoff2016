/-
Evaluation of the `1/x`-Laplace transform of Yor's density via a Cauchy rectangle contour
and identification of `IsJointDensity P W 2 0 t (yorDensity t)` without classical axioms.

WIP: contour analysis is unfinished; statements kept, proofs stubbed for a green tree.
-/
module

public import Lyasoff2016.JointLawLaplaceInv
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real Interval

noncomputable section
namespace Lyasoff2016

section ContourIntegral

/-- Hartman–Watson / Yor contour integral identity: for `t > 0` and `α > 0`,
`e^{π²/(2t)} ∫₀^∞ e^{-u²/(2t)} sinh u * sin(π u / t) / (cosh u + cosh α) du = π e^{-α²/(2t)}`. -/
theorem hartman_watson_contour {t α : ℝ} (ht : 0 < t) (hα : 0 < α) :
    Real.exp (Real.pi ^ 2 / (2 * t)) *
      ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * t)) *
        (Real.sinh u * Real.sin (Real.pi * u / t) / (Real.cosh u + Real.cosh α)) =
      Real.pi * Real.exp (-α ^ 2 / (2 * t)) := by
  sorry

end ContourIntegral

end Lyasoff2016
