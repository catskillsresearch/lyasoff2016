/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
# §5 Integral representations (pp. 1079–1088)
-/
module

public import Lyasoff2016.Foliation
public import Lyasoff2016.Cerf
public import Lyasoff2016.GFun
public import Lyasoff2016.Rrecipe
public import Lyasoff2016.Rrec
public import Lyasoff2016.ContourIntegrand
public import Lyasoff2016.ContourEq
public import Lyasoff2016.PiFormula
public import Lyasoff2016.PiHalfFormula
public import Lyasoff2016.YorDensity
public import Lyasoff2016.PiFormulaLaplace
public import Lyasoff2016.PiFormulaScaling
public import Lyasoff2016.PiFormulaHigher
public import Lyasoff2016.PiHalfFormulaHigher


@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

/- Paper: p. 1061 (1.1) — Yor’s joint density, now using the constructive proof. -/
theorem yor_formula (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (t : ℝ≥0) (ht : 0 < t) :
    IsJointDensity P W 2 0 t (fun x y => yorDensity t x y) :=
  yor_joint_density P W hW t ht

/- Paper: p. 1085–1086.
   Both π/2 and π formulae equal the joint density for p = 2,3,4.
   Route: ContourEq + InverseGamma (+ complex for π/2) + Fubini via Gaussian
   gFun decay (`GFunDecay`) + prop_4_4 uniqueness + Brownian scaling. -/
/-- Density identification for the π / π/2 formulae (Lyasoff pp. 1085–1086). -/
theorem pi_formula (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (hσ : 0 < σ) (ht : 0 < t) (p : ℕ)
    (hp : p = 2 ∨ p = 3 ∨ p = 4) :
    IsJointDensity P W σ 0 t (fun x y =>
      gaussianPDFReal 0 t y * (σ ^ 2)⁻¹ * piHalfFormula p σ t (x * σ ^ 2) (y * σ)) ∧
    IsJointDensity P W σ 0 t (fun x y =>
      gaussianPDFReal 0 t y * (σ ^ 2)⁻¹ * piFormula p σ t (x * σ ^ 2) (y * σ)) := by
  exact ⟨pi_half_formula_general P W hW σ t hσ ht p hp,
    pi_formula_general P W hW σ t hσ ht p hp⟩

/- Paper: Remark 5.5. -/
theorem remark_5_5 :
    ∀ x : ℝ, 0 ≤ x → Real.arcosh (Real.cosh x) = x :=
  fun _ hx => Real.arcosh_cosh hx

end Lyasoff2016
