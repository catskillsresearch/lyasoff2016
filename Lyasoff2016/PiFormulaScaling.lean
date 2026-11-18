/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
π-formula covariance under Brownian scaling, and the order-two π-formula
at every positive volatility. The joint-density scaling lemmas from the
reference volatility `2` live in `JointDensityScaling`.
-/
module

public import Lyasoff2016.JointDensityScaling
public import Lyasoff2016.PiFormulaLaplace

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The π-formula has the exact covariance required by Brownian scaling.
Here `τ = T σ²/4` is the reference horizon at volatility `2`. -/
theorem piFormula_sigma_covariant_fixed
    (p : ℕ) (σ : ℝ) (T : ℝ≥0) (x y : ℝ) (hσ : 0 < σ) :
    piFormula p σ T (x * σ ^ 2) (y * σ) =
      (σ / 2) ^ 4 *
        piFormula p 2 (referenceTimeFromTwo σ T) (x * σ ^ 2) (y * σ) := by
  have hτ :
      (referenceTimeFromTwo σ T : ℝ) * (2 : ℝ) ^ 2 = (T : ℝ) * σ ^ 2 := by
    rw [referenceTimeFromTwo, Real.coe_toNNReal]
    · ring
    · positivity
  unfold piFormula
  rw [hτ]
  split_ifs <;> ring

/-- The order-two π-formula is a joint density for every positive volatility
and positive horizon. -/
theorem pi_formula_two_general
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ : ℝ) (T : ℝ≥0) (hσ : 0 < σ) (hT : 0 < T) :
    IsJointDensity P W σ 0 T fun x y =>
      gaussianPDFReal 0 T y * (σ ^ 2)⁻¹ *
        piFormula 2 σ T (x * σ ^ 2) (y * σ) := by
  let τ := referenceTimeFromTwo σ T
  have hτ : 0 < τ := by
    simpa [τ] using referenceTimeFromTwo_pos hσ hT
  let φ₂ : ℝ → ℝ → ℝ := fun x y =>
    gaussianPDFReal 0 τ y * ((2 : ℝ) ^ 2)⁻¹ *
      piFormula 2 2 τ (x * (2 : ℝ) ^ 2) (y * 2)
  have hφ₂ : IsJointDensity P W 2 0 τ φ₂ :=
    pi_formula_two_sigma_two P W hW τ hτ
  have hφeq : φ₂ = fun x y => yorDensity τ x y := by
    funext x y
    exact remark_5_1_aux τ x y hτ
  have hm₂ : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (φ₂ p.1 p.2)) := by
    rw [hφeq]
    exact yorDensity_ennreal_measurable τ hτ
  have hs := IsJointDensity_scaling_from_two_fixed
    P W hW hσ T φ₂ (by simpa [τ] using hφ₂) (by simpa [τ] using hm₂)
  have hfun :
      (fun x y : ℝ =>
        (σ / 2) ^ 3 * φ₂ (σ ^ 2 / 4 * x) (σ / 2 * y)) =
      (fun x y =>
        gaussianPDFReal 0 T y * (σ ^ 2)⁻¹ *
          piFormula 2 σ T (x * σ ^ 2) (y * σ)) := by
    funext x y
    dsimp [φ₂]
    rw [gaussianPDFReal_referenceTimeFromTwo hσ T y,
      piFormula_sigma_covariant_fixed 2 σ T x y hσ]
    simp only [τ]
    field_simp [hσ.ne']
    ring_nf
  rwa [hfun] at hs

end Lyasoff2016
