/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Correct Brownian scaling from the reference volatility `2`, together with the
algebraic covariance of the π-formula.
-/
module

public import Lyasoff2016.BrownianScaling
public import Lyasoff2016.PiFormulaLaplace

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Reference time at volatility `2` corresponding to target horizon `T` at
volatility `σ`. -/
noncomputable def referenceTimeFromTwo (σ : ℝ) (T : ℝ≥0) : ℝ≥0 :=
  ((T : ℝ) * σ ^ 2 / 4).toNNReal

lemma referenceTimeFromTwo_pos {σ : ℝ} (hσ : 0 < σ) {T : ℝ≥0} (hT : 0 < T) :
    0 < referenceTimeFromTwo σ T := by
  rw [referenceTimeFromTwo, Real.toNNReal_pos]
  positivity

lemma referenceTimeFromTwo_two (T : ℝ≥0) :
    referenceTimeFromTwo 2 T = T := by
  apply NNReal.eq
  rw [referenceTimeFromTwo, Real.coe_toNNReal]
  · norm_num
  · positivity

/-- The target horizon is recovered by scaling the reference horizon back from
volatility `2` to volatility `σ`. -/
lemma referenceTimeFromTwo_div {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    (((4 : ℝ) * referenceTimeFromTwo σ T) / σ ^ 2).toNNReal = T := by
  apply NNReal.eq
  rw [Real.coe_toNNReal, referenceTimeFromTwo, Real.coe_toNNReal]
  · field_simp [hσ.ne']
  · positivity
  · positivity

/-- Joint-law scaling directly from volatility `2` at its corresponding
reference time. -/
theorem jointLaw_scaling_from_two_fixed
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    jointLaw P W σ 0 T =
      (jointLaw P W 2 0 (referenceTimeFromTwo σ T)).map
        (fun p : ℝ × ℝ => (4 / σ ^ 2 * p.1, 2 / σ * p.2)) := by
  let τ := referenceTimeFromTwo σ T
  have hτ : (((4 : ℝ) * τ) / σ ^ 2).toNNReal = T := by
    simpa [τ] using referenceTimeFromTwo_div hσ T
  have hσlaw := jointLaw_scaling P W hW hσ ((4 : ℝ≥0) * τ)
  have h2law := jointLaw_scaling P W hW (show 0 < (2 : ℝ) by norm_num) ((4 : ℝ≥0) * τ)
  norm_num only [NNReal.coe_mul, NNReal.coe_ofNat] at hσlaw h2law
  have hτ2 : (((4 : ℝ) * τ / 4).toNNReal) = τ := by
    apply NNReal.eq
    rw [Real.coe_toNNReal]
    · norm_num
    · positivity
  rw [hτ] at hσlaw
  rw [hτ2] at h2law
  have hmap := congrArg
    (Measure.map (fun p : ℝ × ℝ => ((σ ^ 2)⁻¹ * p.1, σ⁻¹ * p.2))) hσlaw
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at hmap
  have hinv :
      (fun p : ℝ × ℝ => ((σ ^ 2)⁻¹ * p.1, σ⁻¹ * p.2)) ∘
          (fun p : ℝ × ℝ => (σ ^ 2 * p.1, σ * p.2)) = id := by
    funext p
    simp only [Function.comp_apply, id_eq]
    ext <;> dsimp <;> field_simp [hσ.ne']
  rw [hinv, Measure.map_id] at hmap
  rw [← hmap, h2law, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext p
  simp only [Function.comp_apply]
  ext <;> dsimp <;> field_simp [hσ.ne']

/-- Pushforward of a real-valued product density by independent nonzero
coordinate scalings. -/
theorem map_prod_smul_withDensity_ofReal_fixed
    (φ : ℝ → ℝ → ℝ)
    (hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (φ p.1 p.2)))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ((volume : Measure (ℝ × ℝ)).withDensity
        (fun p => ENNReal.ofReal (φ p.1 p.2))).map
          (fun p : ℝ × ℝ => (a * p.1, b * p.2)) =
      (volume : Measure (ℝ × ℝ)).withDensity fun p =>
        ENNReal.ofReal ((a * b)⁻¹ * φ (a⁻¹ * p.1) (b⁻¹ * p.2)) := by
  rw [map_prod_mul_withDensity ha.ne' hb.ne' _ hm]
  congr 1
  funext p
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ |b⁻¹|),
    ← ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
  congr 1
  rw [abs_of_pos (inv_pos.mpr hb), abs_of_pos (inv_pos.mpr ha)]
  field_simp

/-- Scaling a measurable joint density from volatility `2` to a target
volatility and horizon. -/
theorem IsJointDensity_scaling_from_two_fixed
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0)
    (φ₂ : ℝ → ℝ → ℝ)
    (hφ₂ : IsJointDensity P W 2 0 (referenceTimeFromTwo σ T) φ₂)
    (hm₂ : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (φ₂ p.1 p.2))) :
    IsJointDensity P W σ 0 T fun x y =>
      (σ / 2) ^ 3 * φ₂ (σ ^ 2 / 4 * x) (σ / 2 * y) := by
  unfold IsJointDensity at hφ₂ ⊢
  rw [jointLaw_scaling_from_two_fixed P W hW hσ T, hφ₂,
    map_prod_smul_withDensity_ofReal_fixed φ₂ hm₂
      (by positivity : 0 < 4 / σ ^ 2) (by positivity : 0 < 2 / σ)]
  congr 1
  funext p
  congr 1
  field_simp [hσ.ne']
  norm_num

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

/-- Gaussian scaling at the reference horizon `T σ²/4`. -/
lemma gaussianPDFReal_referenceTimeFromTwo
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (y : ℝ) :
    gaussianPDFReal 0 (referenceTimeFromTwo σ T) (σ / 2 * y) =
      (2 / σ) * gaussianPDFReal 0 T y := by
  have hτcoe : (referenceTimeFromTwo σ T : ℝ) = (T : ℝ) * σ ^ 2 / 4 := by
    rw [referenceTimeFromTwo, Real.coe_toNNReal]
    positivity
  have hsqrt :
      √(2 * π * (referenceTimeFromTwo σ T : ℝ)) =
        (σ / 2) * √(2 * π * (T : ℝ)) := by
    rw [hτcoe, show 2 * π * ((T : ℝ) * σ ^ 2 / 4) =
      (σ / 2) ^ 2 * (2 * π * (T : ℝ)) by ring,
      Real.sqrt_mul (sq_nonneg (σ / 2)), Real.sqrt_sq (div_nonneg hσ.le (by norm_num))]
  simp only [gaussianPDFReal_def, sub_zero]
  rw [hsqrt, hτcoe]
  have hs0 : σ ≠ 0 := hσ.ne'
  field_simp
  congr 1
  ring_nf

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
