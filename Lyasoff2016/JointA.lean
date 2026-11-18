/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Paper (3.5) operator `jointA` and product-test identities.
-/
module

public import Lyasoff2016.Aop
public import Lyasoff2016.TwinGenerator
public import Lyasoff2016.JointFokkerPlanckIto


@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real ContDiff

noncomputable section
namespace Lyasoff2016

/-- Paper (3.5) operator at exponential-BM coefficients, acting on a test function. -/
def jointA (σ : ℝ) (ϕ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  σ ^ 2 * x ^ 2 / 2 * iteratedDeriv 2 (fun x' => ϕ x' y) x
    + σ * x * deriv (fun y' => deriv (fun x' => ϕ x' y') x) y
    + (σ ^ 2 * x / 2 + 1 - Real.exp (σ * y)) * deriv (fun x' => ϕ x' y) x

namespace jointA

theorem eq_Aop (σ : ℝ) (ϕ : ℝ → ℝ → ℝ) (x y : ℝ) :
    jointA σ ϕ x y =
      Aop 1 (fun z => Real.exp (σ * z)) ϕ x y (σ * x) (σ ^ 2 * x) := by
  simp only [jointA, Aop]; ring

/-- The (3.4b)−(3.4a) drift difference is `jointA` on product tests. -/
theorem eq_drift_diff (σ : ℝ) (u v : ℝ → ℝ)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (x y : ℝ) :
    jointA σ (fun x y => u x * v y) x y =
      ((1 : ℝ) * deriv u x * v y
        + (σ ^ 2 / 2) * x * deriv u x * v y
        + (σ ^ 2 / 2) * x ^ 2 * deriv (deriv u) x * v y
        + σ * x * deriv u x * deriv v y
        + (1 / 2) * u x * deriv (deriv v) y)
      - (deriv u x * Real.exp (σ * y) * v y
          + u x * ((1 : ℝ) / 2) * deriv (deriv v) y) := by
  have hu_diff : Differentiable ℝ u := hu.differentiable (by decide)
  have hv_diff : Differentiable ℝ v := hv.differentiable (by decide)
  have huder : Differentiable ℝ (deriv u) :=
    ((contDiff_succ_iff_deriv (n := 1)).mp hu).2.2.differentiable (by decide)
  have hx : deriv (fun x' => u x' * v y) x = deriv u x * v y :=
    deriv_mul_const (hu_diff.differentiableAt) (v y)
  have hxx : iteratedDeriv 2 (fun x' => u x' * v y) x = deriv (deriv u) x * v y := by
    have heq : deriv (fun x' => u x' * v y) = fun x' => deriv u x' * v y := by
      funext x'
      exact deriv_mul_const (hu_diff.differentiableAt) (v y)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, heq]
    exact deriv_mul_const (huder.differentiableAt) (v y)
  have hxy : deriv (fun y' => deriv (fun x' => u x' * v y') x) y =
      deriv u x * deriv v y := by
    have h1 : (fun y' => deriv (fun x' => u x' * v y') x) =
        fun y' => deriv u x * v y' := by
      funext y'
      exact deriv_mul_const (hu_diff.differentiableAt) (v y')
    rw [h1]
    exact deriv_const_mul (deriv u x) (hv_diff.differentiableAt)
  simp only [jointA, hxx, hxy, hx]
  ring

/-- Pointwise: `jointA(u⊗v) = twinGenerator − (3.4a drift)`. -/
theorem eq_twinGenerator_sub (σ : ℝ) (u v : ℝ → ℝ)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (x y : ℝ) :
    jointA σ (fun x y => u x * v y) x y =
      twinGenerator σ u v x y -
        (deriv u x * Real.exp (σ * y) * v y +
          u x * ((1 : ℝ) / 2) * deriv (deriv v) y) := by
  simpa [twinGenerator] using eq_drift_diff σ u v hu hv x y

/-- Continuity of the product-test generator. -/
theorem continuous_product (σ : ℝ) {u v : ℝ → ℝ}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v) :
    Continuous fun p : ℝ × ℝ => jointA σ (fun x y => u x * v y) p.1 p.2 := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by decide)
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by decide)
  have htw := twinGenerator.continuous σ hu hv
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by decide)
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by decide)
  have hdv1 : ContDiff ℝ 1 (deriv v) := (contDiff_succ_iff_deriv (n := 1)).mp hv2 |>.2.2
  have hu'c : Continuous (deriv u) := ContDiff.continuous_deriv_one hu1
  have hv''c : Continuous (deriv (deriv v)) := ContDiff.continuous_deriv_one hdv1
  have hdrift : Continuous fun p : ℝ × ℝ =>
      deriv u p.1 * Real.exp (σ * p.2) * v p.2 +
        u p.1 * ((1 : ℝ) / 2) * deriv (deriv v) p.2 :=
    (((hu'c.comp continuous_fst).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_snd))).mul
        (hv.continuous.comp continuous_snd)).add
      (((hu.continuous.comp continuous_fst).mul continuous_const).mul
        (hv''c.comp continuous_snd))
  refine (htw.sub hdrift).congr fun p => ?_
  exact (eq_twinGenerator_sub σ u v hu2 hv2 p.1 p.2).symm

/-- Compactly supported product tests make `jointA(u⊗v)`, `twinGenerator`, and the
(3.4a) drift globally bounded. -/
theorem product_bounds (σ : ℝ) {u v : ℝ → ℝ}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (huC : HasCompactSupport u) (hvC : HasCompactSupport v) :
    ∃ M : ℝ,
      (∀ x y, |jointA σ (fun x y => u x * v y) x y| ≤ M) ∧
      (∀ x y, |twinGenerator σ u v x y| ≤ M) ∧
      (∀ x y,
        |deriv u x * Real.exp (σ * y) * v y +
            u x * ((1 : ℝ) / 2) * deriv (deriv v) y| ≤ M) := by
  obtain ⟨Cu, hu_bdd, hu'_bdd, hu''_bdd⟩ := contDiff_top_compactSupport_bounds hu huC
  obtain ⟨Cv, hv_bdd, hv'_bdd, hv''_bdd⟩ := contDiff_top_compactSupport_bounds hv hvC
  have hCu : 0 ≤ Cu := (abs_nonneg _).trans (hu_bdd 0)
  have hCv : 0 ≤ Cv := (abs_nonneg _).trans (hv_bdd 0)
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by decide)
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by decide)
  have hdu1 : ContDiff ℝ 1 (deriv u) := (contDiff_succ_iff_deriv (n := 1)).mp hu2 |>.2.2
  have hu'c : Continuous (deriv u) := ContDiff.continuous_deriv_one hu1
  have hu''c : Continuous (deriv (deriv u)) := ContDiff.continuous_deriv_one hdu1
  have hvc : Continuous v := hv.continuous
  obtain ⟨K₁, hK₁⟩ := (show Continuous ((fun x : ℝ => x) * deriv u) from
    continuous_id.mul hu'c).bounded_above_of_compact_support huC.deriv.mul_left
  obtain ⟨K₂, hK₂⟩ := (show Continuous ((fun x : ℝ => x ^ 2) * deriv (deriv u)) from
    (continuous_id.pow 2).mul hu''c).bounded_above_of_compact_support
      huC.deriv.deriv.mul_left
  obtain ⟨Kexp, hKexp⟩ :=
    (show Continuous ((fun y : ℝ => Real.exp (σ * y)) * v) from
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hvc
      ).bounded_above_of_compact_support hvC.mul_left
  have hK₁0 : 0 ≤ K₁ := (abs_nonneg _).trans (hK₁ 0)
  have hK₂0 : 0 ≤ K₂ := (abs_nonneg _).trans (hK₂ 0)
  have hKexp0 : 0 ≤ Kexp := (abs_nonneg _).trans (by simpa [Real.norm_eq_abs] using hKexp 0)
  set Mtw : ℝ :=
    Cu * Cv + |σ ^ 2 / 2| * K₁ * Cv + |σ ^ 2 / 2| * K₂ * Cv +
      |σ| * K₁ * Cv + (1 / 2) * Cu * Cv
  set Mdr : ℝ := Cu * Kexp + Cu * (1 / 2) * Cv
  set M : ℝ := Mtw + Mdr
  have htw (x y : ℝ) : |twinGenerator σ u v x y| ≤ Mtw := by
    simp only [twinGenerator]
    have h1 : |(1 : ℝ) * deriv u x * v y| ≤ Cu * Cv := by
      simp only [one_mul, abs_mul]
      exact mul_le_mul (hu'_bdd x) (hv_bdd y) (abs_nonneg _) hCu
    have h2 : |(σ ^ 2 / 2) * x * deriv u x * v y| ≤ |σ ^ 2 / 2| * K₁ * Cv := by
      have : |(σ ^ 2 / 2) * (x * deriv u x) * v y| =
          |σ ^ 2 / 2| * |x * deriv u x| * |v y| := by
        simp [abs_mul, mul_assoc]
      rw [show (σ ^ 2 / 2) * x * deriv u x * v y =
          (σ ^ 2 / 2) * (x * deriv u x) * v y by ring, this]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hK₁ x) (abs_nonneg _))
        (hv_bdd y) (abs_nonneg _) (by positivity)
    have h3 : |(σ ^ 2 / 2) * x ^ 2 * deriv (deriv u) x * v y| ≤ |σ ^ 2 / 2| * K₂ * Cv := by
      have : |(σ ^ 2 / 2) * (x ^ 2 * deriv (deriv u) x) * v y| =
          |σ ^ 2 / 2| * |x ^ 2 * deriv (deriv u) x| * |v y| := by
        simp [abs_mul, mul_assoc]
      rw [show (σ ^ 2 / 2) * x ^ 2 * deriv (deriv u) x * v y =
          (σ ^ 2 / 2) * (x ^ 2 * deriv (deriv u) x) * v y by ring, this]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hK₂ x) (abs_nonneg _))
        (hv_bdd y) (abs_nonneg _) (by positivity)
    have h4 : |σ * x * deriv u x * deriv v y| ≤ |σ| * K₁ * Cv := by
      have : |σ * (x * deriv u x) * deriv v y| = |σ| * |x * deriv u x| * |deriv v y| := by
        simp [abs_mul, mul_assoc]
      rw [show σ * x * deriv u x * deriv v y = σ * (x * deriv u x) * deriv v y by ring, this]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hK₁ x) (abs_nonneg _))
        (hv'_bdd y) (abs_nonneg _) (by positivity)
    have h5 : |(1 / 2) * u x * deriv (deriv v) y| ≤ (1 / 2) * Cu * Cv := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hu_bdd x) (by norm_num))
        (hv''_bdd y) (abs_nonneg _) (by positivity)
    refine (abs_add_le _ _).trans ?_
    refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
    refine (add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl).trans ?_
    refine (add_le_add (add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl) le_rfl).trans ?_
    have := add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5
    simpa [Mtw] using this
  have hdr (x y : ℝ) :
      |deriv u x * Real.exp (σ * y) * v y +
          u x * ((1 : ℝ) / 2) * deriv (deriv v) y| ≤ Mdr := by
    have h1 : |deriv u x * Real.exp (σ * y) * v y| ≤ Cu * Kexp := by
      rw [mul_assoc, abs_mul]
      refine mul_le_mul (hu'_bdd x) ?_ (abs_nonneg _) hCu
      simpa [Real.norm_eq_abs] using hKexp y
    have h2 : |u x * ((1 : ℝ) / 2) * deriv (deriv v) y| ≤ Cu * (1 / 2) * Cv := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact mul_le_mul (mul_le_mul_of_nonneg_right (hu_bdd x) (by norm_num))
        (hv''_bdd y) (abs_nonneg _) (by positivity)
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  refine ⟨M, ?_, ?_, ?_⟩
  · intro x y
    have hu2' : ContDiff ℝ 2 u := hu.of_le (by decide)
    have hv2' : ContDiff ℝ 2 v := hv.of_le (by decide)
    rw [eq_twinGenerator_sub σ u v hu2' hv2' x y]
    exact (abs_sub _ _).trans (add_le_add (htw x y) (hdr x y))
  · intro x y
    exact (htw x y).trans (le_add_of_nonneg_right (by
      have : 0 ≤ Mdr := (abs_nonneg _).trans (hdr 0 0)
      exact this))
  · intro x y
    exact (hdr x y).trans (le_add_of_nonneg_left (by
      have : 0 ≤ Mtw := (abs_nonneg _).trans (htw 0 0)
      exact this))

end jointA

end Lyasoff2016
