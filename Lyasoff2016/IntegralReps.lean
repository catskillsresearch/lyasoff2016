/-
# §5 Integral representations (pp. 1079–1088)
-/
module

public import Lyasoff2016.Foliation
public import Lyasoff2016.YorClassical
public import Lyasoff2016.Cerf
public import Lyasoff2016.GFun
public import Lyasoff2016.Rrecipe
public import Lyasoff2016.Rrec
public import Lyasoff2016.ContourIntegrand
public import Lyasoff2016.ContourEq
public import Lyasoff2016.PiFormula
public import Lyasoff2016.PiHalfFormula
public import Lyasoff2016.YorDensity


@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Paper, display before (5.9a)/(5.9b) with `σ = 2`:
`Re g_{4t,2}(u - iπ) = (4π)⁻¹ e^{π²/(2t)} e^{-u²/(2t)} sin(πu/t)`. -/
lemma gFun_two_re (t : ℝ) (ht : 0 < t) (u : ℝ) :
    (gFun 2 (t * 2 ^ 2) (u - I * π)).re =
      Real.exp (π ^ 2 / (2 * t)) / (4 * π) *
        (Real.exp (-u ^ 2 / (2 * t)) * Real.sin (π * u / t)) := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hπ0 : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hexp : (-2 * ((u : ℂ) - I * π) ^ 2 / ((t * 2 ^ 2 : ℝ) : ℂ)) =
      (((π ^ 2 - u ^ 2) / (2 * t) : ℝ) : ℂ) + ((π * u / t : ℝ) : ℂ) * I := by
    push_cast
    field_simp
    linear_combination (-(π : ℂ) ^ 2) * I_sq
  have hval : gFun 2 (t * 2 ^ 2) (u - I * π) =
      ((Real.exp ((π ^ 2 - u ^ 2) / (2 * t)) * Real.sin (π * u / t) / (4 * π) : ℝ) : ℂ) +
        ((-(Real.exp ((π ^ 2 - u ^ 2) / (2 * t)) * Real.cos (π * u / t) / (4 * π)) : ℝ) : ℂ) *
          I := by
    simp only [gFun]
    rw [hexp, Complex.exp_add, Complex.exp_mul_I, ← ofReal_exp, ← ofReal_cos, ← ofReal_sin]
    push_cast
    field_simp
    linear_combination (Complex.cos ((π : ℂ) * u / t)) * I_sq
  rw [hval]
  simp only [add_re, ofReal_re, re_ofReal_mul, I_re, mul_zero, add_zero]
  have : Real.exp ((π ^ 2 - u ^ 2) / (2 * t)) =
      Real.exp (π ^ 2 / (2 * t)) * Real.exp (-u ^ 2 / (2 * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this]; ring

/-- Algebraic core of Remark 5.1 (no sign restriction on `x`). -/
lemma remark_5_1_aux (t : ℝ≥0) (x y : ℝ) (ht : 0 < t) :
    gaussianPDFReal 0 t y * (2 ^ 2 : ℝ)⁻¹ * piFormula 2 2 t (x * 2 ^ 2) (y * 2) =
      yorDensity t x y := by
  have ht' : (0 : ℝ) < t := ht
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [piFormula, yorDensity]
  unfold piFormula yorDensity theta
  rw [gaussianPDFReal_def]
  have hint : ∫ u in Ioi (0 : ℝ), Real.sinh u *
      (((Real.exp (-(4 / (x * 2 ^ 2)) * Real.exp (y * 2 / 2) * Real.cosh u) : ℝ) : ℂ) *
        gFun 2 ((t : ℝ) * 2 ^ 2) (u - I * π)).re =
      Real.exp (π ^ 2 / (2 * t)) / (4 * π) *
        ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * t)) *
          Real.exp (-(Real.exp y / x) * Real.cosh u) *
          Real.sinh u * Real.sin (π * u / t) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    have he : -(4 / (x * 2 ^ 2)) * Real.exp (y * 2 / 2) * Real.cosh u =
        -(Real.exp y / x) * Real.cosh u := by
      rw [show y * 2 / 2 = y by ring]; field_simp; norm_num
    simp only [re_ofReal_mul, gFun_two_re (t : ℝ) ht' u, he]
    ring
  rw [hint]
  have hs : √(2 * π ^ 3 * t) = π * √(2 * π * t) := by
    rw [show 2 * π ^ 3 * (t : ℝ) = π ^ 2 * (2 * π * t) by ring, Real.sqrt_mul (sq_nonneg π),
      Real.sqrt_sq Real.pi_pos.le]
  have hexp : Real.exp (-(y - 0) ^ 2 / (2 * t)) *
      Real.exp (y * 2 * (((2 : ℕ) : ℝ) - 1) / 2 + (y * 2) ^ 2 / (2 * ((t : ℝ) * 2 ^ 2)) -
        2 * (Real.exp (y * 2) + 1) / (x * 2 ^ 2)) =
      Real.exp y * Real.exp (-(1 + Real.exp (2 * y)) / (2 * x)) := by
    rw [← Real.exp_add, ← Real.exp_add, show y * 2 = 2 * y by ring]
    congr 1
    push_cast
    field_simp
    ring
  rw [hs]
  calc (√(2 * π * t))⁻¹ * Real.exp (-(y - 0) ^ 2 / (2 * t)) * (2 ^ 2 : ℝ)⁻¹ *
        (2 ^ 4 * (16 / (x * 2 ^ 2) ^ 2) *
          Real.exp (y * 2 * (((2 : ℕ) : ℝ) - 1) / 2 + (y * 2) ^ 2 / (2 * ((t : ℝ) * 2 ^ 2)) -
            2 * (Real.exp (y * 2) + 1) / (x * 2 ^ 2)) *
          (Real.exp (π ^ 2 / (2 * t)) / (4 * π) *
            ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * t)) *
              Real.exp (-(Real.exp y / x) * Real.cosh u) *
              Real.sinh u * Real.sin (π * u / t)))
      = (Real.exp (-(y - 0) ^ 2 / (2 * t)) *
          Real.exp (y * 2 * (((2 : ℕ) : ℝ) - 1) / 2 + (y * 2) ^ 2 / (2 * ((t : ℝ) * 2 ^ 2)) -
            2 * (Real.exp (y * 2) + 1) / (x * 2 ^ 2))) *
          ((√(2 * π * t))⁻¹ * (2 ^ 2 : ℝ)⁻¹ * (2 ^ 4 * (16 / (x * 2 ^ 2) ^ 2)) *
            (Real.exp (π ^ 2 / (2 * t)) / (4 * π) *
              ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * t)) *
                Real.exp (-(Real.exp y / x) * Real.cosh u) *
                Real.sinh u * Real.sin (π * u / t))) := by ring
    _ = _ := by
        rw [hexp]
        field_simp
        ring

/- Paper: Remark 5.1.
   Plain recap: the π-formula of order 2 at σ = 2 recovers Yor’s (1.1). -/
theorem remark_5_1 (t : ℝ≥0) (x y : ℝ) (ht : 0 < t) (_hx : 0 < x) :
    gaussianPDFReal 0 t y * (2 ^ 2 : ℝ)⁻¹ *
        piFormula 2 2 t (x * 2 ^ 2) (y * 2) =
      yorDensity t x y :=
  remark_5_1_aux t x y ht

/- Paper: p. 1061 (1.1) — Yor’s joint density (wired to the constructive Laplace/FP proof).
   Plain recap: used by Remark 5.1 to identify the π-formula at order `p = 2`. -/
theorem yor_formula_classical (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (t : ℝ≥0) (ht : 0 < t) :
    IsJointDensity P W 2 0 t (fun x y => yorDensity t x y) :=
  yor_joint_density_classical P W hW t ht

/- Paper: p. 1061 (1.1) — Yor’s theorem via Remark 5.1 once the π-formula is known, or
   directly via `yor_formula_classical`. -/
theorem yor_formula (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (t : ℝ≥0) (ht : 0 < t) :
    IsJointDensity P W 2 0 t (fun x y => yorDensity t x y) :=
  yor_formula_classical P W hW t ht

/-- The π-formula of order 2 recovers Yor’s density, hence is a joint density at `σ = 2`. -/
theorem pi_formula_two_sigma_two (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (t : ℝ≥0) (ht : 0 < t) :
    IsJointDensity P W 2 0 t (fun x y =>
      gaussianPDFReal 0 t y * (2 ^ 2 : ℝ)⁻¹ * piFormula 2 2 t (x * 2 ^ 2) (y * 2)) := by
  have h := yor_formula_classical P W hW t ht
  have hfun :
      (fun x y : ℝ =>
        gaussianPDFReal 0 t y * ((2 : ℝ) ^ 2)⁻¹ * piFormula 2 2 t (x * (2 : ℝ) ^ 2) (y * 2)) =
        fun x y => yorDensity t x y := by
    funext x y
    exact remark_5_1_aux t x y ht
  rwa [← hfun] at h

/- Paper: p. 1085–1086.
   Plain recap: both π/2 and π formulae equal the joint density for p = 2,3,4.
   Special case `p = 2`, `σ = 2` for the π-formula is also `pi_formula_two_sigma_two`
   (Yor + Remark 5.1). The general identification is classical analytic input. -/
/-- Density identification for the π / π/2 formulae (Lyasoff pp. 1085–1086); hole. -/
theorem pi_formula (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (hσ : 0 < σ) (ht : 0 < t) (p : ℕ)
    (hp : p = 2 ∨ p = 3 ∨ p = 4) :
    IsJointDensity P W σ 0 t (fun x y =>
      gaussianPDFReal 0 t y * (σ ^ 2)⁻¹ * piHalfFormula p σ t (x * σ ^ 2) (y * σ)) ∧
    IsJointDensity P W σ 0 t (fun x y =>
      gaussianPDFReal 0 t y * (σ ^ 2)⁻¹ * piFormula p σ t (x * σ ^ 2) (y * σ)) := by
  sorry

/- Paper: Remark 5.5. -/
theorem remark_5_5 :
    ∀ x : ℝ, 0 ≤ x → Real.arcosh (Real.cosh x) = x :=
  fun _ hx => Real.arcosh_cosh hx

end Lyasoff2016
