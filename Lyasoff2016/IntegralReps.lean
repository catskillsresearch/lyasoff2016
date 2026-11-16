/-
# §5 Integral representations (pp. 1079–1088)
-/
import Lyasoff2016.Foliation

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

/- Paper: p. 1082–1083, complex error function used to build g_{t,p} for p = 3,4.
   Plain recap: entire function erf on ℂ, defined via the Gaussian integral. -/
def cerf (z : ℂ) : ℂ :=
  (2 / Real.sqrt Real.pi : ℂ) * ∫ t in (0 : ℝ)..1, Complex.exp (-(t * z) ^ 2) * z

/- Paper: (5.8), functions g_{t,p} for p = 2,3,4.
   Plain recap: entire (even) building blocks for the contour representation.
   g_{t,2}(z) = e^{-2z²/t}/(4πi);
   g_{t,3}(z) = e^{t/8} √t/(4i√(2π)) (cerf((t+4z)/(2√(2t))) + cerf((t−4z)/(2√(2t))));
   g_{t,4}(z) = e^{t/2} √t/(2i√(2π)) (cerf((t+2z)/√(2t)) + cerf((t−2z)/√(2t)))
              − e^{t/8} cosh z · √t/(i√(2π)) (cerf((t+4z)/(2√(2t))) + cerf((t−4z)/(2√(2t)))). -/
def gFun (p : ℕ) (t : ℝ) (z : ℂ) : ℂ :=
  match p with
  | 2 => cexp (-2 * z ^ 2 / t) / (4 * π * I)
  | 3 =>
      Real.exp (t / 8) * (√t / (4 * I * √(2 * π))) *
        (cerf ((t + 4 * z) / (2 * √(2 * t))) + cerf ((t - 4 * z) / (2 * √(2 * t))))
  | 4 =>
      Real.exp (t / 2) * (√t / (2 * I * √(2 * π))) *
          (cerf ((t + 2 * z) / √(2 * t)) + cerf ((t - 2 * z) / √(2 * t))) -
        Real.exp (t / 8) * Complex.cosh z * (√t / (I * √(2 * π))) *
          (cerf ((t + 4 * z) / (2 * √(2 * t))) + cerf ((t - 4 * z) / (2 * √(2 * t))))
  | _ => 0

/-- `g_{t,2}` is entire (as a quotient of an entire function by a nonzero constant). -/
theorem gFun_two_contDiff (t : ℝ) (_ht : t ≠ 0) :
    ContDiff ℂ ⊤ (gFun 2 t) := by
  unfold gFun
  have h1 : ContDiff ℂ ⊤ fun z : ℂ => -2 * z ^ 2 / (t : ℂ) := by fun_prop
  have h2 : ContDiff ℂ ⊤ fun z : ℂ => cexp (-2 * z ^ 2 / (t : ℂ)) := h1.cexp
  have h3 : ContDiff ℂ ⊤ fun _ : ℂ => (4 * π * I : ℂ) := contDiff_const
  convert h2.div h3 (fun _ => by simp [Complex.I_ne_zero, Real.pi_ne_zero]) using 1

/- Paper: (5.7), residue recipe R.
   Plain recap: residue contribution used when closing contours. -/
def Rrec (p : ℕ) (t : ℝ) (_y : ℝ) (a : ℝ) : ℂ :=
  gFun p t (a * Complex.I)

/- Paper: (5.2)/(5.3), strip contour equation for the Laplace inversion.
   Plain recap: after residue calculus on ζ_a the Laplace transform of the conditional
   density equals the real-part integral against g_{t,p}(u−ia) sinh(u−ia) /
   (cosh(u−ia)−cosh y)^{p−1}.  The opening angle a is an extra parameter of the claim
   `g_solves_contour_equation`. -/
def contourIntegrand (p : ℕ) (t a y u : ℝ) : ℂ :=
  gFun p t (u - I * a) * Complex.sinh (u - I * a) /
    (Complex.cosh (u - I * a) - Complex.cosh y) ^ (p - 1)

def contourEq (p : ℕ) (t : ℝ) (y : ℝ) (a : ℝ) (φc : ℝ → ℝ → ℝ) : Prop :=
  ∀ ξ ≥ 0, laplaceCond φc y ξ =
    (∫ u : ℝ, ((-(4 : ℂ) / (ξ : ℂ)).cpow (p - 1) *
      contourIntegrand p t a y u).re)

/- Paper: p. 1083–1085.
   Plain recap: g_{t,p} solves the contour equation for opening angles a ∈ [π/2, 3π/2].
   PAPER NOTE: the skeleton quantified over an arbitrary φc; the intended claim is that
   the true conditional density (and equivalently the π-formula candidate) satisfies the
   contour equation. Hypotheses restored to the paper's meaning. -/
theorem g_solves_contour_equation (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (σ : ℝ) (t : ℝ≥0)
    (hσ : 0 < σ) (ht : 0 < t) (p : ℕ) (hp : p = 2 ∨ p = 3 ∨ p = 4)
    (y : ℝ) (a : ℝ) (ha : Real.pi / 2 ≤ a ∧ a ≤ 3 * Real.pi / 2)
    (φc : ℝ → ℝ → ℝ) (hφc : IsCondDensity P W σ t φc) :
    contourEq p t y a φc := by
  -- Contour/residue analysis of `gFun p` against the Laplace transform of `φc`.
  sorry

/- Paper: (5.9b)/(5.10b), π-formula for the conditional density, normalised so that
   `gaussianPDFReal 0 t y * (σ²)⁻¹ * piFormula p σ t (x σ²) (y σ)` is the joint density.
   PAPER NOTE: includes the Jacobian/scaling factor σ⁴ and the paper's sinh-integral
   form; the skeleton's stub `∫ (gFun …).re` omitted these and made Remark 5.1 false. -/
def piFormula (p : ℕ) (σ t x y : ℝ) : ℝ :=
  σ ^ 4 * (16 / x ^ p) *
    Real.exp (y * (p - 1) / 2 + y ^ 2 / (2 * (t * σ ^ 2)) - 2 * (Real.exp y + 1) / x) *
    ∫ u in Ioi (0 : ℝ), Real.sinh u *
      (((Real.exp (-(4 / x) * Real.exp (y / 2) * Real.cosh u) : ℝ) : ℂ) *
        gFun p (t * σ ^ 2) (u - I * π)).re

/- Paper: (5.9a)/(5.10a), π/2-formula (same normalisation). -/
def piHalfFormula (p : ℕ) (σ t x y : ℝ) : ℝ :=
  σ ^ 4 * (16 / x ^ p) *
    Real.exp (y * (p - 1) / 2 + y ^ 2 / (2 * (t * σ ^ 2)) - 2 * (Real.exp y + 1) / x) *
    ∫ u in Ioi (0 : ℝ), Real.sinh u *
      (((Real.exp (-(4 / x) * Real.exp (y / 2) * Real.cosh u) : ℝ) : ℂ) *
        gFun p (t * σ ^ 2) (u - I * (Real.pi / 2))).re

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

/- Paper: p. 1061 (1.1) — Yor’s classical joint density (independent of the contour analysis).
   Plain recap: this is the classical input used by Remark 5.1 to identify the π-formula
   at order `p = 2`; the contour derivation in §5 recovers it as a special case. -/
theorem yor_formula_classical (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (t : ℝ≥0) (ht : 0 < t) :
    IsJointDensity P W 2 0 t (fun x y => yorDensity t x y) := by
  sorry

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
   The case `p = 2` reduces to Yor via Remark 5.1 and Brownian scaling; `p = 3,4`
   need the contour analysis of `g_solves_contour_equation`. -/
theorem pi_formula (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (hσ : 0 < σ) (ht : 0 < t) (p : ℕ)
    (hp : p = 2 ∨ p = 3 ∨ p = 4) :
    IsJointDensity P W σ 0 t (fun x y =>
      gaussianPDFReal 0 t y * (σ ^ 2)⁻¹ * piHalfFormula p σ t (x * σ ^ 2) (y * σ)) ∧
    IsJointDensity P W σ 0 t (fun x y =>
      gaussianPDFReal 0 t y * (σ ^ 2)⁻¹ * piFormula p σ t (x * σ ^ 2) (y * σ)) := by
  -- Case split on the order `p`.
  rcases hp with rfl | rfl | rfl
  · -- `p = 2`: π-formula via Yor + Remark 5.1 + Brownian scaling; π/2-formula via contour.
    refine ⟨?_, ?_⟩
    · -- π/2-formula of order 2
      sorry
    · -- π-formula of order 2
      if hσ2 : σ = 2 then
        subst hσ2
        exact pi_formula_two_sigma_two P W hW t ht
      else
        -- general `σ` by Brownian scaling from the `σ = 2` case
        sorry
  · -- `p = 3`: contour analysis with `gFun 3`
    sorry
  · -- `p = 4`: contour analysis with `gFun 4` (needed for Asian pricing)
    sorry

/- Paper: Remark 5.5. -/
theorem remark_5_5 :
    ∀ x : ℝ, 0 ≤ x → Real.arcosh (Real.cosh x) = x :=
  fun _ hx => Real.arcosh_cosh hx

end Lyasoff2016
