/-
# §5 Integral representations (pp. 1079–1088)
-/
module

public import Lyasoff2016.Foliation
public import Lyasoff2016.YorClassical


@[expose] public section

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

/- Paper: p. 1081, (5.7), the residue recipe g ↦ R_{t,p}[g]:
     R_{t,2}(y) = g(y),   R_{t,p}(y) = (1 / ((p−2) sinh y)) (d/dy) R_{t,p−1}(y)   (p ≥ 3).
   Plain recap: R_{t,p}[g](y) is the residue at z = y of g(z) sinh z / (cosh z − cosh y)^{p−1}
   (display (5.6)), produced recursively from the generic symbol g.
   The recursion divides by sinh y, so for p ≥ 3 the value at y = 0 is Lean's `x / 0 = 0`
   rather than the limit in (5.6); only y ≠ 0 is meaningful there. -/
def Rrecipe (g : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => g
  | 1 => g
  | 2 => g
  | (p + 3) => fun y => deriv (Rrecipe g (p + 2)) y / (((p + 1 : ℕ) : ℂ) * Real.sinh y)

/- Paper: (5.6)/(5.7), R_{t,p}(y) for the concrete choice g = g_{t,p} of (5.8).
   PAPER NOTE: the skeleton's `Rrec p t y a := gFun p t (a i)` was not the paper's recipe
   (R_{t,p} is a function of y and does not involve the contour parameter a). -/
def Rrec (p : ℕ) (t : ℝ) (y : ℝ) : ℂ :=
  Rrecipe (fun s : ℝ => gFun p t s) p y

/-- (5.7) for p = 2: `R_{t,2} = g_{t,2}`. -/
lemma Rrec_two (t y : ℝ) : Rrec 2 t y = gFun 2 t y := rfl

/- Paper: p. 1080, (5.3), the integrand of the contour equation on the lower edge
   u ↦ u − ia of the contour ζ_a (p. 1082):
     g_{t,p}(u − ia) sinh(u − ia) / (cosh(u − ia) − cosh y)^{p−1}. -/
def contourIntegrand (p : ℕ) (t a y u : ℝ) : ℂ :=
  gFun p t (u - I * a) * Complex.sinh (u - I * a) /
    (Complex.cosh (u - I * a) - Complex.cosh y) ^ (p - 1)

/- Paper: p. 1080, (5.3), on the contour ζ = ζ_a of p. 1082, in the form of the display
   on p. 1083 ("With a completely analogous calculation, (5.3) can be cast as"):
     2 ∫_{−∞}^{∞} ℜ( g_{t,p}(u − ia) / (cosh(u − ia) − cosh y)^{p−1} · sinh(u − ia) ) du
       = ((−4)^{p−2} / (p−2)!) e^{−2y²/t}.
   Plain recap: ζ_a is the boundary of the strip {|ℑ z| < a}; since g_{t,p}(z̄) = −conj g_{t,p}(z)
   the upper edge contributes the conjugate of the lower one, leaving twice the real part.
   This is the only condition imposed on g_{t,p} (footnote 9).  The integrand is also
   required to be integrable (pp. 1084–1085).
   PAPER NOTE: earlier versions of `contourEq` took a density `φc` and equated
   `laplaceCond φc y ξ` with `0`, resp. with `∫ ℜ((−4/ξ)^{p−1} · contourIntegrand)`.  Neither
   is in the paper, and both are false for a genuine conditional density (at ξ = 0 they give
   `∫ φc(x|y) dx = 0`).  (5.3) involves no density: it is a statement about g_{t,p}, the
   contour ζ_a and y only. -/
def contourEq (p : ℕ) (t : ℝ) (y : ℝ) (a : ℝ) : Prop :=
  Integrable (fun u : ℝ => contourIntegrand p t a y u) ∧
  2 * ∫ u : ℝ, (contourIntegrand p t a y u).re =
    (-4 : ℝ) ^ (p - 2) / ((p - 2).factorial : ℝ) * Real.exp (-2 * y ^ 2 / t)

/- Paper: p. 1082–1085.
   Plain recap: g_{t,p} of (5.8) solves the contour equation (5.3) on ζ_a for every opening
   a ∈ [π/2, 3π/2] and every y ∈ ℝ (residues at z = ±y via (5.5)–(5.7); the vertical sides
   cancel because g_{t,p} is even).
   STATUS: not proved in Lean; the residue computation is taken as analytic input. -/
/-- Contour/residue identity (Lyasoff pp. 1082–1085); hole pending residue analysis. -/
theorem g_solves_contour_equation (p : ℕ) (hp : p = 2 ∨ p = 3 ∨ p = 4)
    (t : ℝ) (ht : 0 < t) (y : ℝ) (a : ℝ) (ha : Real.pi / 2 ≤ a ∧ a ≤ 3 * Real.pi / 2) :
    contourEq p t y a := by
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
