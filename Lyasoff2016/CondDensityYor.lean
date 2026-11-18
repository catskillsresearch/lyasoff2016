/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
# §4 A genuine conditional density of `(expInt, W)` from Yor's formula

Brownian scaling from the reference volatility `2` (`IsJointDensity_scaling_from_two_fixed`)
applied to Yor's joint density (`yor_joint_density`) gives a joint density of
`(∫₀ᵀ e^{σW_s} ds, W_T)` for every `σ > 0`; dividing by the Gaussian marginal gives a
conditional density `scaledYorCondDensity σ T` in the sense of `IsCondDensity`.

Because the `θ`-argument `e^y / x` of Yor's density is constant along the curves
`(x e^{σ y/2}, y)`, this conditional density satisfies the integrated foliation ODE (4.5)
by pure algebra (`scaledYorCondDensity_foliation_ode`).
-/
module

public import Lyasoff2016.Setting
public import Lyasoff2016.YorJointDensity
public import Lyasoff2016.PiFormulaScaling
public import Lyasoff2016.YorAnalytic

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Conditional density of `∫₀ᵀ e^{σ W_s} ds` given `W_T = y`, obtained from Yor's
σ = 2 joint density by Brownian scaling and division by the Gaussian marginal. -/
def scaledYorCondDensity (σ : ℝ) (T : ℝ≥0) (x y : ℝ) : ℝ :=
  (σ / 2) ^ 3 * yorDensity (referenceTimeFromTwo σ T) (σ ^ 2 / 4 * x) (σ / 2 * y) /
    gaussianPDFReal 0 T y

/-- `scaledYorCondDensity σ T` is a conditional density of `(expInt W σ 0 T, W T)`. -/
theorem isCondDensity_scaledYorCondDensity (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) {σ : ℝ} (hσ : 0 < σ) {T : ℝ≥0} (hT : 0 < T) :
    IsCondDensity P W σ T (scaledYorCondDensity σ T) := by
  have hτ : 0 < referenceTimeFromTwo σ T := referenceTimeFromTwo_pos hσ hT
  have h := IsJointDensity_scaling_from_two_fixed P W hW hσ T
    (fun x y => yorDensity (referenceTimeFromTwo σ T) x y)
    (yor_joint_density P W hW _ hτ) (yorDensity_ennreal_measurable _ hτ)
  unfold IsCondDensity
  convert h using 3 with x y
  have hg : gaussianPDFReal 0 T y ≠ 0 := (gaussianPDFReal_pos 0 T y hT.ne').ne'
  unfold scaledYorCondDensity
  field_simp

/-- The integrated foliation ODE (4.5) for `scaledYorCondDensity`: Yor's `θ`-factor is
invariant along the foliation, and the remaining factors are explicit. -/
theorem scaledYorCondDensity_foliation_ode {σ : ℝ} (hσ : 0 < σ) {T : ℝ≥0} (hT : 0 < T) :
    ∀ x > 0, ∀ u : ℝ,
      scaledYorCondDensity σ T (x / σ ^ 2 * Real.exp (u / 2)) (u / σ) =
        scaledYorCondDensity σ T (x / σ ^ 2) 0 *
          Real.exp (-u / 2 - 4 / x * Real.cosh (u / 2) + 4 / x +
            u ^ 2 / (2 * σ ^ 2 * (T : ℝ))) := by
  intro x hx u
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  set E := Real.exp (u / 2) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hEne : E ≠ 0 := hEpos.ne'
  have hx1 : σ ^ 2 / 4 * (x / σ ^ 2 * E) = x / 4 * E := by field_simp
  have hx0 : σ ^ 2 / 4 * (x / σ ^ 2) = x / 4 := by field_simp
  have hy1 : σ / 2 * (u / σ) = u / 2 := by field_simp
  unfold scaledYorCondDensity yorDensity
  rw [hx1, hx0, hy1, mul_zero, Real.exp_zero]
  have hr : Real.exp (u / 2) / (x / 4 * E) = 1 / (x / 4) := by
    rw [← hE]; field_simp
  rw [hr]
  set Θ := theta (1 / (x / 4)) (referenceTimeFromTwo σ T)
  have h2 : Real.exp (2 * (u / 2)) = E ^ 2 := by
    rw [hE, ← Real.exp_nat_mul]; congr 1
  have hcosh : Real.cosh (u / 2) = (E + E⁻¹) / 2 := by
    rw [Real.cosh_eq, hE, Real.exp_neg]
  have hexp1 : Real.exp (-(1 + E ^ 2) / (2 * (x / 4 * E))) =
      Real.exp (-4 / x * Real.cosh (u / 2) + 4 / x) * Real.exp (-(1 + 1) / (2 * (x / 4))) := by
    rw [← Real.exp_add]; congr 1; rw [hcosh]; field_simp; ring
  have hneg : Real.exp (-u / 2) = E⁻¹ := by rw [hE, ← Real.exp_neg]; ring_nf
  simp only [gaussianPDFReal_def, sub_zero]
  rw [h2, hexp1]
  have hsplit : Real.exp (-u / 2 - 4 / x * Real.cosh (u / 2) + 4 / x +
      u ^ 2 / (2 * σ ^ 2 * (T : ℝ))) =
      Real.exp (-u / 2) * Real.exp (-4 / x * Real.cosh (u / 2) + 4 / x) *
        Real.exp (u ^ 2 / (2 * σ ^ 2 * (T : ℝ))) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hgauss : Real.exp (-(u / σ) ^ 2 / (2 * (T : ℝ))) *
      Real.exp (u ^ 2 / (2 * σ ^ 2 * (T : ℝ))) = 1 := by
    rw [← Real.exp_add, ← Real.exp_zero]; congr 1; field_simp; ring
  rw [hsplit, hneg]
  have hsq : (√(2 * π * (T : ℝ)))⁻¹ ≠ 0 := by
    have : 0 < 2 * π * (T : ℝ) := by positivity
    exact inv_ne_zero (Real.sqrt_pos.2 this).ne'
  have hge : Real.exp (-(u / σ) ^ 2 / (2 * (T : ℝ))) ≠ 0 := (Real.exp_pos _).ne'
  have hzero : -(0:ℝ) ^ 2 / (2 * (T : ℝ)) = 0 := by ring
  rw [hzero, Real.exp_zero]
  simp only [mul_zero, Real.exp_zero]
  field_simp
  have hg2 : Real.exp (-(u ^ 2 / (σ ^ 2 * 2 * (T : ℝ)))) *
      Real.exp (u ^ 2 / (σ ^ 2 * 2 * (T : ℝ))) = 1 := by
    rw [← Real.exp_add, ← Real.exp_zero]; congr 1; ring
  linear_combination (-Θ) * hg2

/-- Each conditional slice of `scaledYorCondDensity` has unit mass on `(0, ∞)`. -/
theorem integral_scaledYorCondDensity {σ : ℝ} (hσ : 0 < σ) {T : ℝ≥0} (hT : 0 < T) (y : ℝ) :
    ∫ x in Ioi (0 : ℝ), scaledYorCondDensity σ T x y = 1 := by
  have hτ : 0 < referenceTimeFromTwo σ T := referenceTimeFromTwo_pos hσ hT
  have hg : gaussianPDFReal 0 T y ≠ 0 := (gaussianPDFReal_pos 0 T y hT.ne').ne'
  have hb : (0 : ℝ) < σ ^ 2 / 4 := by positivity
  unfold scaledYorCondDensity
  simp_rw [div_eq_mul_inv _ (gaussianPDFReal 0 T y)]
  rw [integral_mul_const, integral_const_mul,
    integral_comp_mul_left_Ioi (fun x => yorDensity (referenceTimeFromTwo σ T) x (σ / 2 * y))
      0 hb, mul_zero, yorDensity_integral_x_eq_gaussian _ hτ,
    gaussianPDFReal_referenceTimeFromTwo hσ T y, smul_eq_mul]
  field_simp
  ring

/-! ## A smooth version and the Theorem 4.1 transport PDE -/

/-- The explicit `x > 0` branch of the σ = 2 conditional density `yorCondDensity`. -/
def yorCondExplicit (τ X Y : ℝ) : ℝ :=
  (Real.exp (Real.pi ^ 2 / (2 * τ)) / Real.pi) *
    Real.exp (Y ^ 2 / (2 * τ) - (1 + Real.exp (2 * Y)) / (2 * X) + Y) *
    (X ^ 2)⁻¹ * Jm τ 0 (Real.exp Y / X)

lemma yorCondDensity_eq_explicit (τ : ℝ) {X : ℝ} (hX : 0 < X) (Y : ℝ) :
    yorCondDensity τ X Y = yorCondExplicit τ X Y := by
  simp [yorCondDensity, yorCondExplicit, hX, zpow_neg, zpow_ofNat]

lemma yorCondExplicit_hasDerivAt_X {τ : ℝ} (hτ : 0 < τ) {X : ℝ} (hX : 0 < X) (Y : ℝ) :
    HasDerivAt (fun X' => yorCondExplicit τ X' Y)
      ((Real.exp (Real.pi ^ 2 / (2 * τ)) / Real.pi) *
        Real.exp (Y ^ 2 / (2 * τ) - (1 + Real.exp (2 * Y)) / (2 * X) + Y) *
        ((1 + Real.exp (2 * Y)) / (2 * X ^ 2) * (X ^ 2)⁻¹ * Jm τ 0 (Real.exp Y / X)
          - 2 / X ^ 3 * Jm τ 0 (Real.exp Y / X)
          + (X ^ 2)⁻¹ * Jm τ 1 (Real.exp Y / X) * (-(Real.exp Y) / X ^ 2))) X := by
  have hX0 : X ≠ 0 := hX.ne'
  have hr : 0 < Real.exp Y / X := div_pos (Real.exp_pos _) hX
  have hlin : HasDerivAt (fun X' : ℝ => 2 * X') 2 X := by
    simpa using (hasDerivAt_id X).const_mul (2 : ℝ)
  have hA : HasDerivAt (fun X' : ℝ => Y ^ 2 / (2 * τ) - (1 + Real.exp (2 * Y)) / (2 * X') + Y)
      (-((0 * (2 * X) - (1 + Real.exp (2 * Y)) * 2) / (2 * X) ^ 2)) X :=
    ((hasDerivAt_const X _).sub ((hasDerivAt_const X _).div hlin
      (mul_ne_zero two_ne_zero hX0))).add_const _ |>.congr_deriv (by ring)
  have hsq : HasDerivAt (fun X' : ℝ => (X' ^ 2)⁻¹) (-(2 * X) / (X ^ 2) ^ 2) X := by
    have h := (hasDerivAt_pow 2 X).inv (pow_ne_zero 2 hX0)
    refine h.congr_deriv ?_
    push_cast; ring
  have hrX : HasDerivAt (fun X' : ℝ => Real.exp Y / X') (-(Real.exp Y) / X ^ 2) X := by
    have h := (hasDerivAt_const X (Real.exp Y)).div (hasDerivAt_id X) hX0
    refine h.congr_deriv ?_
    simp
  have hJ := (Jm.hasDerivAt hτ 0 hr).comp X hrX
  have h := (((hasDerivAt_const X (Real.exp (Real.pi ^ 2 / (2 * τ)) / Real.pi)).mul
    hA.exp).mul hsq).mul hJ
  unfold yorCondExplicit
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply, Function.comp_apply, zero_add, zero_mul]
  field_simp
  ring

lemma yorCondExplicit_hasDerivAt_Y {τ : ℝ} (hτ : 0 < τ) {X : ℝ} (hX : 0 < X) (Y : ℝ) :
    HasDerivAt (fun Y' => yorCondExplicit τ X Y')
      ((Real.exp (Real.pi ^ 2 / (2 * τ)) / Real.pi) *
        Real.exp (Y ^ 2 / (2 * τ) - (1 + Real.exp (2 * Y)) / (2 * X) + Y) * (X ^ 2)⁻¹ *
        ((Y / τ - Real.exp (2 * Y) / X + 1) * Jm τ 0 (Real.exp Y / X)
          + Jm τ 1 (Real.exp Y / X) * (Real.exp Y / X))) Y := by
  have hX0 : X ≠ 0 := hX.ne'
  have hτ0 : τ ≠ 0 := hτ.ne'
  have hr : 0 < Real.exp Y / X := div_pos (Real.exp_pos _) hX
  have h2 : HasDerivAt (fun Y' : ℝ => Real.exp (2 * Y')) (Real.exp (2 * Y) * 2) Y := by
    simpa using ((hasDerivAt_id Y).const_mul (2 : ℝ)).exp
  have hA : HasDerivAt (fun Y' : ℝ => Y' ^ 2 / (2 * τ) - (1 + Real.exp (2 * Y')) / (2 * X) + Y')
      (Y / τ - Real.exp (2 * Y) / X + 1) Y := by
    have := (((hasDerivAt_pow 2 Y).div_const (2 * τ)).sub
      ((h2.const_add 1).div_const (2 * X))).add (hasDerivAt_id Y)
    refine this.congr_deriv ?_
    push_cast
    field_simp
  have hrY : HasDerivAt (fun Y' : ℝ => Real.exp Y' / X) (Real.exp Y / X) Y :=
    (Real.hasDerivAt_exp Y).div_const X
  have hJ := (Jm.hasDerivAt hτ 0 hr).comp Y hrY
  have h := (((hasDerivAt_const Y (Real.exp (Real.pi ^ 2 / (2 * τ)) / Real.pi)).mul
    hA.exp).mul (hasDerivAt_const Y (X ^ 2)⁻¹)).mul hJ
  unfold yorCondExplicit
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply, Function.comp_apply, zero_add, zero_mul, add_zero, mul_zero]
  ring

/-- The σ = 2 transport identity for the explicit branch: the `Jm τ 1` terms cancel
because the vector field `X ∂_X + ∂_Y` annihilates the θ-argument `e^Y / X`. -/
lemma yorCondExplicit_transport {τ : ℝ} (hτ : 0 < τ) {X : ℝ} (hX : 0 < X) (Y : ℝ) :
    X * ((Real.exp (Real.pi ^ 2 / (2 * τ)) / Real.pi) *
        Real.exp (Y ^ 2 / (2 * τ) - (1 + Real.exp (2 * Y)) / (2 * X) + Y) *
        ((1 + Real.exp (2 * Y)) / (2 * X ^ 2) * (X ^ 2)⁻¹ * Jm τ 0 (Real.exp Y / X)
          - 2 / X ^ 3 * Jm τ 0 (Real.exp Y / X)
          + (X ^ 2)⁻¹ * Jm τ 1 (Real.exp Y / X) * (-(Real.exp Y) / X ^ 2))) +
      (Real.exp (Real.pi ^ 2 / (2 * τ)) / Real.pi) *
        Real.exp (Y ^ 2 / (2 * τ) - (1 + Real.exp (2 * Y)) / (2 * X) + Y) * (X ^ 2)⁻¹ *
        ((Y / τ - Real.exp (2 * Y) / X + 1) * Jm τ 0 (Real.exp Y / X)
          + Jm τ 1 (Real.exp Y / X) * (Real.exp Y / X)) =
      (Y / τ + (1 - Real.exp (2 * Y)) / (2 * X) - 1) * yorCondExplicit τ X Y := by
  have hX0 : X ≠ 0 := hX.ne'
  have hτ0 : τ ≠ 0 := hτ.ne'
  unfold yorCondExplicit
  field_simp
  ring

/-- A conditional density of `(expInt W σ 0 T, W T)` built from the smooth σ = 2
conditional density `yorCondDensity` by Brownian scaling. It agrees everywhere with
`scaledYorCondDensity`. -/
def smoothYorCondDensity (σ : ℝ) (T : ℝ≥0) (x y : ℝ) : ℝ :=
  (σ / 2) ^ 2 * yorCondDensity (referenceTimeFromTwo σ T) (σ ^ 2 / 4 * x) (σ / 2 * y)

lemma smoothYorCondDensity_eq_scaled {σ : ℝ} (hσ : 0 < σ) {T : ℝ≥0} (hT : 0 < T) :
    smoothYorCondDensity σ T = scaledYorCondDensity σ T := by
  have hτ : 0 < referenceTimeFromTwo σ T := referenceTimeFromTwo_pos hσ hT
  funext x y
  have hg : gaussianPDFReal 0 T y ≠ 0 := (gaussianPDFReal_pos 0 T y hT.ne').ne'
  have hσ0 : σ ≠ 0 := hσ.ne'
  unfold smoothYorCondDensity scaledYorCondDensity
  rw [← gaussianPDFReal_mul_yorCondDensity hτ, gaussianPDFReal_referenceTimeFromTwo hσ T y]
  field_simp

theorem isCondDensity_smoothYorCondDensity (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) {σ : ℝ} (hσ : 0 < σ) {T : ℝ≥0} (hT : 0 < T) :
    IsCondDensity P W σ T (smoothYorCondDensity σ T) := by
  rw [smoothYorCondDensity_eq_scaled hσ hT]
  exact isCondDensity_scaledYorCondDensity P W hW hσ hT

/-- The Theorem 4.1 transport PDE for `smoothYorCondDensity`. -/
theorem smoothYorCondDensity_transport_pde {σ : ℝ} (hσ : 0 < σ) {T : ℝ≥0} (hT : 0 < T) :
    ∀ x > 0, ∀ y : ℝ,
      σ ^ 2 * x / 2 * deriv (fun z => smoothYorCondDensity σ T z y) x +
          σ * deriv (fun y' => smoothYorCondDensity σ T x y') y
        = (σ * y / (T : ℝ) + (1 - Real.exp (σ * y)) / x - σ ^ 2 / 2) *
            smoothYorCondDensity σ T x y := by
  intro x hx y
  set τR : ℝ := (referenceTimeFromTwo σ T : ℝ) with hτRdef
  have hτ : 0 < τR := referenceTimeFromTwo_pos hσ hT
  have hτv : τR = (T : ℝ) * σ ^ 2 / 4 := by
    rw [hτRdef, referenceTimeFromTwo, Real.coe_toNNReal]; positivity
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have hX : 0 < σ ^ 2 / 4 * x := by positivity
  -- x-derivative
  have hlinx : HasDerivAt (fun z : ℝ => σ ^ 2 / 4 * z) (σ ^ 2 / 4) x := by
    simpa using (hasDerivAt_id x).const_mul (σ ^ 2 / 4)
  have hdx := ((yorCondExplicit_hasDerivAt_X hτ hX (σ / 2 * y)).comp x hlinx).const_mul
    ((σ / 2) ^ 2)
  have heqx : (fun z => smoothYorCondDensity σ T z y) =ᶠ[𝓝 x]
      (fun z => (σ / 2) ^ 2 * ((fun X' => yorCondExplicit τR X' (σ / 2 * y)) ∘
        (fun z : ℝ => σ ^ 2 / 4 * z)) z) := by
    filter_upwards [Ioi_mem_nhds hx] with z hz
    have hz' : 0 < σ ^ 2 / 4 * z := mul_pos (by positivity) hz
    simp only [smoothYorCondDensity, Function.comp_apply]
    rw [yorCondDensity_eq_explicit _ hz']
  rw [(hdx.congr_of_eventuallyEq heqx).deriv]
  -- y-derivative
  have hliny : HasDerivAt (fun z : ℝ => σ / 2 * z) (σ / 2) y := by
    simpa using (hasDerivAt_id y).const_mul (σ / 2)
  have hdy := ((yorCondExplicit_hasDerivAt_Y hτ hX (σ / 2 * y)).comp y hliny).const_mul
    ((σ / 2) ^ 2)
  have heqy : (fun y' => smoothYorCondDensity σ T x y') =
      (fun y' => (σ / 2) ^ 2 * ((fun Y' => yorCondExplicit τR (σ ^ 2 / 4 * x) Y') ∘
        (fun z : ℝ => σ / 2 * z)) y') := by
    funext y'
    simp only [smoothYorCondDensity, Function.comp_apply]
    rw [yorCondDensity_eq_explicit _ hX]
  rw [heqy, hdy.deriv]
  have hP := yorCondExplicit_transport hτ hX (σ / 2 * y)
  have h2y : 2 * (σ / 2 * y) = σ * y := by ring
  rw [h2y] at hP
  have hbr : σ ^ 2 / 2 * ((σ / 2 * y) / τR + (1 - Real.exp (σ * y)) / (2 * (σ ^ 2 / 4 * x)) - 1)
      = σ * y / (T : ℝ) + (1 - Real.exp (σ * y)) / x - σ ^ 2 / 2 := by
    rw [hτv]; field_simp; ring
  simp only [smoothYorCondDensity]
  rw [yorCondDensity_eq_explicit _ hX, ← hbr]
  simp only [h2y]
  linear_combination ((σ / 2) ^ 2 * (σ ^ 2 / 2)) * hP

end Lyasoff2016
