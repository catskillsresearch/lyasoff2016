/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Constructive identification of the π/2-formula with the π-formula (and hence with Yor).

The order-two cosine–sine kernel exchange is `piHalf_cos_integral_eq_pi_sin_integral` below,
proved by Laplace uniqueness (`piHalfFormula_sigma_two_laplace` vs.
`piFormula_sigma_two_laplace`) plus continuity in `x`; with it, `remark_5_1_half_aux` matches
Remark 5.1 and the density transfer is purely algebraic.
-/
module

public import Lyasoff2016.PiHalfFormula
public import Lyasoff2016.PiHalfFormulaHigher
public import Lyasoff2016.PiFormulaLaplace
public import Lyasoff2016.PiFormulaScaling


@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Integrable Gaussian–`cosh` envelope dominating both the cosine and the sine kernels. -/
private lemma integrable_gauss_mul_cosh {t : ℝ} (ht : 0 < t) :
    Integrable fun u : ℝ => Real.exp (-u ^ 2 / (2 * t)) * Real.cosh u := by
  have h := GFunDecay.integrable_cosh_sq_mul_gaussian (T := 2 * t) (by positivity)
  refine h.mono' (Continuous.aestronglyMeasurable (by fun_prop))
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 := Real.one_le_cosh u
  have hE : 0 ≤ Real.exp (-u ^ 2 / (2 * t)) := (Real.exp_pos _).le
  nlinarith [mul_nonneg hE (mul_nonneg (Real.cosh_pos u).le (by linarith : 0 ≤ Real.cosh u - 1))]

/-- The integrand of the order-two π/2-formula at `σ = 2` in cosine form (paper (5.10a)). -/
private lemma piHalf_two_integrand_eq (t : ℝ) (ht : 0 < t) (z y : ℝ) (hz : 0 < z) (u : ℝ) :
    Real.cosh u *
        (I * cexp (-I * ((4 / ((z * 2 ^ 2 : ℝ) : ℂ)) *
          Real.exp (y * 2 / 2) * Real.sinh u)) *
          gFun 2 (t * 2 ^ 2) (u - I * (π / 2))).re =
      Real.exp (π ^ 2 / (8 * t)) / (4 * π) *
        (Real.exp (-u ^ 2 / (2 * t)) * Real.cosh u *
          Real.cos ((Real.exp y / z) * Real.sinh u - π * u / (2 * t))) := by
  have hphase :
      cexp (-I * (((Real.exp y / z) * Real.sinh u : ℝ) : ℂ)) =
        ((Real.cos ((Real.exp y / z) * Real.sinh u) : ℝ) : ℂ) -
          ((Real.sin ((Real.exp y / z) * Real.sinh u) : ℝ) : ℂ) * I := by
    have harg :
        -I * (((Real.exp y / z) * Real.sinh u : ℝ) : ℂ) =
          (((-((Real.exp y / z) * Real.sinh u) : ℝ) : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [harg, Complex.exp_mul_I]
    apply Complex.ext <;> simp
    ring
  rw [show
    (4 / ((z * 2 ^ 2 : ℝ) : ℂ)) * Real.exp (y * 2 / 2) * Real.sinh u =
        (((Real.exp y / z) * Real.sinh u : ℝ) : ℂ) by
      rw [show y * 2 / 2 = y by ring]
      push_cast
      field_simp [hz.ne']
      ring, hphase]
  obtain ⟨hgre, hgim⟩ := gFun_two_re_half t ht u
  have hosc :
      (I * (((Real.cos ((Real.exp y / z) * Real.sinh u) : ℝ) : ℂ) -
        ((Real.sin ((Real.exp y / z) * Real.sinh u) : ℝ) : ℂ) * I)).re =
          Real.sin ((Real.exp y / z) * Real.sinh u) ∧
      (I * (((Real.cos ((Real.exp y / z) * Real.sinh u) : ℝ) : ℂ) -
        ((Real.sin ((Real.exp y / z) * Real.sinh u) : ℝ) : ℂ) * I)).im =
          Real.cos ((Real.exp y / z) * Real.sinh u) := by
    constructor <;>
      simp only [mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im, sub_re,
        sub_im, zero_mul, one_mul, mul_zero, mul_one, zero_sub, sub_zero,
        add_zero, zero_add]
    ring
  rw [mul_re, hgre, hgim, hosc.1, hosc.2]
  rw [Real.cos_sub]
  ring

/- Paper: Remark 5.1 and (5.10a)/(5.10b) for p = 2.
   Plain recap: both sides are, up to the same positive prefactor, the order-two π/2- and
   π-formulae at `σ = 2`.  These have the same `1/x`-Laplace transform
   (`piHalfFormula_sigma_two_laplace`, `piFormula_sigma_two_laplace`: both contours ζ_{π/2} and
   ζ_π give the right-hand side of (5.3)), hence agree for a.e. `x > 0` (`prop_4_4`); both
   are continuous in `x > 0` by dominated convergence, hence agree for every `x > 0`. -/
/-- Paper (5.10a) cosine integral matches (5.10b) after the Gaussian `g_{t,2}` phase shift. -/
theorem piHalf_cos_integral_eq_pi_sin_integral
    (t : ℝ) (ht : 0 < t) (x y : ℝ) (hx : 0 < x) :
    Real.exp (π ^ 2 / (8 * t)) *
      ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * t)) * Real.cosh u *
        Real.cos ((Real.exp y / x) * Real.sinh u - π * u / (2 * t)) =
    Real.exp (π ^ 2 / (2 * t)) *
      ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * t)) *
        Real.exp (-(Real.exp y / x) * Real.cosh u) * Real.sinh u * Real.sin (π * u / t) := by
  -- Both sides as functions of the first argument `z > 0`.
  let F : ℝ → ℝ := fun z => Real.exp (π ^ 2 / (8 * t)) *
    ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * t)) * Real.cosh u *
      Real.cos ((Real.exp y / z) * Real.sinh u - π * u / (2 * t))
  let G : ℝ → ℝ := fun z => Real.exp (π ^ 2 / (2 * t)) *
    ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * t)) *
      Real.exp (-(Real.exp y / z) * Real.cosh u) * Real.sinh u * Real.sin (π * u / t)
  -- The common positive prefactor of the two formulae.
  let K : ℝ → ℝ := fun z => (2 ^ 2 : ℝ)⁻¹ * (2 ^ 4 * (16 / (z * 2 ^ 2) ^ 2) *
    Real.exp (y * 2 * (((2 : ℕ) : ℝ) - 1) / 2 + (y * 2) ^ 2 / (2 * (t * 2 ^ 2)) -
      2 * (Real.exp (y * 2) + 1) / (z * 2 ^ 2))) / (4 * π)
  have hK : ∀ z, 0 < z → K z ≠ 0 := fun z hz => by
    dsimp only [K]
    positivity
  have hφh : ∀ z, 0 < z →
      (2 ^ 2 : ℝ)⁻¹ * piHalfFormula 2 2 t (z * 2 ^ 2) (y * 2) = K z * F z := by
    intro z hz
    rw [piHalfFormula, ite_eq_left (by positivity),
      setIntegral_congr_fun measurableSet_Ioi
        (fun u _ => piHalf_two_integrand_eq t ht z y hz u), integral_const_mul]
    dsimp only [K, F]
    ring
  have hφπ : ∀ z, 0 < z →
      (2 ^ 2 : ℝ)⁻¹ * piFormula 2 2 t (z * 2 ^ 2) (y * 2) = K z * G z := by
    intro z hz
    have hpoint : ∀ u : ℝ,
        Real.sinh u *
            (((Real.exp (-(4 / (z * 2 ^ 2)) * Real.exp (y * 2 / 2) * Real.cosh u) : ℝ) : ℂ) *
              gFun 2 (t * 2 ^ 2) (u - I * π)).re =
          Real.exp (π ^ 2 / (2 * t)) / (4 * π) *
            (Real.exp (-u ^ 2 / (2 * t)) * Real.exp (-(Real.exp y / z) * Real.cosh u) *
              Real.sinh u * Real.sin (π * u / t)) := by
      intro u
      have he : -(4 / (z * 2 ^ 2)) * Real.exp (y * 2 / 2) * Real.cosh u =
          -(Real.exp y / z) * Real.cosh u := by
        rw [show y * 2 / 2 = y by ring]
        field_simp
        ring
      rw [re_ofReal_mul, gFun_two_re t ht u, he]
      ring
    rw [piFormula, ite_eq_left (by positivity),
      setIntegral_congr_fun measurableSet_Ioi (fun u _ => hpoint u), integral_const_mul]
    dsimp only [K, G]
    ring
  -- Equal `1/x`-Laplace transforms give almost-everywhere equality.
  have hae : ∀ᵐ z ∂volume.restrict (Ioi (0 : ℝ)), F z = G z := by
    have htn : 0 < Real.toNNReal t := by simpa using ht
    have hcoe : ((Real.toNNReal t : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht.le
    let φh : ℝ → ℝ := fun z => (2 ^ 2 : ℝ)⁻¹ * piHalfFormula 2 2 t (z * 2 ^ 2) (y * 2)
    let φπ : ℝ → ℝ := fun z => (2 ^ 2 : ℝ)⁻¹ * piFormula 2 2 t (z * 2 ^ 2) (y * 2)
    have hh0 := piHalfFormula_sigma_two_laplace (p := 2) (Or.inl rfl)
      (Real.toNNReal t) htn (v := 0) le_rfl y
    have hπ0 := piFormula_sigma_two_laplace (p := 2) (Or.inl rfl)
      (Real.toNNReal t) htn (v := 0) le_rfl y
    rw [hcoe] at hh0 hπ0
    have hhint : IntegrableOn φh (Ioi 0) := by
      simpa only [φh, neg_zero, zero_div, Real.exp_zero, one_mul] using hh0.1
    have hπint : IntegrableOn φπ (Ioi 0) := by
      simpa only [φπ, neg_zero, zero_div, Real.exp_zero, one_mul] using hπ0.1
    have h44 := prop_4_4 φh φπ hhint.aestronglyMeasurable hπint.aestronglyMeasurable
      hhint hπint (by
        intro v hv
        have hh := piHalfFormula_sigma_two_laplace (p := 2) (Or.inl rfl)
          (Real.toNNReal t) htn hv y
        have hπ := piFormula_sigma_two_laplace (p := 2) (Or.inl rfl)
          (Real.toNNReal t) htn hv y
        rw [hcoe] at hh hπ
        simpa only [laplaceCond, φh, φπ, mul_assoc] using hh.2.trans hπ.2.symm)
    filter_upwards [h44, ae_restrict_mem measurableSet_Ioi] with z hz hzpos
    have hz0 : 0 < z := hzpos
    have hz' : (2 ^ 2 : ℝ)⁻¹ * piHalfFormula 2 2 t (z * 2 ^ 2) (y * 2) =
        (2 ^ 2 : ℝ)⁻¹ * piFormula 2 2 t (z * 2 ^ 2) (y * 2) := hz
    rw [hφh z hz0, hφπ z hz0] at hz'
    exact mul_left_cancel₀ (hK z hz0) hz'
  -- Both sides are continuous on `(0, ∞)` by dominated convergence.
  have henv := (integrable_gauss_mul_cosh ht).integrableOn (s := Ioi (0 : ℝ))
  have hdiv : ContinuousOn (fun z : ℝ => Real.exp y / z) (Ioi 0) :=
    continuousOn_const.div continuousOn_id fun z hz => (mem_Ioi.1 hz).ne'
  have hFc : ContinuousOn F (Ioi 0) := by
    refine continuousOn_const.mul ?_
    refine continuousOn_of_dominated
      (bound := fun u => Real.exp (-u ^ 2 / (2 * t)) * Real.cosh u) ?_ ?_ henv ?_
    · intro z _
      exact Continuous.aestronglyMeasurable (by fun_prop)
    · intro z _
      refine Eventually.of_forall fun u => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
    · refine Eventually.of_forall fun u => ?_
      exact continuousOn_const.mul (Real.continuous_cos.comp_continuousOn
        ((hdiv.mul continuousOn_const).sub continuousOn_const))
  have hGc : ContinuousOn G (Ioi 0) := by
    refine continuousOn_const.mul ?_
    refine continuousOn_of_dominated
      (bound := fun u => Real.exp (-u ^ 2 / (2 * t)) * Real.cosh u) ?_ ?_ henv ?_
    · intro z _
      exact Continuous.aestronglyMeasurable (by fun_prop)
    · intro z hz
      have hz0 : 0 < z := hz
      refine Eventually.of_forall fun u => ?_
      have hE : 0 ≤ Real.exp (-u ^ 2 / (2 * t)) := (Real.exp_pos _).le
      have h1 : Real.exp (-(Real.exp y / z) * Real.cosh u) ≤ 1 := by
        have h0 : 0 ≤ Real.exp y / z * Real.cosh u := by
          have := Real.cosh_pos u
          positivity
        exact Real.exp_le_one_iff.2 (by linarith)
      have h2 : |Real.sinh u| ≤ Real.cosh u := by
        rw [Real.abs_sinh, ← Real.cosh_abs u]
        exact (Real.sinh_lt_cosh _).le
      have h3 : |Real.sin (π * u / t)| ≤ 1 := Real.abs_sin_le_one _
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hE,
        abs_of_nonneg (Real.exp_pos _).le]
      calc Real.exp (-u ^ 2 / (2 * t)) * Real.exp (-(Real.exp y / z) * Real.cosh u) *
            |Real.sinh u| * |Real.sin (π * u / t)|
          ≤ Real.exp (-u ^ 2 / (2 * t)) * 1 * Real.cosh u * 1 := by gcongr
        _ = Real.exp (-u ^ 2 / (2 * t)) * Real.cosh u := by ring
    · refine Eventually.of_forall fun u => ?_
      exact ((continuousOn_const.mul (Real.continuous_exp.comp_continuousOn
        (hdiv.neg.mul continuousOn_const))).mul continuousOn_const).mul continuousOn_const
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae isOpen_Ioi hFc hGc (mem_Ioi.2 hx)

/-- Algebraic core of the order-two π/2-formula at `σ = 2` (paper (5.10a)). -/
lemma remark_5_1_half_aux (t : ℝ≥0) (x y : ℝ) (ht : 0 < t) :
    gaussianPDFReal 0 t y * (2 ^ 2 : ℝ)⁻¹ * piHalfFormula 2 2 t (x * 2 ^ 2) (y * 2) =
      yorDensity t x y := by
  have ht' : (0 : ℝ) < t := ht
  rw [piHalfFormula]
  split_ifs with hxscaled
  rotate_left
  · have hx : x ≤ 0 := by nlinarith
    simpa using (yorDensity_zero_of_nonpos ht' hx y).symm
  have hx : 0 < x := by nlinarith
  unfold yorDensity theta
  rw [gaussianPDFReal_def]
  have hphase : ∀ u : ℝ,
      cexp (-I * (((Real.exp y / x) * Real.sinh u : ℝ) : ℂ)) =
        ((Real.cos ((Real.exp y / x) * Real.sinh u) : ℝ) : ℂ) -
          ((Real.sin ((Real.exp y / x) * Real.sinh u) : ℝ) : ℂ) * I := by
    intro u
    have harg :
        -I * (((Real.exp y / x) * Real.sinh u : ℝ) : ℂ) =
          (((-((Real.exp y / x) * Real.sinh u) : ℝ) : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [harg, Complex.exp_mul_I]
    apply Complex.ext
    · simp
    · simp; ring
  have hint :
      ∫ u in Ioi (0 : ℝ), Real.cosh u *
          (I * cexp (-I * (((4 / ((x * 2 ^ 2 : ℝ) : ℂ)) *
            Real.exp (y * 2 / 2) * Real.sinh u))) *
            gFun 2 ((t : ℝ) * 2 ^ 2) (u - I * (π / 2))).re =
        Real.exp (π ^ 2 / (2 * t)) / (4 * π) *
          ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * t)) *
            Real.exp (-(Real.exp y / x) * Real.cosh u) *
            Real.sinh u * Real.sin (π * u / t) := by
    have hcos := piHalf_cos_integral_eq_pi_sin_integral (t : ℝ) ht' x y hx
    have hpoint :
        ∀ u : ℝ,
          Real.cosh u *
              (I * cexp (-I * (((4 / ((x * 2 ^ 2 : ℝ) : ℂ)) *
                Real.exp (y * 2 / 2) * Real.sinh u))) *
                gFun 2 ((t : ℝ) * 2 ^ 2) (u - I * (π / 2))).re =
            Real.exp (π ^ 2 / (8 * t)) / (4 * π) *
              (Real.exp (-u ^ 2 / (2 * t)) * Real.cosh u *
                Real.cos ((Real.exp y / x) * Real.sinh u - π * u / (2 * t))) := by
      intro u
      rw [show
        (4 / ((x * 2 ^ 2 : ℝ) : ℂ)) * Real.exp (y * 2 / 2) * Real.sinh u =
            (((Real.exp y / x) * Real.sinh u : ℝ) : ℂ) by
          rw [show y * 2 / 2 = y by ring]
          push_cast
          field_simp [hx.ne']
          ring, hphase u]
      obtain ⟨hgre, hgim⟩ := gFun_two_re_half (t : ℝ) ht' u
      have hosc :
          (I * (((Real.cos ((Real.exp y / x) * Real.sinh u) : ℝ) : ℂ) -
            ((Real.sin ((Real.exp y / x) * Real.sinh u) : ℝ) : ℂ) * I)).re =
              Real.sin ((Real.exp y / x) * Real.sinh u) ∧
          (I * (((Real.cos ((Real.exp y / x) * Real.sinh u) : ℝ) : ℂ) -
            ((Real.sin ((Real.exp y / x) * Real.sinh u) : ℝ) : ℂ) * I)).im =
              Real.cos ((Real.exp y / x) * Real.sinh u) := by
        constructor
        · simp only [mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im, sub_re,
            sub_im, zero_mul, one_mul, mul_zero, mul_one, zero_sub, sub_zero,
            add_zero]; ring
        · simp only [mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im, sub_re,
            sub_im, zero_mul, one_mul, mul_zero, mul_one, zero_sub, sub_zero,
            add_zero]; ring
      rw [mul_re, hgre, hgim, hosc.1, hosc.2]
      rw [Real.cos_sub]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hpoint u),
      integral_const_mul]
    calc
      Real.exp (π ^ 2 / (8 * t)) / (4 * π) *
          (∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * t)) * Real.cosh u *
            Real.cos ((Real.exp y / x) * Real.sinh u - π * u / (2 * t))) =
        (4 * π)⁻¹ * (Real.exp (π ^ 2 / (8 * t)) *
          ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * t)) * Real.cosh u *
            Real.cos ((Real.exp y / x) * Real.sinh u - π * u / (2 * t))) := by ring
      _ =
        (4 * π)⁻¹ * (Real.exp (π ^ 2 / (2 * t)) *
          ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * t)) *
            Real.exp (-(Real.exp y / x) * Real.cosh u) *
            Real.sinh u * Real.sin (π * u / t)) := by rw [hcos]
      _ = _ := by ring
  rw [hint]
  have hs : √(2 * π ^ 3 * t) = π * √(2 * π * t) := by
    rw [show 2 * π ^ 3 * (t : ℝ) = π ^ 2 * (2 * π * t) by ring,
      Real.sqrt_mul (sq_nonneg π), Real.sqrt_sq Real.pi_pos.le]
  have hexp : Real.exp (-(y - 0) ^ 2 / (2 * t)) *
      Real.exp (y * 2 * (((2 : ℕ) : ℝ) - 1) / 2 +
        (y * 2) ^ 2 / (2 * ((t : ℝ) * 2 ^ 2)) -
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
          Real.exp (y * 2 * (((2 : ℕ) : ℝ) - 1) / 2 +
            (y * 2) ^ 2 / (2 * ((t : ℝ) * 2 ^ 2)) -
            2 * (Real.exp (y * 2) + 1) / (x * 2 ^ 2)) *
          (Real.exp (π ^ 2 / (2 * t)) / (4 * π) *
            ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * t)) *
              Real.exp (-(Real.exp y / x) * Real.cosh u) *
              Real.sinh u * Real.sin (π * u / t)))
      = (Real.exp (-(y - 0) ^ 2 / (2 * t)) *
          Real.exp (y * 2 * (((2 : ℕ) : ℝ) - 1) / 2 +
            (y * 2) ^ 2 / (2 * ((t : ℝ) * 2 ^ 2)) -
            2 * (Real.exp (y * 2) + 1) / (x * 2 ^ 2))) *
          ((√(2 * π * t))⁻¹ * (2 ^ 2 : ℝ)⁻¹ *
            (2 ^ 4 * (16 / (x * 2 ^ 2) ^ 2)) *
            (Real.exp (π ^ 2 / (2 * t)) / (4 * π) *
              ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * t)) *
                Real.exp (-(Real.exp y / x) * Real.cosh u) *
                Real.sinh u * Real.sin (π * u / t))) := by ring
    _ = _ := by
      rw [hexp]
      field_simp
      ring

theorem piHalf_eq_piFormula_two_sigma_two
    (t : ℝ≥0) (x y : ℝ) (ht : 0 < t) :
    piHalfFormula 2 2 t (x * 2 ^ 2) (y * 2) =
      piFormula 2 2 t (x * 2 ^ 2) (y * 2) := by
  have hyor := remark_5_1_half_aux t x y ht
  have hpi := remark_5_1_aux t x y ht
  have hG : gaussianPDFReal 0 t y ≠ 0 := by
    rw [gaussianPDFReal_def]; positivity
  have hσ : (2 ^ 2 : ℝ)⁻¹ ≠ 0 := by norm_num
  have heq := hyor.trans hpi.symm
  exact mul_left_cancel₀ (mul_ne_zero hG hσ) heq

lemma piHalfFormula_sigma_covariant_fixed
    (p : ℕ) (σ : ℝ) (T : ℝ≥0) (x y : ℝ) (hσ : 0 < σ) :
    piHalfFormula p σ T (x * σ ^ 2) (y * σ) =
      (σ / 2) ^ 4 *
        piHalfFormula p 2 (referenceTimeFromTwo σ T) (x * σ ^ 2) (y * σ) := by
  have hτ :
      (referenceTimeFromTwo σ T : ℝ) * (2 : ℝ) ^ 2 = (T : ℝ) * σ ^ 2 := by
    rw [referenceTimeFromTwo, Real.coe_toNNReal]
    · ring
    · positivity
  unfold piHalfFormula
  rw [hτ]
  split_ifs <;> ring

/-- `remark_5_1` comparison at arguments `(xσ², yσ)` after reparametrisation. -/
theorem piHalf_eq_piFormula_ref_coords
    (τ : ℝ≥0) (σ x y : ℝ) (hτ : 0 < τ) (_hσ : 0 < σ) :
    piHalfFormula 2 2 τ (x * σ ^ 2) (y * σ) =
      piFormula 2 2 τ (x * σ ^ 2) (y * σ) := by
  have h := piHalf_eq_piFormula_two_sigma_two τ (σ ^ 2 / 4 * x) (σ / 2 * y) hτ
  convert h using 2 <;> ring_nf

theorem piHalf_eq_piFormula_two_general
    (σ : ℝ) (T : ℝ≥0) (x y : ℝ) (hσ : 0 < σ) (hT : 0 < T) :
    piHalfFormula 2 σ T (x * σ ^ 2) (y * σ) =
      piFormula 2 σ T (x * σ ^ 2) (y * σ) := by
  let τ := referenceTimeFromTwo σ T
  have hτ : 0 < τ := referenceTimeFromTwo_pos hσ hT
  calc piHalfFormula 2 σ T (x * σ ^ 2) (y * σ) =
        (σ / 2) ^ 4 * piHalfFormula 2 2 τ (x * σ ^ 2) (y * σ) :=
      piHalfFormula_sigma_covariant_fixed 2 σ T x y hσ
    _ = (σ / 2) ^ 4 * piFormula 2 2 τ (x * σ ^ 2) (y * σ) := by
        congr 1
        exact piHalf_eq_piFormula_ref_coords τ σ x y hτ hσ
    _ = piFormula 2 σ T (x * σ ^ 2) (y * σ) := by
        simpa using (piFormula_sigma_covariant_fixed 2 σ T x y hσ).symm

theorem scaled_piHalf_joint_eq_scaled_pi_joint
    (σ : ℝ) (T : ℝ≥0) (x y : ℝ) (hσ : 0 < σ) (hT : 0 < T) :
    gaussianPDFReal 0 T y * (σ ^ 2)⁻¹ * piHalfFormula 2 σ T (x * σ ^ 2) (y * σ) =
      gaussianPDFReal 0 T y * (σ ^ 2)⁻¹ * piFormula 2 σ T (x * σ ^ 2) (y * σ) := by
  congr 1
  exact piHalf_eq_piFormula_two_general σ T x y hσ hT

theorem pi_half_formula_two_sigma_two
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W)
    (t : ℝ≥0) (ht : 0 < t) :
    IsJointDensity P W 2 0 t (fun x y =>
      gaussianPDFReal 0 t y * (2 ^ 2 : ℝ)⁻¹ * piHalfFormula 2 2 t (x * 2 ^ 2) (y * 2)) := by
  have h := yor_joint_density P W hW t ht
  have hfun : (fun x y : ℝ =>
      gaussianPDFReal 0 t y * ((2 : ℝ) ^ 2)⁻¹ *
        piHalfFormula 2 2 t (x * (2 : ℝ) ^ 2) (y * 2)) =
      fun x y => yorDensity t x y := by
    funext x y
    exact remark_5_1_half_aux t x y ht
  rwa [← hfun] at h

theorem pi_half_formula_two_general
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W)
    (σ : ℝ) (T : ℝ≥0) (hσ : 0 < σ) (hT : 0 < T) :
    IsJointDensity P W σ 0 T (fun x y =>
      gaussianPDFReal 0 T y * (σ ^ 2)⁻¹ *
        piHalfFormula 2 σ T (x * σ ^ 2) (y * σ)) := by
  let τ := referenceTimeFromTwo σ T
  have hτ : 0 < τ := referenceTimeFromTwo_pos hσ hT
  let φ₂ : ℝ → ℝ → ℝ := fun x y =>
    gaussianPDFReal 0 τ y * ((2 : ℝ) ^ 2)⁻¹ *
      piHalfFormula 2 2 τ (x * (2 : ℝ) ^ 2) (y * 2)
  have hφ₂ : IsJointDensity P W 2 0 τ φ₂ :=
    pi_half_formula_two_sigma_two P W hW τ hτ
  have hφeq : φ₂ = fun x y => yorDensity τ x y := by
    funext x y
    exact remark_5_1_half_aux τ x y hτ
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
          piHalfFormula 2 σ T (x * σ ^ 2) (y * σ)) := by
    funext x y
    dsimp [φ₂]
    rw [gaussianPDFReal_referenceTimeFromTwo hσ T y,
      piHalfFormula_sigma_covariant_fixed 2 σ T x y hσ]
    simp only [τ]
    field_simp [hσ.ne']
    ring_nf
  rwa [hfun] at hs

end Lyasoff2016