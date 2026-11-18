/-
Constructive identification of the π/2-formulae with the joint density.
Mirrors `PiFormulaHigher` at aperture `a = π/2` (paper (5.9a)/(5.10a)).
-/
module

public import Lyasoff2016.ContourEq
public import Lyasoff2016.Foliation
public import Lyasoff2016.InverseGammaIntegral
public import Lyasoff2016.PiFormulaHigher
public import Lyasoff2016.PiHalfFormula
public import Lyasoff2016.PiFormulaScaling
public import Lyasoff2016.GFunDecay


@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/-! The π/2 edge integrand after the paper's trig reduction (vision OCR p.24):
`ℜ(-i cosh u · g(u-iπ/2) / (-i sinh u - cosh y)^{p-1})`. -/

private def piHalfContourReal (p : ℕ) (T A u : ℝ) : ℝ :=
  (Complex.cosh u : ℂ).re *
    ((-I * gFun p T (u - I * (π / 2)) /
      ((-I * Complex.sinh u - (A : ℂ)) ^ (p - 1))).re)

private lemma piHalfContourReal_eq_contourIntegrand
    (p : ℕ) (T A u : ℝ) (hA : 1 ≤ A) :
    (contourIntegrand p T (π / 2) (Real.arcosh A) u).re =
      piHalfContourReal p T A u := by
  have hcosh :
      Complex.cosh ((u : ℂ) - I * ((π : ℂ) / 2)) = -I * Real.sinh u := by
    have harg : I * ((π : ℂ) / 2) = ((π : ℂ) / 2) * I := by ring
    rw [harg, Complex.cosh_sub, Complex.cosh_mul_I, Complex.sinh_mul_I]
    simp
    ring
  have hsinh :
      Complex.sinh ((u : ℂ) - I * ((π : ℂ) / 2)) = -I * Real.cosh u := by
    have harg : I * ((π : ℂ) / 2) = ((π : ℂ) / 2) * I := by ring
    rw [harg, Complex.sinh_sub, Complex.cosh_mul_I, Complex.sinh_mul_I]
    simp
    ring
  have harc : Complex.cosh (Real.arcosh A : ℂ) = (A : ℂ) := by
    apply Complex.ext
    · rw [Complex.cosh_ofReal_re, Real.cosh_arcosh hA]
      simp
    · simp [Complex.cosh_ofReal_im]
  unfold contourIntegrand piHalfContourReal
  push_cast at hcosh hsinh ⊢
  rw [hcosh, hsinh, harc]
  simp only [Complex.cosh_ofReal_re]
  simp only [div_eq_mul_inv]
  rw [mul_re]
  simp
  ring

private lemma piHalfContourReal_even
    (p : ℕ) (hp : p = 2 ∨ p = 3 ∨ p = 4) (T A : ℝ) :
    Function.Even (piHalfContourReal p T A) := by
  intro u
  have hz : (((-u : ℝ) : ℂ) - I * (π / 2)) =
      -(starRingEnd ℂ ((u : ℂ) - I * (π / 2))) := by
    push_cast
    simp only [map_sub, conj_ofReal, map_mul, conj_I, neg_mul, map_div₀,
      map_ofNat]
    ring
  have hg : gFun p T (((-u : ℝ) : ℂ) - I * (π / 2)) =
      -starRingEnd ℂ (gFun p T ((u : ℂ) - I * (π / 2))) := by
    rw [hz, gFun.even, gFun.conj p hp]
  have hsreal :
      starRingEnd ℂ (Complex.sinh (u : ℂ)) = Complex.sinh (u : ℂ) := by
    rw [← Complex.sinh_conj]
    simp
  have hg' : gFun p T (-(u : ℂ) - I * (π / 2)) =
      -starRingEnd ℂ (gFun p T ((u : ℂ) - I * (π / 2))) := by
    simpa only [ofReal_neg] using hg
  have hq :
      -I * gFun p T (((-u : ℝ) : ℂ) - I * (π / 2)) /
          (-I * Complex.sinh ((-u : ℝ) : ℂ) - (A : ℂ)) ^ (p - 1) =
        starRingEnd ℂ
          (-I * gFun p T ((u : ℂ) - I * (π / 2)) /
            (-I * Complex.sinh u - (A : ℂ)) ^ (p - 1)) := by
    simp only [ofReal_neg, Complex.sinh_neg]
    rw [hg']
    simp only [map_div₀, map_mul, map_pow, map_sub, map_neg, conj_I, conj_ofReal,
      ]
    rw [hsreal]
    ring
  unfold piHalfContourReal
  rw [Complex.cosh_ofReal_re, Complex.cosh_ofReal_re, Real.cosh_neg, hq, conj_re]

private lemma piHalfContourReal_integrable
    {p : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 4)
    {T : ℝ} (hT : 0 < T) {A : ℝ} (hA : 1 ≤ A) :
    Integrable (piHalfContourReal p T A) := by
  have hc := g_solves_contour_equation p hp T hT (Real.arcosh A) (π / 2)
    (by constructor <;> linarith [Real.pi_pos])
  exact hc.1.re.congr (ae_of_all _ fun u =>
    piHalfContourReal_eq_contourIntegrand p T A u hA)

private lemma piHalfContourReal_integral
    {p : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 4)
    {T : ℝ} (hT : 0 < T) {A : ℝ} (hA : 1 ≤ A) :
    ∫ u in Ioi (0 : ℝ), piHalfContourReal p T A u =
      (-4 : ℝ) ^ (p - 2) / (((p - 2).factorial : ℝ) * 4) *
        Real.exp (-2 * Real.arcosh A ^ 2 / T) := by
  have hc := g_solves_contour_equation p hp T hT (Real.arcosh A) (π / 2)
    (by constructor <;> linarith [Real.pi_pos])
  have heven := piHalfContourReal_even p hp T A
  have habs :
      (fun u : ℝ => piHalfContourReal p T A |u|) =
        piHalfContourReal p T A := by
    funext u
    rcases le_total 0 u with hu | hu
    · rw [abs_of_nonneg hu]
    · rw [abs_of_nonpos hu, heven u]
  have hfull :
      ∫ u : ℝ, piHalfContourReal p T A u =
        2 * ∫ u in Ioi (0 : ℝ), piHalfContourReal p T A u := by
    rw [← habs, integral_comp_abs, habs]
  have hcontour :
      ∫ u : ℝ, (contourIntegrand p T (π / 2) (Real.arcosh A) u).re =
        ∫ u : ℝ, piHalfContourReal p T A u :=
    integral_congr_ae (ae_of_all _ fun u =>
      piHalfContourReal_eq_contourIntegrand p T A u hA)
  rcases hc with ⟨_, hc⟩
  rw [hcontour, hfull] at hc
  rcases hp with rfl | rfl | rfl <;>
    norm_num [Nat.factorial] at hc ⊢ <;> linarith

/-! ### Fubini kernel for the `1/x`-Laplace transform of the π/2-formula -/

private lemma charA_one_le' {v y : ℝ} (hv : 0 ≤ v) :
    1 ≤ charA v y := by
  unfold charA
  exact (Real.one_le_cosh y).trans
    (le_add_of_nonneg_right (mul_nonneg hv (Real.exp_pos _).le))

/-- Complex inverse-Gamma scale `v + e^y (cosh y + i sinh u)`: its real part is positive and
its imaginary part carries the oscillation of the π/2-kernel. -/
private def piHalfScale (v y u : ℝ) : ℂ :=
  ((v + Real.exp y * Real.cosh y : ℝ) : ℂ) + I * ((Real.exp y * Real.sinh u : ℝ) : ℂ)

private lemma piHalfScale_re (v y u : ℝ) :
    (piHalfScale v y u).re = v + Real.exp y * Real.cosh y := by
  simp only [piHalfScale, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]

private lemma piHalfScale_re_pos {v y : ℝ} (hv : 0 ≤ v) (u : ℝ) :
    0 < (piHalfScale v y u).re := by
  rw [piHalfScale_re]
  have := Real.cosh_pos y
  positivity

private lemma piHalfScale_eq (v y u : ℝ) :
    piHalfScale v y u =
      ((Real.exp y : ℝ) : ℂ) * (((charA v y : ℝ) : ℂ) + I * ((Real.sinh u : ℝ) : ℂ)) := by
  unfold piHalfScale charA
  have he : cexp (y : ℂ) * cexp (-(y : ℂ)) = 1 := by
    rw [← Complex.exp_add]; simp
  push_cast
  linear_combination (-(v : ℂ)) * he

/-- The complex Fubini kernel: `cosh u · i g(u − iπ/2) · x⁻ᵖ exp(−(v + e^y(cosh y + i sinh u))/x)`.
The oscillatory factor `exp(−i e^y sinh u / x)` has modulus one. -/
private def piHalfKernelC (p : ℕ) (T v y x u : ℝ) : ℂ :=
  ((Real.cosh u : ℝ) : ℂ) * (I * gFun p T (u - I * (π / 2))) *
    ((1 : ℂ) / (x : ℂ) ^ p * cexp (-(piHalfScale v y u) / x))

private lemma piHalfKernelC_norm (p : ℕ) (T v y : ℝ) {x : ℝ} (hx : 0 < x) (u : ℝ) :
    ‖piHalfKernelC p T v y x u‖ =
      (Real.cosh u * ‖gFun p T (u - I * (π / 2))‖) *
        (Real.exp (-v / x) *
          (1 / x ^ p * Real.exp (-(Real.exp y * Real.cosh y) / x))) := by
  unfold piHalfKernelC
  have hre : (-(piHalfScale v y u) / (x : ℂ)).re =
      -v / x + -(Real.exp y * Real.cosh y) / x := by
    rw [Complex.div_ofReal_re, Complex.neg_re, piHalfScale_re]
    ring
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.cosh_pos u), Complex.norm_I, one_mul, Complex.norm_exp, hre, Real.exp_add,
    norm_div, norm_one, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
  ring

private lemma piHalfKernelC_inner_integrable
    {p : ℕ} (hp : 2 ≤ p) {T v y : ℝ} (hv : 0 ≤ v) (u : ℝ) :
    IntegrableOn (fun x => piHalfKernelC p T v y x u) (Ioi 0) := by
  unfold piHalfKernelC
  exact (integrableOn_inv_pow_cexp_neg_div hp (piHalfScale_re_pos hv u)).const_mul _

private lemma piHalfKernelC_inner_integral
    {p : ℕ} (hp : 2 ≤ p) {T v y : ℝ} (hv : 0 ≤ v) (u : ℝ) :
    ∫ x in Ioi (0 : ℝ), piHalfKernelC p T v y x u =
      ((Real.cosh u : ℝ) : ℂ) * (I * gFun p T (u - I * (π / 2))) *
        (((p - 2).factorial : ℂ) / (piHalfScale v y u) ^ (p - 1)) := by
  unfold piHalfKernelC
  rw [integral_const_mul, integral_inv_pow_cexp_neg_div hp (piHalfScale_re_pos hv u)]

private lemma piHalfKernelC_inner_norm_integral
    {p : ℕ} (hp : 2 ≤ p) {T v y : ℝ} (hv : 0 ≤ v) (u : ℝ) :
    ∫ x in Ioi (0 : ℝ), ‖piHalfKernelC p T v y x u‖ =
      (Real.cosh u * ‖gFun p T (u - I * (π / 2))‖) *
        (((p - 2).factorial : ℝ) / (v + Real.exp y * Real.cosh y) ^ (p - 1)) := by
  have hpos : 0 < v + Real.exp y * Real.cosh y := by
    have := Real.cosh_pos y
    positivity
  rw [setIntegral_congr_fun measurableSet_Ioi
      (fun x hx => piHalfKernelC_norm p T v y hx u), integral_const_mul,
    integral_exp_neg_div_mul_one_div_pow_exp_neg_div hp hpos]

/-- Absolute Fubini for the π/2-kernel: the modulus integrates in `x` to an inverse-Gamma
constant times `cosh u · |g(u − iπ/2)|`, which is integrable by the Gaussian decay of
`g_{t,p}` on horizontal lines (`GFunDecay`). -/
private lemma piHalfKernelC_integrable
    {p : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 4)
    {T : ℝ} (hT : 0 < T) {v : ℝ} (hv : 0 ≤ v) (y : ℝ) :
    Integrable (Function.uncurry (piHalfKernelC p T v y))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hp2 : 2 ≤ p := by omega
  have hsm : StronglyMeasurable (Function.uncurry (piHalfKernelC p T v y)) := by
    have hg : Continuous (gFun p T) := (gFun.contDiff p T).continuous
    apply Measurable.stronglyMeasurable
    unfold piHalfKernelC piHalfScale Function.uncurry
    fun_prop
  rw [integrable_prod_iff' hsm.aestronglyMeasurable]
  refine ⟨ae_of_all _ fun u => piHalfKernelC_inner_integrable hp2 hv u, ?_⟩
  have hnorm :
      (fun u => ∫ x in Ioi (0 : ℝ), ‖piHalfKernelC p T v y x u‖) =
        fun u => (((p - 2).factorial : ℝ) / (v + Real.exp y * Real.cosh y) ^ (p - 1)) *
          (Real.cosh u * ‖gFun p T (u - I * (π / 2))‖) := by
    funext u
    rw [piHalfKernelC_inner_norm_integral hp2 hv, mul_comm]
  change Integrable (fun u => ∫ x in Ioi (0 : ℝ),
    ‖piHalfKernelC p T v y x u‖) (volume.restrict (Ioi 0))
  rw [hnorm]
  exact ((GFunDecay.integrable_cosh_mul_norm_gFun_piHalf hp hT).integrableOn).const_mul _

private lemma piHalfFormula_scaled_eq_kernel
    {p : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 4)
    {t : ℝ} (ht : 0 < t) {v : ℝ} (x y : ℝ) (hx : 0 < x) :
    Real.exp (-v / x) * (2 ^ 2 : ℝ)⁻¹ *
        piHalfFormula p 2 t (x * 2 ^ 2) (y * 2) =
      (4 : ℝ) ^ ((3 : ℤ) - (p : ℤ)) *
        Real.exp (y * ((p : ℝ) - 1) + y ^ 2 / (2 * t)) *
          ∫ u in Ioi (0 : ℝ), (piHalfKernelC p (t * 4) v y x u).re := by
  have hy : y * 2 / 2 = y := by ring
  have hT : t * 2 ^ 2 = t * 4 := by norm_num
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hpoint : ∀ u : ℝ, (piHalfKernelC p (t * 4) v y x u).re =
      (Real.exp (-v / x) *
        (1 / x ^ p * Real.exp (-(Real.exp y * Real.cosh y) / x))) *
        (Real.cosh u *
          (I * cexp (-I * ((4 / ((x * 2 ^ 2 : ℝ) : ℂ)) *
            Real.exp (y * 2 / 2) * Real.sinh u)) *
              gFun p (t * 2 ^ 2) (u - I * (π / 2))).re) := by
    intro u
    have hexp : cexp (-(piHalfScale v y u) / x) =
        ((Real.exp (-v / x) * Real.exp (-(Real.exp y * Real.cosh y) / x) : ℝ) : ℂ) *
          cexp (-I * ((4 / ((x * 2 ^ 2 : ℝ) : ℂ)) *
            Real.exp (y * 2 / 2) * Real.sinh u)) := by
      rw [hy]
      push_cast
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      unfold piHalfScale
      push_cast
      field_simp
      ring
    have hK : piHalfKernelC p (t * 4) v y x u =
        ((Real.exp (-v / x) *
          (1 / x ^ p * Real.exp (-(Real.exp y * Real.cosh y) / x)) * Real.cosh u : ℝ) : ℂ) *
          (I * cexp (-I * ((4 / ((x * 2 ^ 2 : ℝ) : ℂ)) *
            Real.exp (y * 2 / 2) * Real.sinh u)) *
              gFun p (t * 2 ^ 2) (u - I * (π / 2))) := by
      unfold piHalfKernelC
      rw [hexp, hT]
      push_cast
      ring
    rw [hK, Complex.re_ofReal_mul]
    ring
  have hinner :
      ∫ u in Ioi (0 : ℝ), (piHalfKernelC p (t * 4) v y x u).re =
        (Real.exp (-v / x) *
          (1 / x ^ p * Real.exp (-(Real.exp y * Real.cosh y) / x))) *
        ∫ u in Ioi (0 : ℝ), Real.cosh u *
          (I * cexp (-I * ((4 / ((x * 2 ^ 2 : ℝ) : ℂ)) *
            Real.exp (y * 2 / 2) * Real.sinh u)) *
              gFun p (t * 2 ^ 2) (u - I * (π / 2))).re := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun u _ => hpoint u
  rw [hinner, piHalfFormula, ite_eq_left (by positivity : 0 < x * 2 ^ 2)]
  generalize (∫ u in Ioi (0 : ℝ), Real.cosh u *
    (I * cexp (-I * ((4 / ((x * 2 ^ 2 : ℝ) : ℂ)) *
      Real.exp (y * 2 / 2) * Real.sinh u)) *
        gFun p (t * 2 ^ 2) (u - I * (π / 2))).re) = J
  have ht0 : (t : ℝ) ≠ 0 := ht.ne'
  have he : Real.exp y * Real.exp (-y) = 1 := by
    rw [← Real.exp_add]
    simp
  have hcosh : Real.exp (y * 2) + 1 =
      2 * Real.exp y * Real.cosh y := by
    rw [Real.cosh_eq]
    calc
      Real.exp (y * 2) + 1 =
          Real.exp y * Real.exp y + Real.exp y * Real.exp (-y) := by
        rw [he, ← Real.exp_add]
        congr 2
        ring
      _ = _ := by ring
  have hexp :
      Real.exp ((y * 2) * (((p : ℕ) : ℝ) - 1) / 2 +
          (y * 2) ^ 2 / (2 * (t * 4)) -
          2 * (Real.exp (y * 2) + 1) / (x * 4)) =
        Real.exp (y * (((p : ℕ) : ℝ) - 1) + y ^ 2 / (2 * t)) *
          Real.exp (-(Real.exp y * Real.cosh y) / x) := by
    rw [← Real.exp_add]
    congr 1
    rw [hcosh]
    field_simp [hx.ne', ht0]
    ring
  norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num]
  rw [hexp]
  rcases hp with rfl | rfl | rfl <;>
    norm_num [Nat.factorial] <;>
    field_simp [hx.ne', ht0] <;> ring

/-- Paper: both π and π/2 contours yield the same RHS of (5.3), hence after
inverse-Gamma both Laplaces match (pp. 1083–1086).  The exchange of the two integrations is
justified by the Gaussian decay of `g_{t,p}` on the line `ℑ z = −π/2` (`GFunDecay`); the
`x`-integral is the complex inverse-Gamma integral with scale
`v + e^y (cosh y + i sinh u)`, and the remaining `u`-integral is the contour equation (5.3)
at `a = π/2`. -/
theorem piHalfFormula_sigma_two_laplace
    {p : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 4)
    (t : ℝ≥0) (ht : 0 < t) {v : ℝ} (hv : 0 ≤ v) (y : ℝ) :
    IntegrableOn
      (fun x => Real.exp (-v / x) *
        (2 ^ 2 : ℝ)⁻¹ * piHalfFormula p 2 t (x * 2 ^ 2) (y * 2))
      (Ioi 0) ∧
    ∫ x in Ioi (0 : ℝ), Real.exp (-v / x) *
        (2 ^ 2 : ℝ)⁻¹ * piHalfFormula p 2 t (x * 2 ^ 2) (y * 2) =
      (gaussianPDFReal 0 t y)⁻¹ *
        gaussianPDFReal 0 t (Real.arcosh (charA v y)) := by
  have htR : (0 : ℝ) < t := ht
  have hp2 : 2 ≤ p := by omega
  have hT : (0 : ℝ) < (t : ℝ) * 4 := by positivity
  have hkC := piHalfKernelC_integrable hp hT hv y
  have hk : Integrable
      (Function.uncurry fun x u => (piHalfKernelC p ((t : ℝ) * 4) v y x u).re)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := hkC.re
  have hsections :
      IntegrableOn (fun x => ∫ u in Ioi (0 : ℝ),
        (piHalfKernelC p ((t : ℝ) * 4) v y x u).re) (Ioi 0) :=
    hk.integral_prod_left
  let C : ℝ := (4 : ℝ) ^ ((3 : ℤ) - (p : ℤ)) *
    Real.exp (y * ((p : ℝ) - 1) + y ^ 2 / (2 * (t : ℝ)))
  have hpoint : ∀ x ∈ Ioi (0 : ℝ),
      Real.exp (-v / x) * (2 ^ 2 : ℝ)⁻¹ *
          piHalfFormula p 2 t (x * 2 ^ 2) (y * 2) =
        C * ∫ u in Ioi (0 : ℝ), (piHalfKernelC p ((t : ℝ) * 4) v y x u).re := by
    intro x hx
    exact piHalfFormula_scaled_eq_kernel hp htR (v := v) x y hx
  have hA := charA_one_le' (v := v) (y := y) hv
  constructor
  · refine (hsections.const_mul C).congr ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => (hpoint x hx).symm
  · rw [setIntegral_congr_fun measurableSet_Ioi hpoint, integral_const_mul]
    rw [integral_integral_swap hk]
    have hinner :
        (fun u => ∫ x in Ioi (0 : ℝ),
          (piHalfKernelC p ((t : ℝ) * 4) v y x u).re) =
        fun u => ((p - 2).factorial : ℝ) *
          Real.exp (-y * ((p : ℝ) - 1)) * (-1 : ℝ) ^ p *
            piHalfContourReal p ((t : ℝ) * 4) (charA v y) u := by
      funext u
      have hre :
          ∫ x in Ioi (0 : ℝ), (piHalfKernelC p ((t : ℝ) * 4) v y x u).re =
            (∫ x in Ioi (0 : ℝ), piHalfKernelC p ((t : ℝ) * 4) v y x u).re :=
        Complex.reCLM.integral_comp_comm (piHalfKernelC_inner_integrable hp2 hv u)
      rw [hre, piHalfKernelC_inner_integral hp2 hv, piHalfScale_eq]
      unfold piHalfContourReal
      set g : ℂ := gFun p ((t : ℝ) * 4) (u - I * (π / 2)) with hg
      set Z : ℂ := ((charA v y : ℝ) : ℂ) + I * ((Real.sinh u : ℝ) : ℂ) with hZ
      have hZ0 : Z ≠ 0 := by
        intro h
        have hr := congrArg Complex.re h
        simp [hZ] at hr
        linarith
      have hE0 : ((Real.exp y : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.exp_pos y).ne'
      have hexpneg :
          Real.exp (-y * ((p : ℝ) - 1)) = (Real.exp y ^ (p - 1))⁻¹ := by
        rw [← Real.exp_nat_mul, ← Real.exp_neg]
        congr 1
        rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
        ring
      have h1 : ((Real.cosh u : ℝ) : ℂ) * (I * g) *
            (((p - 2).factorial : ℂ) / (((Real.exp y : ℝ) : ℂ) * Z) ^ (p - 1)) =
          ((Real.cosh u * ((p - 2).factorial : ℝ) * (Real.exp y ^ (p - 1))⁻¹ : ℝ) : ℂ) *
            (I * g / Z ^ (p - 1)) := by
        rw [mul_pow]
        push_cast
        field_simp
      have hden : -I * Complex.sinh (u : ℂ) - ((charA v y : ℝ) : ℂ) = -Z := by
        rw [hZ, Complex.ofReal_sinh]
        ring
      have h2 : -I * g / (-I * Complex.sinh (u : ℂ) - ((charA v y : ℝ) : ℂ)) ^ (p - 1) =
          (((-1 : ℝ) ^ p : ℝ) : ℂ) * (I * g / Z ^ (p - 1)) := by
        rw [hden]
        rcases hp with rfl | rfl | rfl <;> norm_num <;> field_simp
      rw [h1, h2, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.cosh_ofReal_re, hexpneg]
      have hsq : ((-1 : ℝ) ^ p) * ((-1 : ℝ) ^ p) = 1 := by
        rw [← mul_pow]; norm_num
      linear_combination (-(Real.cosh u * ((p - 2).factorial : ℝ) * (Real.exp y ^ (p - 1))⁻¹ *
        (I * g / Z ^ (p - 1)).re)) * hsq
    rw [hinner, integral_const_mul,
      piHalfContourReal_integral hp hT hA]
    dsimp [C]
    have hsqrt : √(2 * π * (t : ℝ)) ≠ 0 := by positivity
    have hgauss :
        (gaussianPDFReal 0 t y)⁻¹ *
            gaussianPDFReal 0 t (Real.arcosh (charA v y)) =
          Real.exp (y ^ 2 / (2 * (t : ℝ))) *
            Real.exp (-(Real.arcosh (charA v y) ^ 2) / (2 * (t : ℝ))) := by
      simp only [gaussianPDFReal_def, sub_zero]
      field_simp [hsqrt]
      rw [← Real.exp_add]
      convert Real.exp_zero.symm using 1
      ring_nf
    rw [hgauss]
    have hq :
        -2 * Real.arcosh (charA v y) ^ 2 / ((t : ℝ) * 4) =
          -(Real.arcosh (charA v y) ^ 2) / (2 * (t : ℝ)) := by
      field_simp [htR.ne']
      ring
    rw [hq]
    rcases hp with rfl | rfl | rfl
    all_goals norm_num [Nat.factorial]
    all_goals ring_nf
    all_goals repeat rw [← Real.exp_add]
    all_goals (congr 1; field_simp [htR.ne']; ring)

private lemma piHalfFormula_sigma_two_measurable
    (p : ℕ) (t : ℝ) :
    Measurable (fun q : ℝ × ℝ =>
      (2 ^ 2 : ℝ)⁻¹ * piHalfFormula p 2 t (q.1 * 2 ^ 2) (q.2 * 2)) := by
  have hg : Continuous (gFun p (t * 4)) := (gFun.contDiff p (t * 4)).continuous
  have hsm : StronglyMeasurable (fun q : (ℝ × ℝ) × ℝ =>
      Real.cosh q.2 *
        (I * cexp (-I * (((4 / (q.1.1 * 4) : ℝ) : ℂ) *
          Real.exp ((q.1.2 * 2) / 2) * Real.sinh q.2)) *
            gFun p (t * 4) (q.2 - I * (Real.pi / 2))).re) := by
    apply Measurable.stronglyMeasurable
    fun_prop
  have hi : Measurable (fun q : ℝ × ℝ =>
      ∫ u in Ioi (0 : ℝ), Real.cosh u *
        (I * cexp (-I * (((4 / (q.1 * 4) : ℝ) : ℂ) *
          Real.exp ((q.2 * 2) / 2) * Real.sinh u)) *
            gFun p (t * 4) (u - I * (Real.pi / 2))).re) :=
    (StronglyMeasurable.integral_prod_right
      (ν := volume.restrict (Ioi (0 : ℝ))) hsm).measurable
  let A : ℝ × ℝ → ℝ := fun q =>
    (2 ^ 2 : ℝ)⁻¹ *
      (2 ^ 4 * (16 / (q.1 * 2 ^ 2) ^ p) *
        Real.exp (q.2 * 2 * (((p : ℕ) : ℝ) - 1) / 2 +
          (q.2 * 2) ^ 2 / (2 * (t * 2 ^ 2)) -
          2 * (Real.exp (q.2 * 2) + 1) / (q.1 * 2 ^ 2)))
  have hA : Measurable A := by
    dsimp [A]
    fun_prop
  have hfun : (fun q : ℝ × ℝ =>
      (2 ^ 2 : ℝ)⁻¹ * piHalfFormula p 2 t (q.1 * 2 ^ 2) (q.2 * 2)) =
      fun q => if 0 < q.1 then A q *
        (∫ u in Ioi (0 : ℝ), Real.cosh u *
          (I * cexp (-I * (((4 / (q.1 * 4) : ℝ) : ℂ) *
            Real.exp ((q.2 * 2) / 2) * Real.sinh u)) *
              gFun p (t * 4) (u - I * (Real.pi / 2))).re) else 0 := by
    funext q
    unfold piHalfFormula A
    by_cases hq : 0 < q.1
    · rw [ite_eq_left hq, ite_eq_left (by positivity : 0 < q.1 * 2 ^ 2)]
      norm_num
      simp only [sub_eq_add_neg, add_comm]
      ring
    · rw [ite_eq_right (not_lt.mpr (le_of_not_gt hq)),
        ite_eq_right (not_lt.mpr
          (mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hq) (sq_nonneg 2)))]
      ring
  rw [hfun]
  apply Measurable.ite
  · exact measurableSet_lt measurable_const measurable_fst
  · exact hA.mul hi
  · exact measurable_const

/-- The `σ = 2` π/2-formula is a constructive joint density for `p = 2,3,4`. -/
theorem pi_half_formula_sigma_two
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (t : ℝ≥0) (ht : 0 < t)
    (p : ℕ) (hp : p = 2 ∨ p = 3 ∨ p = 4) :
    IsJointDensity P W 2 0 t (fun x y =>
      gaussianPDFReal 0 t y * (2 ^ 2 : ℝ)⁻¹ *
        piHalfFormula p 2 t (x * 2 ^ 2) (y * 2)) := by
  let φh : ℝ → ℝ → ℝ := fun x y =>
    (2 ^ 2 : ℝ)⁻¹ * piHalfFormula p 2 t (x * 2 ^ 2) (y * 2)
  let φπ : ℝ → ℝ → ℝ := fun x y =>
    (2 ^ 2 : ℝ)⁻¹ * piFormula p 2 t (x * 2 ^ 2) (y * 2)
  have hae : ∀ y : ℝ, ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
      φh x y = φπ x y := by
    intro y
    have hh0 := piHalfFormula_sigma_two_laplace hp t ht (v := 0) (by norm_num) y
    have hπ0 := piFormula_sigma_two_laplace hp t ht (v := 0) (by norm_num) y
    have hhint : IntegrableOn (fun x => φh x y) (Ioi 0) := by
      simpa only [φh, neg_zero, zero_div, Real.exp_zero, one_mul] using hh0.1
    have hπint : IntegrableOn (fun x => φπ x y) (Ioi 0) := by
      simpa only [φπ, neg_zero, zero_div, Real.exp_zero, one_mul] using hπ0.1
    apply prop_4_4 (fun x => φh x y) (fun x => φπ x y)
      hhint.aestronglyMeasurable hπint.aestronglyMeasurable hhint hπint
    intro u hu
    have hhu := piHalfFormula_sigma_two_laplace hp t ht (v := u) hu y
    have hπu := piFormula_sigma_two_laplace hp t ht (v := u) hu y
    simpa only [laplaceCond, φh, φπ, mul_assoc] using hhu.2.trans hπu.2.symm
  have haeFull : ∀ y : ℝ, ∀ᵐ x ∂volume, φh x y = φπ x y := by
    intro y
    have hrest := (ae_restrict_iff' measurableSet_Ioi).mp (hae y)
    filter_upwards [hrest] with x hx
    by_cases hxp : 0 < x
    · exact hx hxp
    · simp [φh, φπ, piHalfFormula, piFormula, hxp]
  have hφhm : Measurable (Function.uncurry φh) := by
    change Measurable (fun q : ℝ × ℝ =>
      (2 ^ 2 : ℝ)⁻¹ * piHalfFormula p 2 t (q.1 * 2 ^ 2) (q.2 * 2))
    exact piHalfFormula_sigma_two_measurable p (t : ℝ)
  have hφπm : Measurable (Function.uncurry φπ) := by
    change Measurable (fun q : ℝ × ℝ =>
      (2 ^ 2 : ℝ)⁻¹ * piFormula p 2 t (q.1 * 2 ^ 2) (q.2 * 2))
    exact piFormula_sigma_two_measurable p (t : ℝ)
  have heqset : MeasurableSet {q : ℝ × ℝ | φh q.1 q.2 = φπ q.1 q.2} := by
    have hz := measurableSet_singleton (0 : ℝ)
    convert hz.preimage (hφhm.sub hφπm) using 1
    ext q
    simp [Function.uncurry, sub_eq_zero]
  have haeprod : ∀ᵐ q ∂(volume : Measure ℝ).prod volume,
      φh q.1 q.2 = φπ q.1 q.2 := by
    rw [Measure.ae_prod_iff_ae_ae heqset, Measure.ae_ae_comm heqset]
    exact ae_of_all _ haeFull
  have hπ := pi_formula_sigma_two P W hW t ht p hp
  unfold IsJointDensity at hπ ⊢
  rw [hπ]
  apply withDensity_congr_ae
  filter_upwards [haeprod] with q hq
  dsimp [φh, φπ] at hq
  simpa [mul_assoc] using congrArg
    (fun z : ℝ => ENNReal.ofReal (gaussianPDFReal 0 t q.2 * z)) hq.symm

/-- The π/2-formula is a constructive joint density for `p = 2,3,4`. -/
theorem pi_half_formula_general
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W)
    (σ : ℝ) (T : ℝ≥0) (hσ : 0 < σ) (hT : 0 < T)
    (p : ℕ) (hp : p = 2 ∨ p = 3 ∨ p = 4) :
    IsJointDensity P W σ 0 T fun x y =>
      gaussianPDFReal 0 T y * (σ ^ 2)⁻¹ *
        piHalfFormula p σ T (x * σ ^ 2) (y * σ) := by
  let τ := referenceTimeFromTwo σ T
  have hτ : 0 < τ := by
    simpa [τ] using referenceTimeFromTwo_pos hσ hT
  let φ₂ : ℝ → ℝ → ℝ := fun x y =>
    gaussianPDFReal 0 τ y * ((2 : ℝ) ^ 2)⁻¹ *
      piHalfFormula p 2 τ (x * (2 : ℝ) ^ 2) (y * 2)
  have hφ₂ : IsJointDensity P W 2 0 τ φ₂ :=
    pi_half_formula_sigma_two P W hW τ hτ p hp
  have hmcond : Measurable (fun q : ℝ × ℝ =>
      ((2 : ℝ) ^ 2)⁻¹ * piHalfFormula p 2 τ
        (q.1 * (2 : ℝ) ^ 2) (q.2 * 2)) :=
    piHalfFormula_sigma_two_measurable p (τ : ℝ)
  have hm₂ : Measurable (fun q : ℝ × ℝ => ENNReal.ofReal (φ₂ q.1 q.2)) := by
    apply ENNReal.measurable_ofReal.comp
    have hg : Measurable (fun q : ℝ × ℝ => gaussianPDFReal 0 τ q.2) := by
      fun_prop
    dsimp [φ₂]
    convert hg.mul hmcond using 1
    funext q
    simp only [Pi.mul_apply]
    ring
  have hs := IsJointDensity_scaling_from_two_fixed
    P W hW hσ T φ₂ (by simpa [τ] using hφ₂) (by simpa [τ] using hm₂)
  have hfun :
      (fun x y : ℝ =>
        (σ / 2) ^ 3 * φ₂ (σ ^ 2 / 4 * x) (σ / 2 * y)) =
      (fun x y =>
        gaussianPDFReal 0 T y * (σ ^ 2)⁻¹ *
          piHalfFormula p σ T (x * σ ^ 2) (y * σ)) := by
    funext x y
    dsimp [φ₂]
    rw [gaussianPDFReal_referenceTimeFromTwo hσ T y]
    -- Covariance of piHalf under scaling (same algebra as piFormula_sigma_covariant_fixed).
    have hcov :
        piHalfFormula p σ T (x * σ ^ 2) (y * σ) =
          (σ / 2) ^ 4 *
            piHalfFormula p 2 τ (x * σ ^ 2) (y * σ) := by
      have hτ' :
          (referenceTimeFromTwo σ T : ℝ) * (2 : ℝ) ^ 2 = (T : ℝ) * σ ^ 2 := by
        rw [referenceTimeFromTwo, Real.coe_toNNReal]
        · ring
        · positivity
      unfold piHalfFormula
      rw [hτ']
      split_ifs <;> ring
    -- Adjust coordinates (σ²/4 * x, σ/2 * y) vs (x σ², y σ) for the σ=2 formula.
    have hcoord :
        piHalfFormula p 2 τ ((σ ^ 2 / 4 * x) * 2 ^ 2) ((σ / 2 * y) * 2) =
          piHalfFormula p 2 τ (x * σ ^ 2) (y * σ) := by
      congr 1 <;> ring
    rw [hcov, ← hcoord]
    field_simp [hσ.ne']
  rwa [hfun] at hs

end Lyasoff2016
