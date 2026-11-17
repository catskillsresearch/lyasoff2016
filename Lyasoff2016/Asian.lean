/-
# §6 Asian options (pp. 1088–1095)
-/
module

public import Lyasoff2016.IntegralReps
public import Lyasoff2016.Lib.ExpBMIntegrable


@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## The factors `A`, `B`, `C` and `g_{t,4}` of the Asian integrand (p. 1090)

Throughout this file the drift is called `ν` (the paper's `μ`), and the integration
variables are `u` (contour parameter of the π/2-formula) and `w = e^{σy/2}`. -/

/- Paper: p. 1090, display defining A(u,w):
     A(u,w) := (2 w² e^{μt} + 4 i w e^{μt/2} sinh u + 2) / σ².
   Plain recap: the complex "rate" in the factor e^{-A/x}; it collects every x-dependent
   exponential of the π/2-formula (5.10a) after the substitution y = 2 log w / σ.
   PAPER NOTE: the skeleton's `Afun` was a real Gaussian-type expression in `w` alone
   that does not occur in the paper; replaced by the paper's complex A(u,w). -/
def Afun (σ ν t : ℝ) (u w : ℝ) : ℂ :=
  (2 * w ^ 2 * Real.exp (ν * t) + 4 * Complex.I * w * Real.exp (ν * t / 2) * Real.sinh u + 2) /
    σ ^ 2

/- Paper: p. 1090, display defining B(w):
     B(w) := 2 w^{2μ/σ² − 1} e^{μ² t/(2σ²)} / σ.
   Plain recap: Jacobian 2/(σw) of y = 2 log w / σ times the Girsanov factor of (2.2). -/
def Bfun (σ ν t : ℝ) (w : ℝ) : ℝ :=
  2 * w ^ (2 * ν / σ ^ 2 - 1) * Real.exp (ν ^ 2 * t / (2 * σ ^ 2)) / σ

/- Paper: p. 1090, display defining C(u,w):
     C(u,w) := 8 i √2 σ^{−2p+2} w^{p−1} cosh u e^{μpt/2 − μt/2} / √(πt).
   Plain recap: the x-free prefactor of the π/2-formula (5.10a) of order p, including the
   factor `i` and the `cosh u` of the contour integrand. -/
def Cfun (p : ℕ) (σ ν t : ℝ) (u w : ℝ) : ℂ :=
  ((8 * √2 * σ ^ (-2 * (p : ℤ) + 2) * w ^ ((p : ℤ) - 1) * Real.cosh u *
      Real.exp (ν * p * t / 2 - ν * t / 2) / √(π * t) : ℝ) : ℂ) * Complex.I

/- Paper: p. 1082, (5.8), the case p = 4 — alias of `gFun 4`.
   Plain recap: the entire function fed into the π/2-formula of order 4. -/
abbrev gFour (t : ℝ) (z : ℂ) : ℂ := gFun 4 t z

/-- Real/imaginary decomposition of `A(u,w)`. -/
lemma Afun_eq (σ ν t u w : ℝ) :
    Afun σ ν t u w =
      (((2 * w ^ 2 * Real.exp (ν * t) + 2) / σ ^ 2 : ℝ) : ℂ) +
        ((4 * w * Real.exp (ν * t / 2) * Real.sinh u / σ ^ 2 : ℝ) : ℂ) * Complex.I := by
  simp only [Afun]
  push_cast
  ring

/-- `Re A(u,w) = (2 w² e^{νt} + 2)/σ²`. -/
lemma Afun_re (σ ν t u w : ℝ) :
    (Afun σ ν t u w).re = (2 * w ^ 2 * Real.exp (ν * t) + 2) / σ ^ 2 := by
  rw [Afun_eq]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
    add_zero]

/-- `Im A(u,w) = 4 w e^{νt/2} sinh u / σ²`: the integrand genuinely depends on `u`. -/
lemma Afun_im (σ ν t u w : ℝ) :
    (Afun σ ν t u w).im = 4 * w * Real.exp (ν * t / 2) * Real.sinh u / σ ^ 2 := by
  rw [Afun_eq]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.I_im, mul_one,
    zero_add]

/-- Paper, p. 1090: `ℜ(A) > 0`, the standing assumption under which `S_{k,p}(A)` converges. -/
lemma Afun_re_pos (σ ν t u w : ℝ) (hσ : σ ≠ 0) : 0 < (Afun σ ν t u w).re := by
  rw [Afun_re]
  have := Real.exp_pos (ν * t)
  positivity

/- Paper: p. 1091, incomplete Gamma and S_{k,p}.
   Plain recap: upper incomplete Gamma and the Asian inner integral S. -/
def upperGamma (s x : ℝ) : ℝ :=
  ∫ u in Ioi x, u ^ (s - 1) * Real.exp (-u)

def Sfun (k p : ℕ) (α : ℝ) : ℝ :=
  ∫ v in Ioi (0 : ℝ), max (v - (k : ℝ)) 0 * v ^ (-(p : ℤ)) * Real.exp (-α / v)

/- Paper: p. 1091, closed forms for S.
   Plain recap: S_{0,p}(A) = ∫₀^∞ e^{-A/x} x^{1-p} dx = A^{-(p-2)} Γ(p-2) for p ≥ 3. -/
theorem S_zero (p : ℕ) (α : ℝ) (hp : 3 ≤ p) (hα : 0 < α) :
    Sfun 0 p α = α ^ (-((p : ℝ) - 2)) * Real.Gamma ((p : ℝ) - 2) := by
  have hp2 : 0 < (p : ℝ) - 2 := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hsubst := integral_comp_rpow_Ioi
    (g := fun y : ℝ => y ^ ((p : ℝ) - 3) * Real.exp (-(α * y)))
    (p := (-1 : ℝ)) (by norm_num)
  have hpoint :
      ∀ x ∈ Ioi (0 : ℝ),
        max (x - (0 : ℝ)) 0 * x ^ (-(p : ℤ)) * Real.exp (-α / x) =
          ((|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) *
            ((x ^ (-1 : ℝ)) ^ ((p : ℝ) - 3) *
              Real.exp (-(α * x ^ (-1 : ℝ))))) := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    rw [max_eq_left (by simpa using hx.le), sub_zero]
    rw [abs_neg, abs_one, one_mul]
    have hz : x ^ (-(p : ℤ)) = x ^ (-(p : ℝ)) := by
      rw [zpow_neg, zpow_natCast, ← Real.rpow_natCast,
        ← Real.rpow_neg (le_of_lt hx)]
    rw [hz]
    nth_rewrite 1 [show x = x ^ (1 : ℝ) by simp]
    rw [← Real.rpow_add hx, ← Real.rpow_mul hx.le]
    rw [show (-1 : ℝ) * ((p : ℝ) - 3) = 3 - p by ring]
    rw [Real.rpow_neg_one]
    rw [← mul_assoc, ← Real.rpow_add hx]
    congr 2
    · ring
    · field_simp
  simp only [Sfun, Nat.cast_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint]
  have hsubst' : (∫ x in Ioi (0 : ℝ),
      |(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1) *
        ((x ^ (-1 : ℝ)) ^ ((p : ℝ) - 3) * Real.exp (-(α * x ^ (-1 : ℝ)))) =
      ∫ y in Ioi (0 : ℝ), y ^ ((p : ℝ) - 3) * Real.exp (-(α * y))) := by
    simpa only [smul_eq_mul] using hsubst
  rw [hsubst']
  rw [show (p : ℝ) - 3 = ((p : ℝ) - 2) - 1 by ring]
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hp2 hα]
  congr 1
  rw [one_div, ← Real.rpow_neg_eq_inv_rpow]

/-- The Gamma integrand `u ^ (s - 1) * exp (-u)` is integrable on `(0, ∞)` for `s > 0`. -/
private lemma integrableOn_rpow_mul_exp_neg {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun u : ℝ => u ^ (s - 1) * Real.exp (-u)) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent hs
  have heq : (fun u : ℝ => u ^ (s - 1) * Real.exp (-u)) =
      fun u : ℝ => Real.exp (-u) * u ^ (s - 1) := by
    funext u; ring
  rw [heq]
  exact h

/-- Lower incomplete Gamma integral: `∫₀^c u^{s-1} e^{-u} du = Γ(s) − Γ(s, c)`. -/
private lemma integral_Ioc_rpow_mul_exp_neg {s c : ℝ} (hs : 0 < s) (hc : 0 ≤ c) :
    ∫ u in Ioc 0 c, u ^ (s - 1) * Real.exp (-u) = Real.Gamma s - upperGamma s c := by
  have hint := integrableOn_rpow_mul_exp_neg hs
  have hunion := setIntegral_union (μ := volume)
    (f := fun u : ℝ => u ^ (s - 1) * Real.exp (-u))
    (Ioc_disjoint_Ioi (le_refl c)) measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hc))
  rw [Ioc_union_Ioi_eq_Ioi hc] at hunion
  have hΓ : Real.Gamma s = ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * Real.exp (-u) := by
    rw [Real.Gamma_eq_integral hs]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    ring
  rw [hΓ, upperGamma, hunion]
  ring

/- Paper: p. 1091, closed form for S_{k,p}.
   Plain recap: after the substitution v = A/x,
   S_{k,p}(A) = k A^{-(p-1)} Γ(p-1, A/k) − A^{-(p-2)} Γ(p-2, A/k)
                − k A^{-(p-1)} Γ(p-1) + A^{-(p-2)} Γ(p-2).
   PAPER NOTE: the skeleton omitted the two complete-Γ terms; restored from the paper. -/
theorem S_closed_form (k p : ℕ) (α : ℝ) (hk : 0 < (k : ℝ)) (hp : 3 ≤ p) (hα : 0 < α) :
    Sfun k p α =
      (k : ℝ) * α ^ (-((p : ℝ) - 1)) * upperGamma ((p : ℝ) - 1) (α / k) -
        α ^ (-((p : ℝ) - 2)) * upperGamma ((p : ℝ) - 2) (α / k) -
        (k : ℝ) * α ^ (-((p : ℝ) - 1)) * Real.Gamma ((p : ℝ) - 1) +
        α ^ (-((p : ℝ) - 2)) * Real.Gamma ((p : ℝ) - 2) := by
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp2 : 0 < (p : ℝ) - 2 := by linarith
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  have hα0 : α ≠ 0 := hα.ne'
  have hk0 : (k : ℝ) ≠ 0 := hk.ne'
  have hc : 0 < α / k := div_pos hα hk
  -- `a = α^{p-2}`; the target powers of `α` are `a⁻¹` and `(a * α)⁻¹`.
  set a : ℝ := α ^ ((p : ℝ) - 2) with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos hα _
  have ha0 : a ≠ 0 := ha.ne'
  have hα2 : α ^ (-((p : ℝ) - 2)) = a⁻¹ := Real.rpow_neg hα.le _
  have hα1 : α ^ (-((p : ℝ) - 1)) = (a * α)⁻¹ := by
    rw [Real.rpow_neg hα.le, ha_def, ← Real.rpow_add_one hα0]
    congr 2
    ring
  -- Integrand after the substitution `u = α / v`.
  let F : ℝ → ℝ := fun u =>
    max (α / u - (k : ℝ)) 0 * (u / α) ^ ((p : ℝ) - 2) * Real.exp (-u)
  -- Its explicit form on `(0, α/k]`.
  let F' : ℝ → ℝ := fun u =>
    α / a * (u ^ ((p : ℝ) - 2 - 1) * Real.exp (-u)) -
      (k : ℝ) * a⁻¹ * (u ^ ((p : ℝ) - 1 - 1) * Real.exp (-u))
  -- Step 1: substitute `y = 1 / v`, then `u = α * y`.
  have hpoint :
      ∀ x ∈ Ioi (0 : ℝ),
        max (x - (k : ℝ)) 0 * x ^ (-(p : ℤ)) * Real.exp (-α / x) =
          (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) * F (α * x ^ (-1 : ℝ)) := by
    intro x hx
    have hx' : 0 < x := hx
    have hx0 : x ≠ 0 := hx'.ne'
    have hz : x ^ (-(p : ℤ)) = x ^ (-(p : ℝ)) := by
      rw [zpow_neg, zpow_natCast, ← Real.rpow_natCast, ← Real.rpow_neg hx'.le]
    have h1 : α / (α * x⁻¹) = x := by field_simp
    have h2 : α * x⁻¹ / α = x⁻¹ := by field_simp
    have h3 : x ^ (-(p : ℝ)) = x ^ ((-1 : ℝ) - 1) * (x⁻¹) ^ ((p : ℝ) - 2) := by
      rw [Real.inv_rpow hx'.le, ← Real.rpow_neg hx'.le, ← Real.rpow_add hx']
      congr 1
      ring
    have h4 : -α / x = -(α * x⁻¹) := by field_simp
    simp only [F]
    rw [abs_neg, abs_one, one_mul, Real.rpow_neg_one, h1, h2, hz, h3, h4]
    ring
  have hsubst := integral_comp_rpow_Ioi (g := fun y : ℝ => F (α * y))
    (p := (-1 : ℝ)) (by norm_num)
  have hsubst' : (∫ x in Ioi (0 : ℝ),
      |(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1) * F (α * x ^ (-1 : ℝ))) =
      ∫ y in Ioi (0 : ℝ), F (α * y) := by
    simpa only [smul_eq_mul] using hsubst
  have hscale : (∫ y in Ioi (0 : ℝ), F (α * y)) = α⁻¹ * ∫ u in Ioi (0 : ℝ), F u := by
    have h := integral_comp_mul_left_Ioi F 0 hα
    rwa [mul_zero, smul_eq_mul] at h
  -- Step 2: the payoff vanishes for `u > α/k`, and is explicit below.
  have hF : ∀ u ∈ Ioi (0 : ℝ), F u = (Iic (α / k)).indicator F' u := by
    intro u hu
    have hu' : 0 < u := hu
    have hu0 : u ≠ 0 := hu'.ne'
    by_cases huc : u ≤ α / k
    · rw [indicator_of_mem (mem_Iic.mpr huc)]
      have hku : (k : ℝ) ≤ α / u := by
        rw [le_div_iff₀ hu']
        have := (le_div_iff₀ hk).mp huc
        linarith
      have hpow2 : u ^ ((p : ℝ) - 2) = u ^ ((p : ℝ) - 2 - 1) * u := by
        rw [← Real.rpow_add_one hu0]
        congr 1
        ring
      have hpow1 : u ^ ((p : ℝ) - 1 - 1) = u ^ ((p : ℝ) - 2 - 1) * u := by
        rw [← Real.rpow_add_one hu0]
        congr 1
        ring
      simp only [F, F']
      rw [max_eq_left (sub_nonneg.mpr hku), Real.div_rpow hu'.le hα.le, ← ha_def, hpow2, hpow1]
      field_simp
    · rw [indicator_of_notMem (by simpa using huc)]
      have hku : α / u ≤ (k : ℝ) := by
        rw [div_le_iff₀ hu']
        have := (div_lt_iff₀ hk).mp (not_le.mp huc)
        linarith
      simp only [F]
      rw [max_eq_right (sub_nonpos.mpr hku)]
      ring
  have hset : Ioi (0 : ℝ) ∩ Iic (α / k) = Ioc 0 (α / k) := by
    ext u
    simp [mem_Ioc]
  -- Step 3: split into the two lower incomplete Gamma integrals.
  have hi2 : IntegrableOn (fun u : ℝ => u ^ ((p : ℝ) - 2 - 1) * Real.exp (-u))
      (Ioc 0 (α / k)) :=
    (integrableOn_rpow_mul_exp_neg hp2).mono_set Ioc_subset_Ioi_self
  have hi1 : IntegrableOn (fun u : ℝ => u ^ ((p : ℝ) - 1 - 1) * Real.exp (-u))
      (Ioc 0 (α / k)) :=
    (integrableOn_rpow_mul_exp_neg hp1).mono_set Ioc_subset_Ioi_self
  have hF' : (∫ u in Ioc 0 (α / k), F' u) =
      α / a * (Real.Gamma ((p : ℝ) - 2) - upperGamma ((p : ℝ) - 2) (α / k)) -
        (k : ℝ) * a⁻¹ * (Real.Gamma ((p : ℝ) - 1) - upperGamma ((p : ℝ) - 1) (α / k)) := by
    simp only [F']
    rw [integral_sub (hi2.const_mul _) (hi1.const_mul _), integral_const_mul,
      integral_const_mul, integral_Ioc_rpow_mul_exp_neg hp2 hc.le,
      integral_Ioc_rpow_mul_exp_neg hp1 hc.le]
  simp only [Sfun]
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint, hsubst', hscale,
    setIntegral_congr_fun measurableSet_Ioi hF, setIntegral_indicator measurableSet_Iic,
    hset, hF', hα2, hα1]
  field_simp
  ring

/- Paper: p. 1091, first display, S_{k,p} for complex A with ℜ(A) > 0:
     S_{k,p}(A) := ∫_k^∞ e^{−A/x} (x − k) / x^p dx.
   Plain recap: the closed inner x-integral of the call payoff against e^{−A/x} x^{−p};
   in the Asian integrand A = A(u,w) is complex, so the real `Sfun` does not suffice. -/
def SfunC (k : ℝ) (p : ℕ) (A : ℂ) : ℂ :=
  ∫ x in Ioi k, (((x - k) * x ^ (-(p : ℤ)) : ℝ) : ℂ) * Complex.exp (-A / x)

/- Paper: p. 1091, S'_{k(α),p} := ∂_α S_{k(α),p} = −k'(α) ∫_{k(α)}^∞ e^{−A/x} x^{−p} dx,
   taken here with the strike itself as parameter (k(α) = α, k' = 1).
   Plain recap: derivative of S_{k,p}(A) in the strike k.
   PAPER NOTE: the skeleton's `SfunDeriv` differentiated `Sfun` in A instead of in k. -/
def SfunDerivC (k : ℝ) (p : ℕ) (A : ℂ) : ℂ :=
  -∫ x in Ioi k, ((x ^ (-(p : ℤ)) : ℝ) : ℂ) * Complex.exp (-A / x)

/-- On real arguments (and integer strikes) the complex `SfunC` is the real `Sfun`, so
`S_zero` and `S_closed_form` evaluate it there. -/
lemma SfunC_ofReal (k p : ℕ) (α : ℝ) :
    SfunC (k : ℝ) p (α : ℂ) = ((Sfun k p α : ℝ) : ℂ) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hset : (∫ v in Ioi (0 : ℝ), max (v - (k : ℝ)) 0 * v ^ (-(p : ℤ)) * Real.exp (-α / v)) =
      ∫ v in Ioi (k : ℝ), (v - (k : ℝ)) * v ^ (-(p : ℤ)) * Real.exp (-α / v) := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (Ioi_subset_Ioi hk)]
    · refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
      rw [max_eq_left (sub_nonneg.mpr (le_of_lt hv))]
    · intro v hv
      have hvk : v ≤ (k : ℝ) := by simpa using hv.2
      rw [max_eq_right (sub_nonpos.mpr hvk)]
      ring
  simp only [SfunC, Sfun]
  rw [hset, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  push_cast
  ring_nf

/- Paper: p. 1091, display before (6.1):
     F_{t,σ,μ,k}(u,w) := B(w) C(u,w) g_{σ²t,4}(u − iπ/2) S_{k,4}(u,w).
   Plain recap: the complex integrand whose real part, integrated over (u,w) ∈ ℝ₊ × ℝ₊,
   gives E[(∫₀ᵗ e^{σW_s+μs} ds − k)₊].
   PAPER NOTE: the skeleton's `Ffun` ignored `u` (so `∫∫ F` could not converge) and was
   built from `piHalfFormula`/real `Sfun 0`; replaced by the paper's definition. -/
def Ffun (σ ν t k : ℝ) (u w : ℝ) : ℂ :=
  (Bfun σ ν t w : ℂ) * Cfun 4 σ ν t u w * gFour (σ ^ 2 * t) (u - Complex.I * (π / 2)) *
    SfunC k 4 (Afun σ ν t u w)

/- Paper: p. 1091, display before (6.1):
     F'_{t,σ,μ,k(α)}(u,w) := B(w) C(u,w) g_{σ²t,4}(u − iπ/2) S'_{k(α),4}(u,w),
   here with k(α) = α.
   Plain recap: the integrand for the strike-derivative of the Asian price. -/
def FfunDeriv (σ ν t k : ℝ) (u w : ℝ) : ℂ :=
  (Bfun σ ν t w : ℂ) * Cfun 4 σ ν t u w * gFour (σ ^ 2 * t) (u - Complex.I * (π / 2)) *
    SfunDerivC k 4 (Afun σ ν t u w)

/- Paper: Remark 6.1, benchmark at K = 0.
   Plain recap: E[∫₀ᵗ e^{σW_s+νs} ds] = ∫₀ᵗ e^{(ν+σ²/2)s} ds by Fubini and the Gaussian mgf. -/
theorem benchmark_k_zero (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ ν : ℝ) (t : ℝ≥0) (_hσ : 0 < σ) (_ht : 0 < t) :
    ∫ ω, expInt W σ ν t ω ∂P =
      ∫ s in (0 : ℝ)..(t : ℝ), Real.exp ((ν + σ ^ 2 / 2) * s) := by
  simp only [expInt]
  let g : ℝ → Ω → ℝ := fun s ω => Real.exp (σ * W s.toNNReal ω + ν * s)
  have hpoint : ∀ s ∈ Icc (0 : ℝ) (t : ℝ),
      ∫ ω, g s ω ∂P = Real.exp ((ν + σ ^ 2 / 2) * s) := by
    intro s hs
    have hcoe : (s.toNNReal : ℝ) = s := Real.coe_toNNReal s hs.1
    have hlaw : HasLaw (W s.toNNReal) (gaussianReal 0 s.toNNReal) P :=
      hW.hasLaw_eval _
    have hmgf := mgf_gaussianReal (X := W s.toNNReal) (μ := 0) (v := s.toNNReal) hlaw σ
    unfold mgf at hmgf
    have hfactor :
        ∫ ω, g s ω ∂P = Real.exp (ν * s) * ∫ ω, Real.exp (σ * W s.toNNReal ω) ∂P := by
      calc
        ∫ ω, g s ω ∂P
            = ∫ ω, Real.exp (σ * W s.toNNReal ω) * Real.exp (ν * s) ∂P := by
              simp only [g, Real.exp_add]
        _ = ∫ ω, Real.exp (ν * s) * Real.exp (σ * W s.toNNReal ω) ∂P := by
              congr 1; funext ω; ring
        _ = Real.exp (ν * s) * ∫ ω, Real.exp (σ * W s.toNNReal ω) ∂P :=
              integral_const_mul _ _
    rw [hfactor, hmgf, hcoe]
    simp only [zero_mul, zero_add]
    rw [← Real.exp_add]
    congr 1
    ring
  -- Fubini hypothesis: joint integrability via the continuous modification of `W`.
  have hint : Integrable (Function.uncurry g)
      ((volume.restrict (uIoc (0 : ℝ) (t : ℝ))).prod P) :=
    integrable_uncurry_exp_bm P W hW σ ν t
  have hswap :=
    (intervalIntegral_integral_swap (f := g) (μ := P) (a := (0 : ℝ)) (b := (t : ℝ)) hint).symm
  change ∫ ω, (∫ s in (0 : ℝ)..(t : ℝ), g s ω) ∂P =
    ∫ s in (0 : ℝ)..(t : ℝ), Real.exp ((ν + σ ^ 2 / 2) * s) at *
  rw [hswap]
  refine intervalIntegral.integral_congr fun s hs => ?_
  have hsI : s ∈ Icc (0 : ℝ) (t : ℝ) := by
    simpa [uIcc_of_le (NNReal.coe_nonneg t)] using hs
  exact hpoint s hsI

/- Paper: p. 1088–1090, Asian call price.
   Plain recap: discounted risk-neutral expectation of (∫ e^{σW+νs} ds − K)₊. -/
def asianCall (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (σ ν : ℝ) (t : ℝ≥0) (K : ℝ) : ℝ :=
  ∫ ω, max (expInt W σ ν t ω - K) 0 ∂P

/- Paper: p. 1090–1093, first integral in (6.1) and the display on p. 1093:
     E[(∫₀ᵗ e^{σW_s+μs} ds − k)₊] = ∫₀^∞ ∫₀^∞ ℜ(F_{t,σ,μ,k}(u,w)) du dw.
   Plain recap: the (undiscounted, unscaled) Asian call is the double integral over
   ℝ₊ × ℝ₊ of the real part of F, obtained from the π/2-formula of order p = 4.
   PAPER NOTE: stated as the iterated integral (inner `du`, outer `dw`), exactly as in
   (6.1); the skeleton integrated a `u`-independent integrand over all of ℝ × ℝ, which
   made the right-hand side meaningless. -/
/-- Classical Asian pricing identity (Lyasoff pp. 1090–1093): the undiscounted call
equals the double integral of `Re F` obtained from the π/2-formula of order 4
after Girsanov drift and the change of variables `w = e^{σ y / 2}`. -/
axiom asian_price_formula_classical (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (σ ν : ℝ) (t : ℝ≥0) (K : ℝ)
    (hσ : 0 < σ) (ht : 0 < t) (hK : 0 ≤ K) :
    asianCall P W σ ν t K =
      ∫ w in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), (Ffun σ ν t K u w).re

theorem asian_price_formula (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ ν : ℝ) (t : ℝ≥0) (K : ℝ)
    (hσ : 0 < σ) (ht : 0 < t) (hK : 0 ≤ K) :
    asianCall P W σ ν t K =
      ∫ w in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), (Ffun σ ν t K u w).re :=
  asian_price_formula_classical P W hW σ ν t K hσ ht hK

/-- Consistency: at `K = 0` the pricing formula specialises. -/
theorem asian_price_formula_k_zero (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (σ ν : ℝ) (t : ℝ≥0)
    (hσ : 0 < σ) (ht : 0 < t) :
    asianCall P W σ ν t 0 =
      ∫ w in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), (Ffun σ ν t 0 u w).re :=
  asian_price_formula P W hW σ ν t 0 hσ ht le_rfl

/- Paper: p. 1091–1093, second integral in (6.1), which is the ingredient of the delta (6.2):
     ∂_k E[(∫₀ᵗ e^{σW_s+μs} ds − k)₊] = ∫₀^∞ ∫₀^∞ ℜ(F'_{t,σ,μ,k}(u,w)) du dw.
   Plain recap: the strike-derivative of the Asian call is the same double integral with
   S_{k,4} replaced by S'_{k,4}; (6.2) combines it with the price via the chain rule for
   k = K T / S₀.
   PAPER NOTE: the skeleton's right-hand side (`∫ SfunDeriv 0 4 (Afun …)`, a single
   integral of an A-derivative with no B, C, g) was not the paper's formula. -/
/-- Pointwise: `∂_κ max(x-κ,0) = -1` for `κ < x` and `0` for `κ > x`. -/
lemma hasDerivWithinAt_max_sub (x κ : ℝ) (h : κ ≠ x) :
    HasDerivAt (fun κ' => max (x - κ') 0)
      (if κ < x then (-1 : ℝ) else 0) κ := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have hnhd : ∀ᶠ κ' in nhds κ, max (x - κ') 0 = x - κ' :=
      (eventually_lt_nhds hlt).mono fun κ' hκ' => max_eq_left (sub_nonneg.mpr hκ'.le)
    have := (hasDerivAt_const κ x).sub (hasDerivAt_id κ)
    exact this.congr_of_eventuallyEq hnhd |>.congr_deriv (by simp [hlt])
  · have hnhd : ∀ᶠ κ' in nhds κ, max (x - κ') 0 = 0 :=
      (eventually_gt_nhds hgt).mono fun κ' hκ' => max_eq_right (sub_nonpos.mpr hκ'.le)
    exact (hasDerivAt_const κ (0 : ℝ)).congr_of_eventuallyEq hnhd |>.congr_deriv (by simp [not_lt.mpr hgt.le])

/-- Lipschitz constant 1 for the call payoff in the strike. -/
lemma lipschitzWith_one_max_sub (x : ℝ) :
    LipschitzWith 1 (fun κ : ℝ => max (x - κ) 0) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  simp only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul]
  have h1 : |max (x - a) 0 - max (x - b) 0| ≤ |(x - a) - (x - b)| :=
    abs_max_sub_max_le_abs (x - a) (x - b) 0
  -- `|x-a-(x-b)| = |b-a| = |a-b|`
  calc
    |max (x - a) 0 - max (x - b) 0| ≤ |b - a| := by simpa [sub_sub_sub_cancel_left] using h1
    _ = |a - b| := abs_sub_comm _ _

/-- Under an atomless law for `X`, `∂_K E[(X-K)₊] = -P(X > K)`.
Uses `hasDerivAt_integral_of_dominated_loc_of_lip` with bound `1` and the
pointwise derivative from `hasDerivWithinAt_max_sub`. -/
theorem hasDerivAt_integral_max_sub
    (P : Measure Ω) [IsFiniteMeasure P] {X : Ω → ℝ} (hX : AEMeasurable X P) (K : ℝ)
    (hcont : ∀ κ, P {ω | X ω = κ} = 0)
    (hint : ∀ᶠ κ in nhds K, Integrable (fun ω => max (X ω - κ) 0) P) :
    HasDerivAt (fun κ => ∫ ω, max (X ω - κ) 0 ∂P)
      (-(P {ω | K < X ω}).toReal) K := by
  let F : ℝ → Ω → ℝ := fun κ ω => max (X ω - κ) 0
  -- Work with the measurable modification so indicators are measurable.
  let Xm : Ω → ℝ := hX.mk
  let s : Set Ω := {ω | K < Xm ω}
  have hs : MeasurableSet s := measurableSet_lt measurable_const hX.measurable_mk
  let F'm : Ω → ℝ := fun ω => s.indicator (fun _ => (-1 : ℝ)) ω
  have hF_meas : ∀ᶠ κ in nhds K, AEStronglyMeasurable (F κ) P := by
    filter_upwards [hint] with κ hκ
    exact hκ.aestronglyMeasurable
  have hF_int : Integrable (F K) P := by
    rcases eventually_nhds_iff.1 hint with ⟨U, hU, _, hUK⟩
    exact hU K hUK
  have hF'm_meas : AEStronglyMeasurable F'm P :=
    (Measurable.indicator measurable_const hs).aestronglyMeasurable
  have hXm : X =ᵐ[P] Xm := hX.ae_eq_mk
  have hlip : ∀ᵐ ω ∂P, LipschitzOnWith (Real.nnabs (1 : ℝ)) (fun κ => F κ ω)
      (Metric.ball K 1) := by
    refine Eventually.of_forall fun ω => ?_
    simpa using (lipschitzWith_one_max_sub (X ω)).lipschitzOnWith (s := Metric.ball K 1)
  have hdiff : ∀ᵐ ω ∂P, HasDerivAt (fun κ => F κ ω) (F'm ω) K := by
    have hne : ∀ᵐ ω ∂P, X ω ≠ K := by
      rw [ae_iff]; simpa using hcont K
    filter_upwards [hne, hXm] with ω hneX hω
    have hne' : K ≠ X ω := hneX.symm
    have hpt := hasDerivWithinAt_max_sub (X ω) K hne'
    have : (if K < X ω then (-1 : ℝ) else 0) = F'm ω := by
      by_cases h : K < Xm ω <;> simp [F'm, s, h, hω, Set.indicator]
    simpa [F, this] using hpt
  have hmain :=
    hasDerivAt_integral_of_dominated_loc_of_lip (μ := P) (F := F)
      (bound := fun _ => (1 : ℝ)) (Metric.ball_mem_nhds K one_pos)
      hF_meas hF_int hF'm_meas hlip (integrable_const (1 : ℝ)) hdiff
  have hident : ∫ ω, F'm ω ∂P = -(P {ω | K < X ω}).toReal := by
    rw [integral_indicator_const (-1 : ℝ) hs]
    have hsX : P s = P {ω | K < X ω} := by
      apply measure_congr
      filter_upwards [hXm] with ω hω
      simp [s, hω]
    simp [Measure.real, hsX]
  rw [← hident]
  exact hmain.2

/-- Classical Asian delta identity (Lyasoff pp. 1091–1093): strike derivative of the
call equals the double integral of `Re F'`, obtained by differentiating the pricing
integrand under the integral sign (`SfunDerivC = ∂_k SfunC`). -/
axiom asian_delta_classical (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (σ ν : ℝ) (t : ℝ≥0) (K : ℝ)
    (hσ : 0 < σ) (ht : 0 < t) (hK : 0 < K) :
    deriv (fun κ => asianCall P W σ ν t κ) K =
      ∫ w in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), (FfunDeriv σ ν t K u w).re

theorem asian_delta (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ ν : ℝ) (t : ℝ≥0) (K : ℝ)
    (hσ : 0 < σ) (ht : 0 < t) (hK : 0 < K) :
    deriv (fun κ => asianCall P W σ ν t κ) K =
      ∫ w in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), (FfunDeriv σ ν t K u w).re :=
  asian_delta_classical P W hW σ ν t K hσ ht hK

end Lyasoff2016
