/-
Dufresne's inverse-gamma density for the infinite-horizon integral.
-/
module

public import Lyasoff2016.Auxiliary
public import Lyasoff2016.BrownianScaling
public import Lyasoff2016.IgDensity
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic


@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

/- Paper: p. 1068, (3.3) Dufresne density.
   Plain recap: ψ(x) = (2/σ²)^β / Γ(β) · x^{-β-1} e^{-2/(σ² x)} with β = −2ν/σ² on x > 0
   (and 0 for x ≤ 0, since the infinite-horizon integral is a.s. positive). -/
def dufresne (σ ν x : ℝ) : ℝ :=
  if 0 < x then invGammaDensity (-2 * ν / σ ^ 2 + 1) (2 / σ ^ 2) x else 0

/- Paper: p. 1067–1068, stationary zero-flux ODE.
   Plain recap: Dufresne’s ψ satisfies (σ²/2)(x²ψ)' − (1+(ν+σ²/2)x)ψ = 0. -/

namespace dufresne

theorem zero_flux (σ ν : ℝ) (hσ : 0 < σ) (x : ℝ) (hx : 0 < x) :
    σ ^ 2 / 2 * deriv (fun z => z ^ 2 * dufresne σ ν z) x
      - (1 + (ν + σ ^ 2 / 2) * x) * dufresne σ ν x = 0 := by
  have hx0 : x ≠ 0 := hx.ne'
  have hσ0 : σ ≠ 0 := hσ.ne'
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = -2 * ν / σ ^ 2 + 1 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 2 / σ ^ 2 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = a ^ (p - 1) / Real.Gamma (p - 1) := ⟨_, rfl⟩
  let ψ : ℝ → ℝ := fun z => C * z ^ (-p) * Real.exp (-a / z)
  have hloc : ∀ᶠ z in nhds x, dufresne σ ν z = ψ z := by
    filter_upwards [eventually_gt_nhds hx] with z hz
    simp [dufresne, ψ, invGammaDensity, hz, hp, ha, hC]
  have hψx : dufresne σ ν x = ψ x := by
    simp [dufresne, ψ, invGammaDensity, hx, hp, ha, hC]
  have h1 : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have h2 : HasDerivAt (fun z : ℝ => z ^ (-p)) (-p * x ^ (-p - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx0)
  have h3 : HasDerivAt (fun z : ℝ => -a / z) (a / x ^ 2) x := by
    have h : HasDerivAt (fun z : ℝ => -a / z) ((0 * x - -a * 1) / x ^ 2) x :=
      (hasDerivAt_const x (-a)).div (hasDerivAt_id x) hx0
    convert h using 1
    ring
  have h4 : HasDerivAt (fun z : ℝ => Real.exp (-a / z))
      (Real.exp (-a / x) * (a / x ^ 2)) x := h3.exp
  have key : HasDerivAt (fun z : ℝ => z ^ 2 * ψ z)
      (C * x ^ (-p) * Real.exp (-a / x) * ((2 - p) * x + a)) x := by
    have h := h1.mul ((h2.const_mul C).mul h4)
    convert h using 1
    simp only [Pi.mul_apply]
    rw [Real.rpow_sub_one hx0]
    field_simp
    ring
  have hderiv : deriv (fun z => z ^ 2 * dufresne σ ν z) x =
      C * x ^ (-p) * Real.exp (-a / x) * ((2 - p) * x + a) := by
    have heq : (fun z => z ^ 2 * dufresne σ ν z) =ᶠ[nhds x] fun z => z ^ 2 * ψ z :=
      hloc.mono fun z hz => by simp [hz]
    exact (key.congr_of_eventuallyEq heq).deriv
  rw [hderiv, hψx]
  simp only [ψ]
  rw [hp, ha]
  field_simp
  ring

theorem nonneg (σ ν : ℝ) (hσ : 0 < σ) (hν : ν < 0) {x : ℝ} (hx : 0 < x) :
    0 ≤ dufresne σ ν x := by
  have hβ : 0 < -2 * ν / σ ^ 2 := div_pos (by linarith) (by positivity)
  have hΓ : 0 < Real.Gamma (-2 * ν / σ ^ 2 + 1 - 1) :=
    Real.Gamma_pos_of_pos (by simpa using hβ)
  have ha : (0 : ℝ) ≤ 2 / σ ^ 2 := by positivity
  simp only [dufresne, hx, ↓reduceIte]
  exact mul_nonneg (mul_nonneg (div_nonneg (Real.rpow_nonneg ha _) hΓ.le)
    (Real.rpow_nonneg hx.le _)) (Real.exp_pos _).le

/- Paper: p. 1067–1068, normalization constant c₂ in (3.3).
   Plain recap: Dufresne's ψ integrates to 1 over (0, ∞) (substitution u = 1/x reduces it
   to the Gamma integral). -/
theorem integral_Ioi (σ ν : ℝ) (hσ : 0 < σ) (hν : ν < 0) :
    ∫ x in Ioi (0 : ℝ), dufresne σ ν x = 1 := by
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = -2 * ν / σ ^ 2 := ⟨_, rfl⟩
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = 2 / σ ^ 2 := ⟨_, rfl⟩
  have hβ : 0 < β := by
    rw [hβdef]
    exact div_pos (by linarith) (by positivity)
  have ha : 0 < a := by
    rw [hadef]
    positivity
  have hΓ := Real.Gamma_pos_of_pos hβ
  let g : ℝ → ℝ := fun y => a ^ β / Real.Gamma β * (y ^ (β - 1) * Real.exp (-(a * y)))
  have hsub := integral_comp_rpow_Ioi g (p := -1) (by norm_num)
  have hg : ∫ y in Ioi (0 : ℝ), g y = 1 := by
    simp only [g]
    rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hβ ha, one_div,
      Real.inv_rpow ha.le]
    have : a ^ β ≠ 0 := (Real.rpow_pos_of_pos ha β).ne'
    field_simp
  rw [← hg, ← hsub]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 < x := hx
  simp only [dufresne, hx0, ↓reduceIte, invGammaDensity, g, smul_eq_mul, ← hβdef, ← hadef]
  have h1 : β + 1 - 1 = β := by ring
  have h2 : (x ^ (-1 : ℝ)) ^ (β - 1) = x ^ (-(β - 1)) := by
    rw [← Real.rpow_mul hx0.le]
    congr 1
    ring
  have h3 : x ^ (-1 : ℝ) = x⁻¹ := Real.rpow_neg_one x
  have h4 : x ^ (-(β + 1)) = x ^ ((-1 : ℝ) - 1) * x ^ (-(β - 1)) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have h5 : -a / x = -(a * x⁻¹) := by
    field_simp
  rw [h1, h2, h3, h4, h5, abs_neg, abs_one]
  ring

/-- The inverse-gamma density has the Brownian-scaling covariance required by
`inftyLaw_scaling`. -/
theorem scaling (σ ν x : ℝ) (hσ : 0 < σ) :
    σ⁻¹ ^ 2 * dufresne σ ν (x / σ ^ 2) = dufresne 1 (ν / σ ^ 2) x := by
  by_cases hx : 0 < x
  · have hσ2 : 0 < σ ^ 2 := sq_pos_of_pos hσ
    have hx' : 0 < x / σ ^ 2 := div_pos hx hσ2
    simp only [dufresne, hx, hx', ↓reduceIte, invGammaDensity, one_pow, div_one]
    have hβ : -2 * (ν / σ ^ 2) = -2 * ν / σ ^ 2 := by ring
    rw [hβ]
    have hβ' : -2 * ν / σ ^ 2 + 1 - 1 = -2 * ν / σ ^ 2 := by ring
    rw [hβ']
    have hpow : (2 / σ ^ 2) ^ (-2 * ν / σ ^ 2) =
        2 ^ (-2 * ν / σ ^ 2) / (σ ^ 2) ^ (-2 * ν / σ ^ 2) := by
      rw [Real.div_rpow (by positivity) (by positivity)]
    have hxpow : (x / σ ^ 2) ^ (-(-2 * ν / σ ^ 2 + 1)) =
        x ^ (-(-2 * ν / σ ^ 2 + 1)) /
          (σ ^ 2) ^ (-(-2 * ν / σ ^ 2 + 1)) := by
      rw [Real.div_rpow hx.le (sq_nonneg σ)]
    rw [hpow, hxpow]
    have hexp : -(2 / σ ^ 2) / (x / σ ^ 2) = -2 / x := by field_simp
    rw [hexp]
    have he : -(-2 * ν / σ ^ 2 + 1) = -(-2 * ν / σ ^ 2) - 1 := by ring
    have hscale : σ⁻¹ ^ 2 / (σ ^ 2) ^ (-2 * ν / σ ^ 2) /
        (σ ^ 2) ^ (-(-2 * ν / σ ^ 2 + 1)) = 1 := by
      rw [he, div_div, ← Real.rpow_add hσ2]
      have hexponents :
          -2 * ν / σ ^ 2 + (-(-2 * ν / σ ^ 2) - 1) = (-1 : ℝ) := by ring
      rw [hexponents, Real.rpow_neg_one]
      field_simp
    calc
      σ⁻¹ ^ 2 *
          (2 ^ (-2 * ν / σ ^ 2) / (σ ^ 2) ^ (-2 * ν / σ ^ 2) /
              Real.Gamma (-2 * ν / σ ^ 2) *
            (x ^ (-(-2 * ν / σ ^ 2 + 1)) /
              (σ ^ 2) ^ (-(-2 * ν / σ ^ 2 + 1))) *
            Real.exp (-2 / x)) =
          (σ⁻¹ ^ 2 / (σ ^ 2) ^ (-2 * ν / σ ^ 2) /
              (σ ^ 2) ^ (-(-2 * ν / σ ^ 2 + 1))) *
            (2 ^ (-2 * ν / σ ^ 2) / Real.Gamma (-2 * ν / σ ^ 2) *
              x ^ (-(-2 * ν / σ ^ 2 + 1)) * Real.exp (-2 / x)) := by ring
      _ = _ := by rw [hscale, one_mul]
  · have hx' : ¬ 0 < x / σ ^ 2 := not_lt.mpr (div_nonpos_of_nonpos_of_nonneg
      (not_lt.mp hx) (sq_nonneg σ))
    simp [dufresne, hx, hx']

/-- The nonnegative density used by `dufresne_theorem` is measurable. -/
theorem measurable (σ ν : ℝ) :
    Measurable fun x => ENNReal.ofReal (dufresne σ ν x) := by
  apply Measurable.ennreal_ofReal
  unfold dufresne invGammaDensity
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  fun_prop

/-- Brownian scaling reduces Dufresne's theorem at arbitrary positive volatility to its
unit-volatility case. -/
theorem theorem_of_sigma_one (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (σ ν : ℝ) (hσ : 0 < σ)
    (h1 : IsInftyDensity P W 1 (ν / σ ^ 2) (dufresne 1 (ν / σ ^ 2))) :
    IsInftyDensity P W σ ν (dufresne σ ν) := by
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hνscale : (ν / σ ^ 2) * σ ^ 2 = ν := by field_simp
  have hlaw := inftyLaw_scaling P W hW hσ (ν / σ ^ 2)
  rw [hνscale, h1] at hlaw
  unfold IsInftyDensity
  apply (MeasurableEquiv.mulLeft₀ (σ ^ 2)
    (pow_ne_zero 2 hσ0)).measurableEmbedding.map_injective
  change Measure.map (fun x : ℝ => σ ^ 2 * x) _ =
    Measure.map (fun x : ℝ => σ ^ 2 * x) _
  rw [← hlaw, map_mul_left_withDensity (pow_ne_zero 2 hσ0) _ (measurable σ ν)]
  congr 1
  funext x
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simpa [abs_of_pos hσ, div_eq_inv_mul] using (scaling σ ν x hσ).symm

/- Paper: p. 1068, Remark 3.1 / Dufresne’s theorem.
   Plain recap: the infinite-horizon integral has Dufresne’s density (supported on x > 0).
   Available pieces: `dufresne_zero_flux`, `dufresne_nonneg`, `integral_dufresne_Ioi`,
   `Z_stationary`. -/
theorem eq_igDensity_one (ν : ℝ) :
    dufresne 1 ν = igDensity (-2 * ν) 2 := by
  funext x
  simp [dufresne, igDensity, one_pow, div_one]

end dufresne

/-- Board-facing alias of `dufresne.zero_flux`. -/
theorem dufresne_zero_flux (σ ν : ℝ) (hσ : 0 < σ) (x : ℝ) (hx : 0 < x) :
    σ ^ 2 / 2 * deriv (fun z => z ^ 2 * dufresne σ ν z) x
      - (1 + (ν + σ ^ 2 / 2) * x) * dufresne σ ν x = 0 :=
  dufresne.zero_flux σ ν hσ x hx

/-- The logarithmic derivative implied by the zero-flux ODE:
`(x² ψ)' / (x² ψ) = (2/σ²)(x⁻² + (ν + σ²/2) x⁻¹)` wherever `ψ x ≠ 0`. -/
theorem zero_flux_logDeriv (σ ν : ℝ) (hσ : 0 < σ) (ψ : ℝ → ℝ) (x : ℝ) (hx : 0 < x)
    (hφ : x ^ 2 * ψ x ≠ 0)
    (hflux :
      σ ^ 2 / 2 * deriv (fun z => z ^ 2 * ψ z) x
        - (1 + (ν + σ ^ 2 / 2) * x) * ψ x = 0) :
    deriv (fun z => z ^ 2 * ψ z) x / (x ^ 2 * ψ x) =
      (2 / σ ^ 2) * (x⁻¹ ^ 2 + (ν + σ ^ 2 / 2) * x⁻¹) := by
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hx0 : x ≠ 0 := hx.ne'
  have hψ : ψ x ≠ 0 := by
    intro h; apply hφ; simp [h]
  have : deriv (fun z => z ^ 2 * ψ z) x =
      (2 / σ ^ 2) * (1 + (ν + σ ^ 2 / 2) * x) * ψ x := by
    have := hflux
    field_simp at this ⊢
    linarith
  rw [this]
  field_simp

end Lyasoff2016
