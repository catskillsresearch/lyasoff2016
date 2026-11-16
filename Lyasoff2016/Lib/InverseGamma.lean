/-
Inverse-Gamma / Gamma reciprocal helpers for Dufresne’s theorem.
-/
import Lyasoff2016.Setting
import Lyasoff2016.Lib.MomentUniqueness

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/-- Inverse-Gamma density written as the law of `1/Y` for `Y ~ Gamma(β, rate a)`.
`igDensity β a x = invGammaDensity (β+1) a x` on `(0,∞)`. -/
def igDensity (β a x : ℝ) : ℝ := if 0 < x then invGammaDensity (β + 1) a x else 0

theorem igDensity_nonneg {β a : ℝ} (hβ : 0 < β) (ha : 0 < a) (x : ℝ) : 0 ≤ igDensity β a x := by
  unfold igDensity
  split_ifs with hx
  · have hΓ : 0 < Real.Gamma (β + 1 - 1) := Real.Gamma_pos_of_pos (by simpa using hβ)
    exact mul_nonneg (mul_nonneg (div_nonneg (Real.rpow_nonneg ha.le _) hΓ.le)
      (Real.rpow_nonneg hx.le _)) (Real.exp_pos _).le
  · exact le_rfl

theorem measurable_igDensity (β a : ℝ) : Measurable (igDensity β a) := by
  unfold igDensity invGammaDensity
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  fun_prop

/-- The change of variables `x = 1/y` turns the Inverse-Gamma density into a Gamma density. -/
theorem integral_igDensity_Ioi {β a : ℝ} (hβ : 0 < β) (ha : 0 < a) :
    ∫ x in Ioi (0 : ℝ), igDensity β a x = 1 := by
  have hsub := integral_comp_rpow_Ioi
    (g := fun y : ℝ => a ^ β / Real.Gamma β * (y ^ (β - 1) * Real.exp (-(a * y))))
    (p := (-1 : ℝ)) (by norm_num)
  have hg : ∫ y in Ioi (0 : ℝ),
      a ^ β / Real.Gamma β * (y ^ (β - 1) * Real.exp (-(a * y))) = 1 := by
    rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hβ ha, one_div,
      Real.inv_rpow ha.le]
    have : a ^ β ≠ 0 := (Real.rpow_pos_of_pos ha β).ne'
    field_simp
  rw [← hg, ← hsub]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 < x := hx
  simp only [igDensity, hx0, ↓reduceIte, invGammaDensity, smul_eq_mul]
  have h1 : β + 1 - 1 = β := by ring
  have h2 : (x ^ (-1 : ℝ)) ^ (β - 1) = x ^ (-(β - 1)) := by
    rw [← Real.rpow_mul hx0.le]; congr 1; ring
  have h3 : x ^ (-1 : ℝ) = x⁻¹ := Real.rpow_neg_one x
  have h4 : x ^ (-(β + 1)) = x ^ ((-1 : ℝ) - 1) * x ^ (-(β - 1)) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have h5 : -a / x = -(a * x⁻¹) := by field_simp
  rw [h1, h2, h3, h4, h5, abs_neg, abs_one]
  ring

theorem lintegral_igDensity {β a : ℝ} (hβ : 0 < β) (ha : 0 < a) :
    ∫⁻ x, ENNReal.ofReal (igDensity β a x) = 1 := by
  have h1 := integral_igDensity_Ioi hβ ha
  have hsupp : ∀ x ∉ Ioi (0 : ℝ), igDensity β a x = 0 := fun x hx => by
    simp only [igDensity, mem_Ioi, not_lt] at hx ⊢
    simp [hx]
  have hint : IntegrableOn (igDensity β a) (Ioi 0) :=
    Integrable.of_integral_ne_zero (by rw [h1]; exact one_ne_zero)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] igDensity β a :=
    (ae_restrict_mem measurableSet_Ioi).mono fun x _ => igDensity_nonneg hβ ha x
  have h2 : ENNReal.ofReal (∫ x in Ioi (0 : ℝ), igDensity β a x) =
      ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (igDensity β a x) :=
    ofReal_integral_eq_lintegral_ofReal hint hnn
  have h3 : ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (igDensity β a x) = 1 := by
    rw [← h2, h1, ENNReal.ofReal_one]
  refine Eq.trans ?_ h3
  have hInd := lintegral_indicator (μ := volume) (s := Ioi (0 : ℝ)) measurableSet_Ioi
    (fun x => ENNReal.ofReal (igDensity β a x))
  refine Eq.trans ?_ hInd
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, hsupp x hx, ENNReal.ofReal_zero]

theorem inv_mul_igDensity {β a : ℝ} (hβ : 0 < β) (ha : 0 < a) (x : ℝ) :
    x⁻¹ * igDensity β a x = β / a * igDensity (β + 1) a x := by
  unfold igDensity
  split_ifs with hx
  · simp only [invGammaDensity]
    have e1 : β + 1 - 1 = β := by ring
    have e2 : β + 1 + 1 - 1 = β + 1 := by ring
    have e3 : x ^ (-(β + 1 + 1)) = x ^ (-(β + 1)) * x⁻¹ := by
      rw [show -(β + 1 + 1) = -(β + 1) - 1 by ring, Real.rpow_sub_one hx.ne']
      rfl
    have hΓ : Real.Gamma β ≠ 0 := (Real.Gamma_pos_of_pos hβ).ne'
    rw [e1, e2, e3, Real.Gamma_add_one hβ.ne', Real.rpow_add_one ha.ne']
    field_simp
  · simp

theorem exp_mul_igDensity {β a s : ℝ} (hβ : 0 < β) (ha : 0 < a) (hs : s < a) (x : ℝ) :
    Real.exp (s * x⁻¹) * igDensity β a x = (a / (a - s)) ^ β * igDensity β (a - s) x := by
  unfold igDensity
  split_ifs with hx
  · simp only [invGammaDensity]
    have e1 : β + 1 - 1 = β := by ring
    have has : 0 < a - s := by linarith
    have hexp : Real.exp (s * x⁻¹) * Real.exp (-a / x) = Real.exp (-(a - s) / x) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    rw [e1, Real.div_rpow ha.le has.le]
    calc Real.exp (s * x⁻¹) * (a ^ β / Real.Gamma β * x ^ (-(β + 1)) * Real.exp (-a / x))
        = a ^ β / Real.Gamma β * x ^ (-(β + 1)) * (Real.exp (s * x⁻¹) * Real.exp (-a / x)) := by
          ring
      _ = _ := by
          rw [hexp]
          field_simp
  · simp

/-- Integer moments of a Gamma law with shape `β` and rate `a`. -/
def gammaMoment (β a : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => (β + n) / a * gammaMoment β a n

theorem gammaMoment_nonneg {β a : ℝ} (hβ : 0 < β) (ha : 0 < a) (n : ℕ) :
    0 ≤ gammaMoment β a n := by
  induction n with
  | zero => simp [gammaMoment]
  | succ n ih =>
    simp only [gammaMoment]
    positivity

theorem inv_pow_mul_igDensity {β a : ℝ} (hβ : 0 < β) (ha : 0 < a) (n : ℕ) (x : ℝ) :
    x⁻¹ ^ n * igDensity β a x = gammaMoment β a n * igDensity (β + n) a x := by
  induction n with
  | zero => simp [gammaMoment]
  | succ n ih =>
    have hβn : 0 < β + n := by positivity
    rw [pow_succ', mul_assoc, ih, mul_left_comm, inv_mul_igDensity hβn ha]
    simp only [gammaMoment, Nat.cast_add, Nat.cast_one]
    rw [add_assoc]
    ring

/-- The law with density `igDensity β a`. -/
def igMeasure (β a : ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (igDensity β a x)

theorem isProbabilityMeasure_igMeasure {β a : ℝ} (hβ : 0 < β) (ha : 0 < a) :
    IsProbabilityMeasure (igMeasure β a) :=
  ⟨by rw [igMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_igDensity hβ ha]⟩

theorem lintegral_igMeasure {β a : ℝ} (hβ : 0 < β) (ha : 0 < a) (f g : ℝ → ℝ)
    (hf : Measurable f) (hfg : ∀ x, f x * igDensity β a x = g x) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂(igMeasure β a) = ∫⁻ x, ENNReal.ofReal (g x) := by
  rw [igMeasure, lintegral_withDensity_eq_lintegral_mul _
    (measurable_igDensity β a).ennreal_ofReal hf.ennreal_ofReal]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  rw [← hfg x, mul_comm (f x), ENNReal.ofReal_mul (igDensity_nonneg hβ ha x)]

theorem lintegral_inv_pow_igMeasure {β a : ℝ} (hβ : 0 < β) (ha : 0 < a) (n : ℕ) :
    ∫⁻ y, ENNReal.ofReal (y ^ n) ∂((igMeasure β a).map fun x => x⁻¹) =
      ENNReal.ofReal (gammaMoment β a n) := by
  rw [lintegral_map (by fun_prop) measurable_inv,
    lintegral_igMeasure hβ ha (fun x => x⁻¹ ^ n) _ (by fun_prop)
      (fun x => inv_pow_mul_igDensity hβ ha n x),
    lintegral_congr fun x => ENNReal.ofReal_mul (gammaMoment_nonneg hβ ha n),
    lintegral_const_mul _ (measurable_igDensity _ _).ennreal_ofReal,
    lintegral_igDensity (by positivity) ha, mul_one]

theorem lintegral_exp_inv_igMeasure {β a s : ℝ} (hβ : 0 < β) (ha : 0 < a) (hs : s < a) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (s * y)) ∂((igMeasure β a).map fun x => x⁻¹) =
      ENNReal.ofReal ((a / (a - s)) ^ β) := by
  have has : 0 < a - s := by linarith
  rw [lintegral_map (by fun_prop) measurable_inv,
    lintegral_igMeasure hβ ha (fun x => Real.exp (s * x⁻¹)) _ (by fun_prop)
      (fun x => exp_mul_igDensity hβ ha hs x),
    lintegral_congr fun x => ENNReal.ofReal_mul (by positivity),
    lintegral_const_mul _ (measurable_igDensity _ _).ennreal_ofReal,
    lintegral_igDensity hβ has, mul_one]

theorem ae_nonneg_map_inv_igMeasure (β a : ℝ) :
    ∀ᵐ y ∂((igMeasure β a).map fun x => x⁻¹), 0 ≤ y := by
  rw [ae_map_iff measurable_inv.aemeasurable measurableSet_Ici, igMeasure,
    ae_withDensity_iff (measurable_igDensity β a).ennreal_ofReal]
  refine Eventually.of_forall fun x hx => ?_
  by_cases h : 0 < x
  · exact inv_nonneg.2 h.le
  · simp [igDensity, h] at hx

end Lyasoff2016
