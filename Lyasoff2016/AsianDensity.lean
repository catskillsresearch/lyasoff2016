/-
# Density ingredients for the Asian pricing identity (pp. 1090–1093)

* `aemeasurable_jointMap`: the map `ω ↦ (∫₀ᵗ e^{σW+νs} ds, W_t)` is a.e.-measurable.
* `lintegral_jointLaw_girsanov`: Girsanov (2.2) for nonnegative integrals against the joint law.
* `measurable_piHalfFormula`: joint measurability of the π/2-formula.
* `piHalfFormula_cond_normalized`: the conditional π/2-density integrates to one in `x`.
* `piHalfFormula_ae_nonneg`: the π/2-formula is a.e. nonnegative (so `ENNReal.ofReal` in
  `IsJointDensity` does not clamp anything).
* `asianKernel_fubini`: for fixed `y`, the `u`-integral of `ℜ F` is the `x`-integral of the
  payoff against the Girsanov-tilted π/2-density of order `4`.
* `integral_Ioi_comp_exp_affine`: the substitution `w = e^{σy/2 − νt/2}`.
-/
module

public import Lyasoff2016.PiHalfFormulaHigher
public import Lyasoff2016.CameronMartin
public import Lyasoff2016.Ffun
public import Lyasoff2016.GFunDecay


@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Probabilistic ingredients -/

/-- The pair `(∫₀ᵗ e^{σW_s+νs} ds, W_t)` is a.e.-measurable along a Brownian motion. -/
theorem aemeasurable_jointMap (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ ν : ℝ) (t : ℝ≥0) :
    AEMeasurable (fun ω => (expInt W σ ν t ω, W t ω)) P := by
  let F : (ℝ≥0 → ℝ) → ℝ × ℝ := fun x =>
    (∫ s in (0 : ℝ)..(t : ℝ), Real.exp (σ * x s.toNNReal + ν * s), x t)
  have hF : Measurable fun x : C(ℝ≥0, ℝ) => F (fun s => x s) :=
    (measurable_path_intervalIntegral (fun s w => Real.exp (σ * w + ν * s))
      (show Continuous (fun p : ℝ × ℝ => Real.exp (σ * p.2 + ν * p.1)) by fun_prop)
      0 t).prodMk (ContinuousMap.measurable_eval t)
  exact (isBrownianReal_path_functional P W W hW hW F hF).1

/-- Paper p. 1066, (2.2), for nonnegative integrals: integrating against the joint law with
drift `σθ` is integrating the `y`-shifted function, tilted by `exp(θ y − θ² t / 2)`, against the
driftless joint law. -/
theorem lintegral_jointLaw_girsanov (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ θ : ℝ) (t : ℝ≥0) (H : ℝ × ℝ → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ p, H p ∂jointLaw P W σ (σ * θ) t =
      ∫⁻ q, H (q.1, q.2 - θ * (t : ℝ)) *
        ENNReal.ofReal (Real.exp (θ * q.2 - θ ^ 2 * (t : ℝ) / 2)) ∂jointLaw P W σ 0 t := by
  rw [← jointLaw_girsanov P W hW σ θ t]
  have hsh : Measurable (fun p : ℝ × ℝ => (p.1, p.2 + θ * (t : ℝ))) := by fun_prop
  have hd : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (Real.exp (-θ * p.2 - θ ^ 2 * (t : ℝ) / 2))) := by fun_prop
  have hG : Measurable (fun q : ℝ × ℝ => H (q.1, q.2 - θ * (t : ℝ)) *
      ENNReal.ofReal (Real.exp (θ * q.2 - θ ^ 2 * (t : ℝ) / 2))) :=
    (hH.comp (by fun_prop)).mul (by fun_prop)
  rw [lintegral_map hG hsh]
  refine Eq.trans ?_ (lintegral_withDensity_eq_lintegral_mul _ hd (hG.comp hsh)).symm
  refine lintegral_congr fun p => ?_
  simp only [Pi.mul_apply, Function.comp_apply, add_sub_cancel_right]
  rw [mul_comm, mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  have h0 : θ * (p.2 + θ * (t : ℝ)) - θ ^ 2 * (t : ℝ) / 2 +
      (-θ * p.2 - θ ^ 2 * (t : ℝ) / 2) = 0 := by ring
  rw [h0, Real.exp_zero, ENNReal.ofReal_one, mul_one]

/-! ### Measurability and normalization of the π/2-formula -/

/-- The π/2-formula is jointly measurable in `(x, y)`. -/
theorem measurable_piHalfFormula (p : ℕ) (σ t : ℝ) :
    Measurable (fun q : ℝ × ℝ => piHalfFormula p σ t q.1 q.2) := by
  have hg : Continuous (gFun p (t * σ ^ 2)) := (gFun.contDiff p (t * σ ^ 2)).continuous
  have hsm : StronglyMeasurable (fun q : (ℝ × ℝ) × ℝ =>
      Real.cosh q.2 *
        (I * cexp (-I * ((4 / q.1.1 : ℂ) * Real.exp (q.1.2 / 2) * Real.sinh q.2)) *
            gFun p (t * σ ^ 2) (q.2 - I * (Real.pi / 2))).re) := by
    apply Measurable.stronglyMeasurable
    fun_prop
  have hi : Measurable (fun q : ℝ × ℝ =>
      ∫ u in Ioi (0 : ℝ), Real.cosh u *
        (I * cexp (-I * ((4 / q.1 : ℂ) * Real.exp (q.2 / 2) * Real.sinh u)) *
            gFun p (t * σ ^ 2) (u - I * (Real.pi / 2))).re) :=
    (StronglyMeasurable.integral_prod_right
      (ν := volume.restrict (Ioi (0 : ℝ))) hsm).measurable
  unfold piHalfFormula
  apply Measurable.ite
  · exact measurableSet_lt measurable_const measurable_fst
  · exact Measurable.mul (by fun_prop) hi
  · exact measurable_const

/-- For every `y`, the conditional π/2-density `x ↦ σ⁻² · piHalfFormula p σ T (x σ²) (y σ)`
is integrable on `(0, ∞)` with total mass one (the `v = 0` case of the conditional Laplace
transform, transported from `σ = 2` by Brownian scaling). -/
theorem piHalfFormula_cond_normalized {p : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 4)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (hT : 0 < T) (y : ℝ) :
    IntegrableOn (fun x => (σ ^ 2)⁻¹ * piHalfFormula p σ T (x * σ ^ 2) (y * σ)) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ), (σ ^ 2)⁻¹ * piHalfFormula p σ T (x * σ ^ 2) (y * σ) = 1 := by
  set τ := referenceTimeFromTwo σ T with hτdef
  have hτ : 0 < τ := referenceTimeFromTwo_pos hσ hT
  have hτ' : (τ : ℝ) * (2 : ℝ) ^ 2 = (T : ℝ) * σ ^ 2 := by
    rw [hτdef, referenceTimeFromTwo, Real.coe_toNNReal]
    · ring
    · positivity
  have hcov : ∀ X Y : ℝ,
      piHalfFormula p σ T X Y = (σ / 2) ^ 4 * piHalfFormula p 2 τ X Y := by
    intro X Y
    unfold piHalfFormula
    rw [hτ']
    split_ifs <;> ring
  obtain ⟨hint, hval⟩ :=
    piHalfFormula_sigma_two_laplace hp τ hτ (v := 0) le_rfl (σ / 2 * y)
  set g : ℝ → ℝ := fun x => Real.exp (-0 / x) * (2 ^ 2 : ℝ)⁻¹ *
    piHalfFormula p 2 τ (x * 2 ^ 2) (σ / 2 * y * 2) with hg
  have hb : (0 : ℝ) < σ ^ 2 / 4 := by positivity
  have hfun : (fun x => (σ ^ 2)⁻¹ * piHalfFormula p σ T (x * σ ^ 2) (y * σ)) =
      fun x => σ ^ 2 / 4 * g (σ ^ 2 / 4 * x) := by
    funext x
    simp only [hg, neg_zero, zero_div, Real.exp_zero, one_mul]
    rw [hcov]
    have h1 : σ ^ 2 / 4 * x * 2 ^ 2 = x * σ ^ 2 := by ring
    have h2 : σ / 2 * y * 2 = y * σ := by ring
    rw [h1, h2]
    field_simp
    ring
  have hval1 : ∫ x in Ioi (0 : ℝ), g x = 1 := by
    rw [hval]
    have hA : charA 0 (σ / 2 * y) = Real.cosh |σ / 2 * y| := by
      unfold charA
      rw [Real.cosh_abs]
      ring
    rw [hA, Real.arcosh_cosh (abs_nonneg _)]
    have hgauss : gaussianPDFReal 0 τ |σ / 2 * y| = gaussianPDFReal 0 τ (σ / 2 * y) := by
      simp only [gaussianPDFReal_def, sub_zero, sq_abs]
    rw [hgauss]
    exact inv_mul_cancel₀ (gaussianPDFReal_pos 0 τ _ hτ.ne').ne'
  rw [hfun]
  constructor
  · have h := (integrableOn_Ioi_comp_mul_left_iff g 0 hb).mpr (by simpa using hint)
    exact h.const_mul _
  · rw [integral_const_mul, integral_comp_mul_left_Ioi g 0 hb, mul_zero, hval1]
    simp only [smul_eq_mul, mul_one]
    field_simp

/-- The π/2-formula of order `p = 2, 3, 4` is a.e. nonnegative: its positive part already has
total mass one (it is a density of a probability law), and so does the formula itself. -/
theorem piHalfFormula_ae_nonneg (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (hT : 0 < T)
    {p : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 4) :
    ∀ᵐ y ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure ℝ),
      0 ≤ piHalfFormula p σ T (x * σ ^ 2) (y * σ) := by
  set φc : ℝ → ℝ → ℝ := fun x y =>
    (σ ^ 2)⁻¹ * piHalfFormula p σ T (x * σ ^ 2) (y * σ) with hφc
  have hφm : Measurable (fun q : ℝ × ℝ => φc q.1 q.2) :=
    ((measurable_piHalfFormula p σ T).comp
      (show Measurable (fun q : ℝ × ℝ => (q.1 * σ ^ 2, q.2 * σ)) by fun_prop)).const_mul _
  have hdens := pi_half_formula_general P W hW σ T hσ hT p hp
  unfold IsJointDensity at hdens
  have hprob : IsProbabilityMeasure (jointLaw P W σ 0 T) :=
    (Measure.isProbabilityMeasure_map_iff (aemeasurable_jointMap P W hW σ 0 T)).mpr inferInstance
  have hmass : ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (gaussianPDFReal 0 T q.2 * φc q.1 q.2) = 1 := by
    have h1 : jointLaw P W σ 0 T univ = 1 := measure_univ
    rw [hdens, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
    rw [← h1]
    refine lintegral_congr fun q => ?_
    simp only [hφc, mul_assoc]
  have hvanish : ∀ x y : ℝ, ¬ 0 < x → φc x y = 0 := by
    intro x y hx
    have hx' : ¬ 0 < x * σ ^ 2 := by
      have : x * σ ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hx) (sq_nonneg σ)
      exact not_lt.mpr this
    simp [hφc, piHalfFormula, hx']
  have hind : ∀ y : ℝ, (fun x => φc x y) = (Ioi (0 : ℝ)).indicator (fun x => φc x y) := by
    intro y
    funext x
    by_cases hx : 0 < x
    · rw [Set.indicator_of_mem (mem_Ioi.mpr hx)]
    · rw [Set.indicator_of_notMem (by simpa using hx), hvanish x y hx]
  have hint : ∀ y, Integrable (fun x => φc x y) := by
    intro y
    rw [hind y, integrable_indicator_iff measurableSet_Ioi]
    exact (piHalfFormula_cond_normalized hp hσ T hT y).1
  have hone : ∀ y, ∫ x, φc x y = 1 := by
    intro y
    rw [hind y, integral_indicator measurableSet_Ioi]
    exact (piHalfFormula_cond_normalized hp hσ T hT y).2
  set N : ℝ → ℝ≥0∞ := fun y => ∫⁻ x, ENNReal.ofReal (-φc x y) with hN
  have hsplit : ∀ y, ∫⁻ x, ENNReal.ofReal (φc x y) = 1 + N y := by
    intro y
    have h := integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hint y)
    rw [hone y] at h
    have hA : ∫⁻ x, ENNReal.ofReal (φc x y) ≠ ∞ := (hint y).lintegral_lt_top.ne
    have hNy : N y ≠ ∞ := ((hint y).neg.lintegral_lt_top).ne
    have hreal : (∫⁻ x, ENNReal.ofReal (φc x y)).toReal = (1 + N y).toReal := by
      rw [ENNReal.toReal_add ENNReal.one_ne_top hNy, ENNReal.toReal_one]
      simp only [hN]
      linarith
    exact (ENNReal.toReal_eq_toReal_iff' hA (by simp [hNy])).mp hreal
  have hNm : Measurable N :=
    Measurable.lintegral_prod_left' (f := fun q : ℝ × ℝ => ENNReal.ofReal (-φc q.1 q.2))
      hφm.neg.ennreal_ofReal
  have hg1 : ∫⁻ y, ENNReal.ofReal (gaussianPDFReal 0 T y) = 1 :=
    lintegral_gaussianPDFReal_eq_one 0 hT.ne'
  have hgm : Measurable (fun y => ENNReal.ofReal (gaussianPDFReal 0 T y)) :=
    (measurable_gaussianPDFReal 0 T).ennreal_ofReal
  have hton : ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (gaussianPDFReal 0 T q.2 * φc q.1 q.2) =
      ∫⁻ y, ENNReal.ofReal (gaussianPDFReal 0 T y) * (1 + N y) := by
    have hm : Measurable (fun q : ℝ × ℝ =>
        ENNReal.ofReal (gaussianPDFReal 0 T q.2 * φc q.1 q.2)) :=
      (((measurable_gaussianPDFReal 0 T).comp measurable_snd).mul hφm).ennreal_ofReal
    rw [Measure.volume_eq_prod, lintegral_prod_symm _ hm.aemeasurable]
    refine lintegral_congr fun y => ?_
    simp only [ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 T y)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hsplit]
  rw [hton] at hmass
  simp only [mul_add, mul_one] at hmass
  rw [lintegral_add_left hgm, hg1] at hmass
  have hzero : ∫⁻ y, ENNReal.ofReal (gaussianPDFReal 0 T y) * N y = 0 := by
    have h := hmass
    nth_rewrite 2 [← add_zero (1 : ℝ≥0∞)] at h
    exact (ENNReal.add_right_inj ENNReal.one_ne_top).mp h
  have hzero' := (lintegral_eq_zero_iff (hgm.mul hNm)).mp hzero
  filter_upwards [hzero'] with y hy
  have hNy : N y = 0 := by
    rcases mul_eq_zero.mp hy with h | h
    · exact absurd (ENNReal.ofReal_eq_zero.mp h)
        (not_le.mpr (gaussianPDFReal_pos 0 T y hT.ne'))
    · exact h
  have hNy' := (lintegral_eq_zero_iff (f := fun x => ENNReal.ofReal (-φc x y))
    (hφm.comp (measurable_id.prodMk measurable_const)).neg.ennreal_ofReal).mp hNy
  filter_upwards [hNy'] with x hx
  have hle : -φc x y ≤ 0 := ENNReal.ofReal_eq_zero.mp hx
  have hpos : (0 : ℝ) < (σ ^ 2)⁻¹ := by positivity
  have h0 : 0 ≤ (σ ^ 2)⁻¹ * piHalfFormula p σ T (x * σ ^ 2) (y * σ) := by
    simpa [hφc] using hle
  exact nonneg_of_mul_nonneg_right h0 hpos

/-! ### Fixed-`y` Fubini for the order-4 kernel -/

/-- Paper p. 1090–1091: for fixed `y` (equivalently fixed `w = e^{σy/2 − νt/2}`), the
`u`-integral of `ℜ F_{t,σ,ν,K}(u,w)` times the Jacobian `σ w / 2` is the `x`-integral of the call
payoff against the Girsanov-tilted π/2-density of order `4`.  The `(x, u)`-integrand is absolutely
integrable for fixed `y`: its modulus factors as an inverse-Gamma kernel in `x` times
`cosh u · |g_{σ²t,4}(u − iπ/2)|`. -/
theorem asianKernel_fubini {σ : ℝ} (hσ : 0 < σ) (ν : ℝ) (t : ℝ≥0) (ht : 0 < t) {K : ℝ}
    (hK : 0 ≤ K) (y : ℝ) :
    IntegrableOn (fun x => (x - K) * (Real.exp (ν / σ * y - (ν / σ) ^ 2 * (t : ℝ) / 2) *
        (gaussianPDFReal 0 t y * (σ ^ 2)⁻¹ * piHalfFormula 4 σ t (x * σ ^ 2) (y * σ))))
      (Ioi K) ∧
    σ / 2 * Real.exp (σ * y / 2 - ν * (t : ℝ) / 2) *
        ∫ u in Ioi (0 : ℝ), (Ffun σ ν t K u (Real.exp (σ * y / 2 - ν * (t : ℝ) / 2))).re =
      ∫ x in Ioi K, (x - K) * (Real.exp (ν / σ * y - (ν / σ) ^ 2 * (t : ℝ) / 2) *
        (gaussianPDFReal 0 t y * (σ ^ 2)⁻¹ * piHalfFormula 4 σ t (x * σ ^ 2) (y * σ))) := by
  have htR : (0 : ℝ) < t := ht
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hT : (0 : ℝ) < σ ^ 2 * t := by positivity
  set w : ℝ := Real.exp (σ * y / 2 - ν * (t : ℝ) / 2) with hw
  have hwpos : 0 < w := Real.exp_pos _
  set E : ℝ := Real.exp (ν / σ * y - (ν / σ) ^ 2 * (t : ℝ) / 2) with hE
  set G : ℝ → ℂ := fun u => gFun 4 (σ ^ 2 * t) (u - I * (π / 2)) with hG
  have hGc : Continuous G :=
    ((gFun.contDiff 4 (σ ^ 2 * t)).continuous).comp (by fun_prop)
  set a : ℝ := (2 * Real.exp (y * σ) + 2) / σ ^ 2 with ha
  have hapos : 0 < a := by positivity
  set β : ℝ := 4 * Real.exp (y * σ / 2) / σ ^ 2 with hβ
  set cst : ℝ := 8 * √2 * (σ ^ 6)⁻¹ * Real.exp (y * σ * 3 / 2) / √(π * t) with hcst
  -- the substitution `w = e^{σy/2 − νt/2}` in `A`, `B`, `C`
  have hw2 : w ^ 2 * Real.exp (ν * t) = Real.exp (y * σ) := by
    rw [hw, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hw1 : w * Real.exp (ν * t / 2) = Real.exp (y * σ / 2) := by
    rw [hw, ← Real.exp_add]
    congr 1
    ring
  have hw3 : w ^ 3 * Real.exp (ν * 4 * t / 2 - ν * t / 2) = Real.exp (y * σ * 3 / 2) := by
    rw [hw, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hB : Bfun σ ν t w = 2 / (σ * w) * E := by
    have hpow : w ^ (2 * ν / σ ^ 2 - 1) =
        Real.exp ((σ * y / 2 - ν * (t : ℝ) / 2) * (2 * ν / σ ^ 2 - 1)) := by
      rw [hw, Real.exp_mul]
    have hsplit : Real.exp ((σ * y / 2 - ν * (t : ℝ) / 2) * (2 * ν / σ ^ 2 - 1)) *
        Real.exp (ν ^ 2 * t / (2 * σ ^ 2)) = E / w := by
      rw [hE, hw, ← Real.exp_add, ← Real.exp_sub]
      congr 1
      field_simp
      ring
    unfold Bfun
    rw [hpow, mul_assoc, hsplit]
    field_simp
  have hA : ∀ u : ℝ, Afun σ ν t u w = (a : ℂ) + ((β * Real.sinh u : ℝ) : ℂ) * I := by
    intro u
    rw [Afun.eq]
    have h1 : (2 * w ^ 2 * Real.exp (ν * t) + 2) / σ ^ 2 = a := by
      rw [ha, ← hw2]
      ring
    have h2 : 4 * w * Real.exp (ν * t / 2) * Real.sinh u / σ ^ 2 = β * Real.sinh u := by
      rw [hβ, ← hw1]
      ring
    rw [h1, h2]
  have hC : ∀ u : ℝ, Cfun 4 σ ν t u w = ((cst * Real.cosh u : ℝ) : ℂ) * I := by
    intro u
    unfold Cfun
    have hz1 : σ ^ (-2 * ((4 : ℕ) : ℤ) + 2) = (σ ^ 6)⁻¹ := by
      rw [show (-2 * ((4 : ℕ) : ℤ) + 2) = -((6 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
    have hz2 : w ^ (((4 : ℕ) : ℤ) - 1) = w ^ 3 := by
      rw [show (((4 : ℕ) : ℤ) - 1) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
    rw [hz1, hz2, hcst, ← hw3]
    push_cast
    ring
  -- the `(x, u)`-kernel
  set k : ℝ → ℝ → ℂ := fun x u =>
    (((x - K) * (x ^ 4)⁻¹ : ℝ) : ℂ) *
        cexp (-((a : ℂ) + ((β * Real.sinh u : ℝ) : ℂ) * I) / x) *
      (((2 / (σ * w) * E : ℝ) : ℂ) * (((cst * Real.cosh u : ℝ) : ℂ) * I) * G u) with hk
  have hknorm : ∀ x u, ‖k x u‖ = (|(x - K) * (x ^ 4)⁻¹| * Real.exp (-a / x)) *
      (|2 / (σ * w) * E| * |cst| * (Real.cosh u * ‖G u‖)) := by
    intro x u
    have hre : (-((a : ℂ) + ((β * Real.sinh u : ℝ) : ℂ) * I) / (x : ℂ)).re = -a / x := by
      rw [Complex.div_ofReal_re]
      simp
    simp only [hk, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, hre,
      Complex.norm_I, mul_one, abs_mul, abs_of_pos (Real.cosh_pos u)]
    ring
  have hkm : Measurable (Function.uncurry k) := by
    simp only [hk]
    fun_prop
  have hF1 : IntegrableOn (fun x : ℝ => |(x - K) * (x ^ 4)⁻¹| * Real.exp (-a / x)) (Ioi K) := by
    have hbase := (integrableOn_inv_pow_exp_neg_div (p := 3) (by norm_num) hapos).mono_set
      (Ioi_subset_Ioi hK)
    refine Integrable.mono' hbase (by fun_prop : Measurable _).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_)
    have hx0 : 0 < x := lt_of_le_of_lt hK hx
    have hxK : 0 ≤ x - K := sub_nonneg.mpr (le_of_lt hx)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have h3 : x ^ (-((3 : ℕ) : ℤ)) = x * (x ^ 4)⁻¹ := by
      rw [zpow_neg, zpow_natCast]
      field_simp
    rw [h3]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hF2 : IntegrableOn
      (fun u : ℝ => |2 / (σ * w) * E| * |cst| * (Real.cosh u * ‖G u‖)) (Ioi 0) :=
    ((GFunDecay.integrable_cosh_mul_norm_gFun_piHalf (p := 4)
      (Or.inr (Or.inr rfl)) hT).const_mul _).integrableOn
  have hkint : Integrable (Function.uncurry k)
      ((volume.restrict (Ioi K)).prod (volume.restrict (Ioi 0))) := by
    refine (Integrable.mul_prod hF1 hF2).mono' hkm.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    exact (hknorm z.1 z.2).le
  have hkre : Integrable (Function.uncurry fun x u => (k x u).re)
      ((volume.restrict (Ioi K)).prod (volume.restrict (Ioi 0))) := hkint.re
  -- `F` is the `x`-integral of the kernel
  have hF : ∀ u : ℝ, Ffun σ ν t K u w = ∫ x in Ioi K, k x u := by
    intro u
    have hS : SfunC K 4 (Afun σ ν t u w) = ∫ x in Ioi K, (((x - K) * (x ^ 4)⁻¹ : ℝ) : ℂ) *
        cexp (-((a : ℂ) + ((β * Real.sinh u : ℝ) : ℂ) * I) / x) := by
      unfold SfunC
      rw [hA u]
      refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
      simp only [zpow_neg, zpow_natCast]
    simp only [hk]
    rw [integral_mul_const, ← hS, ← hC u, ← hB]
    unfold Ffun
    simp only [hG]
    ring
  -- the `u`-integral of the kernel is the tilted π/2-density
  have hinner : ∀ x ∈ Ioi K, ∫ u in Ioi (0 : ℝ), (k x u).re =
      2 / (σ * w) * ((x - K) * (E *
        (gaussianPDFReal 0 t y * (σ ^ 2)⁻¹ * piHalfFormula 4 σ t (x * σ ^ 2) (y * σ)))) := by
    intro x hx
    have hx0 : 0 < x := lt_of_le_of_lt hK hx
    have hxσ : 0 < x * σ ^ 2 := by positivity
    have hpt : ∀ u : ℝ, (k x u).re =
        ((x - K) * (x ^ 4)⁻¹ * (2 / (σ * w) * E) * cst * Real.exp (-a / x)) *
          (Real.cosh u *
            (I * cexp (-I * ((4 / ((x * σ ^ 2 : ℝ) : ℂ)) * Real.exp (y * σ / 2) *
              Real.sinh u)) * gFun 4 (t * σ ^ 2) (u - I * (π / 2))).re) := by
      intro u
      have hexp : cexp (-((a : ℂ) + ((β * Real.sinh u : ℝ) : ℂ) * I) / x) =
          ((Real.exp (-a / x) : ℝ) : ℂ) *
            cexp (-I * ((4 / ((x * σ ^ 2 : ℝ) : ℂ)) * Real.exp (y * σ / 2) *
              Real.sinh u)) := by
        rw [Complex.ofReal_exp, ← Complex.exp_add]
        congr 1
        rw [hβ]
        push_cast
        field_simp
        ring
      have hkk : k x u =
          (((x - K) * (x ^ 4)⁻¹ * (2 / (σ * w) * E) * cst * Real.exp (-a / x) *
            Real.cosh u : ℝ) : ℂ) *
          (I * cexp (-I * ((4 / ((x * σ ^ 2 : ℝ) : ℂ)) * Real.exp (y * σ / 2) *
            Real.sinh u)) * gFun 4 (t * σ ^ 2) (u - I * (π / 2))) := by
        simp only [hk, hG]
        rw [hexp, mul_comm (σ ^ 2) (t : ℝ)]
        push_cast
        ring
      rw [hkk, Complex.re_ofReal_mul]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hpt u), integral_const_mul,
      piHalfFormula, ite_eq_left hxσ]
    generalize (∫ u in Ioi (0 : ℝ), Real.cosh u *
      (I * cexp (-I * ((4 / ((x * σ ^ 2 : ℝ) : ℂ)) * Real.exp (y * σ / 2) *
        Real.sinh u)) * gFun 4 (t * σ ^ 2) (u - I * (π / 2))).re) = J
    have hbig : Real.exp (y * σ * (((4 : ℕ) : ℝ) - 1) / 2 + (y * σ) ^ 2 / (2 * (t * σ ^ 2)) -
        2 * (Real.exp (y * σ) + 1) / (x * σ ^ 2)) =
        Real.exp (y * σ * 3 / 2) * Real.exp (y ^ 2 / (2 * t)) * Real.exp (-a / x) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      rw [ha]
      push_cast
      field_simp
      ring
    have hs : √(π * t) ≠ 0 := by positivity
    have hgauss : gaussianPDFReal 0 t y =
        √2 / (2 * √(π * t)) * (Real.exp (y ^ 2 / (2 * t)))⁻¹ := by
      have hsq : √(2 * π * t) = √2 * √(π * t) := by
        rw [mul_assoc, Real.sqrt_mul (by norm_num)]
      have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
      have h20 : √2 ≠ 0 := by positivity
      have hinv : (√2 * √(π * t))⁻¹ = √2 / (2 * √(π * t)) := by
        field_simp
        linarith
      have harg : -(y - 0) ^ 2 / (2 * (t : ℝ)) = -(y ^ 2 / (2 * t)) := by ring
      rw [gaussianPDFReal_def]
      simp only
      rw [harg, Real.exp_neg, hsq, hinv]
    rw [hbig, hgauss, hcst]
    field_simp
    ring
  have hswap : ∫ u in Ioi (0 : ℝ), (Ffun σ ν t K u w).re =
      ∫ x in Ioi K, ∫ u in Ioi (0 : ℝ), (k x u).re := by
    rw [integral_integral_swap hkre]
    refine integral_congr_ae ?_
    filter_upwards [hkint.prod_left_ae] with u hu
    rw [hF u]
    exact (Complex.reCLM.integral_comp_comm hu).symm
  have hcongr : ∫ x in Ioi K, ∫ u in Ioi (0 : ℝ), (k x u).re =
      2 / (σ * w) * ∫ x in Ioi K, (x - K) * (E *
        (gaussianPDFReal 0 t y * (σ ^ 2)⁻¹ * piHalfFormula 4 σ t (x * σ ^ 2) (y * σ))) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hinner, integral_const_mul]
  constructor
  · have h1 : Integrable (fun x => ∫ u in Ioi (0 : ℝ), (k x u).re)
        (volume.restrict (Ioi K)) := hkre.integral_prod_left
    refine (h1.const_mul (σ * w / 2)).congr ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_)
    simp only
    rw [hinner x hx]
    field_simp
  · have hjac : σ / 2 * w * (2 / (σ * w)) = 1 := by
      field_simp
    rw [hswap, hcongr, ← mul_assoc, hjac, one_mul]

/-! ### The substitution `w = e^{σy/2 − c}` -/

/-- Paper p. 1090: the change of variables `w = e^{σ y / 2 − c}`, `dw = (σ w / 2) dy`, mapping
`ℝ` onto `(0, ∞)`.  No integrability is needed (both sides are Bochner integrals). -/
theorem integral_Ioi_comp_exp_affine {σ : ℝ} (hσ : 0 < σ) (c : ℝ) (R : ℝ → ℝ) :
    ∫ w in Ioi (0 : ℝ), R w =
      ∫ y : ℝ, σ / 2 * Real.exp (σ * y / 2 - c) * R (Real.exp (σ * y / 2 - c)) := by
  have himg : (fun y : ℝ => Real.exp (σ * y / 2 - c)) '' univ = Ioi 0 := by
    ext w
    simp only [image_univ, mem_range, mem_Ioi]
    constructor
    · rintro ⟨y, rfl⟩
      exact Real.exp_pos _
    · intro hw
      refine ⟨2 / σ * (Real.log w + c), ?_⟩
      have h : σ * (2 / σ * (Real.log w + c)) / 2 - c = Real.log w := by
        field_simp
        ring
      rw [h, Real.exp_log hw]
  have hderiv : ∀ y ∈ (univ : Set ℝ),
      HasDerivWithinAt (fun y : ℝ => Real.exp (σ * y / 2 - c))
        (σ / 2 * Real.exp (σ * y / 2 - c)) univ y := by
    intro y _
    have h : HasDerivAt (fun y : ℝ => σ * y / 2 - c) (σ / 2) y := by
      simpa using (((hasDerivAt_id y).const_mul σ).div_const 2).sub_const c
    exact (h.exp.congr_deriv (by ring)).hasDerivWithinAt
  have hinj : InjOn (fun y : ℝ => Real.exp (σ * y / 2 - c)) univ := by
    intro y1 _ y2 _ h
    have h' : σ * y1 / 2 - c = σ * y2 / 2 - c := Real.exp_injective h
    have h'' : σ * y1 = σ * y2 := by linarith
    exact mul_left_cancel₀ hσ.ne' h''
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hderiv hinj R
  rw [himg] at h
  rw [h, Measure.restrict_univ]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [smul_eq_mul]
  rw [abs_of_pos (by positivity)]

end Lyasoff2016
