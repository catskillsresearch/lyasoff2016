/-
Moment determinacy for probability measures on `[0, ∞)` with a finite exponential moment.

Used in the proof of Dufresne's theorem (`FokkerPlanck.lean`): the reciprocal of the perpetuity
`∫₀^∞ e^{σ W_s + ν s} ds` has the integer moments of a Gamma law, and a law on `[0, ∞)` whose
moment generating function is finite near `0` is determined by its integer moments.
-/
module

public import Mathlib


@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/-- Two probability measures on `ℝ` whose moment generating functions are finite on `(-∞, a)`
and agree on `(0, a)` are equal (identity theorem for the complex mgf on the strip `Re z < a`,
then uniqueness of characteristic functions). -/
theorem measure_eq_of_mgf_eqOn {ρ₁ ρ₂ : Measure ℝ} [IsProbabilityMeasure ρ₁]
    [IsProbabilityMeasure ρ₂] {a : ℝ} (ha : 0 < a)
    (h₁ : ∀ s < a, Integrable (fun y => Real.exp (s * y)) ρ₁)
    (h₂ : ∀ s < a, Integrable (fun y => Real.exp (s * y)) ρ₂)
    (heq : ∀ s ∈ Ioo 0 a, mgf id ρ₁ s = mgf id ρ₂ s) : ρ₁ = ρ₂ := by
  have hsub₁ : Iio a ⊆ interior (integrableExpSet id ρ₁) :=
    interior_maximal (fun s hs => h₁ s hs) isOpen_Iio
  have hsub₂ : Iio a ⊆ interior (integrableExpSet id ρ₂) :=
    interior_maximal (fun s hs => h₂ s hs) isOpen_Iio
  have hX : AnalyticOnNhd ℂ (complexMGF id ρ₁) {z | z.re ∈ Iio a} :=
    analyticOnNhd_complexMGF.mono fun z hz => hsub₁ hz
  have hY : AnalyticOnNhd ℂ (complexMGF id ρ₂) {z | z.re ∈ Iio a} :=
    analyticOnNhd_complexMGF.mono fun z hz => hsub₂ hz
  have hpre : IsPreconnected {z : ℂ | z.re ∈ Iio a} :=
    ((convex_Iio a).linear_preimage Complex.reLm).isPreconnected
  have key : EqOn (complexMGF id ρ₁) (complexMGF id ρ₂) {z | z.re ∈ Iio a} := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hX hY hpre
      (z₀ := ((a / 2 : ℝ) : ℂ)) (by simp only [mem_ofPred_eq, Complex.ofReal_re, mem_Iio]; linarith)
      ?_
    have h_real : ∃ᶠ (x : ℝ) in 𝓝[≠] (a / 2), complexMGF id ρ₁ x = complexMGF id ρ₂ x := by
      refine Eventually.frequently ?_
      have hmem : Ioo 0 a ∈ 𝓝[≠] (a / 2) :=
        mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith))
      filter_upwards [hmem] with y hy
      rw [complexMGF_ofReal, complexMGF_ofReal, heq y hy]
    rw [frequently_iff_seq_forall] at h_real ⊢
    obtain ⟨xs, hx_tendsto, hx_eq⟩ := h_real
    refine ⟨fun n ↦ xs n, ?_, fun n ↦ ?_⟩
    · rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
      constructor
      · rw [Filter.tendsto_ofReal_iff]
        exact hx_tendsto.1
      · filter_upwards [hx_tendsto.2] with n hn
        simp only [mem_compl_iff, mem_singleton_iff] at hn ⊢
        exact fun h => hn (by exact_mod_cast h)
    · simp [hx_eq]
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [← complexMGF_id_mul_I, ← complexMGF_id_mul_I]
  exact key (by simp [ha])

/-- For a measure concentrated on `[0, ∞)` and `s ≥ 0`, the exponential moment is the power
series of the integer moments (monotone convergence). -/
theorem lintegral_exp_eq_tsum_moments {ρ : Measure ℝ} (hpos : ∀ᵐ y ∂ρ, 0 ≤ y) {s : ℝ}
    (hs : 0 ≤ s) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (s * y)) ∂ρ =
      ∑' n : ℕ, ENNReal.ofReal (s ^ n / (n.factorial : ℝ)) * ∫⁻ y, ENNReal.ofReal (y ^ n) ∂ρ := by
  have hterm : ∀ n : ℕ, ∫⁻ y, ENNReal.ofReal (s ^ n / (n.factorial : ℝ)) * ENNReal.ofReal (y ^ n) ∂ρ =
      ENNReal.ofReal (s ^ n / (n.factorial : ℝ)) * ∫⁻ y, ENNReal.ofReal (y ^ n) ∂ρ := fun n =>
    lintegral_const_mul _ (by fun_prop)
  simp_rw [← hterm]
  rw [← lintegral_tsum (fun n => by fun_prop)]
  refine lintegral_congr_ae ?_
  filter_upwards [hpos] with y hy
  have hsum : Summable fun n : ℕ => (s * y) ^ n / (n.factorial : ℝ) :=
    Real.summable_pow_div_factorial (s * y)
  have hexp : Real.exp (s * y) = ∑' n : ℕ, (s * y) ^ n / (n.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [hexp, ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
  refine tsum_congr fun n => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [mul_pow]
  ring

/-- **Moment determinacy.** Two probability measures on `ℝ` concentrated on `[0, ∞)` with the
same integer moments coincide as soon as one of them has a finite exponential moment
`∫ e^{s y}` for every `0 ≤ s < a`. -/
theorem measure_eq_of_moments {ρ₁ ρ₂ : Measure ℝ} [IsProbabilityMeasure ρ₁]
    [IsProbabilityMeasure ρ₂] (hpos₁ : ∀ᵐ y ∂ρ₁, 0 ≤ y) (hpos₂ : ∀ᵐ y ∂ρ₂, 0 ≤ y)
    {a : ℝ} (ha : 0 < a)
    (hmom : ∀ n : ℕ, ∫⁻ y, ENNReal.ofReal (y ^ n) ∂ρ₁ = ∫⁻ y, ENNReal.ofReal (y ^ n) ∂ρ₂)
    (hfin : ∀ s ∈ Ico 0 a, ∫⁻ y, ENNReal.ofReal (Real.exp (s * y)) ∂ρ₂ ≠ ∞) : ρ₁ = ρ₂ := by
  have hL : ∀ s : ℝ, 0 ≤ s → ∫⁻ y, ENNReal.ofReal (Real.exp (s * y)) ∂ρ₁ =
      ∫⁻ y, ENNReal.ofReal (Real.exp (s * y)) ∂ρ₂ := fun s hs => by
    rw [lintegral_exp_eq_tsum_moments hpos₁ hs, lintegral_exp_eq_tsum_moments hpos₂ hs]
    simp_rw [hmom]
  have hmeas : ∀ s : ℝ, Measurable fun y : ℝ => Real.exp (s * y) := fun s => by fun_prop
  have hint : ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ], (∀ᵐ y ∂ρ, 0 ≤ y) →
      (∀ s ∈ Ico 0 a, ∫⁻ y, ENNReal.ofReal (Real.exp (s * y)) ∂ρ ≠ ∞) →
      ∀ s < a, Integrable (fun y => Real.exp (s * y)) ρ := by
    intro ρ _ hpos hfinρ s hs
    rcases le_or_gt 0 s with h0 | h0
    · refine ⟨(hmeas s).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => (Real.exp_pos _).le)]
      exact lt_top_iff_ne_top.2 (hfinρ s ⟨h0, hs⟩)
    · refine Integrable.mono' (integrable_const (1 : ℝ)) (hmeas s).aestronglyMeasurable ?_
      filter_upwards [hpos] with y hy
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg h0.le hy)
  have h₂ := hint ρ₂ hpos₂ hfin
  have h₁ := hint ρ₁ hpos₁ (fun s hs => by rw [hL s hs.1]; exact hfin s hs)
  refine measure_eq_of_mgf_eqOn ha h₁ h₂ fun s hs => ?_
  simp only [mgf, id_eq]
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => (Real.exp_pos _).le)
      (hmeas s).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => (Real.exp_pos _).le)
      (hmeas s).aestronglyMeasurable, hL s hs.1.le]

/-- First-order lower bound for a negative power: `1 - p u ≤ (1 + u)^{-p}`. -/
lemma one_sub_mul_le_one_add_rpow_neg {u p : ℝ} (hu : 0 ≤ u) (hp : 0 ≤ p) :
    1 - p * u ≤ (1 + u) ^ (-p) := by
  have h1 : (0 : ℝ) < 1 + u := by linarith
  rw [Real.rpow_def_of_pos h1]
  have hlog : Real.log (1 + u) ≤ u := by
    have := Real.log_le_sub_one_of_pos h1
    linarith
  have h2 : -p * u ≤ Real.log (1 + u) * -p := by nlinarith
  calc 1 - p * u = -p * u + 1 := by ring
    _ ≤ Real.log (1 + u) * -p + 1 := by linarith
    _ ≤ Real.exp (Real.log (1 + u) * -p) := Real.add_one_le_exp _

/-- Second-order upper bound for a negative power:
`(1 + u)^{-p} ≤ 1 - p u + p (p + 1) u² / 2` for `u ≥ 0`. -/
lemma one_add_rpow_neg_le {u p : ℝ} (hu : 0 ≤ u) (hp : 0 ≤ p) :
    (1 + u) ^ (-p) ≤ 1 - p * u + p * (p + 1) / 2 * u ^ 2 := by
  let h : ℝ → ℝ := fun v => 1 - p * v + p * (p + 1) / 2 * v ^ 2 - (1 + v) ^ (-p)
  have hd : ∀ v : ℝ, 0 ≤ v → HasDerivAt h
      (-p + p * (p + 1) * v + p * (1 + v) ^ (-(p + 1))) v := by
    intro v hv
    have hv1 : (1 + v) ≠ 0 := by linarith
    have hr : HasDerivAt (fun v : ℝ => (1 + v) ^ (-p)) (-p * (1 + v) ^ (-p - 1)) v := by
      have := ((hasDerivAt_id v).const_add 1).rpow_const (p := -p) (Or.inl hv1)
      simpa using this
    have hq : HasDerivAt (fun v : ℝ => 1 - p * v + p * (p + 1) / 2 * v ^ 2)
        (-p + p * (p + 1) * v) v := by
      have h1 : HasDerivAt (fun v : ℝ => p * v) p v := by
        simpa using (hasDerivAt_id v).const_mul p
      have h2 : HasDerivAt (fun v : ℝ => p * (p + 1) / 2 * v ^ 2) (p * (p + 1) / 2 * (2 * v)) v := by
        simpa using (hasDerivAt_pow 2 v).const_mul (p * (p + 1) / 2)
      have := ((hasDerivAt_const v (1 : ℝ)).sub h1).add h2
      convert this using 1
      ring
    have := hq.sub hr
    convert this using 1
    have : -p - 1 = -(p + 1) := by ring
    rw [this]
    ring
  have hmono : MonotoneOn h (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun v hv => (hd v hv).continuousAt.continuousWithinAt)
      (fun v hv => ?_) (fun v hv => ?_)
    · rw [interior_Ici] at hv
      exact (hd v hv.le).differentiableAt.differentiableWithinAt
    · rw [interior_Ici] at hv
      rw [(hd v hv.le).deriv]
      have hb := one_sub_mul_le_one_add_rpow_neg hv.le (by linarith : (0 : ℝ) ≤ p + 1)
      nlinarith
  have h0 : h 0 = 0 := by simp [h]
  have := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hu) hu
  rw [h0] at this
  simp only [h] at this
  linarith

/-- Taylor bounds for `x ↦ x^{-p}` at `x > 0` with nonnegative increment `c`. -/
lemma rpow_neg_add_bounds {x c p : ℝ} (hx : 0 < x) (hc : 0 ≤ c) (hp : 0 ≤ p) :
    x ^ (-p) - p * c * x ^ (-p - 1) ≤ (x + c) ^ (-p) ∧
      (x + c) ^ (-p) ≤ x ^ (-p) - p * c * x ^ (-p - 1) + p * (p + 1) / 2 * c ^ 2 * x ^ (-p - 2) := by
  have hu : 0 ≤ c / x := div_nonneg hc hx.le
  have hfac : (x + c) ^ (-p) = x ^ (-p) * (1 + c / x) ^ (-p) := by
    rw [← Real.mul_rpow hx.le (by linarith)]
    congr 1
    field_simp
  have hxp : 0 < x ^ (-p) := Real.rpow_pos_of_pos hx _
  have h1 : x ^ (-p - 1) = x ^ (-p) / x := Real.rpow_sub_one hx.ne' _
  have h2 : x ^ (-p - 2) = x ^ (-p) / x ^ 2 := by
    rw [Real.rpow_sub hx, Real.rpow_two]
  constructor
  · rw [hfac, h1]
    have := mul_le_mul_of_nonneg_left (one_sub_mul_le_one_add_rpow_neg hu hp) hxp.le
    calc x ^ (-p) - p * c * (x ^ (-p) / x) = x ^ (-p) * (1 - p * (c / x)) := by
          field_simp
      _ ≤ _ := this
  · rw [hfac, h1, h2]
    have := mul_le_mul_of_nonneg_left (one_add_rpow_neg_le hu hp) hxp.le
    calc x ^ (-p) * (1 + c / x) ^ (-p) ≤ x ^ (-p) * (1 - p * (c / x) + p * (p + 1) / 2 * (c / x) ^ 2) :=
          this
      _ = _ := by
          field_simp

end Lyasoff2016
