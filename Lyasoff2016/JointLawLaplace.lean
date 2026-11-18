/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Integrated distributional Fokker–Planck equation and inverse-argument Laplace transform
for `(∫₀ᵗ e^{2 W_s} ds, W_t)`.
-/
module

public import Lyasoff2016.DistFokkerPlanck
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

section DistFPIntegrated

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- For a Brownian motion `W` and `t > 0`, `expInt W 2 0 t ω > 0` almost surely. -/
lemma expInt_two_pos_ae (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ ω ∂P, 0 < expInt W 2 0 t ω := by
  filter_upwards [hW.cont] with ω hcont
  have hcontR : Continuous fun s : ℝ => Real.exp (2 * W s.toNNReal ω) :=
    Real.continuous_exp.comp (continuous_const.mul (hcont.comp continuous_real_toNNReal))
  have hpos : ∀ s ∈ Icc (0 : ℝ) (t : ℝ), 0 < Real.exp (2 * W s.toNNReal ω) := fun _ _ =>
    Real.exp_pos _
  simpa [expInt] using intervalIntegral.integral_pos ht hcontR.continuousOn
    (fun s hs => (hpos s (Ioc_subset_Icc_self hs)).le) ⟨0, ⟨le_rfl, ht.le⟩, Real.exp_pos _⟩

private lemma integral_Ioi_exp_neg_div {v x : ℝ} (hx : 0 < x) :
    ∫ u in Ioi v, Real.exp (-u / x) = x * Real.exp (-v / x) := by
  have hderiv : ∀ u ∈ Ici v,
      HasDerivAt (fun u' => -x * Real.exp (-u' / x)) (Real.exp (-u / x)) u := by
    intro u _
    have h1 : HasDerivAt (fun u' : ℝ => -u' / x) (-1 / x) u := by
      have h := ((hasDerivAt_id' u).neg).div_const x
      simpa using h
    convert h1.exp.const_mul (-x) using 1
    field_simp [hx.ne']
  have hlim : Tendsto (fun u => -x * Real.exp (-u / x)) atTop (nhds 0) := by
    have ht : Tendsto (fun u : ℝ => -u / x) atTop atBot := by
      rw [show (fun u : ℝ => -u / x) = fun u => (-1 / x) * u by funext u; ring]
      exact Tendsto.const_mul_atTop_of_neg
        (by rw [neg_div]; exact neg_neg_iff_pos.mpr (one_div_pos.mpr hx)) tendsto_id
    have he := Real.tendsto_exp_atBot.comp ht
    simpa [Function.comp_def] using he.const_mul (-x)
  have hint := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hderiv
    (fun u _ => (Real.exp_pos _).le) hlim
  simpa [sub_neg_eq_add] using hint

private lemma integral_Ioi_mul_exp_neg_div {v x : ℝ} (hv : 0 ≤ v) (hx : 0 < x) :
    ∫ u in Ioi v, u * Real.exp (-u / x) = (v * x + x ^ 2) * Real.exp (-v / x) := by
  have hderiv : ∀ u ∈ Ici v,
      HasDerivAt (fun u' => -(u' * x + x ^ 2) * Real.exp (-u' / x)) (u * Real.exp (-u / x)) u := by
    intro u _
    have h1 : HasDerivAt (fun u' : ℝ => -(u' * x + x ^ 2)) (-x) u := by
      have h := (((hasDerivAt_id' u).mul_const x).add_const (x ^ 2)).neg
      convert h using 1; ring
    have h2 : HasDerivAt (fun u' : ℝ => -u' / x) (-1 / x) u := by
      have h := ((hasDerivAt_id' u).neg).div_const x
      simpa using h
    convert h1.fun_mul h2.exp using 1
    field_simp [hx.ne']; ring
  have hlim : Tendsto (fun u => -(u * x + x ^ 2) * Real.exp (-u / x)) atTop (nhds 0) := by
    have hpow : Tendsto (fun y : ℝ => (y * x ^ 2 + x ^ 2) * Real.exp (-y)) atTop (nhds 0) := by
      have h1 : Tendsto (fun y : ℝ => y * Real.exp (-y)) atTop (nhds 0) := by
        simpa [Real.exp_neg, div_eq_mul_inv] using
          (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1)
      have h2 : Tendsto (fun y : ℝ => Real.exp (-y)) atTop (nhds 0) :=
        Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
      have hsum := (h1.const_mul (x ^ 2)).add (h2.const_mul (x ^ 2))
      have hsum0 : x ^ 2 * (0 : ℝ) + x ^ 2 * 0 = 0 := by ring
      rw [hsum0] at hsum
      refine hsum.congr (fun y => ?_)
      ring
    have hscale : Tendsto (fun u : ℝ => u / x) atTop atTop :=
      (tendsto_id).atTop_div_const hx
    have hc := (hpow.comp hscale).neg
    rw [neg_zero] at hc
    refine hc.congr (fun u => ?_)
    simp only [Function.comp_def]
    field_simp [hx.ne']
  have hint := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hderiv
    (fun u hu => mul_nonneg (hv.trans hu.out.le) (Real.exp_pos _).le) hlim
  convert hint using 1; ring

/-- Integrated distributional Fokker–Planck identity for `(expInt W 2 0 t, W t)`:
for every `t > 0`, `v > 0`, and `ψ ∈ C_c^3(ℝ)`,
`E[((2 v + 1 - exp(2 W_t)) / X_t * ψ(W_t) + 2 ψ'(W_t)) * exp(-v / X_t)] = 0`. -/
theorem jointLaw_two_dist_fp [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W)
    (t : ℝ≥0) (ht : 0 < t) {v : ℝ} (hv : 0 < v)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 3 ψ) (hψC : HasCompactSupport ψ) :
    ∫ ω, ((2 * v + 1 - Real.exp (2 * W t ω)) / expInt W 2 0 t ω * ψ (W t ω) +
        2 * deriv ψ (W t ω)) * Real.exp (-v / expInt W 2 0 t ω) ∂P = 0 := by
  let B : ℝ≥0 → Ω → ℝ := hW.toIsPreBrownianReal.mk W
  have hBmeas : ∀ s, Measurable (B s) := hW.toIsPreBrownianReal.measurable_mk
  have hBcont : ∀ ω, Continuous (B · ω) := hW.toIsPreBrownianReal.continuous_mk
  have hBpre : IsPreBrownianReal B P :=
    hW.toIsPreBrownianReal.isBrownianReal_mk.toIsPreBrownianReal
  have hBbm : IsBM P B := ⟨hBpre, Eventually.of_forall hBcont⟩
  have hBW : ∀ᵐ ω ∂P, ∀ s, B s ω = W s ω := hW.mk_ae_forall_eq
  have hBW_int : ∫ ω, ((2 * v + 1 - Real.exp (2 * W t ω)) / expInt W 2 0 t ω * ψ (W t ω) +
        2 * deriv ψ (W t ω)) * Real.exp (-v / expInt W 2 0 t ω) ∂P =
      ∫ ω, ((2 * v + 1 - Real.exp (2 * B t ω)) / expInt B 2 0 t ω * ψ (B t ω) +
        2 * deriv ψ (B t ω)) * Real.exp (-v / expInt B 2 0 t ω) ∂P := by
    refine integral_congr_ae (hBW.mono fun ω hω => ?_)
    dsimp only
    have hX : expInt W 2 0 t ω = expInt B 2 0 t ω := by
      simp only [expInt]; exact intervalIntegral.integral_congr fun s _ => by rw [hω s.toNNReal]
    rw [hX, ← hω t]
  rw [hBW_int]
  obtain ⟨Cψ, R, hCψ0, _, hsupp, hψ0, hψ1, _, _⟩ := contDiff_three_compactSupport_bounds hψ hψC
  let E2 := Real.exp (2 * R)
  have h20 : ∀ y, Real.exp (2 * y) * |ψ y| ≤ E2 * Cψ := fun y => by
    by_cases hy : R ≤ |y|
    · obtain ⟨h0, _, _, _⟩ := hsupp y hy; simp [h0]; positivity
    · have hylt : y ≤ R := (le_abs_self y).trans (not_le.mp hy).le
      exact mul_le_mul (Real.exp_le_exp.mpr (by linarith)) (hψ0 y) (abs_nonneg _) (Real.exp_pos _).le
  let g' : ℝ → Ω → ℝ := fun u ω =>
    if 0 < expInt B 2 0 t ω then
      ((-4 / expInt B 2 0 t ω + 2 * u / expInt B 2 0 t ω ^ 2) * ψ (B t ω) +
        2 / expInt B 2 0 t ω * deriv ψ (B t ω) +
        ((1 - Real.exp (2 * B t ω)) / expInt B 2 0 t ω ^ 2 +
          2 / expInt B 2 0 t ω) * ψ (B t ω)) * Real.exp (-u / expInt B 2 0 t ω)
    else 0
  have hg'_eq : ∀ u > 0, ∀ ω,
      0 < expInt B 2 0 t ω →
      g' u ω = u⁻¹ * (2 * expInt B 2 0 t ω ^ 2 * expInvCut₂ u (expInt B 2 0 t ω) * ψ (B t ω) +
        2 * expInt B 2 0 t ω * expInvCut₁ u (expInt B 2 0 t ω) * deriv ψ (B t ω) +
        (1 + 2 * expInt B 2 0 t ω - Real.exp (2 * B t ω)) *
          expInvCut₁ u (expInt B 2 0 t ω) * ψ (B t ω)) := by
    intro u hu ω hx
    have hx' : ¬ (expInt B 2 0 t ω ≤ 0) := not_le.mpr hx
    simp only [g', hx, ↓reduceIte, expInvCut₁, expInvCut₂]
    field_simp [hu.ne', hx.ne']
    ring
  have hXpos := expInt_two_pos_ae B hBbm t ht
  have hslice_zero : ∀ u ∈ Ioi v, ∫ ω, g' u ω ∂P = 0 := by
    intro u hu
    have hu0 : 0 < u := hv.trans hu
    have hae : g' u =ᵐ[P] fun ω => u⁻¹ * (2 * expInt B 2 0 t ω ^ 2 * expInvCut₂ u (expInt B 2 0 t ω) * ψ (B t ω) +
        2 * expInt B 2 0 t ω * expInvCut₁ u (expInt B 2 0 t ω) * deriv ψ (B t ω) +
        (1 + 2 * expInt B 2 0 t ω - Real.exp (2 * B t ω)) *
          expInvCut₁ u (expInt B 2 0 t ω) * ψ (B t ω)) :=
      hXpos.mono fun ω hω => hg'_eq u hu0 ω hω
    rw [integral_congr_ae hae, integral_const_mul,
      jointLaw_two_fp_u B hBbm t ht hu0 hψ hψC, mul_zero]
  have hX_meas : Measurable (expInt B 2 0 t) := measurable_expInt_bm hBmeas hBcont 2 t
  have hXneg1 : Integrable (fun ω => (expInt B 2 0 t ω) ^ (-1 : ℤ)) P :=
    expInt_zpow_neg_integrable P B hBbm 2 t (by norm_num) ht 1
  let Bω : Ω → ℝ := fun ω =>
    if 0 < expInt B 2 0 t ω then
      (4 * Cψ + 2 * Cψ + (1 + E2) * Cψ + 2 * Cψ) * (1 + (expInt B 2 0 t ω)⁻¹) +
        2 * Cψ * (v * (expInt B 2 0 t ω)⁻¹ + 1)
    else 0
  have hBω_int : Integrable Bω P := by
    have hinv : Integrable (fun ω => if 0 < expInt B 2 0 t ω then (expInt B 2 0 t ω)⁻¹ else 0) P := by
      refine hXneg1.congr (hXpos.mono fun ω hω => ?_)
      simp [hω]
    have h1 : Integrable (fun ω => if 0 < expInt B 2 0 t ω then (1 : ℝ) else 0) P :=
      (integrable_const (1 : ℝ)).congr (hXpos.mono fun ω hω => by simp [hω])
    have heq : Bω = fun ω =>
        (4 * Cψ + 2 * Cψ + (1 + E2) * Cψ + 2 * Cψ) *
            ((if 0 < expInt B 2 0 t ω then (1 : ℝ) else 0) +
             (if 0 < expInt B 2 0 t ω then (expInt B 2 0 t ω)⁻¹ else 0)) +
          2 * Cψ * (v * (if 0 < expInt B 2 0 t ω then (expInt B 2 0 t ω)⁻¹ else 0) +
             (if 0 < expInt B 2 0 t ω then (1 : ℝ) else 0)) := by
      funext ω
      by_cases hω : 0 < expInt B 2 0 t ω <;> simp [Bω, hω]
    rw [heq]
    exact ((h1.add hinv).const_mul _).add (((hinv.const_mul v).add h1).const_mul _)
  have h_inner_abs : ∀ ω, 0 < expInt B 2 0 t ω →
      IntegrableOn (fun u => g' u ω) (Ioi v) ∧
      ∫ u in Ioi v, |g' u ω| ≤ Bω ω := by
    intro ω hx
    set x := expInt B 2 0 t ω
    set y := B t ω
    have h1 : IntegrableOn (fun u => Real.exp (-u / x)) (Ioi v) := by
      have hi := integral_Ioi_exp_neg_div (v := v) hx
      by_contra H
      have : x * Real.exp (-v / x) = 0 := by rw [← hi, integral_undef H]
      exact (mul_pos hx (Real.exp_pos _)).ne' this
    have h2 : IntegrableOn (fun u => u * Real.exp (-u / x)) (Ioi v) := by
      have hi := integral_Ioi_mul_exp_neg_div hv.le hx
      by_contra H
      have : (v * x + x ^ 2) * Real.exp (-v / x) = 0 := by rw [← hi, integral_undef H]
      have hpos : 0 < (v * x + x ^ 2) * Real.exp (-v / x) := by positivity
      exact hpos.ne' this
    let A₁ : ℝ := (4 * Cψ + 2 * Cψ + 2 * Cψ) / x + (Cψ + E2 * Cψ) / x ^ 2
    let A₂ : ℝ := 2 * Cψ / x ^ 2
    have hdom_u : ∀ u ∈ Ioi v, |g' u ω| ≤ A₁ * Real.exp (-u / x) + A₂ * (u * Real.exp (-u / x)) := by
      intro u hu
      have hu0 : 0 ≤ u := (hv.trans hu).le
      have hgu : g' u ω = ((-4 / x + 2 * u / x ^ 2) * ψ y + 2 / x * deriv ψ y +
          ((1 - Real.exp (2 * y)) / x ^ 2 + 2 / x) * ψ y) * Real.exp (-u / x) := by
        simp only [g', hx, ↓reduceIte, x, y]
      rw [hgu, abs_mul, abs_of_pos (Real.exp_pos _)]
      have ht1 : |(-4 / x + 2 * u / x ^ 2) * ψ y| ≤ (4 * Cψ) / x + (2 * Cψ / x ^ 2) * u := by
        rw [abs_mul]
        calc |-4 / x + 2 * u / x ^ 2| * |ψ y|
            ≤ (4 / x + 2 * u / x ^ 2) * Cψ := by
              refine mul_le_mul ((abs_add_le _ _).trans (add_le_add ?_ ?_)) (hψ0 y) (abs_nonneg _)
                (by positivity)
              · rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos hx]
              · rw [abs_div, abs_mul, abs_of_pos two_pos, abs_of_nonneg hu0,
                  abs_of_pos (sq_pos_of_pos hx)]
          _ = (4 * Cψ) / x + (2 * Cψ / x ^ 2) * u := by ring
      have ht2 : |2 / x * deriv ψ y| ≤ 2 * Cψ / x := by
        rw [abs_mul, abs_div, abs_of_pos two_pos, abs_of_pos hx]
        calc 2 / x * |deriv ψ y| ≤ 2 / x * Cψ := mul_le_mul_of_nonneg_left (hψ1 y) (by positivity)
          _ = 2 * Cψ / x := by ring
      have ht3 : |((1 - Real.exp (2 * y)) / x ^ 2 + 2 / x) * ψ y| ≤
          (Cψ + E2 * Cψ) / x ^ 2 + 2 * Cψ / x := by
        have htri : |((1 - Real.exp (2 * y)) / x ^ 2 + 2 / x) * ψ y| ≤
            (|ψ y| + Real.exp (2 * y) * |ψ y|) / x ^ 2 + 2 / x * |ψ y| := by
          rw [show ((1 - Real.exp (2 * y)) / x ^ 2 + 2 / x) * ψ y =
              (ψ y - Real.exp (2 * y) * ψ y) / x ^ 2 + 2 / x * ψ y by ring]
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [abs_div, abs_of_pos (sq_pos_of_pos hx)]
            refine div_le_div_of_nonneg_right ((abs_sub _ _).trans (add_le_add le_rfl ?_)) (sq_nonneg x)
            rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          · rw [abs_mul, abs_div, abs_of_pos two_pos, abs_of_pos hx]
        refine htri.trans ?_
        have := h20 y
        have := hψ0 y
        have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
        calc (|ψ y| + Real.exp (2 * y) * |ψ y|) / x ^ 2 + 2 / x * |ψ y|
            ≤ (Cψ + E2 * Cψ) / x ^ 2 + 2 / x * Cψ := by gcongr
          _ = (Cψ + E2 * Cψ) / x ^ 2 + 2 * Cψ / x := by ring
      have hsum : |(-4 / x + 2 * u / x ^ 2) * ψ y + 2 / x * deriv ψ y +
            ((1 - Real.exp (2 * y)) / x ^ 2 + 2 / x) * ψ y| ≤
          |(-4 / x + 2 * u / x ^ 2) * ψ y| + |2 / x * deriv ψ y| +
            |((1 - Real.exp (2 * y)) / x ^ 2 + 2 / x) * ψ y| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
      have hmain : |(-4 / x + 2 * u / x ^ 2) * ψ y + 2 / x * deriv ψ y +
            ((1 - Real.exp (2 * y)) / x ^ 2 + 2 / x) * ψ y| ≤
          A₁ + A₂ * u := by
        have : (4 * Cψ) / x + (2 * Cψ / x ^ 2) * u + 2 * Cψ / x +
            ((Cψ + E2 * Cψ) / x ^ 2 + 2 * Cψ / x) = A₁ + A₂ * u := by
          simp only [A₁, A₂]; ring
        linarith [hsum, ht1, ht2, ht3]
      calc _ ≤ (A₁ + A₂ * u) * Real.exp (-u / x) :=
            mul_le_mul_of_nonneg_right hmain (Real.exp_pos _).le
        _ = A₁ * Real.exp (-u / x) + A₂ * (u * Real.exp (-u / x)) := by ring
    have hg_cont_u : Continuous (fun u => g' u ω) := by
      have heq : (fun u => g' u ω) = fun u =>
          ((-4 / x + 2 * u / x ^ 2) * ψ y + 2 / x * deriv ψ y +
            ((1 - Real.exp (2 * y)) / x ^ 2 + 2 / x) * ψ y) * Real.exp (-u / x) := by
        funext u; simp only [g', hx, ↓reduceIte, x, y]
      rw [heq]; fun_prop
    have hdom_int : IntegrableOn (fun u => A₁ * Real.exp (-u / x) + A₂ * (u * Real.exp (-u / x))) (Ioi v) :=
      (h1.const_mul A₁).add (h2.const_mul A₂)
    have hg_int : IntegrableOn (fun u => g' u ω) (Ioi v) :=
      hdom_int.mono' hg_cont_u.aestronglyMeasurable
        (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => by
          rw [Real.norm_eq_abs]; exact hdom_u u hu)
    refine ⟨hg_int, ?_⟩
    calc ∫ u in Ioi v, |g' u ω|
        ≤ ∫ u in Ioi v, (A₁ * Real.exp (-u / x) + A₂ * (u * Real.exp (-u / x))) :=
          setIntegral_mono_on hg_int.abs hdom_int measurableSet_Ioi hdom_u
      _ = A₁ * (x * Real.exp (-v / x)) + A₂ * ((v * x + x ^ 2) * Real.exp (-v / x)) := by
          rw [integral_add (h1.const_mul A₁) (h2.const_mul A₂), integral_const_mul, integral_const_mul,
            integral_Ioi_exp_neg_div hx, integral_Ioi_mul_exp_neg_div hv.le hx]
      _ ≤ A₁ * x + A₂ * (v * x + x ^ 2) := by
          have hexp : Real.exp (-v / x) ≤ 1 :=
            Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hv.le) hx.le)
          have hA1 : 0 ≤ A₁ := by simp only [A₁]; positivity
          have hA2 : 0 ≤ A₂ := by simp only [A₂]; positivity
          have hx_nn : 0 ≤ x := hx.le
          have hvx_nn : 0 ≤ v * x + x ^ 2 := by positivity
          calc A₁ * (x * Real.exp (-v / x)) + A₂ * ((v * x + x ^ 2) * Real.exp (-v / x))
              ≤ A₁ * (x * 1) + A₂ * ((v * x + x ^ 2) * 1) := by gcongr
            _ = A₁ * x + A₂ * (v * x + x ^ 2) := by ring
      _ ≤ Bω ω := by
          have hB' : Bω ω = (4 * Cψ + 2 * Cψ + (1 + E2) * Cψ + 2 * Cψ) * (1 + x⁻¹) +
              2 * Cψ * (v * x⁻¹ + 1) := by
            simp only [Bω, hx, ↓reduceIte, x]
          rw [hB']
          have h_lhs : A₁ * x + A₂ * (v * x + x ^ 2) =
              10 * Cψ + (1 + E2) * Cψ * x⁻¹ + 2 * Cψ * v * x⁻¹ := by
            simp only [A₁, A₂]; field_simp [hx.ne']; ring
          have h_rhs : (4 * Cψ + 2 * Cψ + (1 + E2) * Cψ + 2 * Cψ) * (1 + x⁻¹) +
              2 * Cψ * (v * x⁻¹ + 1) =
              11 * Cψ + E2 * Cψ + (9 + E2) * Cψ * x⁻¹ + 2 * Cψ * v * x⁻¹ := by ring
          rw [h_lhs, h_rhs]
          have h1' : 0 ≤ Cψ * x⁻¹ := mul_nonneg hCψ0 (inv_nonneg.mpr hx.le)
          have h2' : 0 ≤ E2 * Cψ := mul_nonneg (Real.exp_pos _).le hCψ0
          linarith [hCψ0, h1', h2']
  have hg'_joint_sm : StronglyMeasurable (Function.uncurry g') := by
    let F_map : ℝ × Ω → ℝ × ℝ × ℝ := fun p => (p.1, expInt B 2 0 t p.2, B t p.2)
    have hF_m : Measurable F_map :=
      measurable_fst.prodMk
        ((hX_meas.comp measurable_snd).prodMk ((hBmeas t).comp measurable_snd))
    let K : ℝ × ℝ × ℝ → ℝ := fun q =>
      if 0 < q.2.1 then
        ((-4 / q.2.1 + 2 * q.1 / q.2.1 ^ 2) * ψ q.2.2 +
          2 / q.2.1 * deriv ψ q.2.2 +
          ((1 - Real.exp (2 * q.2.2)) / q.2.1 ^ 2 +
            2 / q.2.1) * ψ q.2.2) * Real.exp (-q.1 / q.2.1)
      else 0
    have hK_meas : Measurable K := by
      refine Measurable.ite (measurableSet_lt measurable_const (measurable_fst.comp measurable_snd))
        ?_ measurable_const
      have hψm : Measurable ψ := hψ.continuous.measurable
      have hψ'm : Measurable (deriv ψ) :=
        ((contDiff_succ_iff_deriv (n := 2)).mp hψ).2.2.continuous.measurable
      have hm1 : Measurable (fun q : ℝ × ℝ × ℝ => q.1) := measurable_fst
      have hm2 : Measurable (fun q : ℝ × ℝ × ℝ => q.2.1) := measurable_fst.comp measurable_snd
      have hm3 : Measurable (fun q : ℝ × ℝ × ℝ => q.2.2) := measurable_snd.comp measurable_snd
      fun_prop
    exact (hK_meas.comp hF_m).stronglyMeasurable
  have hg'_joint_int : Integrable (Function.uncurry g') ((volume.restrict (Ioi v)).prod P) := by
    rw [integrable_prod_iff' hg'_joint_sm.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards [hXpos] with ω hω
      exact (h_inner_abs ω hω).1
    · refine hBω_int.mono' (hg'_joint_sm.norm.integral_prod_left').aestronglyMeasurable ?_
      filter_upwards [hXpos] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun u => norm_nonneg _)]
      simpa [Real.norm_eq_abs] using (h_inner_abs ω hω).2
  have hswap := integral_integral_swap hg'_joint_int
  have hL : ∫ u in Ioi v, ∫ ω, g' u ω ∂P = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun u hu => hslice_zero u hu]
    simp
  rw [hL] at hswap
  have hR : (fun ω => ∫ u in Ioi v, g' u ω) =ᵐ[P]
      fun ω => ((2 * v + 1 - Real.exp (2 * B t ω)) / expInt B 2 0 t ω * ψ (B t ω) +
        2 * deriv ψ (B t ω)) * Real.exp (-v / expInt B 2 0 t ω) := by
    filter_upwards [hXpos] with ω hx
    set x := expInt B 2 0 t ω
    set y := B t ω
    have h1 : IntegrableOn (fun u => Real.exp (-u / x)) (Ioi v) := by
      have hi := integral_Ioi_exp_neg_div (v := v) hx
      by_contra H; have : x * Real.exp (-v / x) = 0 := by rw [← hi, integral_undef H]
      exact (mul_pos hx (Real.exp_pos _)).ne' this
    have h2 : IntegrableOn (fun u => u * Real.exp (-u / x)) (Ioi v) := by
      have hi := integral_Ioi_mul_exp_neg_div hv.le hx
      by_contra H; have : (v * x + x ^ 2) * Real.exp (-v / x) = 0 := by rw [← hi, integral_undef H]
      have hpos : 0 < (v * x + x ^ 2) * Real.exp (-v / x) := by positivity
      exact hpos.ne' this
    let c₀ : ℝ := -4 / x * ψ y + 2 / x * deriv ψ y + ((1 - Real.exp (2 * y)) / x ^ 2 + 2 / x) * ψ y
    let c₁ : ℝ := 2 / x ^ 2 * ψ y
    have hsplit : (fun u => g' u ω) = fun u => c₀ * Real.exp (-u / x) + c₁ * (u * Real.exp (-u / x)) := by
      funext u
      have hgu : g' u ω = ((-4 / x + 2 * u / x ^ 2) * ψ y + 2 / x * deriv ψ y +
          ((1 - Real.exp (2 * y)) / x ^ 2 + 2 / x) * ψ y) * Real.exp (-u / x) := by
        simp only [g', hx, ↓reduceIte, x, y]
      rw [hgu]; simp only [c₀, c₁]; ring
    rw [hsplit, integral_add (h1.const_mul c₀) (h2.const_mul c₁),
      integral_const_mul, integral_const_mul,
      integral_Ioi_exp_neg_div hx, integral_Ioi_mul_exp_neg_div hv.le hx]
    simp only [c₀, c₁]
    field_simp [hx.ne']
    ring
  rw [integral_congr_ae hR] at hswap
  exact hswap.symm

end DistFPIntegrated

end Lyasoff2016
