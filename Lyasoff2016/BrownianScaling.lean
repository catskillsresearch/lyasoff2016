/-
Brownian scaling for the exponential functionals of the paper (p. 1066).

* `isBrownianReal_path_functional`: any functional of the path that is measurable on
  `C(ℝ≥0, ℝ)` is a.e.-measurable along a Brownian motion, and has the same law under any two
  Brownian motions on the same probability space.
* `jointLaw_scaling`, `inftyLaw_scaling`: with `B_s = σ W_{s/σ²}` this gives
  `(∫₀ᵗ e^{W}, W_t) =ᵈ (σ² ∫₀^{t/σ²} e^{σW}, σ W_{t/σ²})` and the infinite-horizon analogue.
* `map_withDensity_eq_of_map_eq_smul`: pushforward of a density under a measurable
  equivalence that scales the reference measure.
* `jointDensity_scaling_posPart`, `inftyDensity_scaling_posPart`: the resulting scaling
  relations between *continuous* densities, valid everywhere for their positive parts.

`IsJointDensity` only sees `ENNReal.ofReal ∘ φ`, i.e. the positive part of `φ`; a continuous
`φ` may be negative where the law has no mass (e.g. on `x < 0`).  This is why the pointwise
statements are about `max φ 0`.
-/
module

public import Lyasoff2016.Setting


@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Laws of measurable path functionals -/

/-- A functional of the path which is measurable on `C(ℝ≥0, ℝ)` is a.e.-measurable along a
Brownian motion, and its law does not depend on the Brownian motion. -/
theorem isBrownianReal_path_functional {E : Type*} [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W B : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) (hB : IsBrownianReal B P)
    (F : (ℝ≥0 → ℝ) → E) (hF : Measurable fun x : C(ℝ≥0, ℝ) => F (fun s => x s)) :
    AEMeasurable (fun ω => F (fun s => W s ω)) P ∧
      P.map (fun ω => F (fun s => W s ω)) = P.map (fun ω => F (fun s => B s ω)) := by
  let W' := (hW.toIsPreBrownianReal).mk W
  let B' := (hB.toIsPreBrownianReal).mk B
  let pW : Ω → C(ℝ≥0, ℝ) :=
    fun ω => ⟨(fun s => W' s ω), hW.toIsPreBrownianReal.continuous_mk ω⟩
  let pB : Ω → C(ℝ≥0, ℝ) :=
    fun ω => ⟨(fun s => B' s ω), hB.toIsPreBrownianReal.continuous_mk ω⟩
  have hpW : Measurable pW := ContinuousMap.measurable_iff_eval.2 fun s =>
    by simpa [pW, W'] using hW.toIsPreBrownianReal.measurable_mk s
  have hpB : Measurable pB := ContinuousMap.measurable_iff_eval.2 fun s =>
    by simpa [pB, B'] using hB.toIsPreBrownianReal.measurable_mk s
  let e : C(ℝ≥0, ℝ) → (ℝ≥0 → ℝ) := fun x s => x s
  have he : Measurable e := measurable_pi_iff.2 fun s => ContinuousMap.measurable_eval s
  have he_comap : MeasurableSpace.comap e inferInstance =
      (inferInstance : MeasurableSpace C(ℝ≥0, ℝ)) := by
    apply le_antisymm
    · exact he.comap_le
    · rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval]
      refine iSup_le fun s => ?_
      rw [← measurable_iff_comap_le]
      exact (measurable_pi_apply s).comp (comap_measurable e)
  have hrawW : P.map (e ∘ pW) = gaussianLimit :=
    (hW.toIsPreBrownianReal.isBrownianReal_mk.toIsPreBrownianReal.hasLaw_gaussianLimit
      ((he.comp hpW).aemeasurable)).map_eq
  have hrawB : P.map (e ∘ pB) = gaussianLimit :=
    (hB.toIsPreBrownianReal.isBrownianReal_mk.toIsPreBrownianReal.hasLaw_gaussianLimit
      ((he.comp hpB).aemeasurable)).map_eq
  have hpath : P.map pW = P.map pB := by
    have hmap : (P.map pW).map e = (P.map pB).map e := by
      calc
        (P.map pW).map e = P.map (e ∘ pW) := Measure.map_map he hpW
        _ = gaussianLimit := hrawW
        _ = P.map (e ∘ pB) := hrawB.symm
        _ = (P.map pB).map e := (Measure.map_map he hpB).symm
    ext A hA
    have hA' : MeasurableSet[MeasurableSpace.comap e inferInstance] A :=
      he_comap.symm ▸ hA
    rcases hA' with ⟨S, hS, rfl⟩
    rw [← Measure.map_apply he hS, hmap, Measure.map_apply he hS]
  let Φ : C(ℝ≥0, ℝ) → E := fun x => F (fun s => x s)
  have hWae : (fun ω => F (fun s => W s ω)) =ᵐ[P] Φ ∘ pW :=
    hW.mk_ae_forall_eq.mono fun ω hω => by
      simp only [Function.comp_apply, Φ, pW, ContinuousMap.coe_mk]
      congr 1
      funext s
      exact (hω s).symm
  have hBae : (fun ω => F (fun s => B s ω)) =ᵐ[P] Φ ∘ pB :=
    hB.mk_ae_forall_eq.mono fun ω hω => by
      simp only [Function.comp_apply, Φ, pB, ContinuousMap.coe_mk]
      congr 1
      funext s
      exact (hω s).symm
  refine ⟨(hF.comp hpW).aemeasurable.congr hWae.symm, ?_⟩
  calc
    P.map (fun ω => F (fun s => W s ω)) = P.map (Φ ∘ pW) := Measure.map_congr hWae
    _ = (P.map pW).map Φ := (Measure.map_map hF hpW).symm
    _ = (P.map pB).map Φ := by rw [hpath]
    _ = P.map (Φ ∘ pB) := Measure.map_map hF hpB
    _ = P.map (fun ω => F (fun s => B s ω)) := (Measure.map_congr hBae).symm

/-- Measurability on path space of `x ↦ ∫_{s > a} V(s, x_s) ds` for jointly continuous `V`. -/
theorem measurable_path_integral_Ioi (V : ℝ → ℝ → ℝ)
    (hV : Continuous (Function.uncurry V)) (S : Set ℝ) :
    Measurable fun x : C(ℝ≥0, ℝ) => ∫ s in S, V s (x s.toNNReal) := by
  have hev : Continuous (fun p : C(ℝ≥0, ℝ) × ℝ => p.1 p.2.toNNReal) :=
    continuous_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))
  have hc : Continuous (fun p : C(ℝ≥0, ℝ) × ℝ => V p.2 (p.1 p.2.toNNReal)) :=
    hV.comp (continuous_snd.prodMk hev)
  have hsm : StronglyMeasurable (Function.uncurry
      (fun x : C(ℝ≥0, ℝ) => fun s : ℝ => V s (x s.toNNReal))) :=
    hc.stronglyMeasurable
  exact (StronglyMeasurable.integral_prod_right (ν := volume.restrict S) hsm).measurable

/-- Measurability on path space of `x ↦ ∫ₐᵇ V(s, x_s) ds` for jointly continuous `V`. -/
theorem measurable_path_intervalIntegral (V : ℝ → ℝ → ℝ)
    (hV : Continuous (Function.uncurry V)) (a b : ℝ) :
    Measurable fun x : C(ℝ≥0, ℝ) => ∫ s in a..b, V s (x s.toNNReal) := by
  simp only [intervalIntegral]
  exact (measurable_path_integral_Ioi V hV _).sub (measurable_path_integral_Ioi V hV _)

/-! ### The scaled Brownian motion `s ↦ σ W_{s/σ²}` -/

theorem isBrownianReal_scaled (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P)
    {σ : ℝ} (hσ : 0 < σ) :
    IsBrownianReal (fun (s : ℝ≥0) ω => σ * W (((σ ^ 2)⁻¹).toNNReal * s) ω) P := by
  have hpos : 0 < (σ ^ 2)⁻¹ := by positivity
  have hc : ((σ ^ 2)⁻¹).toNNReal ≠ 0 := (Real.toNNReal_pos.2 hpos).ne'
  have h := hW.smul hc
  have hsq : (√(((σ ^ 2)⁻¹).toNNReal : ℝ))⁻¹ = σ := by
    rw [Real.coe_toNNReal _ hpos.le, Real.sqrt_inv, Real.sqrt_sq hσ.le, inv_inv]
  simpa only [hsq] using h

/-- Finite horizon: `(∫₀ᵗ e^{W_s} ds, W_t) =ᵈ (σ² ∫₀^{t/σ²} e^{σ W_s} ds, σ W_{t/σ²})`. -/
theorem jointLaw_scaling (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) {σ : ℝ} (hσ : 0 < σ) (t : ℝ≥0) :
    jointLaw P W 1 0 t =
      (jointLaw P W σ 0 ((t : ℝ) / σ ^ 2).toNNReal).map
        (fun p : ℝ × ℝ => (σ ^ 2 * p.1, σ * p.2)) := by
  have hpos : 0 < (σ ^ 2)⁻¹ := by positivity
  set T : ℝ≥0 := ((t : ℝ) / σ ^ 2).toNNReal with hT
  have hTcoe : (T : ℝ) = (σ ^ 2)⁻¹ * t := by
    rw [hT, Real.coe_toNNReal _ (by positivity), div_eq_inv_mul]
  have hTmul : ((σ ^ 2)⁻¹).toNNReal * t = T := by
    rw [hT, div_eq_inv_mul, Real.toNNReal_mul hpos.le, Real.toNNReal_coe]
  have hB : IsBrownianReal (fun (s : ℝ≥0) ω => σ * W (((σ ^ 2)⁻¹).toNNReal * s) ω) P :=
    isBrownianReal_scaled P W hW hσ
  let F : ℝ → ℝ≥0 → (ℝ≥0 → ℝ) → ℝ × ℝ := fun a u x =>
    (∫ s in (0 : ℝ)..(u : ℝ), Real.exp (a * x s.toNNReal + 0 * s), x u)
  have hF : ∀ a u, Measurable fun x : C(ℝ≥0, ℝ) => F a u (fun s => x s) := fun a u =>
    (measurable_path_intervalIntegral (fun s w => Real.exp (a * w + 0 * s))
      (show Continuous (fun p : ℝ × ℝ => Real.exp (a * p.2 + 0 * p.1)) by fun_prop)
      0 u).prodMk (ContinuousMap.measurable_eval u)
  have h1 := (isBrownianReal_path_functional P W _ hW hB (F 1 t) (hF 1 t)).2
  have hmeas : AEMeasurable (fun ω => (expInt W σ 0 T ω, W T ω)) P :=
    (isBrownianReal_path_functional P W W hW hW (F σ T) (hF σ T)).1
  have hpath : ∀ ω, F 1 t (fun s => σ * W (((σ ^ 2)⁻¹).toNNReal * s) ω) =
      (σ ^ 2 * expInt W σ 0 T ω, σ * W T ω) := by
    intro ω
    refine Prod.ext ?_ ?_
    · show ∫ s in (0 : ℝ)..(t : ℝ),
          Real.exp (1 * (σ * W (((σ ^ 2)⁻¹).toNNReal * s.toNNReal) ω) + 0 * s) =
        σ ^ 2 * expInt W σ 0 T ω
      have hsub := intervalIntegral.integral_comp_mul_left (a := 0) (b := (t : ℝ))
        (fun u => Real.exp (σ * W u.toNNReal ω + 0 * u)) hpos.ne'
      rw [mul_zero, inv_inv, smul_eq_mul, ← hTcoe] at hsub
      simp only [expInt]
      rw [← hsub]
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [Real.toNNReal_mul hpos.le, one_mul, zero_mul]
    · show σ * W (((σ ^ 2)⁻¹).toNNReal * t) ω = σ * W T ω
      rw [hTmul]
  unfold jointLaw
  calc
    P.map (fun ω => (expInt W 1 0 t ω, W t ω))
        = P.map (fun ω => F 1 t (fun s => σ * W (((σ ^ 2)⁻¹).toNNReal * s) ω)) := h1
    _ = P.map ((fun p : ℝ × ℝ => (σ ^ 2 * p.1, σ * p.2)) ∘
          fun ω => (expInt W σ 0 T ω, W T ω)) := by
      congr 1
      funext ω
      exact hpath ω
    _ = (P.map (fun ω => (expInt W σ 0 T ω, W T ω))).map
          (fun p : ℝ × ℝ => (σ ^ 2 * p.1, σ * p.2)) :=
      (AEMeasurable.map_map_of_aemeasurable
        (by fun_prop : Measurable fun p : ℝ × ℝ => (σ ^ 2 * p.1, σ * p.2)).aemeasurable
        hmeas).symm

/-- Infinite horizon:
`∫₀^∞ e^{W_s + ν s} ds =ᵈ σ² ∫₀^∞ e^{σ W_s + ν σ² s} ds`. -/
theorem inftyLaw_scaling (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) {σ : ℝ} (hσ : 0 < σ) (ν : ℝ) :
    P.map (fun ω => ∫ s in Ioi (0 : ℝ), Real.exp (1 * W s.toNNReal ω + ν * s)) =
      (P.map (fun ω => ∫ s in Ioi (0 : ℝ),
        Real.exp (σ * W s.toNNReal ω + ν * σ ^ 2 * s))).map (fun x => σ ^ 2 * x) := by
  have hpos : 0 < (σ ^ 2)⁻¹ := by positivity
  have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ.ne'
  have hB : IsBrownianReal (fun (s : ℝ≥0) ω => σ * W (((σ ^ 2)⁻¹).toNNReal * s) ω) P :=
    isBrownianReal_scaled P W hW hσ
  let G : ℝ → ℝ → (ℝ≥0 → ℝ) → ℝ := fun a b x =>
    ∫ s in Ioi (0 : ℝ), Real.exp (a * x s.toNNReal + b * s)
  have hG : ∀ a b, Measurable fun x : C(ℝ≥0, ℝ) => G a b (fun s => x s) := fun a b =>
    measurable_path_integral_Ioi (fun s w => Real.exp (a * w + b * s))
      (show Continuous (fun p : ℝ × ℝ => Real.exp (a * p.2 + b * p.1)) by fun_prop) _
  have h1 := (isBrownianReal_path_functional P W _ hW hB (G 1 ν) (hG 1 ν)).2
  have hmeas : AEMeasurable
      (fun ω => ∫ s in Ioi (0 : ℝ), Real.exp (σ * W s.toNNReal ω + ν * σ ^ 2 * s)) P :=
    (isBrownianReal_path_functional P W W hW hW (G σ (ν * σ ^ 2)) (hG σ (ν * σ ^ 2))).1
  have hpath : ∀ ω, G 1 ν (fun s => σ * W (((σ ^ 2)⁻¹).toNNReal * s) ω) =
      σ ^ 2 * ∫ s in Ioi (0 : ℝ), Real.exp (σ * W s.toNNReal ω + ν * σ ^ 2 * s) := by
    intro ω
    show ∫ s in Ioi (0 : ℝ),
        Real.exp (1 * (σ * W (((σ ^ 2)⁻¹).toNNReal * s.toNNReal) ω) + ν * s) = _
    have hsub := integral_comp_mul_left_Ioi
      (fun u => Real.exp (σ * W u.toNNReal ω + ν * σ ^ 2 * u)) 0 hpos
    rw [mul_zero, inv_inv, smul_eq_mul] at hsub
    rw [← hsub]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    simp only [Real.toNNReal_mul hpos.le, one_mul]
    congr 2
    field_simp
  calc
    P.map (fun ω => ∫ s in Ioi (0 : ℝ), Real.exp (1 * W s.toNNReal ω + ν * s))
        = P.map (fun ω => G 1 ν (fun s => σ * W (((σ ^ 2)⁻¹).toNNReal * s) ω)) := h1
    _ = P.map ((fun x : ℝ => σ ^ 2 * x) ∘
          fun ω => ∫ s in Ioi (0 : ℝ), Real.exp (σ * W s.toNNReal ω + ν * σ ^ 2 * s)) := by
      congr 1
      funext ω
      exact hpath ω
    _ = _ :=
      (AEMeasurable.map_map_of_aemeasurable
        (by fun_prop : Measurable fun x : ℝ => σ ^ 2 * x).aemeasurable hmeas).symm

/-! ### Pushforward of densities under scalings -/

/-- If a measurable equivalence `e` scales `μ` by `k`, then it sends the density `f` to
`k · f ∘ e⁻¹`. -/
theorem map_withDensity_eq_of_map_eq_smul {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (e : α ≃ᵐ α) (k : ℝ≥0∞) (hk : μ.map e = k • μ) (f : α → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = μ.withDensity (fun x => k * f (e.symm x)) := by
  ext S hS
  have hfe : Measurable fun x => f (e.symm x) := hf.comp e.symm.measurable
  rw [e.map_apply, withDensity_apply _ (e.measurable hS), withDensity_apply _ hS,
    lintegral_const_mul k hfe]
  have h := setLIntegral_map (μ := μ) hS hfe e.measurable
  rw [hk] at h
  simp only [MeasurableEquiv.symm_apply_apply] at h
  rw [← h, Measure.restrict_smul, lintegral_smul_measure]
  rfl

theorem map_mul_left_withDensity {a : ℝ} (ha : a ≠ 0) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ((volume : Measure ℝ).withDensity f).map (fun x => a * x) =
      volume.withDensity (fun x => ENNReal.ofReal |a⁻¹| * f (a⁻¹ * x)) :=
  map_withDensity_eq_of_map_eq_smul volume (MeasurableEquiv.mulLeft₀ a ha)
    (ENNReal.ofReal |a⁻¹|) (Real.map_volume_mul_left ha) f hf

theorem map_prod_mul_withDensity {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    ((volume : Measure (ℝ × ℝ)).withDensity f).map (fun p => (a * p.1, b * p.2)) =
      volume.withDensity (fun p =>
        (ENNReal.ofReal |b⁻¹| * ENNReal.ofReal |a⁻¹|) * f (a⁻¹ * p.1, b⁻¹ * p.2)) := by
  have hk : (volume : Measure (ℝ × ℝ)).map
      ((MeasurableEquiv.mulLeft₀ a ha).prodCongr (MeasurableEquiv.mulLeft₀ b hb)) =
        (ENNReal.ofReal |b⁻¹| * ENNReal.ofReal |a⁻¹|) • volume := by
    have hcoe : (((MeasurableEquiv.mulLeft₀ a ha).prodCongr (MeasurableEquiv.mulLeft₀ b hb) :
        ℝ × ℝ ≃ᵐ ℝ × ℝ) : ℝ × ℝ → ℝ × ℝ) = Prod.map (fun x => a * x) (fun x => b * x) := rfl
    rw [hcoe, Measure.volume_eq_prod, ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
      Real.map_volume_mul_left ha, Real.map_volume_mul_left hb, Measure.prod_smul_right,
      Measure.prod_smul_left, smul_smul]
  exact map_withDensity_eq_of_map_eq_smul volume
    ((MeasurableEquiv.mulLeft₀ a ha).prodCongr (MeasurableEquiv.mulLeft₀ b hb)) _ hk f hf

/-! ### Scaling relations for continuous densities -/

/-- Paper p. 1066, first scaling display, for the positive parts of continuous densities:
`φ_{t,1}(x,y) = σ⁻³ φ_{t/σ²,σ}(x/σ², y/σ)`. -/
theorem jointDensity_scaling_posPart (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) {σ : ℝ} (hσ : 0 < σ) (t : ℝ≥0)
    (φ₁ φσ : ℝ → ℝ → ℝ) (h1 : IsJointDensity P W 1 0 t φ₁)
    (hσ' : IsJointDensity P W σ 0 ((t : ℝ) / σ ^ 2).toNNReal φσ)
    (hc₁ : Continuous (Function.uncurry φ₁)) (hcσ : Continuous (Function.uncurry φσ))
    (x y : ℝ) :
    max (φ₁ x y) 0 = σ⁻¹ ^ 3 * max (φσ (x / σ ^ 2) (y / σ)) 0 := by
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hm₁ : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (φ₁ p.1 p.2) :=
    hc₁.measurable.ennreal_ofReal
  have hmσ : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (φσ p.1 p.2) :=
    hcσ.measurable.ennreal_ofReal
  have hlaw := jointLaw_scaling P W hW hσ t
  unfold IsJointDensity at h1 hσ'
  rw [h1, hσ', map_prod_mul_withDensity (pow_ne_zero 2 hσ0) hσ0 _ hmσ] at hlaw
  have hae := (withDensity_eq_iff_of_sigmaFinite hm₁.aemeasurable
    ((hmσ.comp (by fun_prop : Measurable fun p : ℝ × ℝ =>
      ((σ ^ 2)⁻¹ * p.1, σ⁻¹ * p.2))).const_mul _).aemeasurable).1 hlaw
  have hreal : (fun p : ℝ × ℝ => max (φ₁ p.1 p.2) 0) =ᵐ[volume]
      fun p => σ⁻¹ ^ 3 * max (φσ (p.1 / σ ^ 2) (p.2 / σ)) 0 := by
    filter_upwards [hae] with p hp
    have h := congrArg ENNReal.toReal hp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal', Function.comp_apply] at h
    rw [h, max_eq_left (abs_nonneg _), max_eq_left (abs_nonneg _),
      abs_of_pos (by positivity), abs_of_pos (by positivity),
      div_eq_inv_mul, div_eq_inv_mul]
    ring
  have hcont1 : Continuous fun p : ℝ × ℝ => max (φ₁ p.1 p.2) 0 :=
    hc₁.max continuous_const
  have hcont2 : Continuous fun p : ℝ × ℝ => σ⁻¹ ^ 3 * max (φσ (p.1 / σ ^ 2) (p.2 / σ)) 0 := by
    have hcomp : Continuous fun p : ℝ × ℝ => φσ (p.1 / σ ^ 2) (p.2 / σ) :=
      hcσ.comp (by fun_prop : Continuous fun p : ℝ × ℝ => (p.1 / σ ^ 2, p.2 / σ))
    exact continuous_const.mul (hcomp.max continuous_const)
  exact congrFun ((Continuous.ae_eq_iff_eq volume hcont1 hcont2).1 hreal) (x, y)

/-- Paper p. 1066, third scaling display, for the positive parts of continuous densities:
`ψ_{1,ν}(x) = σ⁻² ψ_{σ,νσ²}(x/σ²)`. -/
theorem inftyDensity_scaling_posPart (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) {σ : ℝ} (hσ : 0 < σ) (ν : ℝ) (ψ₁ ψσ : ℝ → ℝ)
    (h1 : P.map (fun ω => ∫ s in Ioi (0 : ℝ), Real.exp (1 * W s.toNNReal ω + ν * s)) =
      (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (ψ₁ x)))
    (hσ' : P.map (fun ω => ∫ s in Ioi (0 : ℝ),
        Real.exp (σ * W s.toNNReal ω + ν * σ ^ 2 * s)) =
      (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (ψσ x)))
    (hc₁ : Continuous ψ₁) (hcσ : Continuous ψσ) (x : ℝ) :
    max (ψ₁ x) 0 = σ⁻¹ ^ 2 * max (ψσ (x / σ ^ 2)) 0 := by
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hm₁ : Measurable fun x : ℝ => ENNReal.ofReal (ψ₁ x) := hc₁.measurable.ennreal_ofReal
  have hmσ : Measurable fun x : ℝ => ENNReal.ofReal (ψσ x) := hcσ.measurable.ennreal_ofReal
  have hlaw := inftyLaw_scaling P W hW hσ ν
  rw [h1, hσ', map_mul_left_withDensity (pow_ne_zero 2 hσ0) _ hmσ] at hlaw
  have hae := (withDensity_eq_iff_of_sigmaFinite hm₁.aemeasurable
    ((hmσ.comp (by fun_prop : Measurable fun x : ℝ => (σ ^ 2)⁻¹ * x)).const_mul _).aemeasurable).1
      hlaw
  have hreal : (fun x : ℝ => max (ψ₁ x) 0) =ᵐ[volume]
      fun x => σ⁻¹ ^ 2 * max (ψσ (x / σ ^ 2)) 0 := by
    filter_upwards [hae] with p hp
    have h := congrArg ENNReal.toReal hp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal', Function.comp_apply] at h
    rw [h, max_eq_left (abs_nonneg _), abs_of_pos (by positivity), div_eq_inv_mul]
    ring
  have hcont1 : Continuous fun x : ℝ => max (ψ₁ x) 0 := hc₁.max continuous_const
  have hcont2 : Continuous fun x : ℝ => σ⁻¹ ^ 2 * max (ψσ (x / σ ^ 2)) 0 :=
    continuous_const.mul
      ((hcσ.comp (by fun_prop : Continuous fun x : ℝ => x / σ ^ 2)).max continuous_const)
  exact congrFun ((Continuous.ae_eq_iff_eq volume hcont1 hcont2).1 hreal) x

end Lyasoff2016
