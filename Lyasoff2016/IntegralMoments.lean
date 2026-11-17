module

public import Lyasoff2016.Setting
public import BrownianMotion.Gaussian.BrownianMotion
public import BrownianMotion.Auxiliary.Martingale
public import BrownianMotion.StochasticIntegral.DoobLp
public import MathFin.Probability.Brownian.Ito.ItoFormulaLocalized
public import MathFin.Probability.Brownian.Ito.ItoIntegralProcessGeneral
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Probability.Distributions.Gaussian.Real


@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Interval NNReal ENNReal

noncomputable section

namespace Lyasoff2016

/-- Hölder/Jensen bound for a nonnegative function on a positive interval. -/
lemma intervalIntegral_pow_le (f : ℝ → ℝ) (hf : Continuous f) (hn : ∀ s, 0 ≤ f s)
    (T : ℝ) (hT : 0 < T) (p : ℕ) :
    (∫ s in (0 : ℝ)..T, f s) ^ p ≤
      T ^ p * ((∫ s in (0 : ℝ)..T, (f s) ^ p) / T) := by
  have h0 : volume (Ioc (0 : ℝ) T) ≠ 0 := by
    simp [Real.volume_Ioc, hT]
  have htop : volume (Ioc (0 : ℝ) T) ≠ ⊤ := by
    simp [Real.volume_Ioc]
  have hfi : IntegrableOn f (Ioc (0 : ℝ) T) volume :=
    (hf.intervalIntegrable 0 T).1
  have hfpi : IntegrableOn ((fun x : ℝ => x ^ p) ∘ f) (Ioc (0 : ℝ) T) volume := by
    change IntegrableOn (fun x => f x ^ p) (Ioc (0 : ℝ) T) volume
    exact ((hf.pow p).intervalIntegrable 0 T).1
  have hj := (convexOn_pow p).map_set_average_le (continuousOn_pow p) isClosed_Ici
    h0 htop (ae_restrict_of_forall_mem measurableSet_Ioc (fun x _ => hn x)) hfi hfpi
  rw [setAverage_eq, setAverage_eq, measureReal_def, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hT.le), sub_zero, smul_eq_mul,
    inv_mul_eq_div] at hj
  rw [← intervalIntegral.integral_of_le hT.le, ← intervalIntegral.integral_of_le hT.le] at hj
  have hpow :
      (∫ s in (0 : ℝ)..T, f s) ^ p =
        T ^ p * (((∫ s in (0 : ℝ)..T, f s) / T) ^ p) := by
    rw [div_pow]
    field_simp
  rw [hpow]
  gcongr
  simpa [smul_eq_mul, div_eq_inv_mul] using hj

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Positive integer moments of finite-horizon exponential Brownian integrals are integrable. -/
theorem expInt_pow_integrable (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (ht : 0 < t) (p : ℕ) :
    Integrable (fun ω => (expInt W σ 0 t ω) ^ p) P := by
  let B : ℝ≥0 → Ω → ℝ := hW.toIsPreBrownianReal.mk W
  have hBmeas : ∀ s, Measurable (B s) :=
    fun s => hW.toIsPreBrownianReal.measurable_mk s
  have hBcont : ∀ ω, Continuous (B · ω) :=
    fun ω => hW.toIsPreBrownianReal.continuous_mk ω
  have hBpre : IsPreBrownianReal B P :=
    hW.toIsPreBrownianReal.congr
      (fun s => (hW.toIsPreBrownianReal.mk_ae_eq s).symm)
  have hBW : ∀ᵐ ω ∂P, (fun s => B s ω) = (fun s => W s ω) := by
    filter_upwards [hW.cont,
      ae_all_iff.2
        (fun n => hW.toIsPreBrownianReal.mk_ae_eq (TopologicalSpace.denseSeq ℝ≥0 n))]
      with ω hWc heq
    exact (TopologicalSpace.denseRange_denseSeq ℝ≥0).equalizer
      (hBcont ω) hWc (funext heq)
  have hexpInt : expInt B σ 0 t =ᵐ[P] expInt W σ 0 t := by
    filter_upwards [hBW] with ω hω
    simp only [expInt, zero_mul, add_zero]
    congr 1
    funext s
    rw [congrFun hω s.toNNReal]
  have hpath_memLp (c : ℝ) : MemLp (expInt B c 0 t) 2 P := by
    have hM := MathFin.pathIntegral_expGrowth_memLp hBpre hBmeas t
      (w := fun _ x => Real.exp (c * x))
      (fun _ => (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable)
      (K := 1) (c := |c|) (by positivity)
      (fun _ x => by
        rw [abs_of_pos (Real.exp_pos _), one_mul]
        exact Real.exp_le_exp.mpr <| (le_abs_self (c * x)).trans_eq (abs_mul c x))
      (fun ω => Real.continuous_exp.comp (continuous_const.mul (hBcont ω)))
    convert hM using 1
    funext ω
    simp only [expInt, zero_mul, add_zero]
    exact (MathFin.ItoIntegralProcessGeneral.timeMeasure_Ioc_eq_interval
      (g := fun s => Real.exp (c * B s ω)) t).symm
  have hAmeas := (hpath_memLp σ).aestronglyMeasurable.pow p
  have hQint : Integrable (expInt B ((p : ℝ) * σ) 0 t) P :=
    (hpath_memLp ((p : ℝ) * σ)).integrable (by norm_num)
  have hposB : Integrable (fun ω => (expInt B σ 0 t ω) ^ p) P := by
    refine Integrable.mono'
      (hQint.const_mul (((t : ℝ) ^ p) / (t : ℝ))) hAmeas ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by
      exact intervalIntegral.integral_nonneg (by positivity) fun _ _ => Real.exp_nonneg _) _)]
    have hj := intervalIntegral_pow_le
      (fun s : ℝ => Real.exp (σ * B s.toNNReal ω))
      (by fun_prop) (fun _ => Real.exp_nonneg _) (t : ℝ) (by exact_mod_cast ht) p
    have hpow : (fun s : ℝ => Real.exp (σ * B s.toNNReal ω) ^ p) =
        fun s => Real.exp (((p : ℝ) * σ) * B s.toNNReal ω) := by
      funext s
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    simp only [expInt, zero_mul, add_zero]
    rw [hpow] at hj
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hj
  exact hposB.congr (hexpInt.mono fun _ h => congrArg (fun x : ℝ => x ^ p) h)

/-- A continuous function on `ℝ≥0` is bounded above on the compact `[0, t]`. -/
lemma bddAbove_range_Iic_of_continuous (g : ℝ≥0 → ℝ) (hg : Continuous g) (t : ℝ≥0) :
    BddAbove (range fun i : Iic t => g i) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).bddAbove_image hg.continuousOn
  exact ⟨M, by
    rintro _ ⟨i, rfl⟩
    exact hM (mem_image_of_mem g ⟨zero_le, i.2⟩)⟩

/-- For a continuous function, the supremum over `[0, t]` is a countable supremum along a dense
sequence (clamped to `[0, t]`). This is what makes the running maximum measurable. -/
lemma ciSup_Iic_eq_iSup_denseSeq (g : ℝ≥0 → ℝ) (hg : Continuous g) (t : ℝ≥0) :
    ⨆ i : Iic t, g i = ⨆ n : ℕ, g (min (TopologicalSpace.denseSeq ℝ≥0 n) t) := by
  have hbdd := bddAbove_range_Iic_of_continuous g hg t
  have hbdd' : BddAbove (range fun n : ℕ => g (min (TopologicalSpace.denseSeq ℝ≥0 n) t)) := by
    obtain ⟨M, hM⟩ := hbdd
    exact ⟨M, by
      rintro _ ⟨n, rfl⟩
      exact hM ⟨⟨min (TopologicalSpace.denseSeq ℝ≥0 n) t, mem_Iic.2 (min_le_right _ _)⟩, rfl⟩⟩
  have : Nonempty (Iic t) := ⟨⟨t, mem_Iic.2 le_rfl⟩⟩
  refine le_antisymm (ciSup_le fun i => ?_) (ciSup_le fun n => ?_)
  · have hclosed : IsClosed {s : ℝ≥0 |
        g (min s t) ≤ ⨆ n : ℕ, g (min (TopologicalSpace.denseSeq ℝ≥0 n) t)} :=
      isClosed_le (hg.comp (continuous_id.min continuous_const)) continuous_const
    have hall : ∀ s : ℝ≥0,
        g (min s t) ≤ ⨆ n : ℕ, g (min (TopologicalSpace.denseSeq ℝ≥0 n) t) := by
      intro s
      have hs : s ∈ closure (range (TopologicalSpace.denseSeq ℝ≥0)) :=
        TopologicalSpace.denseRange_denseSeq ℝ≥0 s
      refine (hclosed.closure_subset_iff.2 ?_) hs
      rintro _ ⟨n, rfl⟩
      exact le_ciSup hbdd' n
    have hi := hall i
    have hmin : min (i : ℝ≥0) t = i := min_eq_left i.2
    rwa [hmin] at hi
  · exact le_ciSup hbdd ⟨min (TopologicalSpace.denseSeq ℝ≥0 n) t, mem_Iic.2 (min_le_right _ _)⟩

/-- The pathwise time integral of `exp (c * B)` is in `L²` (in particular a.e. measurable). -/
lemma expInt_memLp_two_of_preBrownian (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hBpre : IsPreBrownianReal B P) (hBmeas : ∀ s, Measurable (B s))
    (hBcont : ∀ ω, Continuous (B · ω)) (c : ℝ) (t : ℝ≥0) :
    MemLp (expInt B c 0 t) 2 P := by
  have hM := MathFin.pathIntegral_expGrowth_memLp hBpre hBmeas t
    (w := fun _ x => Real.exp (c * x))
    (fun _ => (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable)
    (K := 1) (c := |c|) (by positivity)
    (fun _ x => by
      rw [abs_of_pos (Real.exp_pos _), one_mul]
      exact Real.exp_le_exp.mpr <| (le_abs_self (c * x)).trans_eq (abs_mul c x))
    (fun ω => Real.continuous_exp.comp (continuous_const.mul (hBcont ω)))
  convert hM using 1
  funext ω
  simp only [expInt, zero_mul, add_zero]
  exact (MathFin.ItoIntegralProcessGeneral.timeMeasure_Ioc_eq_interval
    (g := fun s => Real.exp (c * B s ω)) t).symm

/-- **Exponential moments of the running maximum of Brownian motion** (in square-root form).
For a pre-Brownian motion with continuous paths, `s ↦ exp (θ B_s)` is a nonnegative continuous
submartingale, so Doob's maximal inequality gives the weak-type tail bound
`ε P(sup_{s ≤ t} exp (θ B_s) ≥ ε) ≤ E[exp (θ B_t)]`; the layer-cake formula then yields
integrability of the square root of the running supremum. -/
lemma integrable_sqrt_iSup_exp_preBrownian (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P) (hBmeas : ∀ s, Measurable (B s))
    (hBcont : ∀ ω, Continuous (B · ω)) (θ : ℝ) (t : ℝ≥0) :
    Integrable (fun ω => √(⨆ i : Iic t, Real.exp (θ * B i ω))) P := by
  let 𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω› :=
    Filtration.natural B (fun s => (hBmeas s).stronglyMeasurable)
  have : IsFilteredPreBrownian B 𝓕 P := hB.isFilteredPreBrownian hBmeas
  have hmart : Martingale B 𝓕 P := IsPreBrownianReal.isMartingale B 𝓕 P
  let Y : ℝ≥0 → Ω → ℝ := fun s ω => Real.exp (θ * B s ω)
  have hYint : ∀ s, Integrable (Y s) P := fun s =>
    (hB.hasLaw_eval s).integrable_comp (f := fun x => Real.exp (θ * x))
      (integrable_exp_mul_gaussianReal θ)
  have hsub : Submartingale Y 𝓕 P :=
    hmart.submartingale_convex_comp (φ := fun x => Real.exp (θ * x))
      (convexOn_exp.comp_linearMap (LinearMap.mul ℝ ℝ θ)) (by fun_prop) hYint
  have hYnn : 0 ≤ Y := fun s ω => (Real.exp_pos _).le
  have hYcont : ∀ ω, Continuous (Y · ω) := fun ω =>
    Real.continuous_exp.comp (continuous_const.mul (hBcont ω))
  set S : Ω → ℝ := fun ω => ⨆ i : Iic t, Y i ω with hS
  have hSmeas : Measurable S := by
    have hSeq : S = fun ω => ⨆ n : ℕ, Y (min (TopologicalSpace.denseSeq ℝ≥0 n) t) ω := by
      funext ω
      exact ciSup_Iic_eq_iSup_denseSeq (Y · ω) (hYcont ω) t
    rw [hSeq]
    exact Measurable.iSup fun n => Real.measurable_exp.comp ((hBmeas _).const_mul θ)
  set C : ℝ := ∫ ω, Y t ω ∂P with hC
  have hmax : ∀ ε : ℝ, ε * P.real {ω | ε ≤ S ω} ≤ C := by
    intro ε
    refine (ProbabilityTheory.maximal_ineq hsub hYnn ε t
      (fun ω => (hYcont ω).isRightContinuous)).trans ?_
    exact setIntegral_le_integral (hYint t) (ae_of_all _ (hYnn t))
  have hfnn : ∀ ω, 0 ≤ √(S ω) := fun ω => Real.sqrt_nonneg _
  have hfmeas : Measurable fun ω => √(S ω) := hSmeas.sqrt
  refine ⟨hfmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hfnn),
    lintegral_eq_lintegral_meas_lt P (ae_of_all _ hfnn) hfmeas.aemeasurable]
  have hbound : ∀ u ∈ Ioi (0 : ℝ),
      P {ω | u < √(S ω)} ≤ ENNReal.ofReal ((1 + C) * (1 + u ^ 2)⁻¹) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    rw [← ofReal_measureReal]
    apply ENNReal.ofReal_le_ofReal
    have h1 : P.real {ω | u < √(S ω)} ≤ P.real {ω | u ^ 2 ≤ S ω} :=
      measureReal_mono (fun ω hω => ((Real.lt_sqrt hu0.le).1 hω).le)
    have h2 := hmax (u ^ 2)
    have h3 : P.real {ω | u < √(S ω)} ≤ 1 := measureReal_le_one
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg u), h2, h3]
  calc ∫⁻ u in Ioi (0 : ℝ), P {ω | u < √(S ω)}
      ≤ ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((1 + C) * (1 + u ^ 2)⁻¹) :=
        setLIntegral_mono' measurableSet_Ioi hbound
    _ < ∞ := ((integrable_inv_one_add_sq.const_mul (1 + C)).restrict).lintegral_lt_top

/-- Negative integer moments of finite-horizon exponential Brownian integrals are integrable.
Scaffold: Doob maximal inequality on `s ↦ exp(θ B_s)` + layer cake ⇒ exponential moments of
`⨆_{s≤t} B_s` (and of `-B`); then `integral_exp_ge` upgrades to `(expInt)^{-p}`. -/
theorem expInt_zpow_neg_integrable (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (_hσ : 0 < σ) (ht : 0 < t) (p : ℕ) :
    Integrable (fun ω => (expInt W σ 0 t ω) ^ (-(p : ℤ))) P := by
  let B : ℝ≥0 → Ω → ℝ := hW.toIsPreBrownianReal.mk W
  have hBmeas : ∀ s, Measurable (B s) := fun s => hW.toIsPreBrownianReal.measurable_mk s
  have hBcont : ∀ ω, Continuous (B · ω) := fun ω => hW.toIsPreBrownianReal.continuous_mk ω
  have hBpre : IsPreBrownianReal B P :=
    hW.toIsPreBrownianReal.congr (fun s => (hW.toIsPreBrownianReal.mk_ae_eq s).symm)
  have hBW : ∀ᵐ ω ∂P, (fun s => B s ω) = (fun s => W s ω) := by
    filter_upwards [hW.cont,
      ae_all_iff.2
        (fun n => hW.toIsPreBrownianReal.mk_ae_eq (TopologicalSpace.denseSeq ℝ≥0 n))]
      with ω hWc heq
    exact (TopologicalSpace.denseRange_denseSeq ℝ≥0).equalizer
      (hBcont ω) hWc (funext heq)
  have hexpInt : expInt B σ 0 t =ᵐ[P] expInt W σ 0 t := by
    filter_upwards [hBW] with ω hω
    simp only [expInt, zero_mul, add_zero]
    congr 1
    funext s
    rw [congrFun hω s.toNNReal]
  -- Pathwise bound `(∫ e^{σB})^{-p} ≤ t^{-p} exp(p σ ⨆|B|)` via `integral_exp_ge`, then
  -- exponential moments of the running max from Doob on `exp(θ B)` / `exp(θ (-B))`.
  -- Only the lower envelope of `B` matters: with `θ = -2pσ` and `S = ⨆_{s≤t} exp(θ B_s)`,
  -- `exp(σ B_s) ≥ S^{-1/(2p)}` on `[0,t]`, hence `(∫ e^{σB})^{-p} ≤ t^{-p} √S`.
  have hA : AEStronglyMeasurable (expInt B σ 0 t) P :=
    (expInt_memLp_two_of_preBrownian P B hBpre hBmeas hBcont σ t).aestronglyMeasurable
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  set θ : ℝ := -(2 * (p : ℝ) * σ) with hθ
  set S : Ω → ℝ := fun ω => ⨆ i : Iic t, Real.exp (θ * B i ω) with hS
  have hSint : Integrable (fun ω => √(S ω)) P :=
    integrable_sqrt_iSup_exp_preBrownian P B hBpre hBmeas hBcont θ t
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hBint : Integrable (fun ω => (expInt B σ 0 t ω) ^ (-(p : ℤ))) P := by
    refine Integrable.mono' (hSint.const_mul (((t : ℝ) ^ p)⁻¹)) ?_ ?_
    · have hfun : (fun ω => (expInt B σ 0 t ω) ^ (-(p : ℤ))) =
          fun ω => ((expInt B σ 0 t ω) ^ p)⁻¹ := by
        funext ω
        rw [zpow_neg, zpow_natCast]
      rw [hfun]
      exact (hA.aemeasurable.pow_const p).inv.aestronglyMeasurable
    · filter_upwards with ω
      have hbdd := bddAbove_range_Iic_of_continuous (fun s => Real.exp (θ * B s ω))
        (Real.continuous_exp.comp (continuous_const.mul (hBcont ω))) t
      have ha : 0 < S ω :=
        lt_of_lt_of_le (Real.exp_pos (θ * B 0 ω)) (le_ciSup hbdd ⟨0, mem_Iic.2 zero_le⟩)
      set ℓ : ℝ := Real.log (S ω) with hℓ
      have hpt : ∀ s ∈ Icc (0 : ℝ) t,
          Real.exp (-(ℓ / (2 * p))) ≤ Real.exp (σ * B s.toNNReal ω) := by
        intro s hs
        have hst : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hs.2
        have h1 : Real.exp (θ * B s.toNNReal ω) ≤ S ω :=
          le_ciSup hbdd ⟨s.toNNReal, mem_Iic.2 hst⟩
        have h2 : θ * B s.toNNReal ω ≤ ℓ := (Real.le_log_iff_exp_le ha).2 h1
        apply Real.exp_le_exp.2
        have hp' : (0 : ℝ) < 2 * p := by positivity
        rw [neg_le, le_div_iff₀ hp']
        rw [hθ] at h2
        linarith
      have hcontω : Continuous fun s : ℝ => Real.exp (σ * B s.toNNReal ω) :=
        Real.continuous_exp.comp
          (continuous_const.mul ((hBcont ω).comp continuous_real_toNNReal))
      have hlow : (t : ℝ) * Real.exp (-(ℓ / (2 * p))) ≤ expInt B σ 0 t ω := by
        have h1 : ∫ _ in (0 : ℝ)..t, Real.exp (-(ℓ / (2 * p))) ≤
            ∫ s in (0 : ℝ)..t, Real.exp (σ * B s.toNNReal ω) :=
          intervalIntegral.integral_mono_on htpos.le
            (continuous_const.intervalIntegrable _ _) (hcontω.intervalIntegrable _ _) hpt
        simpa [expInt] using h1
      have hpos : 0 < (t : ℝ) * Real.exp (-(ℓ / (2 * p))) := by positivity
      rw [Real.norm_eq_abs, zpow_neg, zpow_natCast,
        abs_of_pos (inv_pos.2 (pow_pos (hpos.trans_le hlow) p))]
      calc ((expInt B σ 0 t ω) ^ p)⁻¹
          ≤ (((t : ℝ) * Real.exp (-(ℓ / (2 * p)))) ^ p)⁻¹ :=
            inv_anti₀ (pow_pos hpos p) (pow_le_pow_left₀ hpos.le hlow p)
        _ = ((t : ℝ) ^ p)⁻¹ * √(S ω) := by
          rw [mul_pow, mul_inv, ← Real.exp_nat_mul, ← Real.exp_neg]
          have hexp : -((p : ℝ) * -(ℓ / (2 * p))) = ℓ / 2 := by
            field_simp
          rw [hexp, Real.exp_half, hℓ, Real.exp_log ha]
  exact hBint.congr (hexpInt.mono fun _ h => congrArg (fun x : ℝ => x ^ (-(p : ℤ))) h)

end Lyasoff2016
