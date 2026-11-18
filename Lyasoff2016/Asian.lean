/-
# §6 Asian options (pp. 1088–1095)
-/
module

public import Lyasoff2016.FfunDeriv
public import Lyasoff2016.ExpBMIntegrable
public import Lyasoff2016.AsianDensity


@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Asian call price and pricing identities (pp. 1088–1093)

Throughout this file the drift is called `ν` (the paper's `μ`), and the integration
variables are `u` (contour parameter of the π/2-formula) and `w = e^{σy/2}`.

The factors `Afun`, `Bfun`, `Cfun`, `Sfun`, `SfunC`, `Ffun`, and `FfunDeriv` live in
their own modules under this namespace. -/

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

/- Paper: p. 1088–1090, Asian call payoff expectation (undiscounted).
   Plain recap: E[(∫₀ᵗ e^{σW_s+νs} ds − K)₊]. -/
def asianCall (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (σ ν : ℝ) (t : ℝ≥0) (K : ℝ) : ℝ :=
  ∫ ω, max (expInt W σ ν t ω - K) 0 ∂P

/- Paper: p. 1093, market Asian call at t = 0 with S₀ = 1:
     e^{-rT} (1/T) E[(∫₀ᵀ e^{σW+(r−σ²/2)s} ds − KT)₊]. -/
def asianMarketPrice (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (σ r : ℝ) (T : ℝ≥0) (K : ℝ) : ℝ :=
  Real.exp (-r * (T : ℝ)) * (1 / (T : ℝ)) *
    asianCall P W σ (r - σ ^ 2 / 2) T (K * (T : ℝ))

/-- Payoff–density reduction (p. 1090): if `φ ≥ 0` is a joint density of
`(∫₀ᵗ e^{σW_s+νs} ds, W_t)`, then the undiscounted Asian call is
`∬ (x − K)₊ φ(x, y) dx dy`.  No integrability hypothesis is needed: both sides are integrals
of nonnegative functions with the same Lebesgue integral. -/
theorem asianCall_eq_integral_density (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (σ ν : ℝ) (t : ℝ≥0) (K : ℝ) (φ : ℝ → ℝ → ℝ)
    (hφ : IsJointDensity P W σ ν t φ) (hφnn : ∀ x y, 0 ≤ φ x y)
    (hφm : AEMeasurable (fun p : ℝ × ℝ => φ p.1 p.2) volume) :
    asianCall P W σ ν t K = ∫ p : ℝ × ℝ, max (p.1 - K) 0 * φ p.1 p.2 := by
  have hH := aemeasurable_jointMap P W hW σ ν t
  have hpaym : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (max (p.1 - K) 0)) :=
    ((measurable_fst.sub_const K).max measurable_const).ennreal_ofReal
  have hmeas : AEStronglyMeasurable (fun ω => max (expInt W σ ν t ω - K) 0) P :=
    ((hH.fst.sub_const K).max aemeasurable_const).aestronglyMeasurable
  have hnn0 : 0 ≤ᵐ[P] fun ω => max (expInt W σ ν t ω - K) 0 :=
    ae_of_all _ fun ω => le_max_right _ _
  have hprod : AEStronglyMeasurable
      (fun p : ℝ × ℝ => max (p.1 - K) 0 * φ p.1 p.2) volume :=
    (((measurable_fst.sub_const K).max measurable_const).aemeasurable.mul
      hφm).aestronglyMeasurable
  have hnn : 0 ≤ᵐ[volume] fun p : ℝ × ℝ => max (p.1 - K) 0 * φ p.1 p.2 :=
    ae_of_all _ fun p => mul_nonneg (le_max_right _ _) (hφnn _ _)
  have h1 : ∫⁻ ω, ENNReal.ofReal (max (expInt W σ ν t ω - K) 0) ∂P =
      ∫⁻ p, ENNReal.ofReal (max (p.1 - K) 0) ∂jointLaw P W σ ν t := by
    unfold jointLaw
    rw [lintegral_map' hpaym.aemeasurable hH]
  unfold asianCall
  rw [integral_eq_lintegral_of_nonneg_ae hnn0 hmeas,
    integral_eq_lintegral_of_nonneg_ae hnn hprod, h1]
  congr 1
  unfold IsJointDensity at hφ
  rw [hφ]
  refine (lintegral_withDensity_eq_lintegral_mul₀ hφm.ennreal_ofReal
    hpaym.aemeasurable).trans ?_
  refine lintegral_congr fun p => ?_
  simp only [Pi.mul_apply]
  rw [mul_comm, ENNReal.ofReal_mul (le_max_right _ _)]

/- Paper: p. 1090–1093, first integral in (6.1) and the display on p. 1093:
     E[(∫₀ᵗ e^{σW_s+μs} ds − k)₊] = ∫₀^∞ ∫₀^∞ ℜ(F_{t,σ,μ,k}(u,w)) du dw. -/
/-- Asian pricing identity (Lyasoff pp. 1090–1093): the undiscounted call equals the
double integral of `Re F` from the π/2-formula of order 4 after Girsanov drift and
`w = e^{σ y / 2}`.

Proof outline.  (1) The expectation is a (nonnegative) integral against the joint law with drift
`ν`, which by Girsanov (`lintegral_jointLaw_girsanov`) is an integral against the driftless joint
law tilted by `exp(θ y − θ² t / 2)`, `θ = ν/σ`.  (2) The driftless law has the order-4 π/2-density
(`pi_half_formula_general`), which is a.e. nonnegative (`piHalfFormula_ae_nonneg`).  (3) Tonelli
in `(x, y)`.  (4) For each fixed `y`, Fubini in `(x, u)` (`asianKernel_fubini`) turns the
`x`-integral into `(σ w / 2) ∫ ℜ F(u, w) du` with `w = e^{σy/2 − νt/2}`.  (5) The substitution
`y ↦ w` (`integral_Ioi_comp_exp_affine`).

The triple integral in `(x, y, u)` is *not* absolutely convergent for every drift (only for
`−3σ²/2 < ν < σ²/2`), so the `y`-integration is carried out last, on nonnegative integrands. -/
theorem asian_price_formula (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ ν : ℝ) (t : ℝ≥0) (K : ℝ)
    (hσ : 0 < σ) (ht : 0 < t) (hK : 0 ≤ K) :
    asianCall P W σ ν t K =
      ∫ w in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), (Ffun σ ν t K u w).re := by
  have hν : σ * (ν / σ) = ν := by field_simp
  have hp4 : (4 : ℕ) = 2 ∨ (4 : ℕ) = 3 ∨ (4 : ℕ) = 4 := Or.inr (Or.inr rfl)
  -- the driftless order-4 π/2-density
  set f₀ : ℝ → ℝ → ℝ := fun x y =>
    gaussianPDFReal 0 t y * (σ ^ 2)⁻¹ * piHalfFormula 4 σ t (x * σ ^ 2) (y * σ) with hf₀
  have hdens : IsJointDensity P W σ 0 t f₀ :=
    pi_half_formula_general P W hW σ t hσ ht 4 hp4
  have hf₀m : Measurable (fun q : ℝ × ℝ => f₀ q.1 q.2) :=
    (((measurable_gaussianPDFReal 0 t).comp measurable_snd).mul_const _).mul
      ((measurable_piHalfFormula 4 σ t).comp
        (show Measurable (fun q : ℝ × ℝ => (q.1 * σ ^ 2, q.2 * σ)) by fun_prop))
  set pay : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (max (p.1 - K) 0) with hpay
  have hpaym : Measurable pay :=
    ((measurable_fst.sub_const K).max measurable_const).ennreal_ofReal
  have hH := aemeasurable_jointMap P W hW σ ν t
  -- (1) the call as a nonnegative integral against the joint law with drift
  have hstep1 : asianCall P W σ ν t K = (∫⁻ p, pay p ∂jointLaw P W σ ν t).toReal := by
    have hmeas : AEStronglyMeasurable (fun ω => max (expInt W σ ν t ω - K) 0) P :=
      ((hH.fst.sub_const K).max aemeasurable_const).aestronglyMeasurable
    unfold asianCall jointLaw
    rw [lintegral_map' hpaym.aemeasurable hH]
    exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => le_max_right _ _) hmeas
  -- (2) Girsanov and the π/2-density
  set I2 : ℝ × ℝ → ℝ≥0∞ := fun q =>
    pay q * ENNReal.ofReal (Real.exp (ν / σ * q.2 - (ν / σ) ^ 2 * (t : ℝ) / 2)) *
      ENNReal.ofReal (f₀ q.1 q.2) with hI2
  have hGm : Measurable (fun q : ℝ × ℝ => pay (q.1, q.2 - ν / σ * (t : ℝ)) *
      ENNReal.ofReal (Real.exp (ν / σ * q.2 - (ν / σ) ^ 2 * (t : ℝ) / 2))) :=
    (hpaym.comp (by fun_prop)).mul (by fun_prop)
  have hI2m : Measurable I2 := (hpaym.mul (by fun_prop)).mul hf₀m.ennreal_ofReal
  have hstep2 : ∫⁻ p, pay p ∂jointLaw P W σ ν t = ∫⁻ q, I2 q := by
    have h := lintegral_jointLaw_girsanov P W hW σ (ν / σ) t pay hpaym
    rw [hν] at h
    rw [h]
    unfold IsJointDensity at hdens
    rw [hdens]
    refine (lintegral_withDensity_eq_lintegral_mul _ hf₀m.ennreal_ofReal hGm).trans ?_
    refine lintegral_congr fun q => ?_
    simp only [Pi.mul_apply, hI2, hpay]
    rw [mul_comm]
  -- (3) Tonelli
  have hstep3 : ∫⁻ q, I2 q = ∫⁻ y, ∫⁻ x, I2 (x, y) := by
    rw [Measure.volume_eq_prod, lintegral_prod_symm _ hI2m.aemeasurable]
  -- (4) fixed-`y` Fubini in `(x, u)`
  set φ : ℝ → ℝ → ℝ := fun y x =>
    (x - K) * (Real.exp (ν / σ * y - (ν / σ) ^ 2 * (t : ℝ) / 2) * f₀ x y) with hφ
  set Q : ℝ → ℝ := fun y => ∫ x in Ioi K, φ y x with hQ
  have hfub := fun y => asianKernel_fubini hσ ν t ht hK y
  have hnn := piHalfFormula_ae_nonneg P W hW hσ t ht hp4
  have hinner : ∀ᵐ y ∂(volume : Measure ℝ),
      ∫⁻ x, I2 (x, y) = ENNReal.ofReal (Q y) ∧ 0 ≤ Q y := by
    filter_upwards [hnn] with y hy
    have hφnn : 0 ≤ᵐ[volume.restrict (Ioi K)] φ y := by
      filter_upwards [ae_restrict_of_ae hy, ae_restrict_mem measurableSet_Ioi] with x hx hxK
      have h1 : 0 ≤ x - K := sub_nonneg.mpr (le_of_lt hxK)
      have h2 : 0 ≤ f₀ x y :=
        mul_nonneg (mul_nonneg (gaussianPDFReal_nonneg 0 t y) (by positivity)) hx
      exact mul_nonneg h1 (mul_nonneg (Real.exp_pos _).le h2)
    refine ⟨?_, integral_nonneg_of_ae hφnn⟩
    have hpt : ∀ x, I2 (x, y) = (Ioi K).indicator (fun x => ENNReal.ofReal (φ y x)) x := by
      intro x
      by_cases hx : K < x
      · rw [Set.indicator_of_mem (mem_Ioi.mpr hx)]
        simp only [hI2, hpay, hφ]
        rw [max_eq_left (sub_nonneg.mpr hx.le), ENNReal.ofReal_mul (sub_nonneg.mpr hx.le),
          ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]
      · rw [Set.indicator_of_notMem (by simpa using hx)]
        simp only [hI2, hpay]
        rw [max_eq_right (sub_nonpos.mpr (not_lt.mp hx)), ENNReal.ofReal_zero, zero_mul,
          zero_mul]
    rw [lintegral_congr hpt, lintegral_indicator measurableSet_Ioi]
    exact (ofReal_integral_eq_lintegral_ofReal (hfub y).1 hφnn).symm
  have hstep4 : ∫⁻ y, ∫⁻ x, I2 (x, y) = ∫⁻ y, ENNReal.ofReal (Q y) :=
    lintegral_congr_ae (hinner.mono fun y hy => hy.1)
  have hQm : AEStronglyMeasurable Q volume := by
    have hm : Measurable (fun y => (∫⁻ x, I2 (x, y)).toReal) :=
      (Measurable.lintegral_prod_left' hI2m).ennreal_toReal
    refine (hm.aemeasurable.congr ?_).aestronglyMeasurable
    filter_upwards [hinner] with y hy
    rw [hy.1, ENNReal.toReal_ofReal hy.2]
  have hstep5 : ∫ y, Q y = (∫⁻ y, ENNReal.ofReal (Q y)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (hinner.mono fun y hy => hy.2) hQm
  -- (5) the substitution `w = e^{σy/2 − νt/2}`
  have hrhs : ∫ w in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), (Ffun σ ν t K u w).re = ∫ y, Q y := by
    rw [integral_Ioi_comp_exp_affine hσ (ν * (t : ℝ) / 2)
      (fun w => ∫ u in Ioi (0 : ℝ), (Ffun σ ν t K u w).re)]
    exact integral_congr_ae (ae_of_all _ fun y => (hfub y).2)
  rw [hstep1, hstep2, hstep3, hstep4, ← hstep5, hrhs]

/-- Consistency: at `K = 0` the pricing formula specialises. -/
theorem asian_price_formula_k_zero (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (σ ν : ℝ) (t : ℝ≥0)
    (hσ : 0 < σ) (ht : 0 < t) :
    asianCall P W σ ν t 0 =
      ∫ w in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), (Ffun σ ν t 0 u w).re :=
  asian_price_formula P W hW σ ν t 0 hσ ht le_rfl

/- Paper: p. 1091–1093, second integral in (6.1), which is the ingredient of the delta (6.2):
     ∂_k E[(∫₀ᵗ e^{σW_s+μs} ds − k)₊] = ∫₀^∞ ∫₀^∞ ℜ(F'_{t,σ,μ,k}(u,w)) du dw. -/

/-- Under an atomless law for `X`, `∂_K E[(X-K)₊] = -P(X > K)`.
Uses `hasDerivAt_integral_of_dominated_loc_of_lip` with bound `1` and the
pointwise derivative from `hasDerivAt_max_sub`. -/
theorem hasDerivAt_integral_max_sub
    (P : Measure Ω) [IsFiniteMeasure P] {X : Ω → ℝ} (hX : AEMeasurable X P) (K : ℝ)
    (hcont : ∀ κ, P {ω | X ω = κ} = 0)
    (hint : ∀ᶠ κ in nhds K, Integrable (fun ω => max (X ω - κ) 0) P) :
    HasDerivAt (fun κ => ∫ ω, max (X ω - κ) 0 ∂P)
      (-(P {ω | K < X ω}).toReal) K := by
  let F : ℝ → Ω → ℝ := fun κ ω => max (X ω - κ) 0
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
    have hpt := hasDerivAt_max_sub (X ω) K hne'
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

/-- Differentiation under `∬ Re F` in the strike (Lyasoff §6 / (6.1)).
Pointwise `∂_k Re F = Re F'` is `hasDerivAt_Ffun_re`; this axiom isolates the
classical justification for passing the derivative under the double improper integral
on `(0, ∞)²`. -/
axiom hasDerivAt_integral_Re_Ffun (σ ν : ℝ) (t : ℝ≥0) (K : ℝ)
    (hσ : 0 < σ) (ht : 0 < t) (hK : 0 < K) :
    HasDerivAt
      (fun κ => ∫ w in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), (Ffun σ ν (t : ℝ) κ u w).re)
      (∫ w in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), (FfunDeriv σ ν (t : ℝ) K u w).re) K

/-- Asian delta identity (Lyasoff pp. 1091–1093): strike derivative of the call equals
the double integral of `Re F'` (`SfunDerivC = ∂_k SfunC`). -/
theorem asian_delta (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ ν : ℝ) (t : ℝ≥0) (K : ℝ)
    (hσ : 0 < σ) (ht : 0 < t) (hK : 0 < K) :
    deriv (fun κ => asianCall P W σ ν t κ) K =
      ∫ w in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), (FfunDeriv σ ν t K u w).re := by
  have heq :
      (fun κ => asianCall P W σ ν t κ) =ᶠ[nhds K]
        fun κ => ∫ w in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), (Ffun σ ν (t : ℝ) κ u w).re := by
    filter_upwards [eventually_ge_nhds hK] with κ hκ
    exact asian_price_formula P W hW σ ν t κ hσ ht hκ
  exact (hasDerivAt_integral_Re_Ffun σ ν t K hσ ht hK).congr_of_eventuallyEq heq |>.deriv

end Lyasoff2016