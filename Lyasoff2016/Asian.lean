/-
# §6 Asian options (pp. 1088–1095)
-/
module

public import Lyasoff2016.FfunDeriv
public import Lyasoff2016.ExpBMIntegrable


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

/- Paper: p. 1088–1090, Asian call price.
   Plain recap: discounted risk-neutral expectation of (∫ e^{σW+νs} ds − K)₊. -/
def asianCall (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (σ ν : ℝ) (t : ℝ≥0) (K : ℝ) : ℝ :=
  ∫ ω, max (expInt W σ ν t ω - K) 0 ∂P

/- Paper: p. 1090–1093, first integral in (6.1) and the display on p. 1093:
     E[(∫₀ᵗ e^{σW_s+μs} ds − k)₊] = ∫₀^∞ ∫₀^∞ ℜ(F_{t,σ,μ,k}(u,w)) du dw. -/
/-- Asian pricing identity (Lyasoff pp. 1090–1093): the undiscounted call equals the
double integral of `Re F` from the π/2-formula of order 4 after Girsanov drift and
`w = e^{σ y / 2}`. Hole: density → payoff reduction not yet formalized. -/
theorem asian_price_formula (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ ν : ℝ) (t : ℝ≥0) (K : ℝ)
    (hσ : 0 < σ) (ht : 0 < t) (hK : 0 ≤ K) :
    asianCall P W σ ν t K =
      ∫ w in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), (Ffun σ ν t K u w).re := by
  sorry

/-- Consistency: at `K = 0` the pricing formula specialises. -/
theorem asian_price_formula_k_zero (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (σ ν : ℝ) (t : ℝ≥0)
    (hσ : 0 < σ) (ht : 0 < t) :
    asianCall P W σ ν t 0 =
      ∫ w in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), (Ffun σ ν t 0 u w).re :=
  asian_price_formula P W hW σ ν t 0 hσ ht le_rfl

/- Paper: p. 1091–1093, second integral in (6.1), which is the ingredient of the delta (6.2):
     ∂_k E[(∫₀ᵗ e^{σW_s+μs} ds − k)₊] = ∫₀^∞ ∫₀^∞ ℜ(F'_{t,σ,μ,k}(u,w)) du dw. -/
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

/-- Asian delta identity (Lyasoff pp. 1091–1093): strike derivative of the call equals
the double integral of `Re F'` (`SfunDerivC = ∂_k SfunC`). Hole: differentiation under
the integral not yet formalized. -/
theorem asian_delta (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ ν : ℝ) (t : ℝ≥0) (K : ℝ)
    (hσ : 0 < σ) (ht : 0 < t) (hK : 0 < K) :
    deriv (fun κ => asianCall P W σ ν t κ) K =
      ∫ w in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), (FfunDeriv σ ν t K u w).re := by
  sorry

end Lyasoff2016