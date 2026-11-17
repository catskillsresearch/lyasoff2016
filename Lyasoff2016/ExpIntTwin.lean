/-
Time-reversed twin of `expInt` and basic measurability/continuity.
-/
module

public import Lyasoff2016.Setting
public import MathFin.Probability.Brownian.Ito.ItoFormulaTD
public import MathFin.Probability.Brownian.Ito.ItoFormulaAdaptedProcess
public import MathFin.Probability.Brownian.Ito.ItoIntegralProcessGeneral


@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open MeasureTheory.Measure
open MathFin ItoFormulaAdapted ItoIntegralL2 ItoIntegralProcessGeneral
  ItoIntegralLocalised AdaptedDrift LocalisationInMeasure
open scoped NNReal ENNReal

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The time-reversed twin of `expInt`: `Y_s = e^{σ B_s} ∫₀ˢ e^{-σ B_r} dr = ∫₀ˢ e^{σ (B_s - B_r)} dr`.
It solves `dY = (1 + σ² Y / 2) ds + σ Y dB`, and `(Y_s, B_s)` has the law of
`(∫₀ˢ e^{σ B_r} dr, B_s)` at each fixed `s`. -/
def expIntTwin (B : ℝ≥0 → Ω → ℝ) (σ : ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (σ * B s ω) * driftPath (fun r ω ↦ Real.exp (-σ * B r ω)) s ω

/-- The time integral of `e^{a B}` up to a fixed time is measurable. -/
theorem measurable_driftPath_exp {B : ℝ≥0 → Ω → ℝ} (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) (a : ℝ) (s : ℝ≥0) :
    Measurable (driftPath (fun r ω ↦ Real.exp (a * B r ω)) s) :=
  measurable_pathIntegral (w := fun r ω ↦ Real.exp (a * B r ω))
    (fun r ↦ Real.continuous_exp.measurable.comp ((hBmeas r).const_mul a))
    (fun ω ↦ Real.continuous_exp.comp (continuous_const.mul (hBcont ω))) s

namespace expIntTwin

/-- The twin is measurable at each time. -/
theorem measurable {B : ℝ≥0 → Ω → ℝ} (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) (σ : ℝ) (s : ℝ≥0) :
    Measurable (expIntTwin B σ s) :=
  (Real.continuous_exp.measurable.comp ((hBmeas s).const_mul σ)).mul
    (measurable_driftPath_exp hBmeas hBcont (-σ) s)

/-- The twin is adapted to the natural filtration of `B`. -/
theorem stronglyAdapted {B : ℝ≥0 → Ω → ℝ} (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) (σ : ℝ) (s : ℝ≥0) :
    StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)] (expIntTwin B σ s) :=
  ((show Continuous fun x : ℝ ↦ Real.exp (σ * x) by fun_prop).comp_stronglyMeasurable
    (stronglyAdapted_natFiltration hBmeas s)).mul
    ((driftPath_isStronglyPredictable_of_continuous hBmeas
      (fun r ↦ (show Continuous fun x : ℝ ↦ Real.exp (-σ * x) by fun_prop).comp_stronglyMeasurable
        (stronglyAdapted_natFiltration hBmeas r))
      (fun ω ↦ Real.continuous_exp.comp (continuous_const.mul (hBcont ω)))).stronglyAdapted s)

omit [MeasurableSpace Ω] in
/-- Every path of the twin is continuous. -/
theorem continuous {B : ℝ≥0 → Ω → ℝ}
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) (σ : ℝ) (ω : Ω) :
    Continuous fun s ↦ expIntTwin B σ s ω :=
  (Real.continuous_exp.comp (continuous_const.mul (hBcont ω))).mul
    (continuous_driftPath_of_continuous (b := fun r ω ↦ Real.exp (-σ * B r ω))
      (Real.continuous_exp.comp (continuous_const.mul (hBcont ω))))

end expIntTwin

end Lyasoff2016
