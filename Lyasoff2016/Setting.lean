/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

# Setting and §1 Introduction (Lyasoff, Finance Stoch. 20 (2016) 1061–1063)

Paper-position comments use journal page numbers 1061–1096.
-/
import Mathlib
import Mathlib.Probability.BrownianMotion.Basic
import Lyasoff2016.Lib.TimeReversal
import Lyasoff2016.Lib.BMFunctionalLaw

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/-! ## §0 Setting: Brownian motion (Mathlib `IsBrownianReal`) -/

/- Paper: p. 1061 onwards, standing assumption.
   Plain recap: a Brownian motion starts at 0, has continuous paths, and
   Gaussian independent increments. We use Mathlib's `IsBrownianReal`
   (time indexed by `ℝ≥0`). -/
abbrev IsBM {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) : Prop :=
  IsBrownianReal W P

variable {Ω : Type*} [MeasurableSpace Ω]

/- Paper: p. 1062, display after (1.1) / expectations of the form E[f(∫ e^{σW+νs} ds)].
   Plain recap: the integral of exponential Brownian motion with drift up to time t. -/
def expInt (W : ℝ≥0 → Ω → ℝ) (σ ν : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (σ * W s.toNNReal ω + ν * s)

/- Paper: p. 1061, joint law in (1.1).
   Plain recap: the law of the pair (∫₀ᵗ e^{σW_s+νs} ds, W_t). -/
def jointLaw (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (σ ν : ℝ) (t : ℝ≥0) : Measure (ℝ × ℝ) :=
  P.map (fun ω => (expInt W σ ν t ω, W t ω))

/- Paper: p. 1061, (1.1), φ_{t,σ}(x,y).
   Plain recap: φ is a Lebesgue density of that joint law. -/
def IsJointDensity (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (σ ν : ℝ) (t : ℝ≥0)
    (φ : ℝ → ℝ → ℝ) : Prop :=
  jointLaw P W σ ν t =
    (volume : Measure (ℝ × ℝ)).withDensity (fun p => ENNReal.ofReal (φ p.1 p.2))

/- Paper: p. 1065, Prop. 2.2 factorization.
   Plain recap: the conditional density φ(x|y) of the integral given W_t = y,
   related by φ(x,y) = gaussianPDF(y) · φ(x|y). -/
def IsCondDensity (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (σ : ℝ) (t : ℝ≥0)
    (φc : ℝ → ℝ → ℝ) : Prop :=
  IsJointDensity P W σ 0 t (fun x y => gaussianPDFReal 0 t y * φc x y)

/- Paper: used throughout for mixed derivatives of densities.
   Plain recap: mixed partial ∂^{m+n}/∂x^m ∂y^n. -/
def pd (m n : ℕ) (φ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  iteratedDeriv m (fun x' => iteratedDeriv n (fun y' => φ x' y') y) x

/-! ## §1 Introduction (pp. 1061–1063) -/

/- Paper: p. 1062, θ(r,t) in Yor’s formula.
   Plain recap: the Hartman–Watson-type kernel appearing in Yor’s density. -/
def theta (r t : ℝ) : ℝ :=
  r / Real.sqrt (2 * Real.pi ^ 3 * t) * Real.exp (Real.pi ^ 2 / (2 * t)) *
    ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * t)) * Real.exp (-r * Real.cosh u) *
      Real.sinh u * Real.sin (Real.pi * u / t)

/- Paper: p. 1061, (1.1).
   Plain recap: Yor’s candidate joint density for σ = 2. -/
def yorDensity (t x y : ℝ) : ℝ :=
  (1 / x) * Real.exp (-(1 + Real.exp (2 * y)) / (2 * x)) * theta (Real.exp y / x) t

/- Paper: p. 1061 (1.1) — Yor’s theorem [33, (6.c)].
   Plain recap: stated here; proved in `IntegralReps` as `yor_formula` via Remark 5.1. -/

/- Paper: p. 1062, densities of the form (1.2).
   Plain recap: inverse-Gamma shape densities a^{p-1}/Γ(p-1) · x^{-p} e^{-a/x}. -/
def invGammaDensity (p : ℝ) (a x : ℝ) : ℝ :=
  a ^ (p - 1) / Real.Gamma (p - 1) * x ^ (-p) * Real.exp (-a / x)

/- Paper: p. 1063, display (1.3).
   Plain recap: time-reversibility in law for integral functionals of BM:
   (∫ V_i(s,W_s) ds, W_t) has the same law as (∫ V_i(t-s, W_t-W_s) ds, W_t). -/
theorem time_reversal (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (n : ℕ) (V : Fin n → ℝ → ℝ → ℝ)
    (hV : ∀ i, Continuous (Function.uncurry (V i))) (t : ℝ≥0) :
    P.map (fun ω => (fun i => ∫ s in (0 : ℝ)..(t : ℝ), V i s (W s.toNNReal ω), W t ω)) =
    P.map (fun ω =>
      (fun i => ∫ s in (0 : ℝ)..(t : ℝ), V i (t - s) (W t ω - W s.toNNReal ω), W t ω)) := by
  have hB : IsBM P (timeReversed W t) := isBrownianReal_timeReversed P W hW t
  have hlaw := isBrownianReal_integral_functional_law_eq P W (timeReversed W t) hW hB n V hV t
  refine hlaw.trans ?_
  refine Measure.map_congr ?_
  filter_upwards [hW.eval_zero_ae_eq_zero] with ω h0
  exact (timeReversed_functional_eq W t ω n V h0).symm

end Lyasoff2016
