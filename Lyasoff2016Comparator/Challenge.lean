/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import Mathlib.Probability.BrownianMotion.Basic

/-!
# Palomar Challenge (statement of record)

Mathlib-only statement file for the Lyasoff 2016 proof-chart family. Compared
declarations match `Lyasoff2016Comparator/Solution.lean` via the `Lyasoff2016/` library. Framing:
reconstruction/verification of Lyasoff, *Another look at the integral of
exponential Brownian motion and the pricing of Asian options*, Finance Stoch.
20 (2016) 1061–1096. Andrew Lyasoff did not participate in or endorse this
formalization. Every compared theorem's Solution proof uses only `propext` /
`Quot.sound` / `Classical.choice`. Tables 1–4 are reported numerical data only,
outside Comparator (see `PROVENANCE.md` / `formalization.yaml`).
-/
@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real
-- Do not `open scoped ContDiff`: it reserves `ω` as an infinity notation.

namespace Lyasoff2016

-- Force the same level-parameter name Comparator sees on Solution (`u_1`).
-- Mathlib-only Challenge otherwise elaborates `Type*` as `u_2`.
universe u_1

noncomputable section

abbrev IsBM {Ω : Type u_1} [MeasurableSpace Ω] (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) : Prop :=
  IsBrownianReal W P

variable {Ω : Type u_1} [MeasurableSpace Ω]

def expInt (W : ℝ≥0 → Ω → ℝ) (σ ν : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (σ * W s.toNNReal ω + ν * s)

def jointLaw (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (σ ν : ℝ) (t : ℝ≥0) : Measure (ℝ × ℝ) :=
  P.map (fun ω => (expInt W σ ν t ω, W t ω))

def IsJointDensity (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (σ ν : ℝ) (t : ℝ≥0)
    (φ : ℝ → ℝ → ℝ) : Prop :=
  jointLaw P W σ ν t =
    (volume : Measure (ℝ × ℝ)).withDensity (fun p => ENNReal.ofReal (φ p.1 p.2))

def IsCondDensity (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (σ : ℝ) (t : ℝ≥0)
    (φc : ℝ → ℝ → ℝ) : Prop :=
  IsJointDensity P W σ 0 t (fun x y => gaussianPDFReal 0 t y * φc x y)

def pd (m n : ℕ) (φ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  iteratedDeriv m (fun x' => iteratedDeriv n (fun y' => φ x' y') y) x

def invGammaDensity (p : ℝ) (a x : ℝ) : ℝ :=
  a ^ (p - 1) / Real.Gamma (p - 1) * x ^ (-p) * Real.exp (-a / x)

def IsInftyDensity (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (σ ν : ℝ) (ψ : ℝ → ℝ) : Prop :=
  P.map (fun ω => ∫ s in Ioi (0 : ℝ), Real.exp (σ * W s.toNNReal ω + ν * s)) =
    (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (ψ x))

def Zproc (W B : ℝ≥0 → Ω → ℝ) (σ ν : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (ν * (t : ℝ) - σ * B t ω) *
    ((∫ s in Ioi (0 : ℝ), Real.exp (σ * W s.toNNReal ω + ν * s)) +
     ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-ν * s + σ * B s.toNNReal ω))

def gammaMoment (β a : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => (β + n) / a * gammaMoment β a n

def jointA (σ : ℝ) (ϕ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  σ ^ 2 * x ^ 2 / 2 * iteratedDeriv 2 (fun x' => ϕ x' y) x
    + σ * x * deriv (fun y' => deriv (fun x' => ϕ x' y') x) y
    + (σ ^ 2 * x / 2 + 1 - Real.exp (σ * y)) * deriv (fun x' => ϕ x' y) x

def jointDomain : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)

def SatisfiesStrikingIdentity (σ t : ℝ) (φc : ℝ → ℝ → ℝ) : Prop :=
  (∀ y : ℝ, y ≠ 0 →
    ∫ x in Ioi (0 : ℝ), x⁻¹ * φc x (y / σ) =
      y / (t * (Real.exp y - 1))) ∧
  (∫ x in Ioi (0 : ℝ), x⁻¹ * φc x 0 = 1 / t)

def laplaceCond (φc : ℝ → ℝ → ℝ) (y u : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), Real.exp (-u / x) * φc x y

def Sfun (k p : ℕ) (α : ℝ) : ℝ :=
  ∫ v in Ioi (0 : ℝ), max (v - (k : ℝ)) 0 * v ^ (-(p : ℤ)) * Real.exp (-α / v)

def SfunC (k : ℝ) (p : ℕ) (A : ℂ) : ℂ :=
  ∫ x in Ioi k, (((x - k) * x ^ (-(p : ℤ)) : ℝ) : ℂ) * Complex.exp (-A / x)

def SfunDerivC (k : ℝ) (p : ℕ) (A : ℂ) : ℂ :=
  -∫ x in Ioi k, ((x ^ (-(p : ℤ)) : ℝ) : ℂ) * Complex.exp (-A / x)

def upperGamma (s x : ℝ) : ℝ :=
  ∫ u in Ioi x, u ^ (s - 1) * Real.exp (-u)

def asianCall (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (σ ν : ℝ) (t : ℝ≥0) (K : ℝ) : ℝ :=
  ∫ ω, max (expInt W σ ν t ω - K) 0 ∂P

def asianMarketPrice (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (σ r : ℝ) (T : ℝ≥0) (K : ℝ) : ℝ :=
  Real.exp (-r * (T : ℝ)) * (1 / (T : ℝ)) *
    asianCall P W σ (r - σ ^ 2 / 2) T (K * (T : ℝ))

def yorDensity (t x y : ℝ) : ℝ := sorry

def piFormula (p : ℕ) (σ t x y : ℝ) : ℝ := sorry

def piHalfFormula (p : ℕ) (σ t x y : ℝ) : ℝ := sorry

def contourIntegrand (p : ℕ) (t a y u : ℝ) : ℂ := sorry

def Ffun (σ ν t k : ℝ) (u w : ℝ) : ℂ := sorry

def FfunDeriv (σ ν t k : ℝ) (u w : ℝ) : ℂ := sorry

def dufresne (σ ν x : ℝ) : ℝ := sorry

-- Opaque to Comparator: single-file Challenge elaborates Real numerals ≥2 with a
-- shared `jointA._proof_N`, while multi-file Solution gives each decl its own
-- `_proof_N`. Types match; values are supplied by Solution.
def jointFokkerPlanckAdjoint (σ : ℝ) (φ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := sorry

def SatisfiesTheorem41PDE (σ t : ℝ) (φc : ℝ → ℝ → ℝ) : Prop := sorry

def SatisfiesFoliationODE (σ t : ℝ) (φc : ℝ → ℝ → ℝ) : Prop := sorry

def TransformedMassIdentity (σ t : ℝ) (φ0 : ℝ → ℝ) : Prop := sorry

def HasLaplaceReduction (σ t : ℝ) (φc : ℝ → ℝ → ℝ) : Prop := sorry

def contourEq (p : ℕ) (t : ℝ) (y : ℝ) (a : ℝ) : Prop := sorry

theorem time_reversal (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (n : ℕ) (V : Fin n → ℝ → ℝ → ℝ)
    (hV : ∀ i, Continuous (Function.uncurry (V i))) (t : ℝ≥0) :
    P.map (fun ω => (fun i => ∫ s in (0 : ℝ)..(t : ℝ), V i s (W s.toNNReal ω), W t ω)) =
    P.map (fun ω =>
      (fun i => ∫ s in (0 : ℝ)..(t : ℝ), V i (t - s) (W t ω - W s.toNNReal ω), W t ω)) := by
  sorry

theorem lemma_2_1 (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (hσ : 0 < σ) (ht : 0 < t) (p : ℕ) :
    Integrable (fun ω => (expInt W σ 0 t ω) ^ p) P ∧
    Integrable (fun ω => (expInt W σ 0 t ω) ^ (-(p : ℤ))) P := by
  sorry

theorem prop_2_2 (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (hσ : 0 < σ) (ht : 0 < t) :
    ∃ φc : ℝ → ℝ → ℝ, IsCondDensity P W σ t φc ∧
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry φc) (Ioi (0 : ℝ) ×ˢ univ)) ∧
      (∀ y, Tendsto (fun x => φc x y) (nhdsWithin 0 (Ioi 0)) (nhds 0)) ∧
      (∀ m n y, Tendsto (fun x => pd m n φc x y) atTop (nhds 0)) ∧
      (∀ m n y, ∃ l, Tendsto (fun x => pd m n φc x y) (nhdsWithin 0 (Ioi 0)) (nhds l)) ∧
      (∀ m n p : ℕ,
        (∫⁻ y, ENNReal.ofReal (Real.exp (-y ^ 2 / (2 * (t : ℝ)))) *
          ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |(x : ℝ) ^ (p : ℤ) * pd m n φc x y|) < ∞ ∧
        (∫⁻ y, ENNReal.ofReal (Real.exp (-y ^ 2 / (2 * (t : ℝ)))) *
          ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |(x : ℝ) ^ (-(p : ℤ)) * pd m n φc x y|) < ∞) := by
  sorry

theorem scaling_relations (σ : ℝ) (t : ℝ≥0) (hσ : 0 < σ) (ht : 0 < t)
    (φ₁ φσ : ℝ → ℝ → ℝ) (c₁ cσ : ℝ → ℝ → ℝ) (ψ₁ ψσ : ℝ → ℝ) (ν : ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W)
    (h1 : IsJointDensity P W 1 0 t φ₁)
    (hσ' : IsJointDensity P W σ 0 ((↑t : ℝ) / σ ^ 2).toNNReal φσ)
    (hc1 : IsCondDensity P W 1 t c₁)
    (hcσ : IsCondDensity P W σ ((↑t : ℝ) / σ ^ 2).toNNReal cσ)
    (hψ₁ : IsInftyDensity P W 1 ν ψ₁) (hψσ : IsInftyDensity P W σ (ν * σ ^ 2) ψσ)
    (hφcont : Continuous (Function.uncurry φ₁) ∧ Continuous (Function.uncurry φσ))
    (hccont : Continuous (Function.uncurry c₁) ∧ Continuous (Function.uncurry cσ))
    (hψcont : Continuous ψ₁ ∧ Continuous ψσ)
    (hφnn : (∀ x y, 0 ≤ φ₁ x y) ∧ ∀ x y, 0 ≤ φσ x y)
    (hcnn : (∀ x y, 0 ≤ c₁ x y) ∧ ∀ x y, 0 ≤ cσ x y)
    (hψnn : (∀ x, 0 ≤ ψ₁ x) ∧ ∀ x, 0 ≤ ψσ x) :
    (∀ x y, φ₁ x y = σ⁻¹ ^ 3 * φσ (x / σ ^ 2) (y / σ)) ∧
    (∀ x y, c₁ x y = σ⁻¹ ^ 2 * cσ (x / σ ^ 2) (y / σ)) ∧
    (∀ x, ψ₁ x = σ⁻¹ ^ 2 * ψσ (x / σ ^ 2)) := by
  sorry

theorem girsanov_density (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ μ : ℝ) (t : ℝ≥0) (hσ : 0 < σ) (_ht : 0 < t)
    (φμ φ0 : ℝ → ℝ → ℝ) (h1 : IsJointDensity P W σ μ t φμ)
    (h0 : IsJointDensity P W σ 0 t φ0)
    (hcont : Continuous (Function.uncurry φμ) ∧ Continuous (Function.uncurry φ0))
    (hnn : (∀ x y, 0 ≤ φμ x y) ∧ ∀ x y, 0 ≤ φ0 x y) :
    ∀ x y, φμ x y =
      Real.exp (μ / σ * y + μ ^ 2 / (2 * σ ^ 2) * (t : ℝ)) * φ0 x (y + μ / σ * (t : ℝ)) := by
  sorry

theorem infinite_integral_finite (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ ν : ℝ) (hσ : 0 < σ) (hν : ν < 0) :
    ∀ᵐ ω ∂P, ∃ L : ℝ, Tendsto (fun T : ℝ≥0 => expInt W σ ν T ω) atTop (nhds L) := by
  sorry

theorem Z_stationary (P : Measure Ω) [IsProbabilityMeasure P] (W B : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (hB : IsBM P B)
    (hWB : IndepFun (fun ω => fun t : ℝ≥0 => W t ω) (fun ω => fun t : ℝ≥0 => B t ω) P)
    (σ ν : ℝ) (hσ : 0 < σ) (hν : ν < 0) (t : ℝ≥0) :
    P.map (Zproc W B σ ν t) =
      P.map (fun ω => ∫ s in Ioi (0 : ℝ), Real.exp (σ * W s.toNNReal ω + ν * s)) := by
  sorry

theorem dufresne_zero_flux (σ ν : ℝ) (hσ : 0 < σ) (x : ℝ) (hx : 0 < x) :
    σ ^ 2 / 2 * deriv (fun z => z ^ 2 * dufresne σ ν z) x
      - (1 + (ν + σ ^ 2 / 2) * x) * dufresne σ ν x = 0 := by
  sorry

theorem perpetuity_inv_moment (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (ν : ℝ) (hν : ν < 0) :
    ∫⁻ ω, ENNReal.ofReal
        ((∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s))⁻¹) ∂P =
      ENNReal.ofReal (-ν) := by
  sorry

theorem perpetuity_neg_moments (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (ν : ℝ) (hν : ν < 0) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal
        ((∫ s in Ioi (0 : ℝ), Real.exp (W s.toNNReal ω + ν * s))⁻¹ ^ n) ∂P =
      ENNReal.ofReal (gammaMoment (-2 * ν) 2 n) := by
  sorry

theorem dufresne_theorem_sigma_one (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (ν : ℝ) (hν : ν < 0) :
    IsInftyDensity P W 1 ν (dufresne 1 ν) := by
  sorry

theorem dufresne_theorem (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ ν : ℝ) (hσ : 0 < σ) (hν : ν < 0) :
    IsInftyDensity P W σ ν (dufresne σ ν) := by
  sorry

theorem ito_expInt_test_product (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (σ : ℝ) (t : ℝ≥0)
    (u v : ℝ → ℝ) (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (huC : HasCompactSupport u) (hvC : HasCompactSupport v) :
    (∫ ω, u (expInt W σ 0 t ω) * v (W t ω) ∂P) - u 0 * v 0 =
      ∫ s in Ioc (0 : ℝ) t,
        (∫ ω,
          deriv u (expInt W σ 0 s.toNNReal ω) * Real.exp (σ * W s.toNNReal ω) * v (W s.toNNReal ω)
            + u (expInt W σ 0 s.toNNReal ω) * ((1 : ℝ) / 2) *
                deriv (deriv v) (W s.toNNReal ω) ∂P) := by
  sorry

theorem ito_timeReversed_expInt_test_product (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (_ht : 0 < t)
    (u v : ℝ → ℝ) (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (huC : HasCompactSupport u) (hvC : HasCompactSupport v) :
    (∫ ω, u (expInt W σ 0 t ω) * v (W t ω) ∂P) - u 0 * v 0 =
      ∫ s in Ioc (0 : ℝ) t,
        (∫ ω,
          let X := expInt W σ 0 s.toNNReal ω
          let Y := W s.toNNReal ω
          (1 : ℝ) * deriv u X * v Y
            + (σ ^ 2 / 2) * X * deriv u X * v Y
            + (σ ^ 2 / 2) * X ^ 2 * deriv (deriv u) X * v Y
            + σ * X * deriv u X * deriv v Y
            + (1 / 2) * u X * deriv (deriv v) Y ∂P) := by
  sorry

theorem joint_dynkin_Aop_product (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (ht : 0 < t)
    (u v : ℝ → ℝ) (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (huC : HasCompactSupport u) (hvC : HasCompactSupport v) :
    ∫ ω, jointA σ (fun x y => u x * v y) (expInt W σ 0 t ω) (W t ω) ∂P = 0 := by
  sorry

theorem weak_joint_fokker_planck_product (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (ht : 0 < t)
    (φ : ℝ → ℝ → ℝ) (hφ : IsJointDensity P W σ 0 t φ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry φ) jointDomain)
    (hφnn : ∀ x y, 0 ≤ φ x y)
    (hφm : AEMeasurable (fun p : ℝ × ℝ => φ p.1 p.2) volume)
    (u v : ℝ → ℝ) (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (huC : HasCompactSupport u) (hvC : HasCompactSupport v)
    (hsupp : tsupport (fun p : ℝ × ℝ => u p.1 * v p.2) ⊆ jointDomain) :
    ∫ p : ℝ × ℝ, u p.1 * v p.2 * jointFokkerPlanckAdjoint σ φ p.1 p.2 = 0 := by
  sorry

theorem eq_zero_of_integral_product_eq_zero {f : ℝ × ℝ → ℝ}
    (hcont : ContinuousOn f jointDomain)
    (hweak : ∀ (u v : ℝ → ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v →
      HasCompactSupport u → HasCompactSupport v →
      tsupport (fun p : ℝ × ℝ => u p.1 * v p.2) ⊆ jointDomain →
      ∫ p : ℝ × ℝ, u p.1 * v p.2 * f p = 0)
    {x y : ℝ} (hx : 0 < x) :
    f (x, y) = 0 := by
  sorry

theorem jointFokkerPlanckAdjoint_eq_zero (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (ht : 0 < t)
    (φ : ℝ → ℝ → ℝ) (hφ : IsJointDensity P W σ 0 t φ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry φ) jointDomain)
    (hφnn : ∀ x y, 0 ≤ φ x y)
    (hφm : AEMeasurable (fun p : ℝ × ℝ => φ p.1 p.2) volume)
    (x y : ℝ) (hx : 0 < x) :
    jointFokkerPlanckAdjoint σ φ x y = 0 := by
  sorry

theorem fokker_planck_joint (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (_hσ : 0 < σ) (ht : 0 < t)
    (φ : ℝ → ℝ → ℝ) (hφ : IsJointDensity P W σ 0 t φ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry φ) (Ioi (0 : ℝ) ×ˢ univ))
    (hφnn : ∀ x y, 0 ≤ φ x y)
    (hφm : AEMeasurable (fun p : ℝ × ℝ => φ p.1 p.2) volume)
    (x y : ℝ) (hx : 0 < x) :
    deriv (fun x' =>
        σ ^ 2 * x' ^ 2 / 2 * deriv (fun z => φ z y) x'
          + σ * x' * deriv (fun y' => φ x' y') y
          + (Real.exp (σ * y) + σ ^ 2 * x' / 2 - 1) * φ x' y) x = 0 := by
  sorry

theorem remark_3_2 (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (t : ℝ≥0) (_ht : 0 < t) :
    P.map (fun ω =>
      (expInt W 1 0 t ω,
        (⨆ s : Icc (0 : ℝ≥0) t, W s ω) - W t ω,
        ⨆ s : Icc (0 : ℝ≥0) t, W s ω)) =
    P.map (fun ω =>
      (Real.exp (-W t ω) * expInt W 1 0 t ω,
        ⨆ s : Icc (0 : ℝ≥0) t, W s ω,
        (⨆ s : Icc (0 : ℝ≥0) t, W s ω) - W t ω)) := by
  sorry

theorem theorem_4_1_pde (σ t : ℝ) (φc : ℝ → ℝ → ℝ)
    (htransport : SatisfiesTheorem41PDE σ t φc) (x y : ℝ) (hx : 0 < x) :
    σ ^ 2 * x / 2 * deriv (fun z => φc z y) x + σ * deriv (fun y' => φc x y') y
      = (σ * y / t + (1 - Real.exp (σ * y)) / x - σ ^ 2 / 2) * φc x y := by
  sorry

theorem theorem_4_1_striking (σ t : ℝ)
    (φc : ℝ → ℝ → ℝ) (hbalance : SatisfiesStrikingIdentity σ t φc) (y : ℝ) :
    ∫ x in Ioi (0 : ℝ), x⁻¹ * φc x (y / σ)
      = if y = 0 then 1 / t else y / (t * (Real.exp y - 1)) := by
  sorry

theorem formula_4_6 (σ t : ℝ) (hσ : 0 < σ) (φc : ℝ → ℝ → ℝ)
    (hfol : SatisfiesFoliationODE σ t φc) (x y : ℝ) (hx : 0 < x) :
    φc x y =
      φc (x * Real.exp (-(σ * y) / 2)) 0 *
        Real.exp (-(σ * y) / 2 -
          2 / (σ ^ 2 * x) * (Real.exp (σ * y / 2) - 1) ^ 2 + y ^ 2 / (2 * t)) := by
  sorry

theorem prop_4_4 (φ ψ : ℝ → ℝ)
    (_hφm : AEStronglyMeasurable φ (volume.restrict (Ioi 0)))
    (_hψm : AEStronglyMeasurable ψ (volume.restrict (Ioi 0)))
    (hφi : Integrable φ (volume.restrict (Ioi 0)))
    (hψi : Integrable ψ (volume.restrict (Ioi 0)))
    (hφ : ∀ u ≥ 0, laplaceCond (fun x _ => φ x) 0 u =
      laplaceCond (fun x _ => ψ x) 0 u) :
    ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)), φ x = ψ x := by
  sorry

theorem theorem_4_5 (σ t : ℝ) (hσ : 0 < σ) (ht : 0 < t)
    (φc : ℝ → ℝ → ℝ) (hmass : TransformedMassIdentity σ t (fun x => φc x 0))
    (hreduce : HasLaplaceReduction σ t φc) (y u : ℝ) (hu : 0 ≤ u) :
    laplaceCond φc y u =
      Real.exp (y ^ 2 / (2 * t) -
        2 / (σ ^ 2 * t) *
          Real.arcosh (Real.cosh (σ * y / 2) +
            u * σ ^ 2 / 4 * Real.exp (-(σ * y) / 2)) ^ 2) := by
  sorry

theorem cond_density_satisfies_theorem_41_pde (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (_hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (_hσ : 0 < σ) (_ht : 0 < t) :
    ∃ φc : ℝ → ℝ → ℝ, IsCondDensity P W σ t φc ∧ SatisfiesTheorem41PDE σ t φc := by
  sorry

theorem cond_density_satisfies_striking (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (_hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (_hσ : 0 < σ) (_ht : 0 < t) :
    ∃ φc : ℝ → ℝ → ℝ, IsCondDensity P W σ t φc ∧ SatisfiesStrikingIdentity σ t φc := by
  sorry

theorem cond_density_satisfies_foliation_ode (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (_hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (_hσ : 0 < σ) (_ht : 0 < t) :
    ∃ φc : ℝ → ℝ → ℝ, IsCondDensity P W σ t φc ∧ SatisfiesFoliationODE σ t φc := by
  sorry

theorem cond_density_satisfies_laplace_inputs (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (_hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (_hσ : 0 < σ) (_ht : 0 < t) :
    ∃ φc : ℝ → ℝ → ℝ,
      IsCondDensity P W σ t φc ∧
        TransformedMassIdentity σ t (fun x => φc x 0) ∧ HasLaplaceReduction σ t φc := by
  sorry

theorem g_solves_contour_equation (p : ℕ) (hp : p = 2 ∨ p = 3 ∨ p = 4)
    (t : ℝ) (ht : 0 < t) (y : ℝ) (a : ℝ) (ha : Real.pi / 2 ≤ a ∧ a ≤ 3 * Real.pi / 2) :
    contourEq p t y a := by
  sorry

theorem remark_5_1 (t : ℝ≥0) (x y : ℝ) (ht : 0 < t) (_hx : 0 < x) :
    gaussianPDFReal 0 t y * (2 ^ 2 : ℝ)⁻¹ *
        piFormula 2 2 t (x * 2 ^ 2) (y * 2) =
      yorDensity t x y := by
  sorry

theorem pi_formula (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (hσ : 0 < σ) (ht : 0 < t) (p : ℕ)
    (hp : p = 2 ∨ p = 3 ∨ p = 4) :
    IsJointDensity P W σ 0 t (fun x y =>
      gaussianPDFReal 0 t y * (σ ^ 2)⁻¹ * piHalfFormula p σ t (x * σ ^ 2) (y * σ)) ∧
    IsJointDensity P W σ 0 t (fun x y =>
      gaussianPDFReal 0 t y * (σ ^ 2)⁻¹ * piFormula p σ t (x * σ ^ 2) (y * σ)) := by
  sorry

theorem yor_formula (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (t : ℝ≥0) (ht : 0 < t) :
    IsJointDensity P W 2 0 t (fun x y => yorDensity t x y) := by
  sorry

theorem S_zero (p : ℕ) (α : ℝ) (hp : 3 ≤ p) (hα : 0 < α) :
    Sfun 0 p α = α ^ (-((p : ℝ) - 2)) * Real.Gamma ((p : ℝ) - 2) := by
  sorry

theorem S_closed_form (k p : ℕ) (α : ℝ) (hk : 0 < (k : ℝ)) (hp : 3 ≤ p) (hα : 0 < α) :
    Sfun k p α =
      (k : ℝ) * α ^ (-((p : ℝ) - 1)) * upperGamma ((p : ℝ) - 1) (α / k) -
        α ^ (-((p : ℝ) - 2)) * upperGamma ((p : ℝ) - 2) (α / k) -
        (k : ℝ) * α ^ (-((p : ℝ) - 1)) * Real.Gamma ((p : ℝ) - 1) +
        α ^ (-((p : ℝ) - 2)) * Real.Gamma ((p : ℝ) - 2) := by
  sorry

theorem benchmark_k_zero (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ ν : ℝ) (t : ℝ≥0) (_hσ : 0 < σ) (_ht : 0 < t) :
    ∫ ω, expInt W σ ν t ω ∂P =
      ∫ s in (0 : ℝ)..(t : ℝ), Real.exp ((ν + σ ^ 2 / 2) * s) := by
  sorry

theorem asian_price_formula (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ ν : ℝ) (t : ℝ≥0) (K : ℝ)
    (hσ : 0 < σ) (ht : 0 < t) (hK : 0 ≤ K) :
    asianCall P W σ ν t K =
      ∫ w in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), (Ffun σ ν t K u w).re := by
  sorry

theorem asian_delta (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ ν : ℝ) (t : ℝ≥0) (K : ℝ)
    (hσ : 0 < σ) (ht : 0 < t) (hK : 0 < K) :
    deriv (fun κ => asianCall P W σ ν t κ) K =
      ∫ w in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), (FfunDeriv σ ν t K u w).re := by
  sorry

theorem SfunC.hasDerivAt (k : ℝ) (p : ℕ) (A : ℂ)
    (hk : 0 < k) (hp : 3 ≤ p) (hA : 0 < A.re) :
    HasDerivAt (fun κ => SfunC κ p A) (SfunDerivC k p A) k := by
  sorry

theorem hasDerivAt_integral_Re_Ffun
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W)
    (σ ν : ℝ) (t : ℝ≥0) (K : ℝ)
    (hσ : 0 < σ) (ht : 0 < t) (hK : 0 < K) :
    HasDerivAt
      (fun κ => ∫ w in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), (Ffun σ ν (t : ℝ) κ u w).re)
      (∫ w in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), (FfunDeriv σ ν (t : ℝ) K u w).re) K := by
  sorry

end
end Lyasoff2016
