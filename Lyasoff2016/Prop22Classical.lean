/-
Lyasoff Prop. 2.2 (conditional density regularity), wired to the constructive
proof `prop_2_2_constructive` in `YorAnalytic`.
-/
module

public import Lyasoff2016.YorAnalytic


@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Prop. 2.2 (Lyasoff 2016, p. 1065): existence of a conditional density
`φc` of `expInt` given `W_t` that is `C^∞` on `{x > 0}`, vanishes at the origin,
has controlled mixed partials at `0⁺`/`∞`, and Gaussian-weighted moment bounds.

Proved constructively as `prop_2_2_constructive` (Yor conditional density analysis);
kept under this name as a classical citation point. -/
theorem prop_2_2_classical (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (σ : ℝ) (t : ℝ≥0)
    (hσ : 0 < σ) (ht : 0 < t) :
    ∃ φc : ℝ → ℝ → ℝ, IsCondDensity P W σ t φc ∧
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry φc) (Ioi (0 : ℝ) ×ˢ univ)) ∧
      (∀ y, Tendsto (fun x => φc x y) (nhdsWithin 0 (Ioi 0)) (nhds 0)) ∧
      (∀ m n y, Tendsto (fun x => pd m n φc x y) atTop (nhds 0)) ∧
      (∀ m n y, ∃ l, Tendsto (fun x => pd m n φc x y) (nhdsWithin 0 (Ioi 0)) (nhds l)) ∧
      (∀ m n p : ℕ,
        (∫⁻ y, ENNReal.ofReal (Real.exp (-y ^ 2 / (2 * (t : ℝ)))) *
          ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |(x : ℝ) ^ (p : ℤ) * pd m n φc x y|) < ∞ ∧
        (∫⁻ y, ENNReal.ofReal (Real.exp (-y ^ 2 / (2 * (t : ℝ)))) *
          ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |(x : ℝ) ^ (-(p : ℤ)) * pd m n φc x y|) < ∞) :=
  prop_2_2_constructive P W hW σ t hσ ht

end Lyasoff2016
