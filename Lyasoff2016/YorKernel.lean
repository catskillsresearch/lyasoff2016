/-
Smoothness and rapid decay at `0` and `∞` of the Hartman–Watson integral kernel
`J(t, r) = ∫₀^∞ exp(-u²/(2t) - r cosh u) sinh u sin(π u / t) du` and all its derivatives.

WIP: proofs deferred; statements kept so the library stays green.
-/
module

public import Lyasoff2016.YorJointDensity
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

section KernelSmoothness

/-- `m`-th formal derivative of the Hartman–Watson integral kernel:
`Jm t m r = (-1)^m ∫₀^∞ (cosh u)^m exp(-u²/(2t) - r cosh u) sinh u sin(π u / t) du`. -/
def Jm (t : ℝ) (m : ℕ) (r : ℝ) : ℝ :=
  (-1 : ℝ) ^ m * ∫ u in Ioi (0 : ℝ), (Real.cosh u) ^ m *
    Real.exp (-u ^ 2 / (2 * t) - r * Real.cosh u) * Real.sinh u * Real.sin (Real.pi * u / t)

/-- Integrability of `(cosh u)^m * exp(-u²/(2t)) * sinh u` on `Ioi 0`. -/
lemma integrableOn_cosh_pow_exp_neg_quad_mul_sinh {t : ℝ} (ht : 0 < t) (m : ℕ) :
    IntegrableOn (fun u : ℝ => (Real.cosh u) ^ m * Real.exp (-u ^ 2 / (2 * t)) * Real.sinh u)
      (Ioi 0) := by
  sorry

/-- `Jm t m` is continuous on `[0, ∞)` for every `t > 0, m : ℕ`. -/
lemma Jm_continuousOn {t : ℝ} (ht : 0 < t) (m : ℕ) :
    ContinuousOn (Jm t m) (Ici 0) := by
  sorry

/-- Derivative of `Jm t m` on `(0, ∞)` is `Jm t (m + 1)`. -/
lemma Jm_hasDerivAt {t : ℝ} (ht : 0 < t) (m : ℕ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (Jm t m) (Jm t (m + 1) r) r := by
  sorry

/-- `Jm t m` is `C^k` on `(0, ∞)` for every `k, m : ℕ`. -/
lemma Jm_contDiffOn {t : ℝ} (ht : 0 < t) :
    ∀ k m : ℕ, ContDiffOn ℝ k (Jm t m) (Ioi 0) := by
  sorry

/-- Iterated derivative of `Jm t 0` at `r > 0` equals `Jm t k r`. -/
lemma iteratedDeriv_Jm {t : ℝ} (ht : 0 < t) (k : ℕ) {r : ℝ} (hr : 0 < r) :
    iteratedDeriv k (Jm t 0) r = Jm t k r := by
  sorry

end KernelSmoothness

section KernelVanishingAndDecay

/-- Every derivative of the Hartman–Watson kernel vanishes at `r = 0`: `Jm t m 0 = 0`. -/
lemma Jm_zero_eq_zero {t : ℝ} (ht : 0 < t) (m : ℕ) : Jm t m 0 = 0 := by
  sorry

/-- Exponential decay of `Jm t m r` for `r ≥ 0`. -/
lemma Jm_exp_decay {t : ℝ} (ht : 0 < t) (m : ℕ) :
    ∃ C ≥ 0, ∀ r ≥ 0, |Jm t m r| ≤ C * Real.exp (-r) := by
  sorry

/-- Polynomial vanishing of `Jm t m r` as `r → 0⁺` for every `m, N : ℕ`. -/
lemma Jm_poly_decay {t : ℝ} (ht : 0 < t) :
    ∀ N m : ℕ, ∃ C ≥ 0, ∀ r ≥ 0, |Jm t m r| ≤ C * r ^ N := by
  sorry

/-- Combined kernel bound: `|Jm t m r| ≤ C * r^N * exp(-r / 2)` for all `r ≥ 0` and `m, N : ℕ`. -/
lemma Jm_bound {t : ℝ} (ht : 0 < t) (m N : ℕ) :
    ∃ C ≥ 0, ∀ r ≥ 0, |Jm t m r| ≤ C * r ^ N * Real.exp (-r / 2) := by
  sorry

end KernelVanishingAndDecay

end Lyasoff2016
