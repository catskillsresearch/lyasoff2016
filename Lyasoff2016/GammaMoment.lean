/-
Integer moments of a Gamma law, and their Inverse-Gamma pairings.
-/
module

public import Lyasoff2016.IgDensity


@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/-- Integer moments of a Gamma law with shape `β` and rate `a`. -/
def gammaMoment (β a : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => (β + n) / a * gammaMoment β a n

namespace gammaMoment

theorem nonneg {β a : ℝ} (hβ : 0 < β) (ha : 0 < a) (n : ℕ) :
    0 ≤ gammaMoment β a n := by
  induction n with
  | zero => simp [gammaMoment]
  | succ n ih =>
    simp only [gammaMoment]
    positivity

theorem inv_pow_mul_igDensity {β a : ℝ} (hβ : 0 < β) (ha : 0 < a) (n : ℕ) (x : ℝ) :
    x⁻¹ ^ n * igDensity β a x = gammaMoment β a n * igDensity (β + n) a x := by
  induction n with
  | zero => simp [gammaMoment]
  | succ n ih =>
    have hβn : 0 < β + n := by positivity
    rw [pow_succ', mul_assoc, ih, mul_left_comm, igDensity.inv_mul hβn ha]
    simp only [gammaMoment, Nat.cast_add, Nat.cast_one]
    rw [add_assoc]
    ring

theorem lintegral_inv_pow_igMeasure {β a : ℝ} (hβ : 0 < β) (ha : 0 < a) (n : ℕ) :
    ∫⁻ y, ENNReal.ofReal (y ^ n) ∂((igMeasure β a).map fun x => x⁻¹) =
      ENNReal.ofReal (gammaMoment β a n) := by
  rw [lintegral_map (by fun_prop) measurable_inv,
    igDensity.lintegral_measure hβ ha (fun x => x⁻¹ ^ n) _ (by fun_prop)
      (fun x => inv_pow_mul_igDensity hβ ha n x),
    lintegral_congr fun x => ENNReal.ofReal_mul (nonneg hβ ha n),
    lintegral_const_mul _ (igDensity.measurable _ _).ennreal_ofReal,
    igDensity.lintegral (by positivity) ha, mul_one]

end gammaMoment

end Lyasoff2016
