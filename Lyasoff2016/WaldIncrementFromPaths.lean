/-
Wald increment as a continuous-path functional.
-/
module

public import Lyasoff2016.Setting


@[expose] public section

open scoped NNReal Real

noncomputable section
namespace Lyasoff2016

/-- Wald increment as a continuous-path functional. -/
def waldIncrementFromPaths (k : ℕ) (t : ℝ≥0) (s : ℝ) (b : C(ℝ≥0, ℝ)) : ℝ :=
  Real.exp ((k : ℝ) * (b t - b s.toNNReal) - (k : ℝ) ^ 2 * ((t : ℝ) - s) / 2)

namespace waldIncrementFromPaths

theorem continuous_time (k : ℕ) (t : ℝ≥0) (b : C(ℝ≥0, ℝ)) :
    Continuous fun s : ℝ => waldIncrementFromPaths k t s b := by
  unfold waldIncrementFromPaths; fun_prop

theorem measurable (k : ℕ) (t : ℝ≥0) (s : ℝ) :
    Measurable fun b : C(ℝ≥0, ℝ) => waldIncrementFromPaths k t s b := by
  unfold waldIncrementFromPaths; fun_prop

end waldIncrementFromPaths

end Lyasoff2016
