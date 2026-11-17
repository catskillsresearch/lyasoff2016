/-
Smooth step from `0` on `(-∞, a]` to `1` on `[b, ∞)`.
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition


@[expose] public section

open Set Filter Topology
open scoped Real

noncomputable section
namespace Lyasoff2016

/-- Smooth step from `0` (on `(-∞, a]`) to `1` (on `[b, ∞)`), for `a < b`. -/
def smoothStepRight (a b x : ℝ) : ℝ :=
  Real.smoothTransition ((x - a) / (b - a))

namespace smoothStepRight

theorem contDiff (a b : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (smoothStepRight a b) := by
  unfold smoothStepRight
  exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem zero_of_le {a b x : ℝ} (hab : a < b) (hx : x ≤ a) :
    smoothStepRight a b x = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sub_pos.mpr hab).le)

theorem one_of_le {a b x : ℝ} (hab : a < b) (hx : b ≤ x) :
    smoothStepRight a b x = 1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div (sub_pos.mpr hab)).mpr (by linarith))

theorem mem_Icc (a b x : ℝ) :
    0 ≤ smoothStepRight a b x ∧ smoothStepRight a b x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

end smoothStepRight

end Lyasoff2016
