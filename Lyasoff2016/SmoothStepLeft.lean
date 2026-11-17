/-
Smooth step from `1` on `(-∞, c]` to `0` on `[d, ∞)`.
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition


@[expose] public section

open Set Filter Topology
open scoped Real

noncomputable section
namespace Lyasoff2016

/-- Smooth step from `1` (on `(-∞, c]`) to `0` (on `[d, ∞)`), for `c < d`. -/
def smoothStepLeft (c d x : ℝ) : ℝ :=
  Real.smoothTransition ((d - x) / (d - c))

namespace smoothStepLeft

theorem contDiff (c d : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (smoothStepLeft c d) := by
  unfold smoothStepLeft
  exact Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)

theorem one_of_le {c d x : ℝ} (hcd : c < d) (hx : x ≤ c) :
    smoothStepLeft c d x = 1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div (sub_pos.mpr hcd)).mpr (by linarith))

theorem zero_of_le {c d x : ℝ} (hcd : c < d) (hx : d ≤ x) :
    smoothStepLeft c d x = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sub_pos.mpr hcd).le)

theorem mem_Icc (c d x : ℝ) :
    0 ≤ smoothStepLeft c d x ∧ smoothStepLeft c d x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

end smoothStepLeft

end Lyasoff2016
