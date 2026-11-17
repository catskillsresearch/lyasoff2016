/-
Smooth bump equal to `1` on `[b, c]` and `0` outside `(a, d)`.
-/
module

public import Lyasoff2016.SmoothStepRight
public import Lyasoff2016.SmoothStepLeft
public import Mathlib.Topology.Algebra.Support


@[expose] public section

open Set Filter Topology
open scoped Real

noncomputable section
namespace Lyasoff2016

/-- Smooth bump equal to `1` on `[b, c]` and `0` outside `(a, d)`, for `a < b ≤ c < d`. -/
def smoothBump (a b c d x : ℝ) : ℝ :=
  smoothStepRight a b x * smoothStepLeft c d x

namespace smoothBump

theorem contDiff (a b c d : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (smoothBump a b c d) :=
  (smoothStepRight.contDiff a b).mul (smoothStepLeft.contDiff c d)

theorem mem_Icc (a b c d x : ℝ) :
    0 ≤ smoothBump a b c d x ∧ smoothBump a b c d x ≤ 1 :=
  ⟨mul_nonneg (smoothStepRight.mem_Icc a b x).1 (smoothStepLeft.mem_Icc c d x).1,
   (mul_le_of_le_one_right (smoothStepRight.mem_Icc a b x).1 (smoothStepLeft.mem_Icc c d x).2).trans
     (smoothStepRight.mem_Icc a b x).2⟩

theorem one_of_mem {a b c d x : ℝ} (hab : a < b) (hcd : c < d)
    (hbx : b ≤ x) (hxc : x ≤ c) : smoothBump a b c d x = 1 := by
  rw [smoothBump, smoothStepRight.one_of_le hab hbx, smoothStepLeft.one_of_le hcd hxc, mul_one]

theorem zero_of_not_mem {a b c d x : ℝ} (hab : a < b) (hcd : c < d)
    (hx : x ≤ a ∨ d ≤ x) : smoothBump a b c d x = 0 := by
  rcases hx with h | h
  · rw [smoothBump, smoothStepRight.zero_of_le hab h, zero_mul]
  · rw [smoothBump, smoothStepLeft.zero_of_le hcd h, mul_zero]

theorem hasCompactSupport {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    HasCompactSupport (smoothBump a b c d) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := a) (b := d)) ?_
  intro x hx
  by_contra hnot
  change ¬(a ≤ x ∧ x ≤ d) at hnot
  push_neg at hnot
  by_cases hax : a ≤ x
  · exact hx (zero_of_not_mem hab hcd (Or.inr (hnot hax).le))
  · exact hx (zero_of_not_mem hab hcd (Or.inl (le_of_lt (lt_of_not_ge hax))))

end smoothBump

end Lyasoff2016
