/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Truncated logarithm: bounded measurable approximation to `log` on `(0, ∞)`.
-/
module

public import Lyasoff2016.Setting


@[expose] public section

open Set Filter Topology
open scoped Real

noncomputable section
namespace Lyasoff2016

def truncLog (n : ℕ) (x : ℝ) : ℝ :=
  if 0 < x then max (-(n : ℝ)) (min (n : ℝ) (Real.log x)) else 0

namespace truncLog

theorem measurable (n : ℕ) : Measurable (truncLog n) := by
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  exact Measurable.max measurable_const <|
    Measurable.min measurable_const Real.measurable_log

theorem abs_bound (n : ℕ) (x : ℝ) : |truncLog n x| ≤ n := by
  simp only [truncLog]
  split_ifs with hx
  · refine abs_le.2 ⟨le_max_left _ _, max_le (neg_le_self (Nat.cast_nonneg n)) (min_le_left _ _)⟩
  · simp

theorem tendsto_log (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n : ℕ => truncLog n x) atTop (nhds (Real.log x)) := by
  have h : ∀ᶠ n : ℕ in atTop, truncLog n x = Real.log x := by
    filter_upwards [eventually_ge_atTop (Nat.ceil |Real.log x|)] with n hn
    have h1 : |Real.log x| ≤ n := (Nat.le_ceil _).trans (Nat.cast_le.2 hn)
    have hlo : -(n : ℝ) ≤ Real.log x := (_root_.abs_le.1 h1).1
    have hhi : Real.log x ≤ n := (_root_.abs_le.1 h1).2
    simp only [truncLog, hx, ite_true, min_eq_right hhi, max_eq_right hlo]
  exact tendsto_nhds_of_eventually_eq h

end truncLog

end Lyasoff2016

