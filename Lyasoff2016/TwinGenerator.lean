/-
Generator of `(expIntTwin, B)` on product test functions (paper (3.4b)).
-/
module

public import Lyasoff2016.Setting
public import Mathlib.Analysis.Calculus.ContDiff.Basic


@[expose] public section

open Set Filter Topology
open scoped Real

noncomputable section
namespace Lyasoff2016

/-- The integrand of paper (3.4b) for a product test `u ⊗ v`: the generator of `(expIntTwin, B)`
applied to `u ⊗ v`. -/
def twinGenerator (σ : ℝ) (u v : ℝ → ℝ) (x y : ℝ) : ℝ :=
  (1 : ℝ) * deriv u x * v y
    + (σ ^ 2 / 2) * x * deriv u x * v y
    + (σ ^ 2 / 2) * x ^ 2 * deriv (deriv u) x * v y
    + σ * x * deriv u x * deriv v y
    + (1 / 2) * u x * deriv (deriv v) y

namespace twinGenerator

/-- The integrand of (3.4b) is jointly continuous for smooth tests. -/
theorem continuous (σ : ℝ) {u v : ℝ → ℝ}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v) :
    Continuous fun p : ℝ × ℝ ↦ twinGenerator σ u v p.1 p.2 := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by decide)
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by decide)
  have hdu1 : ContDiff ℝ 1 (deriv u) := (contDiff_succ_iff_deriv (n := 1)).mp hu2 |>.2.2
  have huc : Continuous u := hu.continuous
  have hu'c : Continuous (deriv u) := ContDiff.continuous_deriv_one hu1
  have hu''c : Continuous (deriv (deriv u)) := ContDiff.continuous_deriv_one hdu1
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by decide)
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by decide)
  have hdv1 : ContDiff ℝ 1 (deriv v) := (contDiff_succ_iff_deriv (n := 1)).mp hv2 |>.2.2
  have hvc : Continuous v := hv.continuous
  have hv'c : Continuous (deriv v) := ContDiff.continuous_deriv_one hv1
  have hv''c : Continuous (deriv (deriv v)) := ContDiff.continuous_deriv_one hdv1
  unfold twinGenerator
  fun_prop

end twinGenerator

end Lyasoff2016
