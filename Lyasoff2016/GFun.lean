/-
Building blocks g_{t,p} for the contour representation (5.8).
-/
module

public import Lyasoff2016.Cerf


@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/- Paper: (5.8), functions g_{t,p} for p = 2,3,4.
   Plain recap: entire (even) building blocks for the contour representation.
   g_{t,2}(z) = e^{-2z²/t}/(4πi);
   g_{t,3}(z) = e^{t/8} √t/(4i√(2π)) (cerf((t+4z)/(2√(2t))) + cerf((t−4z)/(2√(2t))));
   g_{t,4}(z) = e^{t/2} √t/(2i√(2π)) (cerf((t+2z)/√(2t)) + cerf((t−2z)/√(2t)))
              − e^{t/8} cosh z · √t/(i√(2π)) (cerf((t+4z)/(2√(2t))) + cerf((t−4z)/(2√(2t)))). -/
def gFun (p : ℕ) (t : ℝ) (z : ℂ) : ℂ :=
  match p with
  | 2 => cexp (-2 * z ^ 2 / t) / (4 * π * I)
  | 3 =>
      Real.exp (t / 8) * (√t / (4 * I * √(2 * π))) *
        (cerf ((t + 4 * z) / (2 * √(2 * t))) + cerf ((t - 4 * z) / (2 * √(2 * t))))
  | 4 =>
      Real.exp (t / 2) * (√t / (2 * I * √(2 * π))) *
          (cerf ((t + 2 * z) / √(2 * t)) + cerf ((t - 2 * z) / √(2 * t))) -
        Real.exp (t / 8) * Complex.cosh z * (√t / (I * √(2 * π))) *
          (cerf ((t + 4 * z) / (2 * √(2 * t))) + cerf ((t - 4 * z) / (2 * √(2 * t))))
  | _ => 0

namespace gFun

/-- `g_{t,2}` is entire (as a quotient of an entire function by a nonzero constant). -/
theorem two_contDiff (t : ℝ) (_ht : t ≠ 0) :
    ContDiff ℂ ⊤ (gFun 2 t) := by
  unfold gFun
  have h1 : ContDiff ℂ ⊤ fun z : ℂ => -2 * z ^ 2 / (t : ℂ) := by fun_prop
  have h2 : ContDiff ℂ ⊤ fun z : ℂ => cexp (-2 * z ^ 2 / (t : ℂ)) := h1.cexp
  have h3 : ContDiff ℂ ⊤ fun _ : ℂ => (4 * π * I : ℂ) := contDiff_const
  convert h2.div h3 (fun _ => by simp [Complex.I_ne_zero, Real.pi_ne_zero]) using 1

end gFun

end Lyasoff2016