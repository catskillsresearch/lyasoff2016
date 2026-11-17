/-
Complex rate factor `A(u,w)` in the Asian π/2 integrand (p. 1090).
-/
module

public import Lyasoff2016.Setting


@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/- Paper: p. 1090, display defining A(u,w):
     A(u,w) := (2 w² e^{μt} + 4 i w e^{μt/2} sinh u + 2) / σ². -/
def Afun (σ ν t : ℝ) (u w : ℝ) : ℂ :=
  (2 * w ^ 2 * Real.exp (ν * t) + 4 * Complex.I * w * Real.exp (ν * t / 2) * Real.sinh u + 2) /
    σ ^ 2

namespace Afun

/-- Real/imaginary decomposition of `A(u,w)`. -/
theorem eq (σ ν t u w : ℝ) :
    Afun σ ν t u w =
      (((2 * w ^ 2 * Real.exp (ν * t) + 2) / σ ^ 2 : ℝ) : ℂ) +
        ((4 * w * Real.exp (ν * t / 2) * Real.sinh u / σ ^ 2 : ℝ) : ℂ) * Complex.I := by
  simp only [Afun]
  push_cast
  ring

/-- `Re A(u,w) = (2 w² e^{νt} + 2)/σ²`. -/
theorem re (σ ν t u w : ℝ) :
    (Afun σ ν t u w).re = (2 * w ^ 2 * Real.exp (ν * t) + 2) / σ ^ 2 := by
  rw [eq]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
    add_zero]

/-- `Im A(u,w) = 4 w e^{νt/2} sinh u / σ²`: the integrand genuinely depends on `u`. -/
theorem im (σ ν t u w : ℝ) :
    (Afun σ ν t u w).im = 4 * w * Real.exp (ν * t / 2) * Real.sinh u / σ ^ 2 := by
  rw [eq]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.I_im, mul_one,
    zero_add]

/-- Paper, p. 1090: `ℜ(A) > 0`, the standing assumption under which `S_{k,p}(A)` converges. -/
theorem re_pos (σ ν t u w : ℝ) (hσ : σ ≠ 0) : 0 < (Afun σ ν t u w).re := by
  rw [re]
  have := Real.exp_pos (ν * t)
  positivity

end Afun

end Lyasoff2016