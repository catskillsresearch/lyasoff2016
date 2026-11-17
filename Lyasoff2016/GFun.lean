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

/-- `g_{t,3}` is entire: a constant multiple of a sum of `cerf` composed with affine maps. -/
theorem three_contDiff (t : ℝ) : ContDiff ℂ ⊤ (gFun 3 t) := by
  have h1 : ContDiff ℂ ⊤ fun z : ℂ => cerf ((t + 4 * z) / (2 * √(2 * t))) :=
    cerf.contDiff.comp (by fun_prop)
  have h2 : ContDiff ℂ ⊤ fun z : ℂ => cerf ((t - 4 * z) / (2 * √(2 * t))) :=
    cerf.contDiff.comp (by fun_prop)
  exact contDiff_const.mul (h1.add h2)

/-- `g_{t,4}` is entire: built from `cerf` composed with affine maps and `cosh`. -/
theorem four_contDiff (t : ℝ) : ContDiff ℂ ⊤ (gFun 4 t) := by
  have h1 : ContDiff ℂ ⊤ fun z : ℂ => cerf ((t + 2 * z) / √(2 * t)) :=
    cerf.contDiff.comp (by fun_prop)
  have h2 : ContDiff ℂ ⊤ fun z : ℂ => cerf ((t - 2 * z) / √(2 * t)) :=
    cerf.contDiff.comp (by fun_prop)
  have h3 : ContDiff ℂ ⊤ fun z : ℂ => cerf ((t + 4 * z) / (2 * √(2 * t))) :=
    cerf.contDiff.comp (by fun_prop)
  have h4 : ContDiff ℂ ⊤ fun z : ℂ => cerf ((t - 4 * z) / (2 * √(2 * t))) :=
    cerf.contDiff.comp (by fun_prop)
  have hcosh : ContDiff ℂ ⊤ fun z : ℂ => Complex.cosh z :=
    Complex.differentiable_cosh.contDiff
  exact (contDiff_const.mul (h1.add h2)).sub
    (((contDiff_const.mul hcosh).mul contDiff_const).mul (h3.add h4))

/-- Every `g_{t,p}` is entire. (For `p ∉ {2,3,4}` the function is `0` by convention, and no
sign condition on `t` is needed: division by `0` is `0`, which only makes the maps constant.) -/
theorem contDiff (p : ℕ) (t : ℝ) : ContDiff ℂ ⊤ (gFun p t) := by
  by_cases h2 : p = 2
  · subst h2
    by_cases ht : t = 0
    · subst ht
      have h : gFun 2 0 = fun _ => 1 / (4 * π * I) := by
        funext z
        simp [gFun]
      rw [h]
      exact contDiff_const
    · exact two_contDiff t ht
  by_cases h3 : p = 3
  · subst h3
    exact three_contDiff t
  by_cases h4 : p = 4
  · subst h4
    exact four_contDiff t
  have h : gFun p t = fun _ => 0 := by
    funext z
    unfold gFun
    split <;> first | rfl | contradiction
  rw [h]
  exact contDiff_const

lemma two_apply (t : ℝ) (z : ℂ) :
    gFun 2 t z = cexp (-2 * z ^ 2 / t) / (4 * π * I) := rfl

/-- `g_{t,2}` is even. -/
theorem two_even (t : ℝ) (z : ℂ) : gFun 2 t (-z) = gFun 2 t z := by
  simp only [gFun, neg_sq]

/-- `g_{t,3}` is even: `z ↦ -z` swaps the two `cerf` terms. -/
theorem three_even (t : ℝ) (z : ℂ) : gFun 3 t (-z) = gFun 3 t z := by
  simp only [gFun]
  rw [show (t : ℂ) + 4 * -z = t - 4 * z by ring, show (t : ℂ) - 4 * -z = t + 4 * z by ring]
  ring

/-- `g_{t,4}` is even: `z ↦ -z` swaps the `cerf` terms in each pair and `cosh` is even. -/
theorem four_even (t : ℝ) (z : ℂ) : gFun 4 t (-z) = gFun 4 t z := by
  simp only [gFun, Complex.cosh_neg]
  rw [show (t : ℂ) + 4 * -z = t - 4 * z by ring, show (t : ℂ) - 4 * -z = t + 4 * z by ring,
    show (t : ℂ) + 2 * -z = t - 2 * z by ring, show (t : ℂ) - 2 * -z = t + 2 * z by ring]
  ring

/-- Every `g_{t,p}` is even in `z` (trivially so for `p ∉ {2,3,4}`, where it is `0`). -/
theorem even (p : ℕ) (t : ℝ) (z : ℂ) : gFun p t (-z) = gFun p t z := by
  by_cases h2 : p = 2
  · subst h2
    exact two_even t z
  by_cases h3 : p = 3
  · subst h3
    exact three_even t z
  by_cases h4 : p = 4
  · subst h4
    exact four_even t z
  unfold gFun
  split <;> first | rfl | contradiction

/-- Unfolding of `g_{t,3}`. -/
theorem three_apply (t : ℝ) (z : ℂ) : gFun 3 t z =
    Real.exp (t / 8) * (√t / (4 * I * √(2 * π))) *
      (cerf ((t + 4 * z) / (2 * √(2 * t))) + cerf ((t - 4 * z) / (2 * √(2 * t)))) := rfl

theorem four_apply (t : ℝ) (z : ℂ) : gFun 4 t z =
    Real.exp (t / 2) * (√t / (2 * I * √(2 * π))) *
        (cerf ((t + 2 * z) / √(2 * t)) + cerf ((t - 2 * z) / √(2 * t))) -
      Real.exp (t / 8) * Complex.cosh z * (√t / (I * √(2 * π))) *
        (cerf ((t + 4 * z) / (2 * √(2 * t))) + cerf ((t - 4 * z) / (2 * √(2 * t)))) := rfl

/-- `g_{t,4} = A − 4 cosh · g_{t,3}`. -/
theorem four_eq (t : ℝ) (z : ℂ) : gFun 4 t z =
    Real.exp (t / 2) * (√t / (2 * I * √(2 * π))) *
        (cerf ((t + 2 * z) / √(2 * t)) + cerf ((t - 2 * z) / √(2 * t))) -
      4 * Complex.cosh z * gFun 3 t z := by
  rw [four_apply, three_apply]
  ring

/-- Gaussian exponent identity behind `g_{t,3}'`. -/
private lemma exp_sq_three {t : ℝ} (ht : 0 < t) (z : ℂ) (ε : ℂ) (hε : ε ^ 2 = 1) :
    cexp (-((t + ε * 4 * z) / (2 * √(2 * t))) ^ 2) =
      cexp (-(t / 8)) * cexp (-(ε * z)) * cexp (-2 * z ^ 2 / t) := by
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hs : ((√(2 * t) : ℝ) : ℂ) ^ 2 = 2 * t := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [div_pow, mul_pow, hs]
  field_simp
  linear_combination (-128 * z ^ 2) * hε

private lemma exp_sq_three_add {t : ℝ} (ht : 0 < t) (z : ℂ) :
    cexp (-((t + 4 * z) / (2 * √(2 * t))) ^ 2) =
      cexp (-(t / 8)) * cexp (-z) * cexp (-2 * z ^ 2 / t) := by
  have h := exp_sq_three ht z 1 (by norm_num)
  simp only [one_mul] at h
  exact h

private lemma exp_sq_three_sub {t : ℝ} (ht : 0 < t) (z : ℂ) :
    cexp (-((t - 4 * z) / (2 * √(2 * t))) ^ 2) =
      cexp (-(t / 8)) * cexp z * cexp (-2 * z ^ 2 / t) := by
  have h := exp_sq_three ht z (-1) (by norm_num)
  rw [show (t : ℂ) + -1 * 4 * z = t - 4 * z by ring, show -(-1 * z) = z by ring] at h
  exact h

theorem three_hasDerivAt {t : ℝ} (ht : 0 < t) (z : ℂ) :
    HasDerivAt (gFun 3 t) (-(Complex.sinh z * cexp (-2 * z ^ 2 / t)) / (π * I)) z := by
  have h1 : HasDerivAt (fun w : ℂ => cerf ((t + 4 * w) / (2 * √(2 * t))))
      ((2 / √π : ℂ) * cexp (-((t + 4 * z) / (2 * √(2 * t))) ^ 2) * (4 / (2 * √(2 * t)))) z := by
    have hin : HasDerivAt (fun w : ℂ => ((t : ℂ) + 4 * w) / (2 * √(2 * t)))
        (4 / (2 * √(2 * t))) z := by
      simpa using (((hasDerivAt_id' z).const_mul (4 : ℂ)).const_add (t : ℂ)).div_const
        (2 * (√(2 * t) : ℂ))
    exact (cerf.hasDerivAt _).comp z hin
  have h2 : HasDerivAt (fun w : ℂ => cerf ((t - 4 * w) / (2 * √(2 * t))))
      ((2 / √π : ℂ) * cexp (-((t - 4 * z) / (2 * √(2 * t))) ^ 2) * (-4 / (2 * √(2 * t)))) z := by
    have hin : HasDerivAt (fun w : ℂ => ((t : ℂ) - 4 * w) / (2 * √(2 * t)))
        (-4 / (2 * √(2 * t))) z := by
      simpa using (((hasDerivAt_id' z).const_mul (4 : ℂ)).const_sub (t : ℂ)).div_const
        (2 * (√(2 * t) : ℂ))
    exact (cerf.hasDerivAt _).comp z hin
  have h := (h1.add h2).const_mul ((Real.exp (t / 8) : ℂ) * (√t / (4 * I * √(2 * π))))
  refine HasDerivAt.congr_deriv (f := gFun 3 t) h ?_
  rw [exp_sq_three_add ht, exp_sq_three_sub ht]
  have hexp : (Real.exp (t / 8) : ℂ) * cexp (-(t / 8)) = 1 := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]; simp
  have hsa : ((√(2 * t) : ℝ) : ℂ) = (√2 : ℝ) * (√t : ℝ) := by
    rw [Real.sqrt_mul (by norm_num)]; push_cast; ring
  have hsb : ((√(2 * π) : ℝ) : ℂ) = (√2 : ℝ) * (√π : ℝ) := by
    rw [Real.sqrt_mul (by norm_num)]; push_cast; ring
  have hs2 : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hb2 : ((√π : ℝ) : ℂ) ^ 2 = π := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have ha0 : ((√t : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr ht).ne'
  have hb0 : ((√π : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hs0 : ((√2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hsa, hsb]
  generalize (Real.exp (t / 8) : ℂ) = e at *
  generalize cexp (-(t / 8)) = e' at *
  generalize ((√2 : ℝ) : ℂ) = s at *
  generalize ((√t : ℝ) : ℂ) = a at *
  generalize ((√π : ℝ) : ℂ) = b at *
  have key : e * (a / (4 * I * (s * b))) *
        (2 / b * (e' * cexp (-z) * cexp (-2 * z ^ 2 / t)) * (4 / (2 * (s * a))) +
          2 / b * (e' * cexp z * cexp (-2 * z ^ 2 / t)) * (-4 / (2 * (s * a)))) =
      (e * e') * (cexp (-2 * z ^ 2 / t) * (cexp (-z) - cexp z)) / (I * s ^ 2 * b ^ 2) := by
    field_simp
    ring
  rw [key, hexp, hs2, hb2, Complex.sinh]
  field_simp
  ring

/-- Gaussian exponent identity behind the first pair of `cerf` terms of `g_{t,4}'`. -/
private lemma exp_sq_four {t : ℝ} (ht : 0 < t) (z : ℂ) (ε : ℂ) (hε : ε ^ 2 = 1) :
    cexp (-((t + ε * 2 * z) / √(2 * t)) ^ 2) =
      cexp (-(t / 2)) * cexp (-(ε * z)) ^ 2 * cexp (-2 * z ^ 2 / t) := by
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hs : ((√(2 * t) : ℝ) : ℂ) ^ 2 = 2 * t := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring
  rw [← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [div_pow, hs]
  push_cast
  field_simp
  linear_combination (-4 * z ^ 2) * hε

private lemma exp_sq_four_add {t : ℝ} (ht : 0 < t) (z : ℂ) :
    cexp (-((t + 2 * z) / √(2 * t)) ^ 2) =
      cexp (-(t / 2)) * cexp (-z) ^ 2 * cexp (-2 * z ^ 2 / t) := by
  have h := exp_sq_four ht z 1 (by norm_num)
  simp only [one_mul] at h
  exact h

private lemma exp_sq_four_sub {t : ℝ} (ht : 0 < t) (z : ℂ) :
    cexp (-((t - 2 * z) / √(2 * t)) ^ 2) =
      cexp (-(t / 2)) * cexp z ^ 2 * cexp (-2 * z ^ 2 / t) := by
  have h := exp_sq_four ht z (-1) (by norm_num)
  rw [show (t : ℂ) + -1 * 2 * z = t - 2 * z by ring, show -(-1 * z) = z by ring] at h
  exact h

/-- `g_{t,4}'(z) = −4 sinh z · g_{t,3}(z)`. -/
theorem four_hasDerivAt {t : ℝ} (ht : 0 < t) (z : ℂ) :
    HasDerivAt (gFun 4 t) (-4 * Complex.sinh z * gFun 3 t z) z := by
  have h1 : HasDerivAt (fun w : ℂ => cerf ((t + 2 * w) / √(2 * t)))
      ((2 / √π : ℂ) * cexp (-((t + 2 * z) / √(2 * t)) ^ 2) * (2 / √(2 * t))) z := by
    have hin : HasDerivAt (fun w : ℂ => ((t : ℂ) + 2 * w) / √(2 * t)) (2 / √(2 * t)) z := by
      simpa using (((hasDerivAt_id' z).const_mul (2 : ℂ)).const_add (t : ℂ)).div_const
        ((√(2 * t) : ℝ) : ℂ)
    exact (cerf.hasDerivAt _).comp z hin
  have h2 : HasDerivAt (fun w : ℂ => cerf ((t - 2 * w) / √(2 * t)))
      ((2 / √π : ℂ) * cexp (-((t - 2 * z) / √(2 * t)) ^ 2) * (-2 / √(2 * t))) z := by
    have hin : HasDerivAt (fun w : ℂ => ((t : ℂ) - 2 * w) / √(2 * t)) (-2 / √(2 * t)) z := by
      simpa using (((hasDerivAt_id' z).const_mul (2 : ℂ)).const_sub (t : ℂ)).div_const
        ((√(2 * t) : ℝ) : ℂ)
    exact (cerf.hasDerivAt _).comp z hin
  have hA := (h1.add h2).const_mul ((Real.exp (t / 2) : ℂ) * (√t / (2 * I * √(2 * π))))
  have hB := ((Complex.hasDerivAt_cosh z).const_mul (4 : ℂ)).mul (three_hasDerivAt ht z)
  have h := hA.sub hB
  have hfun : gFun 4 t = fun w : ℂ =>
      (Real.exp (t / 2) : ℂ) * (√t / (2 * I * √(2 * π))) *
          (cerf ((t + 2 * w) / √(2 * t)) + cerf ((t - 2 * w) / √(2 * t))) -
        4 * Complex.cosh w * gFun 3 t w := funext (four_eq t)
  rw [hfun]
  refine HasDerivAt.congr_deriv h ?_
  rw [exp_sq_four_add ht, exp_sq_four_sub ht]
  have hexp : (Real.exp (t / 2) : ℂ) * cexp (-(t / 2)) = 1 := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]; simp
  have hsa : ((√(2 * t) : ℝ) : ℂ) = (√2 : ℝ) * (√t : ℝ) := by
    rw [Real.sqrt_mul (by norm_num)]; push_cast; ring
  have hsb : ((√(2 * π) : ℝ) : ℂ) = (√2 : ℝ) * (√π : ℝ) := by
    rw [Real.sqrt_mul (by norm_num)]; push_cast; ring
  have hs2 : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hb2 : ((√π : ℝ) : ℂ) ^ 2 = π := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have ha0 : ((√t : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr ht).ne'
  have hb0 : ((√π : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hs0 : ((√2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hXY : cexp z * cexp (-z) = 1 := by rw [← Complex.exp_add]; simp
  rw [hsa, hsb]
  generalize gFun 3 t z = G
  generalize (Real.exp (t / 2) : ℂ) = e at *
  generalize cexp (-(t / 2)) = e' at *
  generalize ((√2 : ℝ) : ℂ) = s at *
  generalize ((√t : ℝ) : ℂ) = a at *
  generalize ((√π : ℝ) : ℂ) = b at *
  have key : e * (a / (2 * I * (s * b))) *
        (2 / b * (e' * cexp (-z) ^ 2 * cexp (-2 * z ^ 2 / t)) * (2 / (s * a)) +
          2 / b * (e' * cexp z ^ 2 * cexp (-2 * z ^ 2 / t)) * (-2 / (s * a))) =
      (e * e') * (2 * cexp (-2 * z ^ 2 / t) * (cexp (-z) ^ 2 - cexp z ^ 2)) /
        (I * s ^ 2 * b ^ 2) := by
    field_simp
    ring
  rw [key, hexp, hs2, hb2, Complex.sinh, Complex.cosh]
  field_simp
  ring

end gFun

end Lyasoff2016