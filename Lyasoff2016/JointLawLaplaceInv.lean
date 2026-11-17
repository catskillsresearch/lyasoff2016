/-
Inversion of the distributional Fokker–Planck PDE along characteristics
`A(v, y) = cosh y + v * exp(-y)` to compute `E[f(W_t) * exp(-v₀ / ∫₀ᵗ e^{2 W_s} ds)]`.
-/
module

public import Lyasoff2016.JointLawLaplace
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Topology.ContinuousMap.Weierstrass

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real Polynomial

noncomputable section
namespace Lyasoff2016

section SmoothCutoffs

/-- Smooth step from `0` (on `(-∞, a]`) to `1` (on `[b, ∞)`), for `a < b`. -/
def smoothStepRight (a b x : ℝ) : ℝ :=
  Real.smoothTransition ((x - a) / (b - a))

/-- Smooth step from `1` (on `(-∞, c]`) to `0` (on `[d, ∞)`), for `c < d`. -/
def smoothStepLeft (c d x : ℝ) : ℝ :=
  Real.smoothTransition ((d - x) / (d - c))

/-- Smooth bump equal to `1` on `[b, c]` and `0` outside `(a, d)`, for `a < b ≤ c < d`. -/
def smoothBump (a b c d x : ℝ) : ℝ :=
  smoothStepRight a b x * smoothStepLeft c d x

lemma smoothStepRight_contDiff (a b : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (smoothStepRight a b) := by
  unfold smoothStepRight
  exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

lemma smoothStepLeft_contDiff (c d : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (smoothStepLeft c d) := by
  unfold smoothStepLeft
  exact Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)

lemma smoothBump_contDiff (a b c d : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (smoothBump a b c d) :=
  (smoothStepRight_contDiff a b).mul (smoothStepLeft_contDiff c d)

lemma smoothStepRight_zero_of_le {a b x : ℝ} (hab : a < b) (hx : x ≤ a) :
    smoothStepRight a b x = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sub_pos.mpr hab).le)

lemma smoothStepRight_one_of_le {a b x : ℝ} (hab : a < b) (hx : b ≤ x) :
    smoothStepRight a b x = 1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div (sub_pos.mpr hab)).mpr (by linarith))

lemma smoothStepRight_mem_Icc (a b x : ℝ) :
    0 ≤ smoothStepRight a b x ∧ smoothStepRight a b x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma smoothStepLeft_one_of_le {c d x : ℝ} (hcd : c < d) (hx : x ≤ c) :
    smoothStepLeft c d x = 1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div (sub_pos.mpr hcd)).mpr (by linarith))

lemma smoothStepLeft_zero_of_le {c d x : ℝ} (hcd : c < d) (hx : d ≤ x) :
    smoothStepLeft c d x = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sub_pos.mpr hcd).le)

lemma smoothStepLeft_mem_Icc (c d x : ℝ) :
    0 ≤ smoothStepLeft c d x ∧ smoothStepLeft c d x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma smoothBump_mem_Icc (a b c d x : ℝ) :
    0 ≤ smoothBump a b c d x ∧ smoothBump a b c d x ≤ 1 :=
  ⟨mul_nonneg (smoothStepRight_mem_Icc a b x).1 (smoothStepLeft_mem_Icc c d x).1,
   (mul_le_of_le_one_right (smoothStepRight_mem_Icc a b x).1 (smoothStepLeft_mem_Icc c d x).2).trans
     (smoothStepRight_mem_Icc a b x).2⟩

lemma smoothBump_one_of_mem {a b c d x : ℝ} (hab : a < b) (hcd : c < d)
    (hbx : b ≤ x) (hxc : x ≤ c) : smoothBump a b c d x = 1 := by
  simp [smoothBump, smoothStepRight_one_of_le hab hbx, smoothStepLeft_one_of_le hcd hxc]

lemma smoothBump_zero_of_not_mem {a b c d x : ℝ} (hab : a < b) (hcd : c < d)
    (hx : x ≤ a ∨ d ≤ x) : smoothBump a b c d x = 0 := by
  rcases hx with h | h
  · simp [smoothBump, smoothStepRight_zero_of_le hab h]
  · simp [smoothBump, smoothStepLeft_zero_of_le hcd h]

lemma smoothBump_hasCompactSupport {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    HasCompactSupport (smoothBump a b c d) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := a) (b := d)) ?_
  intro x hx
  by_contra hnot
  simp only [mem_Icc, not_and_or, not_le] at hnot
  exact hx (smoothBump_zero_of_not_mem hab hcd (hnot.imp le_of_lt le_of_lt))

end SmoothCutoffs

section CharacteristicGeometry

/-- Characteristic invariant `A(v, y) = cosh y + v * exp(-y)`. -/
def charA (v y : ℝ) : ℝ := Real.cosh y + v * Real.exp (-y)

/-- Critical point `y₀(v) = (1/2) * log(1 + 2v)` where `∂_y A(v, y) = 0`. -/
def yCrit (v : ℝ) : ℝ := (1 / 2 : ℝ) * Real.log (1 + 2 * v)

/-- Upper inverse branch `y_+(v, a) = log(a + √(a² - (1 + 2v)))`. -/
def yPlus (v a : ℝ) : ℝ := Real.log (a + Real.sqrt (a ^ 2 - (1 + 2 * v)))

/-- Lower inverse branch `y_-(v, a) = log(a - √(a² - (1 + 2v)))`. -/
def yMinus (v a : ℝ) : ℝ := Real.log (a - Real.sqrt (a ^ 2 - (1 + 2 * v)))

lemma charA_eq (v y : ℝ) :
    charA v y = (Real.exp y + (1 + 2 * v) * Real.exp (-y)) / 2 := by
  simp only [charA, Real.cosh_eq]; ring

lemma deriv_charA_y_eq (v y : ℝ) :
    Real.sinh y - v * Real.exp (-y) = (Real.exp y - (1 + 2 * v) * Real.exp (-y)) / 2 := by
  simp only [Real.sinh_eq]; ring

lemma hasDerivAt_charA_y (v y : ℝ) :
    HasDerivAt (charA v) (Real.sinh y - v * Real.exp (-y)) y := by
  have h1 := Real.hasDerivAt_cosh y
  have h2 := ((hasDerivAt_id' y).neg.exp).const_mul v
  unfold charA
  convert h1.fun_add h2 using 1
  simp [sub_eq_add_neg, mul_neg]

lemma hasDerivAt_charA_v (v y : ℝ) :
    HasDerivAt (fun v' => charA v' y) (Real.exp (-y)) v := by
  have h := ((hasDerivAt_id' v).mul_const (Real.exp (-y))).const_add (Real.cosh y)
  simpa [charA] using h

lemma charA_sq_sub (v y : ℝ) :
    charA v y ^ 2 - (1 + 2 * v) = (Real.sinh y - v * Real.exp (-y)) ^ 2 := by
  rw [charA_eq, deriv_charA_y_eq]
  have hmul : Real.exp y * Real.exp (-y) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc ((Real.exp y + (1 + 2 * v) * Real.exp (-y)) / 2) ^ 2 - (1 + 2 * v)
      = ((Real.exp y - (1 + 2 * v) * Real.exp (-y)) / 2) ^ 2 +
          (1 + 2 * v) * (Real.exp y * Real.exp (-y) - 1) := by ring
    _ = ((Real.exp y - (1 + 2 * v) * Real.exp (-y)) / 2) ^ 2 := by rw [hmul]; ring

lemma exp_two_mul_yCrit {v : ℝ} (hv : 0 ≤ v) :
    Real.exp (2 * yCrit v) = 1 + 2 * v := by
  simp only [yCrit]
  rw [show 2 * ((1 / 2 : ℝ) * Real.log (1 + 2 * v)) = Real.log (1 + 2 * v) by ring]
  exact Real.exp_log (by linarith)

lemma charA_yCrit {v : ℝ} (hv : 0 ≤ v) :
    charA v (yCrit v) = Real.sqrt (1 + 2 * v) := by
  have h12v : 0 < 1 + 2 * v := by linarith
  have hsq : Real.exp (yCrit v) ^ 2 = 1 + 2 * v := by
    rw [← Real.exp_nat_mul]; simpa [Nat.cast_ofNat] using exp_two_mul_yCrit hv
  have hexp_pos : 0 < Real.exp (yCrit v) := Real.exp_pos _
  have he : Real.exp (yCrit v) = Real.sqrt (1 + 2 * v) := by
    rw [← Real.sqrt_sq hexp_pos.le, hsq]
  have he_neg : (1 + 2 * v) * Real.exp (-yCrit v) = Real.sqrt (1 + 2 * v) := by
    calc (1 + 2 * v) * Real.exp (-yCrit v)
        = (Real.exp (yCrit v) * Real.exp (yCrit v)) * (Real.exp (yCrit v))⁻¹ := by
            rw [← hsq, sq, Real.exp_neg]
      _ = Real.exp (yCrit v) := mul_inv_cancel_right₀ hexp_pos.ne' _
      _ = Real.sqrt (1 + 2 * v) := he
  rw [charA_eq, he, he_neg]
  ring

lemma charA_ge_sqrt {v : ℝ} (hv : 0 ≤ v) (y : ℝ) :
    Real.sqrt (1 + 2 * v) ≤ charA v y := by
  have hpos : 0 < charA v y := by
    unfold charA
    exact add_pos_of_pos_of_nonneg (Real.cosh_pos y) (mul_nonneg hv (Real.exp_pos _).le)
  have hsq : 1 + 2 * v ≤ charA v y ^ 2 := by
    have := charA_sq_sub v y
    nlinarith [sq_nonneg (Real.sinh y - v * Real.exp (-y))]
  rw [← Real.sqrt_sq hpos.le]
  exact Real.sqrt_le_sqrt hsq

lemma charA_deriv_pos_iff {v : ℝ} (hv : 0 ≤ v) (y : ℝ) :
    0 < Real.sinh y - v * Real.exp (-y) ↔ yCrit v < y := by
  rw [deriv_charA_y_eq]
  have hexp : 0 < Real.exp (-y) := Real.exp_pos (-y)
  have hfactor : (Real.exp y - (1 + 2 * v) * Real.exp (-y)) / 2 =
      Real.exp (-y) * (Real.exp (2 * y) - (1 + 2 * v)) / 2 := by
    have hmul : Real.exp (-y) * Real.exp (2 * y) = Real.exp y := by
      rw [← Real.exp_add]; congr 1; ring
    linarith [mul_sub (Real.exp (-y)) (Real.exp (2 * y)) (1 + 2 * v)]
  rw [hfactor]
  constructor
  · intro h
    have h2 : 0 < Real.exp (2 * y) - (1 + 2 * v) := by nlinarith
    have h3 : Real.exp (2 * yCrit v) < Real.exp (2 * y) := by
      rw [exp_two_mul_yCrit hv]; linarith
    linarith [Real.exp_lt_exp.mp h3]
  · intro h
    have h3 : 1 + 2 * v < Real.exp (2 * y) := by
      rw [← exp_two_mul_yCrit hv]; exact Real.exp_lt_exp.mpr (by linarith)
    have h2 : 0 < Real.exp (2 * y) - (1 + 2 * v) := by linarith
    positivity

lemma charA_deriv_neg_iff {v : ℝ} (hv : 0 ≤ v) (y : ℝ) :
    Real.sinh y - v * Real.exp (-y) < 0 ↔ y < yCrit v := by
  rw [deriv_charA_y_eq]
  have hexp : 0 < Real.exp (-y) := Real.exp_pos (-y)
  have hfactor : (Real.exp y - (1 + 2 * v) * Real.exp (-y)) / 2 =
      Real.exp (-y) * (Real.exp (2 * y) - (1 + 2 * v)) / 2 := by
    have hmul : Real.exp (-y) * Real.exp (2 * y) = Real.exp y := by
      rw [← Real.exp_add]; congr 1; ring
    linarith [mul_sub (Real.exp (-y)) (Real.exp (2 * y)) (1 + 2 * v)]
  rw [hfactor]
  constructor
  · intro h
    have h2 : Real.exp (2 * y) - (1 + 2 * v) < 0 := by
      by_contra hge
      push Not at hge
      have : 0 ≤ Real.exp (-y) * (Real.exp (2 * y) - (1 + 2 * v)) / 2 := by positivity
      linarith
    have h3 : Real.exp (2 * y) < Real.exp (2 * yCrit v) := by
      rw [exp_two_mul_yCrit hv]; linarith
    linarith [Real.exp_lt_exp.mp h3]
  · intro h
    have h3 : Real.exp (2 * y) < 1 + 2 * v := by
      rw [← exp_two_mul_yCrit hv]; exact Real.exp_lt_exp.mpr (by linarith)
    have h2 : Real.exp (2 * y) - (1 + 2 * v) < 0 := by linarith
    have : Real.exp (-y) * (Real.exp (2 * y) - (1 + 2 * v)) < 0 :=
      mul_neg_of_pos_of_neg hexp h2
    linarith

lemma charA_strictMonoOn {v : ℝ} (hv : 0 ≤ v) :
    StrictMonoOn (charA v) (Ici (yCrit v)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici _) (by unfold charA; fun_prop) fun y hy => ?_
  have hd := (hasDerivAt_charA_y v y).deriv
  rw [hd]
  exact (charA_deriv_pos_iff hv y).mpr (by simpa using hy)

lemma charA_strictAntiOn {v : ℝ} (hv : 0 ≤ v) :
    StrictAntiOn (charA v) (Iic (yCrit v)) := by
  refine strictAntiOn_of_deriv_neg (convex_Iic _) (by unfold charA; fun_prop) fun y hy => ?_
  have hd := (hasDerivAt_charA_y v y).deriv
  rw [hd]
  exact (charA_deriv_neg_iff hv y).mpr (by simpa using hy)

lemma sqrt_sq_sub_lt_self {v a : ℝ} (hv : 0 ≤ v) (ha : Real.sqrt (1 + 2 * v) < a) :
    Real.sqrt (a ^ 2 - (1 + 2 * v)) < a := by
  have ha0 : 0 < a := (Real.sqrt_nonneg _).trans_lt ha
  have h12v : 0 < 1 + 2 * v := by linarith
  rw [Real.sqrt_lt' ha0]
  linarith

lemma charA_yPlus {v a : ℝ} (hv : 0 ≤ v) (ha : Real.sqrt (1 + 2 * v) < a) :
    yCrit v < yPlus v a ∧ charA v (yPlus v a) = a := by
  have ha0 : 0 < a := (Real.sqrt_nonneg _).trans_lt ha
  have h12v : 0 < 1 + 2 * v := by linarith
  have hsub : 0 < a ^ 2 - (1 + 2 * v) := by
    have := Real.lt_sq_of_sqrt_lt ha
    linarith
  set s := Real.sqrt (a ^ 2 - (1 + 2 * v))
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hsub
  have harg_pos : 0 < a + s := by positivity
  have hprod : (a + s) * (a - s) = 1 + 2 * v := by
    have : s ^ 2 = a ^ 2 - (1 + 2 * v) := Real.sq_sqrt hsub.le
    nlinarith
  have hgt_sqrt : Real.sqrt (1 + 2 * v) < a + s := lt_trans ha (by linarith)
  have hy : yCrit v < yPlus v a := by
    have h2 : 1 + 2 * v < (a + s) ^ 2 := by
      nlinarith [Real.lt_sq_of_sqrt_lt ha, hs_pos]
    have hexp : Real.exp (2 * yCrit v) < Real.exp (2 * yPlus v a) := by
      rw [exp_two_mul_yCrit hv, yPlus, show 2 * Real.log (a + s) = Real.log ((a + s) ^ 2) by
        rw [Real.log_pow]; ring]
      rw [Real.exp_log (by positivity)]
      exact h2
    linarith [Real.exp_lt_exp.mp hexp]
  refine ⟨hy, ?_⟩
  rw [charA_eq, yPlus, Real.exp_log harg_pos, Real.exp_neg, Real.exp_log harg_pos]
  have hinv : (1 + 2 * v) * (a + s)⁻¹ = a - s := by
    field_simp [harg_pos.ne']
    linarith [hprod]
  rw [hinv]
  ring

lemma charA_yMinus {v a : ℝ} (hv : 0 ≤ v) (ha : Real.sqrt (1 + 2 * v) < a) :
    yMinus v a < yCrit v ∧ charA v (yMinus v a) = a := by
  have ha0 : 0 < a := (Real.sqrt_nonneg _).trans_lt ha
  have h12v : 0 < 1 + 2 * v := by linarith
  have hsub : 0 < a ^ 2 - (1 + 2 * v) := by
    have := Real.lt_sq_of_sqrt_lt ha
    linarith
  set s := Real.sqrt (a ^ 2 - (1 + 2 * v))
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hsub
  have hs_lt : s < a := sqrt_sq_sub_lt_self hv ha
  have harg_pos : 0 < a - s := sub_pos.mpr hs_lt
  have hprod : (a + s) * (a - s) = 1 + 2 * v := by
    have : s ^ 2 = a ^ 2 - (1 + 2 * v) := Real.sq_sqrt hsub.le
    nlinarith
  have hy : yMinus v a < yCrit v := by
    have h2 : (a - s) ^ 2 < 1 + 2 * v := by
      have : a - s < a + s := by linarith
      nlinarith [hprod, harg_pos]
    have hexp : Real.exp (2 * yMinus v a) < Real.exp (2 * yCrit v) := by
      rw [exp_two_mul_yCrit hv, yMinus, show 2 * Real.log (a - s) = Real.log ((a - s) ^ 2) by
        rw [Real.log_pow]; ring]
      rw [Real.exp_log (by positivity)]
      exact h2
    linarith [Real.exp_lt_exp.mp hexp]
  refine ⟨hy, ?_⟩
  rw [charA_eq, yMinus, Real.exp_log harg_pos, Real.exp_neg, Real.exp_log harg_pos]
  have hinv : (1 + 2 * v) * (a - s)⁻¹ = a + s := by
    field_simp [harg_pos.ne']
    linarith [hprod]
  rw [hinv]
  ring

lemma yPlus_charA {v y : ℝ} (hv : 0 ≤ v) (hy : yCrit v < y) :
    yPlus v (charA v y) = y := by
  have ha : Real.sqrt (1 + 2 * v) < charA v y := by
    rw [← charA_yCrit hv]
    exact charA_strictMonoOn hv le_rfl hy.le hy
  obtain ⟨hy', hchar⟩ := charA_yPlus hv ha
  exact (charA_strictMonoOn hv).injOn hy'.le hy.le hchar

lemma yMinus_charA {v y : ℝ} (hv : 0 ≤ v) (hy : y < yCrit v) :
    yMinus v (charA v y) = y := by
  have ha : Real.sqrt (1 + 2 * v) < charA v y := by
    rw [← charA_yCrit hv]
    exact charA_strictAntiOn hv hy.le le_rfl hy
  obtain ⟨hy', hchar⟩ := charA_yMinus hv ha
  exact (charA_strictAntiOn hv).injOn hy'.le hy.le hchar

lemma charA_lower_bound {v y : ℝ} (hv : 0 ≤ v) :
    Real.exp |y| / 2 ≤ charA v y := by
  unfold charA
  have h1 : Real.exp |y| / 2 ≤ Real.cosh y := by
    rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hy, Real.cosh_eq]
      linarith [Real.exp_pos (-y)]
    · rw [abs_of_nonpos hy, Real.cosh_eq]
      linarith [Real.exp_pos y]
  linarith [mul_nonneg hv (Real.exp_pos (-y)).le]

lemma yPlus_contDiffOn {v : ℝ} (_hv : 0 ≤ v) {n : ℕ∞} :
    ContDiffOn ℝ n (yPlus v) (Ioi (Real.sqrt (1 + 2 * v))) := by
  intro a ha
  have ha0 : 0 < a := (Real.sqrt_nonneg _).trans_lt ha
  have hsub : 0 < a ^ 2 - (1 + 2 * v) := by
    have := Real.lt_sq_of_sqrt_lt ha; linarith
  have hs_pos : 0 < Real.sqrt (a ^ 2 - (1 + 2 * v)) := Real.sqrt_pos.mpr hsub
  have harg : a + Real.sqrt (a ^ 2 - (1 + 2 * v)) ≠ 0 := by positivity
  have h1 : ContDiffAt ℝ n (fun x : ℝ => x ^ 2 - (1 + 2 * v)) a := by fun_prop
  have h2 : ContDiffAt ℝ n (fun x : ℝ => Real.sqrt (x ^ 2 - (1 + 2 * v))) a :=
    h1.sqrt hsub.ne'
  have h3 : ContDiffAt ℝ n (fun x : ℝ => x + Real.sqrt (x ^ 2 - (1 + 2 * v))) a :=
    contDiffAt_id.add h2
  exact ((Real.contDiffAt_log.mpr harg).comp a h3).contDiffWithinAt

lemma yMinus_contDiffOn {v : ℝ} (hv : 0 ≤ v) {n : ℕ∞} :
    ContDiffOn ℝ n (yMinus v) (Ioi (Real.sqrt (1 + 2 * v))) := by
  intro a ha
  have hsub : 0 < a ^ 2 - (1 + 2 * v) := by
    have := Real.lt_sq_of_sqrt_lt ha; linarith
  have harg_pos : 0 < a - Real.sqrt (a ^ 2 - (1 + 2 * v)) :=
    sub_pos.mpr (sqrt_sq_sub_lt_self hv ha)
  have h1 : ContDiffAt ℝ n (fun x : ℝ => x ^ 2 - (1 + 2 * v)) a := by fun_prop
  have h2 : ContDiffAt ℝ n (fun x : ℝ => Real.sqrt (x ^ 2 - (1 + 2 * v))) a :=
    h1.sqrt hsub.ne'
  have h3 : ContDiffAt ℝ n (fun x : ℝ => x - Real.sqrt (x ^ 2 - (1 + 2 * v))) a :=
    contDiffAt_id.sub h2
  exact ((Real.contDiffAt_log.mpr harg_pos.ne').comp a h3).contDiffWithinAt

lemma charA_image_Ioi_yCrit {v : ℝ} (hv : 0 ≤ v) :
    charA v '' Ioi (yCrit v) = Ioi (Real.sqrt (1 + 2 * v)) := by
  ext a
  simp only [mem_image, mem_Ioi]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← charA_yCrit hv]
    exact charA_strictMonoOn hv le_rfl hy.le hy
  · intro ha
    obtain ⟨hy, hchar⟩ := charA_yPlus hv ha
    exact ⟨yPlus v a, hy, hchar⟩

lemma charA_image_Iio_yCrit {v : ℝ} (hv : 0 ≤ v) :
    charA v '' Iio (yCrit v) = Ioi (Real.sqrt (1 + 2 * v)) := by
  ext a
  simp only [mem_image, mem_Ioi]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← charA_yCrit hv]
    exact charA_strictAntiOn hv hy.le le_rfl hy
  · intro ha
    obtain ⟨hy, hchar⟩ := charA_yMinus hv ha
    exact ⟨yMinus v a, hy, hchar⟩

end CharacteristicGeometry

section TransportEquation

private def ψBranch (sgn : Bool) (F : ℝ → ℝ) (v y : ℝ) : ℝ :=
  if (if sgn then yCrit v < y else y < yCrit v) then Real.exp (-y) * F (charA v y) else 0

private def hBranch (sgn : Bool) (F : ℝ → ℝ) (v y : ℝ) : ℝ :=
  if (if sgn then yCrit v < y else y < yCrit v) then
    2 * (Real.sinh y - v * Real.exp (-y)) * F (charA v y)
  else 0

private lemma abs_sinh_le_cosh (y : ℝ) : |Real.sinh y| ≤ Real.cosh y := by
  rw [Real.sinh_eq, Real.cosh_eq, abs_div, abs_of_pos (two_pos : (0 : ℝ) < 2)]
  refine div_le_div_of_nonneg_right ?_ two_pos.le
  refine (abs_sub _ _).trans ?_
  rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]

private lemma hBranch_eq_mul_ψBranch (sgn : Bool) (F : ℝ → ℝ) (v y : ℝ) :
    hBranch sgn F v y = (Real.exp (2 * y) - 2 * v - 1) * ψBranch sgn F v y := by
  have hmul : Real.exp (2 * y) * Real.exp (-y) = Real.exp y := by
    rw [← Real.exp_add]; congr 1; ring
  have halg : 2 * (Real.sinh y - v * Real.exp (-y)) * F (charA v y) =
      (Real.exp (2 * y) - 2 * v - 1) * (Real.exp (-y) * F (charA v y)) := by
    calc 2 * (Real.sinh y - v * Real.exp (-y)) * F (charA v y)
        = (Real.exp y - Real.exp (-y) - 2 * v * Real.exp (-y)) * F (charA v y) := by
            rw [Real.sinh_eq]; ring
      _ = (Real.exp (2 * y) * Real.exp (-y) - Real.exp (-y) - 2 * v * Real.exp (-y)) * F (charA v y) := by
            rw [hmul]
      _ = (Real.exp (2 * y) - 2 * v - 1) * (Real.exp (-y) * F (charA v y)) := by ring
  unfold hBranch ψBranch
  cases sgn <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · split_ifs
    · exact halg
    · ring
  · split_ifs
    · exact halg
    · ring

private lemma branch_compactSupport_bound {F : ℝ → ℝ} (hFC : HasCompactSupport F) :
    ∃ R > 0, ∀ sgn v, 0 ≤ v → ∀ y, R ≤ |y| →
      ψBranch sgn F v y = 0 ∧ hBranch sgn F v y = 0 := by
  obtain ⟨M, hM0, hM⟩ : ∃ M > 0, ∀ a, M ≤ |a| → F a = 0 := by
    obtain ⟨M, hM⟩ := hFC.isCompact.isBounded.subset_closedBall (0 : ℝ)
    refine ⟨max M 1 + 1, by positivity, fun a ha => ?_⟩
    by_contra hne
    have hmem : a ∈ tsupport F := subset_tsupport F hne
    have := hM hmem
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    linarith [le_max_left M 1, le_max_right M 1]
  refine ⟨max (Real.log (2 * (M + 1))) 1, by positivity, fun sgn v hv y hy => ?_⟩
  have hlog : Real.log (2 * (M + 1)) ≤ |y| := (le_max_left _ _).trans hy
  have hexp : 2 * (M + 1) ≤ Real.exp |y| := by
    rw [← Real.exp_log (by positivity : 0 < 2 * (M + 1))]
    exact Real.exp_le_exp.mpr hlog
  have hA : M ≤ |charA v y| := by
    have h1 := charA_lower_bound hv (y := y)
    have h2 : 0 ≤ charA v y := (by positivity : 0 ≤ Real.exp |y| / 2).trans h1
    rw [abs_of_nonneg h2]
    linarith
  have hF0 : F (charA v y) = 0 := hM (charA v y) hA
  simp [ψBranch, hBranch, hF0]

private lemma ψBranch_contDiff {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    {v₀ a₀ : ℝ} (_hv₀ : 0 ≤ v₀) (ha₀ : Real.sqrt (1 + 2 * v₀) < a₀)
    (hF0 : ∀ a ≤ a₀, F a = 0) (sgn : Bool) {v : ℝ} (hv : 0 ≤ v) (hvv₀ : v ≤ v₀) :
    ContDiff ℝ 3 (ψBranch sgn F v) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  have hcrit : charA v (yCrit v) < a₀ := by
    rw [charA_yCrit hv]
    exact lt_of_le_of_lt (Real.sqrt_le_sqrt (by linarith)) ha₀
  rcases lt_trichotomy (yCrit v) y with hy | hy | hy
  · have hF_smooth : ContDiffAt ℝ 3 (fun y' => Real.exp (-y') * F (charA v y')) y := by
      have hA : ContDiff ℝ 3 (charA v) := by unfold charA; fun_prop
      exact (contDiff_id.neg.exp.contDiffAt).mul ((hF.comp hA).contDiffAt)
    cases sgn
    · have h_ev : ψBranch false F v =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        filter_upwards [eventually_gt_nhds hy] with y' hy'
        simp [ψBranch, not_lt.mpr hy'.le]
      exact contDiffAt_const.congr_of_eventuallyEq h_ev
    · have h_ev : ψBranch true F v =ᶠ[𝓝 y] fun y' => Real.exp (-y') * F (charA v y') := by
        filter_upwards [eventually_gt_nhds hy] with y' hy'
        simp [ψBranch, hy']
      exact hF_smooth.congr_of_eventuallyEq h_ev
  · have hAcont : Continuous (charA v) := by unfold charA; fun_prop
    have h_nhds : {y' : ℝ | charA v y' < a₀} ∈ 𝓝 (yCrit v) :=
      hAcont.continuousAt.preimage_mem_nhds (Iio_mem_nhds hcrit)
    have h_ev : ψBranch sgn F v =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      rw [← hy]
      filter_upwards [h_nhds] with y' hy'
      simp [ψBranch, hF0 _ (le_of_lt hy')]
    exact contDiffAt_const.congr_of_eventuallyEq h_ev
  · have hF_smooth : ContDiffAt ℝ 3 (fun y' => Real.exp (-y') * F (charA v y')) y := by
      have hA : ContDiff ℝ 3 (charA v) := by unfold charA; fun_prop
      exact (contDiff_id.neg.exp.contDiffAt).mul ((hF.comp hA).contDiffAt)
    cases sgn
    · have h_ev : ψBranch false F v =ᶠ[𝓝 y] fun y' => Real.exp (-y') * F (charA v y') := by
        filter_upwards [eventually_lt_nhds hy] with y' hy'
        simp [ψBranch, hy']
      exact hF_smooth.congr_of_eventuallyEq h_ev
    · have h_ev : ψBranch true F v =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        filter_upwards [eventually_lt_nhds hy] with y' hy'
        simp [ψBranch, not_lt.mpr hy'.le]
      exact contDiffAt_const.congr_of_eventuallyEq h_ev

private lemma ψBranch_hasCompactSupport {F : ℝ → ℝ} (hFC : HasCompactSupport F)
    (sgn : Bool) {v : ℝ} (hv : 0 ≤ v) :
    HasCompactSupport (ψBranch sgn F v) := by
  obtain ⟨R, hR0, hR⟩ := branch_compactSupport_bound hFC
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -R) (b := R)) ?_
  intro y hy
  by_contra hnot
  have habs : R ≤ |y| := by
    simp only [mem_Icc, not_and_or, not_le] at hnot
    rcases hnot with h | h
    · exact le_trans (by linarith) (neg_le_abs y)
    · exact le_trans h.le (le_abs_self y)
  exact hy (hR sgn v hv y habs).1

private lemma hasDerivAt_hBranch_v {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    {v₀ a₀ : ℝ} (_hv₀ : 0 ≤ v₀) (_ha₀ : Real.sqrt (1 + 2 * v₀) < a₀)
    (hF0 : ∀ a ≤ a₀, F a = 0) (sgn : Bool) {δ : ℝ}
    (hδ : Real.sqrt (1 + 2 * (v₀ + δ)) < a₀) (_hδ0 : 0 < δ)
    {v : ℝ} (hv : 0 < v) (hvv₀ : v < v₀ + δ) (y : ℝ) :
    HasDerivAt (fun v' => hBranch sgn F v' y) (2 * deriv (ψBranch sgn F v) y) v := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hFdiff : Differentiable ℝ F := hF1.differentiable (by norm_num)
  have hcrit : charA v (yCrit v) < a₀ := by
    rw [charA_yCrit hv.le]
    exact lt_of_le_of_lt (Real.sqrt_le_sqrt (by linarith)) hδ
  have hyCrit_at : ContinuousAt yCrit v := by
    have h12v : (1 + 2 * v) ≠ 0 := by linarith
    exact continuousAt_const.mul (ContinuousAt.log (by fun_prop) h12v)
  rcases lt_trichotomy (yCrit v) y with hy | hy | hy
  · have h_ev_v : ∀ᶠ v' in 𝓝 v,
        hBranch sgn F v' y = if sgn then 2 * (Real.sinh y - v' * Real.exp (-y)) * F (charA v' y) else 0 := by
      filter_upwards [hyCrit_at.eventually (isOpen_Iio.mem_nhds hy)] with v' hv'
      cases sgn <;> simp [hBranch, hv', not_lt.mpr hv'.le]
    have h_ev_y : ψBranch sgn F v =ᶠ[𝓝 y]
        if sgn then fun y' => Real.exp (-y') * F (charA v y') else fun _ => (0 : ℝ) := by
      filter_upwards [eventually_gt_nhds hy] with y' hy'
      cases sgn <;> simp [ψBranch, hy', not_lt.mpr hy'.le]
    rw [h_ev_y.deriv_eq]
    cases sgn
    · simp only [Bool.false_eq_true, ↓reduceIte, deriv_const', mul_zero]
      exact (hasDerivAt_const v (0 : ℝ)).congr_of_eventuallyEq h_ev_v
    · simp only [↓reduceIte]
      have hd_y : deriv (fun y' => Real.exp (-y') * F (charA v y')) y =
          (-Real.exp (-y)) * F (charA v y) +
          Real.exp (-y) * (deriv F (charA v y) * (Real.sinh y - v * Real.exp (-y))) := by
        have h1 : HasDerivAt (fun y' => Real.exp (-y')) (-Real.exp (-y)) y := by
          simpa using (hasDerivAt_id' y).neg.exp
        have h2 : HasDerivAt (fun y' => F (charA v y'))
            (deriv F (charA v y) * (Real.sinh y - v * Real.exp (-y))) y :=
          (hFdiff (charA v y)).hasDerivAt.comp y (hasDerivAt_charA_y v y)
        exact (h1.mul h2).deriv
      rw [hd_y]
      have hd_v : HasDerivAt (fun v' => 2 * (Real.sinh y - v' * Real.exp (-y)) * F (charA v' y))
          (2 * (-Real.exp (-y)) * F (charA v y) +
            2 * (Real.sinh y - v * Real.exp (-y)) * (deriv F (charA v y) * Real.exp (-y))) v := by
        have h1 : HasDerivAt (fun v' => 2 * (Real.sinh y - v' * Real.exp (-y)))
            (2 * (-Real.exp (-y))) v := by
          have h := ((hasDerivAt_id' v).mul_const (Real.exp (-y))).const_sub (Real.sinh y)
          convert h.const_mul 2 using 1; ring
        have h2 : HasDerivAt (fun v' => F (charA v' y))
            (deriv F (charA v y) * Real.exp (-y)) v :=
          (hFdiff (charA v y)).hasDerivAt.comp v (hasDerivAt_charA_v v y)
        exact h1.mul h2
      refine hd_v.congr_of_eventuallyEq h_ev_v |>.congr_deriv ?_
      ring
  · have hA_cont_v : ContinuousAt (fun v' => charA v' y) v := by
      unfold charA; fun_prop
    have h_ev_v : ∀ᶠ v' in 𝓝 v, hBranch sgn F v' y = 0 := by
      have h_nhds : {v' : ℝ | charA v' y < a₀} ∈ 𝓝 v :=
        hA_cont_v.preimage_mem_nhds (Iio_mem_nhds (hy ▸ hcrit))
      filter_upwards [h_nhds] with v' hv'
      simp [hBranch, hF0 _ hv'.le]
    have hA_cont_y : ContinuousAt (charA v) y := by unfold charA; fun_prop
    have h_ev_y : ψBranch sgn F v =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      have h_nhds : {y' : ℝ | charA v y' < a₀} ∈ 𝓝 y :=
        hA_cont_y.preimage_mem_nhds (Iio_mem_nhds (hy ▸ hcrit))
      filter_upwards [h_nhds] with y' hy'
      simp [ψBranch, hF0 _ hy'.le]
    rw [h_ev_y.deriv_eq, deriv_const', mul_zero]
    exact (hasDerivAt_const v (0 : ℝ)).congr_of_eventuallyEq h_ev_v
  · have h_ev_v : ∀ᶠ v' in 𝓝 v,
        hBranch sgn F v' y = if sgn then 0 else 2 * (Real.sinh y - v' * Real.exp (-y)) * F (charA v' y) := by
      filter_upwards [hyCrit_at.eventually (isOpen_Ioi.mem_nhds hy)] with v' hv'
      cases sgn <;> simp [hBranch, hv', not_lt.mpr hv'.le]
    have h_ev_y : ψBranch sgn F v =ᶠ[𝓝 y]
        if sgn then fun _ => (0 : ℝ) else fun y' => Real.exp (-y') * F (charA v y') := by
      filter_upwards [eventually_lt_nhds hy] with y' hy'
      cases sgn <;> simp [ψBranch, hy', not_lt.mpr hy'.le]
    rw [h_ev_y.deriv_eq]
    cases sgn
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hd_y : deriv (fun y' => Real.exp (-y') * F (charA v y')) y =
          (-Real.exp (-y)) * F (charA v y) +
          Real.exp (-y) * (deriv F (charA v y) * (Real.sinh y - v * Real.exp (-y))) := by
        have h1 : HasDerivAt (fun y' => Real.exp (-y')) (-Real.exp (-y)) y := by
          simpa using (hasDerivAt_id' y).neg.exp
        have h2 : HasDerivAt (fun y' => F (charA v y'))
            (deriv F (charA v y) * (Real.sinh y - v * Real.exp (-y))) y :=
          (hFdiff (charA v y)).hasDerivAt.comp y (hasDerivAt_charA_y v y)
        exact (h1.mul h2).deriv
      rw [hd_y]
      have hd_v : HasDerivAt (fun v' => 2 * (Real.sinh y - v' * Real.exp (-y)) * F (charA v' y))
          (2 * (-Real.exp (-y)) * F (charA v y) +
            2 * (Real.sinh y - v * Real.exp (-y)) * (deriv F (charA v y) * Real.exp (-y))) v := by
        have h1 : HasDerivAt (fun v' => 2 * (Real.sinh y - v' * Real.exp (-y)))
            (2 * (-Real.exp (-y))) v := by
          have h := ((hasDerivAt_id' v).mul_const (Real.exp (-y))).const_sub (Real.sinh y)
          convert h.const_mul 2 using 1; ring
        have h2 : HasDerivAt (fun v' => F (charA v' y))
            (deriv F (charA v y) * Real.exp (-y)) v :=
          (hFdiff (charA v y)).hasDerivAt.comp v (hasDerivAt_charA_v v y)
        exact h1.mul h2
      refine hd_v.congr_of_eventuallyEq h_ev_v |>.congr_deriv ?_
      ring
    · simp only [↓reduceIte, deriv_const', mul_zero]
      exact (hasDerivAt_const v (0 : ℝ)).congr_of_eventuallyEq h_ev_v

private lemma hBranch_continuous {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    {v₀ a₀ : ℝ} (hv₀ : 0 ≤ v₀) (ha₀ : Real.sqrt (1 + 2 * v₀) < a₀)
    (hF0 : ∀ a ≤ a₀, F a = 0) (sgn : Bool) {v : ℝ} (hv : 0 ≤ v) (hvv₀ : v ≤ v₀) :
    Continuous (hBranch sgn F v) := by
  have heq : hBranch sgn F v = fun y => (Real.exp (2 * y) - 2 * v - 1) * ψBranch sgn F v y := by
    funext y; exact hBranch_eq_mul_ψBranch sgn F v y
  rw [heq]
  have hψc : Continuous (ψBranch sgn F v) :=
    (ψBranch_contDiff hF hv₀ ha₀ hF0 sgn hv hvv₀).continuous
  fun_prop

private lemma deriv_ψBranch_continuous {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    {v₀ a₀ : ℝ} (hv₀ : 0 ≤ v₀) (ha₀ : Real.sqrt (1 + 2 * v₀) < a₀)
    (hF0 : ∀ a ≤ a₀, F a = 0) (sgn : Bool) {v : ℝ} (hv : 0 ≤ v) (hvv₀ : v ≤ v₀) :
    Continuous (deriv (ψBranch sgn F v)) := by
  have hψ3 := ψBranch_contDiff hF hv₀ ha₀ hF0 sgn hv hvv₀
  exact ((contDiff_succ_iff_deriv (n := 2)).mp hψ3).2.2.continuous

private lemma deriv_ψBranch_bound {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F) (_hFC : HasCompactSupport F)
    {v₀ a₀ : ℝ} (hv₀ : 0 ≤ v₀) (ha₀ : Real.sqrt (1 + 2 * v₀) < a₀)
    (hF0 : ∀ a ≤ a₀, F a = 0) (sgn : Bool) {R CF : ℝ} (hR0 : 0 < R) (hCF0 : 0 ≤ CF)
    (hR : ∀ sgn' v', 0 ≤ v' → ∀ y, R ≤ |y| → ψBranch sgn' F v' y = 0 ∧ hBranch sgn' F v' y = 0)
    (hF_bdd : ∀ a, |F a| ≤ CF) (hF'_bdd : ∀ a, |deriv F a| ≤ CF)
    {v : ℝ} (hv : 0 ≤ v) (hvv₀ : v ≤ v₀) (y : ℝ) :
    |deriv (ψBranch sgn F v) y| ≤
      Real.exp R * CF + Real.exp R * CF * (Real.cosh R + v₀ * Real.exp R) := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hFdiff : Differentiable ℝ F := hF1.differentiable (by norm_num)
  by_cases hyR : R < |y|
  · have h_ev : ψBranch sgn F v =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      have h_nhds : {y' : ℝ | R < |y'|} ∈ 𝓝 y :=
        isOpen_lt continuous_const continuous_abs |>.mem_nhds hyR
      filter_upwards [h_nhds] with y' hy'
      exact (hR sgn v hv y' hy'.le).1
    rw [h_ev.deriv_eq, deriv_const', abs_zero]
    have hc : 0 ≤ Real.cosh R + v₀ * Real.exp R := by positivity
    positivity
  · have hyR' : |y| ≤ R := not_lt.mp hyR
    have hcrit : charA v (yCrit v) < a₀ := by
      rw [charA_yCrit hv]
      exact lt_of_le_of_lt (Real.sqrt_le_sqrt (by linarith)) ha₀
    have hexp_le : Real.exp (-y) ≤ Real.exp R := Real.exp_le_exp.mpr ((neg_le_abs y).trans hyR')
    have hfac_le : |Real.sinh y - v * Real.exp (-y)| ≤ Real.cosh R + v₀ * Real.exp R := by
      calc |Real.sinh y - v * Real.exp (-y)|
          ≤ |Real.sinh y| + |v * Real.exp (-y)| := abs_sub _ _
        _ ≤ Real.cosh y + v * Real.exp (-y) := by
            rw [abs_mul, abs_of_nonneg hv, abs_of_pos (Real.exp_pos _)]
            exact add_le_add (abs_sinh_le_cosh y) le_rfl
        _ ≤ Real.cosh R + v₀ * Real.exp R :=
            add_le_add (Real.cosh_le_cosh.mpr (by rw [abs_of_pos hR0]; exact hyR'))
              (mul_le_mul hvv₀ hexp_le (Real.exp_pos _).le hv₀)
    have hval_le : |-Real.exp (-y) * F (charA v y) +
          Real.exp (-y) * (deriv F (charA v y) * (Real.sinh y - v * Real.exp (-y)))| ≤
        Real.exp R * CF + Real.exp R * CF * (Real.cosh R + v₀ * Real.exp R) := by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul hexp_le (hF_bdd _) (abs_nonneg _) (Real.exp_pos _).le
      · rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_mul]
        calc Real.exp (-y) * (|deriv F (charA v y)| * |Real.sinh y - v * Real.exp (-y)|)
            ≤ Real.exp R * (CF * (Real.cosh R + v₀ * Real.exp R)) :=
              mul_le_mul hexp_le (mul_le_mul (hF'_bdd _) hfac_le (abs_nonneg _) hCF0)
                (by positivity) (Real.exp_pos _).le
          _ = Real.exp R * CF * (Real.cosh R + v₀ * Real.exp R) := by ring
    rcases lt_trichotomy (yCrit v) y with hy | hy | hy
    · have h_ev_y : ψBranch sgn F v =ᶠ[𝓝 y]
          if sgn then fun y' => Real.exp (-y') * F (charA v y') else fun _ => (0 : ℝ) := by
        filter_upwards [eventually_gt_nhds hy] with y' hy'
        cases sgn <;> simp [ψBranch, hy', not_lt.mpr hy'.le]
      rw [h_ev_y.deriv_eq]
      cases sgn
      · simp only [Bool.false_eq_true, ↓reduceIte, deriv_const', abs_zero]
        have hc : 0 ≤ Real.cosh R + v₀ * Real.exp R := by positivity
        positivity
      · simp only [↓reduceIte]
        have hd_y : deriv (fun y' => Real.exp (-y') * F (charA v y')) y =
            (-Real.exp (-y)) * F (charA v y) +
            Real.exp (-y) * (deriv F (charA v y) * (Real.sinh y - v * Real.exp (-y))) := by
          have h1 : HasDerivAt (fun y' => Real.exp (-y')) (-Real.exp (-y)) y := by
            simpa using (hasDerivAt_id' y).neg.exp
          have h2 : HasDerivAt (fun y' => F (charA v y'))
              (deriv F (charA v y) * (Real.sinh y - v * Real.exp (-y))) y :=
            (hFdiff (charA v y)).hasDerivAt.comp y (hasDerivAt_charA_y v y)
          exact (h1.mul h2).deriv
        rw [hd_y]
        exact hval_le
    · have hA_cont_y : ContinuousAt (charA v) y := by unfold charA; fun_prop
      have h_ev_y : ψBranch sgn F v =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        have h_nhds : {y' : ℝ | charA v y' < a₀} ∈ 𝓝 y :=
          hA_cont_y.preimage_mem_nhds (Iio_mem_nhds (hy ▸ hcrit))
        filter_upwards [h_nhds] with y' hy'
        simp [ψBranch, hF0 _ hy'.le]
      rw [h_ev_y.deriv_eq, deriv_const', abs_zero]
      have hc : 0 ≤ Real.cosh R + v₀ * Real.exp R := by positivity
      positivity
    · have h_ev_y : ψBranch sgn F v =ᶠ[𝓝 y]
          if sgn then fun _ => (0 : ℝ) else fun y' => Real.exp (-y') * F (charA v y') := by
        filter_upwards [eventually_lt_nhds hy] with y' hy'
        cases sgn <;> simp [ψBranch, hy', not_lt.mpr hy'.le]
      rw [h_ev_y.deriv_eq]
      cases sgn
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hd_y : deriv (fun y' => Real.exp (-y')) y = -Real.exp (-y) := by
          simpa using ((hasDerivAt_id' y).neg.exp).deriv
        have hd_y' : deriv (fun y' => Real.exp (-y') * F (charA v y')) y =
            (-Real.exp (-y)) * F (charA v y) +
            Real.exp (-y) * (deriv F (charA v y) * (Real.sinh y - v * Real.exp (-y))) := by
          have h1 : HasDerivAt (fun y' => Real.exp (-y')) (-Real.exp (-y)) y := by
            simpa using (hasDerivAt_id' y).neg.exp
          have h2 : HasDerivAt (fun y' => F (charA v y'))
              (deriv F (charA v y) * (Real.sinh y - v * Real.exp (-y))) y :=
            (hFdiff (charA v y)).hasDerivAt.comp y (hasDerivAt_charA_y v y)
          exact (h1.mul h2).deriv
        rw [hd_y']
        exact hval_le
      · simp only [↓reduceIte, deriv_const', abs_zero]
        have hc : 0 ≤ Real.cosh R + v₀ * Real.exp R := by positivity
        positivity

private lemma transport_branch_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W)
    (t : ℝ≥0) (ht : 0 < t) {v₀ a₀ : ℝ} (hv₀ : 0 < v₀) (ha₀ : Real.sqrt (1 + 2 * v₀) < a₀)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F) (hFC : HasCompactSupport F)
    (hF0 : ∀ a ≤ a₀, F a = 0) (sgn : Bool) :
    ∫ ω, hBranch sgn F v₀ (W t ω) * Real.exp (-v₀ / expInt W 2 0 t ω) ∂P =
      ∫ ω, hBranch sgn F 0 (W t ω) ∂P := by
  let B : ℝ≥0 → Ω → ℝ := hW.toIsPreBrownianReal.mk W
  have hBmeas : ∀ s, Measurable (B s) := hW.toIsPreBrownianReal.measurable_mk
  have hBcont : ∀ ω, Continuous (B · ω) := hW.toIsPreBrownianReal.continuous_mk
  have hBpre : IsPreBrownianReal B P :=
    hW.toIsPreBrownianReal.isBrownianReal_mk.toIsPreBrownianReal
  have hBbm : IsBM P B := ⟨hBpre, Eventually.of_forall hBcont⟩
  have hBW : ∀ᵐ ω ∂P, ∀ s, B s ω = W s ω := hW.mk_ae_forall_eq
  have hXpos := expInt_two_pos_ae B hBbm t ht
  have hBW_lhs :
      ∫ ω, hBranch sgn F v₀ (W t ω) * Real.exp (-v₀ / expInt W 2 0 t ω) ∂P =
      ∫ ω, hBranch sgn F v₀ (B t ω) * Real.exp (-v₀ / expInt B 2 0 t ω) ∂P := by
    refine integral_congr_ae (hBW.mono fun ω hω => ?_)
    dsimp only
    have hX : expInt W 2 0 t ω = expInt B 2 0 t ω := by
      simp only [expInt]; exact intervalIntegral.integral_congr fun s _ => by rw [hω s.toNNReal]
    rw [hX, ← hω t]
  have hBW_rhs :
      ∫ ω, hBranch sgn F 0 (W t ω) ∂P = ∫ ω, hBranch sgn F 0 (B t ω) ∂P := by
    refine integral_congr_ae (hBW.mono fun ω hω => ?_)
    dsimp only
    rw [← hω t]
  rw [hBW_lhs, hBW_rhs]
  have hXmeas : Measurable (expInt B 2 0 t) := measurable_expInt_bm hBmeas hBcont 2 t
  obtain ⟨R, hR0, hR⟩ := branch_compactSupport_bound hFC
  obtain ⟨CF, _, hCF0, _, _, hF_bdd, hF'_bdd, _, _⟩ := contDiff_three_compactSupport_bounds hF hFC
  have ha₀2 : 1 + 2 * v₀ < a₀ ^ 2 := Real.lt_sq_of_sqrt_lt ha₀
  let δ : ℝ := (a₀ ^ 2 - (1 + 2 * v₀)) / 4
  have hδ0 : 0 < δ := by dsimp [δ]; linarith
  have hδ : Real.sqrt (1 + 2 * (v₀ + δ)) < a₀ := by
    have ha₀pos : 0 < a₀ := (Real.sqrt_nonneg _).trans_lt ha₀
    rw [Real.sqrt_lt' ha₀pos]
    dsimp [δ]; linarith
  let vMax : ℝ := v₀ + δ / 2
  have hvMax0 : 0 ≤ vMax := by dsimp [vMax]; linarith
  have hvMax_lt : Real.sqrt (1 + 2 * vMax) < a₀ := by
    refine lt_of_le_of_lt (Real.sqrt_le_sqrt ?_) hδ
    dsimp [vMax]; linarith
  let Φ : ℝ → Ω → ℝ := fun v ω =>
    hBranch sgn F v (B t ω) * Real.exp (-v / expInt B 2 0 t ω)
  let G : ℝ → ℝ := fun v => ∫ ω, Φ v ω ∂P
  have hΦ_meas : ∀ v ∈ Icc (0 : ℝ) vMax, AEStronglyMeasurable (Φ v) P := by
    intro v ⟨hv0, hvM⟩
    have hc : Continuous (hBranch sgn F v) :=
      hBranch_continuous hF hvMax0 hvMax_lt hF0 sgn hv0 hvM
    have hm1 : Measurable (fun ω => hBranch sgn F v (B t ω)) := hc.measurable.comp (hBmeas t)
    have hm2 : Measurable (fun ω => Real.exp (-v / expInt B 2 0 t ω)) :=
      Real.continuous_exp.measurable.comp (measurable_const.div hXmeas)
    exact (hm1.mul hm2).aestronglyMeasurable
  have h_hBranch_bdd : ∀ v ∈ Icc (0 : ℝ) vMax, ∀ y,
      |hBranch sgn F v y| ≤ 2 * (Real.cosh R + vMax * Real.exp R) * CF := by
    intro v ⟨hv0, hvM⟩ y
    by_cases hy : R ≤ |y|
    · rw [(hR sgn v hv0 y hy).2, abs_zero]
      positivity
    · have hyR : |y| ≤ R := (not_le.mp hy).le
      have hmy : -y ≤ R := (neg_le_abs y).trans hyR
      have hsinh : |Real.sinh y| ≤ Real.cosh R :=
        (abs_sinh_le_cosh y).trans (Real.cosh_le_cosh.mpr (by rw [abs_of_pos hR0]; exact hyR))
      have hexp : Real.exp (-y) ≤ Real.exp R := Real.exp_le_exp.mpr hmy
      have hfac : |Real.sinh y - v * Real.exp (-y)| ≤ Real.cosh R + vMax * Real.exp R := by
        calc |Real.sinh y - v * Real.exp (-y)|
            ≤ |Real.sinh y| + |v * Real.exp (-y)| := abs_sub _ _
          _ ≤ Real.cosh R + vMax * Real.exp R := by
              refine add_le_add hsinh ?_
              rw [abs_mul, abs_of_nonneg hv0, abs_of_pos (Real.exp_pos _)]
              exact mul_le_mul hvM hexp (Real.exp_pos _).le hvMax0
      unfold hBranch
      cases sgn <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · split_ifs
        · rw [abs_mul, abs_mul, abs_of_pos two_pos]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hfac two_pos.le) (hF_bdd (charA v y))
            (abs_nonneg _) (by positivity)
        · rw [abs_zero]; positivity
      · split_ifs
        · rw [abs_mul, abs_mul, abs_of_pos two_pos]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hfac two_pos.le) (hF_bdd (charA v y))
            (abs_nonneg _) (by positivity)
        · rw [abs_zero]; positivity
  have hΦ_bdd : ∀ v ∈ Icc (0 : ℝ) vMax, ∀ᵐ ω ∂P,
      |Φ v ω| ≤ 2 * (Real.cosh R + vMax * Real.exp R) * CF := by
    intro v hv
    filter_upwards [hXpos] with ω hω
    have hexp : Real.exp (-v / expInt B 2 0 t ω) ≤ 1 :=
      Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hv.1) hω.le)
    calc |Φ v ω| = |hBranch sgn F v (B t ω)| * Real.exp (-v / expInt B 2 0 t ω) := by
          simp only [Φ, abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ (2 * (Real.cosh R + vMax * Real.exp R) * CF) * 1 :=
          mul_le_mul (h_hBranch_bdd v hv (B t ω)) hexp (Real.exp_pos _).le (by positivity)
      _ = 2 * (Real.cosh R + vMax * Real.exp R) * CF := mul_one _
  have h_deriv_zero : ∀ v₁ ∈ Ioo 0 v₀, ∀ v ∈ Icc v₁ v₀, HasDerivAt G 0 v := by
    intro v₁ ⟨hv₁0, hv₁lt⟩ v ⟨hv₁v, hvv₀⟩
    have hv0 : 0 < v := hv₁0.trans_le hv₁v
    have hvvM : v < vMax := lt_of_le_of_lt hvv₀ (by dsimp [vMax]; linarith)
    let s : Set ℝ := Ioo (v₁ / 2) vMax
    have hs_nhds : s ∈ 𝓝 v := isOpen_Ioo.mem_nhds ⟨by linarith, hvvM⟩
    let Φ' : ℝ → Ω → ℝ := fun v' ω =>
      ((2 * v' + 1 - Real.exp (2 * B t ω)) / expInt B 2 0 t ω * ψBranch sgn F v' (B t ω) +
        2 * deriv (ψBranch sgn F v') (B t ω)) * Real.exp (-v' / expInt B 2 0 t ω)
    have hΦ_ev_meas : ∀ᶠ v' in 𝓝 v, AEStronglyMeasurable (Φ v') P := by
      filter_upwards [hs_nhds] with v' hv'
      exact hΦ_meas v' ⟨by linarith [hv'.1], hv'.2.le⟩
    have hΦ_int : Integrable (Φ v) P :=
      (integrable_const _).mono' (hΦ_meas v ⟨hv0.le, hvvM.le⟩)
        ((hΦ_bdd v ⟨hv0.le, hvvM.le⟩).mono fun ω hω => by simpa [Real.norm_eq_abs] using hω)
    have hΦ'_meas : AEStronglyMeasurable (Φ' v) P := by
      have hψc : Continuous (ψBranch sgn F v) :=
        (ψBranch_contDiff hF hvMax0 hvMax_lt hF0 sgn hv0.le hvvM.le).continuous
      have hψ'c : Continuous (deriv (ψBranch sgn F v)) :=
        deriv_ψBranch_continuous hF hvMax0 hvMax_lt hF0 sgn hv0.le hvvM.le
      have hm1 : Measurable (fun ω => ψBranch sgn F v (B t ω)) := hψc.measurable.comp (hBmeas t)
      have hm2 : Measurable (fun ω => deriv (ψBranch sgn F v) (B t ω)) := hψ'c.measurable.comp (hBmeas t)
      have hm3 : Measurable (B t) := hBmeas t
      have hm4 : Measurable (fun ω => ((2 * v + 1 - Real.exp (2 * B t ω)) / expInt B 2 0 t ω *
          ψBranch sgn F v (B t ω) + 2 * deriv (ψBranch sgn F v) (B t ω)) *
          Real.exp (-v / expInt B 2 0 t ω)) := by
        refine ((Measurable.mul ?_ hm1).add (measurable_const.mul hm2)).mul ?_
        · exact (measurable_const.sub (Real.continuous_exp.measurable.comp (measurable_const.mul hm3))).div hXmeas
        · exact Real.continuous_exp.measurable.comp (measurable_const.div hXmeas)
      exact hm4.aestronglyMeasurable
    let K : ℝ :=
      2 * (Real.exp R * CF + Real.exp R * CF * (Real.cosh R + vMax * Real.exp R)) +
      (2 * (Real.cosh R + vMax * Real.exp R) * CF) * (1 / (Real.exp 1 * (v₁ / 2)))
    have h_bound : ∀ᵐ ω ∂P, ∀ v' ∈ s, ‖Φ' v' ω‖ ≤ K := by
      filter_upwards [hXpos] with ω hω v' hv'
      have hv'0 : 0 < v' := by linarith [hv'.1]
      have hv'M : v' ≤ vMax := hv'.2.le
      set x := expInt B 2 0 t ω
      set y := B t ω
      have hd1 : |deriv (ψBranch sgn F v') y| ≤
          Real.exp R * CF + Real.exp R * CF * (Real.cosh R + vMax * Real.exp R) :=
        deriv_ψBranch_bound hF hFC hvMax0 hvMax_lt hF0 sgn hR0 hCF0 hR hF_bdd hF'_bdd hv'0.le hv'M y
      have hhexp1 : Real.exp (-v' / x) ≤ 1 :=
        Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hv'0.le) hω.le)
      have hhexp2 : x⁻¹ * Real.exp (-v' / x) ≤ 1 / (Real.exp 1 * (v₁ / 2)) := by
        have hv12 : 0 < v₁ / 2 := by linarith
        have hle1 : Real.exp (-v' / x) ≤ Real.exp (-(v₁ / 2) / x) :=
          Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith [hv'.1]) hω.le)
        have h_exp : (v₁ / 2) / x ≤ Real.exp ((v₁ / 2) / x) / Real.exp 1 := by
          have hadd := Real.add_one_le_exp ((v₁ / 2) / x - 1)
          rw [sub_add_cancel, Real.exp_sub] at hadd
          exact hadd
        have hle2 : x⁻¹ * Real.exp (-(v₁ / 2) / x) ≤ 1 / (Real.exp 1 * (v₁ / 2)) := by
          have h_exp : (v₁ / 2) / x ≤ Real.exp ((v₁ / 2) / x) / Real.exp 1 := by
            have hadd := Real.add_one_le_exp ((v₁ / 2) / x - 1)
            rw [sub_add_cancel, Real.exp_sub] at hadd
            exact hadd
          have h_exp' : (v₁ / 2) / x * Real.exp 1 ≤ Real.exp ((v₁ / 2) / x) :=
            (le_div_iff₀ (Real.exp_pos 1)).mp h_exp
          have hpos_den : 0 < Real.exp ((v₁ / 2) / x) * (Real.exp 1 * (v₁ / 2)) := by positivity
          rw [neg_div, Real.exp_neg, ← div_eq_mul_inv, inv_eq_one_div, div_div,
            div_le_div_iff₀ (mul_pos hω (Real.exp_pos _)) (mul_pos (Real.exp_pos 1) hv12)]
          calc 1 * (Real.exp 1 * (v₁ / 2))
              = x * ((v₁ / 2) / x * Real.exp 1) := by field_simp [hω.ne']
            _ ≤ x * Real.exp ((v₁ / 2) / x) := mul_le_mul_of_nonneg_left h_exp' hω.le
            _ = 1 * (x * Real.exp (v₁ / 2 / x)) := by ring_nf
        exact (mul_le_mul_of_nonneg_left hle1 (inv_nonneg.mpr hω.le)).trans hle2
      have hterm1 : |((2 * v' + 1 - Real.exp (2 * y)) / x * ψBranch sgn F v' y) * Real.exp (-v' / x)| ≤
          (2 * (Real.cosh R + vMax * Real.exp R) * CF) * (1 / (Real.exp 1 * (v₁ / 2))) := by
        have heq_h : (2 * v' + 1 - Real.exp (2 * y)) / x * ψBranch sgn F v' y =
            -(hBranch sgn F v' y * x⁻¹) := by
          rw [hBranch_eq_mul_ψBranch]; ring
        rw [heq_h, neg_mul, abs_neg, mul_assoc, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hω),
          abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul (h_hBranch_bdd v' ⟨hv'0.le, hv'M⟩ y) hhexp2 (by positivity) (by positivity)
      have hterm2 : |(2 * deriv (ψBranch sgn F v') y) * Real.exp (-v' / x)| ≤
          2 * (Real.exp R * CF + Real.exp R * CF * (Real.cosh R + vMax * Real.exp R)) := by
        rw [abs_mul, abs_mul, abs_of_pos two_pos, abs_of_pos (Real.exp_pos _)]
        calc 2 * |deriv (ψBranch sgn F v') y| * Real.exp (-v' / x)
            ≤ 2 * (Real.exp R * CF + Real.exp R * CF * (Real.cosh R + vMax * Real.exp R)) * 1 := by
              gcongr
          _ = 2 * (Real.exp R * CF + Real.exp R * CF * (Real.cosh R + vMax * Real.exp R)) := mul_one _
      have hΦ'_eq : Φ' v' ω =
          ((2 * v' + 1 - Real.exp (2 * y)) / x * ψBranch sgn F v' y) * Real.exp (-v' / x) +
            (2 * deriv (ψBranch sgn F v') y) * Real.exp (-v' / x) := by
        dsimp only [Φ', x, y]; ring
      rw [Real.norm_eq_abs, hΦ'_eq]
      calc |((2 * v' + 1 - Real.exp (2 * y)) / x * ψBranch sgn F v' y) * Real.exp (-v' / x) +
              (2 * deriv (ψBranch sgn F v') y) * Real.exp (-v' / x)|
          ≤ |((2 * v' + 1 - Real.exp (2 * y)) / x * ψBranch sgn F v' y) * Real.exp (-v' / x)| +
              |(2 * deriv (ψBranch sgn F v') y) * Real.exp (-v' / x)| := abs_add_le _ _
        _ ≤ K := by dsimp [K]; linarith
    have h_diff : ∀ᵐ ω ∂P, ∀ v' ∈ s, HasDerivAt (Φ · ω) (Φ' v' ω) v' := by
      filter_upwards [hXpos] with ω hω v' hv'
      have hv'0 : 0 < v' := by linarith [hv'.1]
      have hv'M : v' < v₀ + δ := lt_of_lt_of_le hv'.2 (by dsimp [vMax]; linarith)
      set x := expInt B 2 0 t ω
      set y := B t ω
      have h1 : HasDerivAt (fun u => hBranch sgn F u y) (2 * deriv (ψBranch sgn F v') y) v' :=
        hasDerivAt_hBranch_v hF hv₀.le ha₀ hF0 sgn hδ hδ0 hv'0 hv'M y
      have h2 : HasDerivAt (fun u => Real.exp (-u / x)) ((-1 / x) * Real.exp (-v' / x)) v' := by
        have hlin : HasDerivAt (fun u : ℝ => -u / x) (-1 / x) v' := by
          simpa using ((hasDerivAt_id' v').neg).div_const x
        simpa [mul_comm] using hlin.exp
      have hprod := h1.mul h2
      refine hprod.congr_deriv ?_
      have heq_h := hBranch_eq_mul_ψBranch sgn F v' y
      rw [heq_h]
      dsimp only [Φ', x, y]
      simp only [div_eq_mul_inv, neg_mul]
      field_simp [hω.ne']
      ring
    have h_param := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs_nhds hΦ_ev_meas hΦ_int
      hΦ'_meas h_bound (integrable_const K) h_diff
    have h_fp : ∫ ω, Φ' v ω ∂P = 0 := by
      have hψ3 := ψBranch_contDiff hF hvMax0 hvMax_lt hF0 sgn hv0.le hvvM.le
      have hψC := ψBranch_hasCompactSupport hFC sgn hv0.le
      exact jointLaw_two_dist_fp B hBbm t ht hv0 hψ3 hψC
    rw [h_fp] at h_param
    exact h_param.2
  have hG_const : ∀ v₁ ∈ Ioo 0 v₀, G v₀ = G v₁ := by
    intro v₁ hv₁
    have hcont : ContinuousOn G (Icc v₁ v₀) := fun v hv =>
      (h_deriv_zero v₁ hv₁ v hv).continuousAt.continuousWithinAt
    have hderiv : ∀ v ∈ Ico v₁ v₀, HasDerivWithinAt G 0 (Ici v) v := fun v hv =>
      (h_deriv_zero v₁ hv₁ v ⟨hv.1, hv.2.le⟩).hasDerivWithinAt
    exact constant_of_has_deriv_right_zero hcont hderiv v₀ (right_mem_Icc.mpr hv₁.2.le)
  have hG_tendsto : Tendsto G (nhdsWithin 0 (Ioi 0)) (nhds (G 0)) := by
    have hG_ev : Tendsto (fun v => ∫ ω, Φ v ω ∂P) (nhdsWithin 0 (Ioi 0)) (nhds (∫ ω, Φ 0 ω ∂P)) := by
      refine tendsto_integral_filter_of_dominated_convergence
        (fun _ => 2 * (Real.cosh R + vMax * Real.exp R) * CF) ?_ ?_ (integrable_const _) ?_
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < vMax by dsimp [vMax]; linarith)] with v hv
        exact hΦ_meas v ⟨hv.1.le, hv.2.le⟩
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < vMax by dsimp [vMax]; linarith)] with v hv
        exact (hΦ_bdd v ⟨hv.1.le, hv.2.le⟩).mono fun ω hω => by
          simpa [Real.norm_eq_abs] using hω
      · filter_upwards [hXpos] with ω hω
        set y := B t ω
        set x := expInt B 2 0 t ω
        have hexp_t : Tendsto (fun v : ℝ => Real.exp (-v / x)) (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
          have h0 : Tendsto (fun v : ℝ => -v / x) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
            have hc : Continuous (fun v : ℝ => -v / x) := by fun_prop
            have ht0 : Tendsto (fun v : ℝ => -v / x) (𝓝 (0 : ℝ)) (𝓝 0) := by
              have h := hc.tendsto (0 : ℝ)
              simpa only [neg_zero, zero_div] using h
            exact ht0.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
          simpa [Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp h0
        have hh_t : Tendsto (fun v : ℝ => hBranch sgn F v y)
            (nhdsWithin 0 (Ioi 0)) (nhds (hBranch sgn F 0 y)) := by
          have hyCrit_0 : ContinuousWithinAt yCrit (Ici 0) 0 := by
            have h12 : (1 + 2 * (0 : ℝ)) ≠ 0 := by norm_num
            show ContinuousWithinAt (fun u : ℝ => (1 / 2 : ℝ) * Real.log (1 + 2 * u)) (Ici 0) 0
            exact (continuousAt_const.mul (ContinuousAt.log (f := fun u : ℝ => 1 + 2 * u)
              (by fun_prop) h12)).continuousWithinAt
          have hyCrit_nhds : Tendsto yCrit (nhdsWithin 0 (Ioi 0)) (nhds (yCrit 0)) :=
            hyCrit_0.tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
          rcases lt_trichotomy (yCrit 0) y with hy | hy | hy
          · have h_ev : (fun v => hBranch sgn F v y) =ᶠ[nhdsWithin 0 (Ioi 0)]
                (if sgn then fun v => 2 * (Real.sinh y - v * Real.exp (-y)) * F (charA v y) else fun _ => 0) := by
              filter_upwards [hyCrit_nhds.eventually (isOpen_Iio.mem_nhds hy)] with v hv
              cases sgn <;> simp [hBranch, hv, not_lt.mpr hv.le]
            refine Tendsto.congr' h_ev.symm ?_
            cases sgn
            · simp [hBranch, not_lt.mpr hy.le]
            · simp only [↓reduceIte, hBranch, hy]
              have hc : Continuous (fun v : ℝ => 2 * (Real.sinh y - v * Real.exp (-y)) * F (charA v y)) := by
                have hFcont := hF.continuous
                unfold charA; fun_prop
              exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
          · have hcrit0 : charA 0 y < a₀ := by
              rw [← hy, charA_yCrit le_rfl]
              exact lt_of_le_of_lt (Real.sqrt_le_sqrt (by linarith)) ha₀
            have hA_cont : Continuous (fun v : ℝ => charA v y) := by unfold charA; fun_prop
            have h_ev : (fun v => hBranch sgn F v y) =ᶠ[nhdsWithin 0 (Ioi 0)] fun _ => 0 := by
              have hnhds : {v : ℝ | charA v y < a₀} ∈ 𝓝 (0 : ℝ) :=
                hA_cont.continuousAt.preimage_mem_nhds (Iio_mem_nhds hcrit0)
              filter_upwards [nhdsWithin_le_nhds hnhds] with v hv
              simp [hBranch, hF0 _ hv.le]
            have h0 : hBranch sgn F 0 y = 0 := by simp [hBranch, hF0 _ hcrit0.le]
            rw [h0]
            exact tendsto_const_nhds.congr' h_ev.symm
          · have h_ev : (fun v => hBranch sgn F v y) =ᶠ[nhdsWithin 0 (Ioi 0)]
                (if sgn then fun _ => 0 else fun v => 2 * (Real.sinh y - v * Real.exp (-y)) * F (charA v y)) := by
              filter_upwards [hyCrit_nhds.eventually (isOpen_Ioi.mem_nhds hy)] with v hv
              cases sgn <;> simp [hBranch, hv, not_lt.mpr hv.le]
            refine Tendsto.congr' h_ev.symm ?_
            cases sgn
            · simp only [Bool.false_eq_true, ↓reduceIte, hBranch, hy]
              have hc : Continuous (fun v : ℝ => 2 * (Real.sinh y - v * Real.exp (-y)) * F (charA v y)) := by
                have hFcont := hF.continuous
                unfold charA; fun_prop
              exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
            · simp [hBranch, not_lt.mpr hy.le]
        have hmul := hh_t.mul hexp_t
        simpa [Φ, mul_one] using hmul
    exact hG_ev
  have hG_eq : G v₀ = G 0 := by
    have h_const : (fun _ : ℝ => G v₀) =ᶠ[nhdsWithin 0 (Ioi 0)] G := by
      filter_upwards [Ioo_mem_nhdsGT hv₀] with v₁ hv₁
      exact hG_const v₁ hv₁
    exact tendsto_nhds_unique (tendsto_const_nhds.congr' h_const) hG_tendsto
  have hG0 : G 0 = ∫ ω, hBranch sgn F 0 (B t ω) ∂P := by
    refine integral_congr_ae (hXpos.mono fun ω _ => ?_)
    simp [Φ]
  exact hG_eq.trans hG0

end TransportEquation

section LaplaceInversion

private lemma gaussianPDFReal_neg_eq (v : ℝ≥0) (y : ℝ) :
    gaussianPDFReal 0 v (-y) = gaussianPDFReal 0 v y := by
  simp [gaussianPDFReal_def]

private lemma continuous_arcosh_charA {v : ℝ} (hv : 0 ≤ v) :
    Continuous (fun y => Real.arcosh (charA v y)) := by
  have h1 : Continuous (charA v) := by unfold charA; fun_prop
  refine Real.continuousOn_arcosh.comp_continuous h1 fun y => ?_
  have h12v : (1 : ℝ) ≤ 1 + 2 * v := by linarith
  exact (Real.sqrt_one ▸ Real.sqrt_le_sqrt h12v).trans (charA_ge_sqrt hv y)

private lemma branch_eval_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W)
    (t : ℝ≥0) (ht : 0 < t) {v₀ a₀ : ℝ} (hv₀ : 0 < v₀) (ha₀ : Real.sqrt (1 + 2 * v₀) < a₀)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F) (_hFC : HasCompactSupport F)
    (hF0 : ∀ a ≤ a₀, F a = 0) (sgn : Bool) :
    ∫ ω, hBranch sgn F 0 (W t ω) ∂P =
      ∫ y in (if sgn then Ioi (yCrit v₀) else Iio (yCrit v₀)),
        hBranch sgn F v₀ y * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)) := by
  have hFcont : Continuous F := hF.continuous
  have h0cont : Continuous (hBranch sgn F 0) :=
    hBranch_continuous hF hv₀.le ha₀ hF0 sgn le_rfl hv₀.le
  have hlaw : HasLaw (W t) (gaussianReal 0 t) P := hW.hasLaw_eval t
  have hmap : ∫ ω, hBranch sgn F 0 (W t ω) ∂P = ∫ y, hBranch sgn F 0 y ∂(gaussianReal 0 t) := by
    rw [← hlaw.map_eq, integral_map hlaw.aemeasurable h0cont.aestronglyMeasurable]
  rw [hmap, integral_gaussianReal_eq_integral_smul ht.ne']
  simp_rw [smul_eq_mul]
  have hyCrit0 : yCrit 0 = 0 := by simp [yCrit]
  have h1le_sq : (1 : ℝ) ≤ Real.sqrt (1 + 2 * v₀) :=
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (1 + 2 * v₀) := Real.sqrt_le_sqrt (by linarith)
  have h1le_a0 : 1 < a₀ := lt_of_le_of_lt h1le_sq ha₀
  let g : ℝ → ℝ := fun a => 2 * F a * gaussianPDFReal 0 t (Real.arcosh a)
  have hcosh_eq : charA 0 = Real.cosh := by funext y; simp [charA]
  have h_cosh_Ioi : Real.cosh '' Ioi (0 : ℝ) = Ioi (1 : ℝ) := by
    simpa [hcosh_eq, hyCrit0] using charA_image_Ioi_yCrit (v := 0) le_rfl
  have h_cosh_Iio : Real.cosh '' Iio (0 : ℝ) = Ioi (1 : ℝ) := by
    simpa [hcosh_eq, hyCrit0] using charA_image_Iio_yCrit (v := 0) le_rfl
  have hstep1 : ∫ a in Ioi (1 : ℝ), g a =
      ∫ a in Ioi (Real.sqrt (1 + 2 * v₀)), g a := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    by_cases ha1 : a ≤ 1
    · have ha_not1 : a ∉ Ioi (1 : ℝ) := not_lt.mpr ha1
      have ha_not2 : a ∉ Ioi (Real.sqrt (1 + 2 * v₀)) := not_lt.mpr (ha1.trans h1le_sq)
      simp [ha_not1, ha_not2]
    · by_cases ha_sq : a ≤ Real.sqrt (1 + 2 * v₀)
      · have hle : a ≤ a₀ := ha_sq.trans ha₀.le
        simp [g, hF0 a hle, not_lt.mpr ha_sq]
      · have h1 : a ∈ Ioi (1 : ℝ) := lt_of_not_ge ha1
        have h2 : a ∈ Ioi (Real.sqrt (1 + 2 * v₀)) := lt_of_not_ge ha_sq
        simp [h1, h2]
  cases sgn
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hsplit : ∫ y : ℝ, gaussianPDFReal 0 t y * hBranch false F 0 y =
        ∫ y in Iio (0 : ℝ), gaussianPDFReal 0 t y * (2 * Real.sinh y * F (Real.cosh y)) := by
      rw [← integral_indicator measurableSet_Iio]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      by_cases hy : y < 0
      · simp [hy, hBranch, hyCrit0, charA, mul_comm]
      · simp [hy, hBranch, hyCrit0]
    rw [hsplit]
    have hcov1 : ∫ a in Ioi (1 : ℝ), g a =
        ∫ y in Iio (0 : ℝ), |Real.sinh y| * g (Real.cosh y) := by
      rw [← h_cosh_Iio]
      refine integral_image_eq_integral_abs_deriv_smul measurableSet_Iio ?_ ?_ g
      · intro y _; exact (Real.hasDerivAt_cosh y).hasDerivWithinAt
      · have hinj : InjOn (charA 0) (Iio 0) :=
          (charA_strictAntiOn (v := 0) le_rfl).injOn.mono (by simp [hyCrit0])
        simpa [hcosh_eq] using hinj
    have hcov2 : ∫ a in Ioi (Real.sqrt (1 + 2 * v₀)), g a =
        ∫ y in Iio (yCrit v₀), |Real.sinh y - v₀ * Real.exp (-y)| * g (charA v₀ y) := by
      rw [← charA_image_Iio_yCrit hv₀.le]
      refine integral_image_eq_integral_abs_deriv_smul measurableSet_Iio ?_ ?_ g
      · intro y _; exact (hasDerivAt_charA_y v₀ y).hasDerivWithinAt
      · exact (charA_strictAntiOn hv₀.le).injOn.mono Iio_subset_Iic_self
    have hlhs_eq : ∫ y in Iio (0 : ℝ), gaussianPDFReal 0 t y * (2 * Real.sinh y * F (Real.cosh y)) =
        - ∫ y in Iio (0 : ℝ), |Real.sinh y| * g (Real.cosh y) := by
      rw [← integral_neg]
      refine setIntegral_congr_fun measurableSet_Iio fun y hy => ?_
      have hsinh_neg : Real.sinh y < 0 := by
        simpa [hyCrit0] using (charA_deriv_neg_iff (v := 0) le_rfl y).mpr (by simpa [hyCrit0] using mem_Iio.mp hy)
      have harcosh : Real.arcosh (Real.cosh y) = -y := by
        rw [← Real.cosh_neg y]
        exact Real.arcosh_cosh (neg_nonneg.mpr (mem_Iio.mp hy).le)
      rw [abs_of_neg hsinh_neg]
      simp only [g, harcosh, gaussianPDFReal_neg_eq]
      ring
    have hrhs_eq : ∫ y in Iio (yCrit v₀), hBranch false F v₀ y * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)) =
        - ∫ y in Iio (yCrit v₀), |Real.sinh y - v₀ * Real.exp (-y)| * g (charA v₀ y) := by
      rw [← integral_neg]
      refine setIntegral_congr_fun measurableSet_Iio fun y hy => ?_
      have hd_neg : Real.sinh y - v₀ * Real.exp (-y) < 0 :=
        (charA_deriv_neg_iff hv₀.le y).mpr hy
      rw [abs_of_neg hd_neg]
      simp only [hBranch, mem_Iio.mp hy, Bool.false_eq_true, ↓reduceIte, g]
      ring
    rw [hlhs_eq, hrhs_eq, ← hcov1, ← hcov2, hstep1]
  · simp only [↓reduceIte]
    have hsplit : ∫ y : ℝ, gaussianPDFReal 0 t y * hBranch true F 0 y =
        ∫ y in Ioi (0 : ℝ), gaussianPDFReal 0 t y * (2 * Real.sinh y * F (Real.cosh y)) := by
      rw [← integral_indicator measurableSet_Ioi]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      by_cases hy : 0 < y
      · simp [hy, hBranch, hyCrit0, charA]
      · simp [hy, hBranch, hyCrit0]
    rw [hsplit]
    have hcov1 : ∫ a in Ioi (1 : ℝ), g a =
        ∫ y in Ioi (0 : ℝ), |Real.sinh y| * g (Real.cosh y) := by
      rw [← h_cosh_Ioi]
      refine integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi ?_ ?_ g
      · intro y _; exact (Real.hasDerivAt_cosh y).hasDerivWithinAt
      · have hinj : InjOn (charA 0) (Ioi 0) :=
          (charA_strictMonoOn (v := 0) le_rfl).injOn.mono (by simp [hyCrit0])
        simpa [hcosh_eq] using hinj
    have hcov2 : ∫ a in Ioi (Real.sqrt (1 + 2 * v₀)), g a =
        ∫ y in Ioi (yCrit v₀), |Real.sinh y - v₀ * Real.exp (-y)| * g (charA v₀ y) := by
      rw [← charA_image_Ioi_yCrit hv₀.le]
      refine integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi ?_ ?_ g
      · intro y _; exact (hasDerivAt_charA_y v₀ y).hasDerivWithinAt
      · exact (charA_strictMonoOn hv₀.le).injOn.mono Ioi_subset_Ici_self
    have hlhs_eq : ∫ y in Ioi (0 : ℝ), gaussianPDFReal 0 t y * (2 * Real.sinh y * F (Real.cosh y)) =
        ∫ y in Ioi (0 : ℝ), |Real.sinh y| * g (Real.cosh y) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
      have hsinh_pos : 0 < Real.sinh y := by
        simpa [hyCrit0] using (charA_deriv_pos_iff (v := 0) le_rfl y).mpr (by simpa [hyCrit0] using mem_Ioi.mp hy)
      have harcosh : Real.arcosh (Real.cosh y) = y :=
        Real.arcosh_cosh (mem_Ioi.mp hy).le
      rw [abs_of_pos hsinh_pos]
      simp only [g, harcosh]
      ring
    have hrhs_eq : ∫ y in Ioi (yCrit v₀), hBranch true F v₀ y * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)) =
        ∫ y in Ioi (yCrit v₀), |Real.sinh y - v₀ * Real.exp (-y)| * g (charA v₀ y) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
      have hd_pos : 0 < Real.sinh y - v₀ * Real.exp (-y) :=
        (charA_deriv_pos_iff hv₀.le y).mpr hy
      rw [abs_of_pos hd_pos]
      simp only [hBranch, mem_Ioi.mp hy, ↓reduceIte, g]
      ring
    rw [hlhs_eq, hrhs_eq, ← hcov1, ← hcov2, hstep1]

private lemma jointLaw_two_laplace_inv_branch {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W)
    (t : ℝ≥0) (ht : 0 < t) {v₀ : ℝ} (hv₀ : 0 < v₀)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) (hfC : HasCompactSupport f)
    (sgn : Bool) (hc_vanish : ∃ c, (if sgn then yCrit v₀ < c ∧ ∀ y ≤ c, f y = 0
                                      else c < yCrit v₀ ∧ ∀ y ≥ c, f y = 0)) :
    ∫ ω, f (W t ω) * Real.exp (-v₀ / expInt W 2 0 t ω) ∂P =
      ∫ y : ℝ, f y * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)) := by
  obtain ⟨c, hc⟩ := hc_vanish
  let a₀ : ℝ := charA v₀ c
  have ha₀ : Real.sqrt (1 + 2 * v₀) < a₀ := by
    rw [← charA_yCrit hv₀.le]
    cases sgn
    · simp only [Bool.false_eq_true, ↓reduceIte] at hc
      exact charA_strictAntiOn hv₀.le hc.1.le le_rfl hc.1
    · simp only [↓reduceIte] at hc
      exact charA_strictMonoOn hv₀.le le_rfl hc.1.le hc.1
  let F : ℝ → ℝ := fun a =>
    if a ≤ Real.sqrt (1 + 2 * v₀) then 0
    else f (if sgn then yPlus v₀ a else yMinus v₀ a) /
      ((if sgn then 2 else -2) * Real.sqrt (a ^ 2 - (1 + 2 * v₀)))
  have hF0 : ∀ a ≤ a₀, F a = 0 := by
    intro a ha
    by_cases hsq : a ≤ Real.sqrt (1 + 2 * v₀)
    · simp [F, hsq]
    · have hgt : Real.sqrt (1 + 2 * v₀) < a := not_le.mp hsq
      simp only [F, hsq, ↓reduceIte]
      cases sgn
      · simp only [Bool.false_eq_true, ↓reduceIte] at hc ⊢
        obtain ⟨hyM, hcharM⟩ := charA_yMinus hv₀.le hgt
        have hcy : c ≤ yMinus v₀ a := by
          by_contra hlt
          push Not at hlt
          have := charA_strictAntiOn hv₀.le hyM.le hc.1.le hlt
          linarith [hcharM, ha]
        rw [hc.2 _ hcy, zero_div]
      · simp only [↓reduceIte] at hc ⊢
        obtain ⟨hyP, hcharP⟩ := charA_yPlus hv₀.le hgt
        have hyc : yPlus v₀ a ≤ c := by
          by_contra hlt
          push Not at hlt
          have := charA_strictMonoOn hv₀.le hc.1.le hyP.le hlt
          linarith [hcharP, ha]
        rw [hc.2 _ hyc, zero_div]
  have hF_smooth : ContDiff ℝ 3 F := by
    rw [contDiff_iff_contDiffAt]
    intro a
    by_cases ha_lt : a < a₀
    · have h_ev : F =ᶠ[𝓝 a] fun _ => (0 : ℝ) := by
        filter_upwards [eventually_lt_nhds ha_lt] with a' ha'
        exact hF0 a' ha'.le
      exact contDiffAt_const.congr_of_eventuallyEq h_ev
    · have ha_gt : Real.sqrt (1 + 2 * v₀) < a := lt_of_lt_of_le ha₀ (not_lt.mp ha_lt)
      have h_ev : F =ᶠ[𝓝 a] fun a' =>
          f (if sgn then yPlus v₀ a' else yMinus v₀ a') /
            ((if sgn then 2 else -2) * Real.sqrt (a' ^ 2 - (1 + 2 * v₀))) := by
        filter_upwards [eventually_gt_nhds ha_gt] with a' ha'
        simp [F, not_le.mpr ha']
      have hsub : 0 < a ^ 2 - (1 + 2 * v₀) := by
        have := Real.lt_sq_of_sqrt_lt ha_gt; linarith
      have hs_pos : 0 < Real.sqrt (a ^ 2 - (1 + 2 * v₀)) := Real.sqrt_pos.mpr hsub
      have hden_ne : (if sgn then (2 : ℝ) else -2) * Real.sqrt (a ^ 2 - (1 + 2 * v₀)) ≠ 0 := by
        cases sgn <;> simp <;> positivity
      have hden_smooth : ContDiffAt ℝ 3
          (fun a' : ℝ => (if sgn then (2 : ℝ) else -2) * Real.sqrt (a' ^ 2 - (1 + 2 * v₀))) a := by
        have h1 : ContDiffAt ℝ 3 (fun x : ℝ => x ^ 2 - (1 + 2 * v₀)) a := by fun_prop
        exact contDiffAt_const.mul (h1.sqrt hsub.ne')
      have hy_smooth : ContDiffAt ℝ 3 (if sgn then yPlus v₀ else yMinus v₀) a := by
        cases sgn
        · simpa using (yMinus_contDiffOn hv₀.le (n := 3)).contDiffAt (isOpen_Ioi.mem_nhds ha_gt)
        · simpa using (yPlus_contDiffOn hv₀.le (n := 3)).contDiffAt (isOpen_Ioi.mem_nhds ha_gt)
      have hnum_smooth : ContDiffAt ℝ 3 (fun a' => f (if sgn then yPlus v₀ a' else yMinus v₀ a')) a := by
        cases sgn
        · exact (hf.contDiffAt).comp a hy_smooth
        · exact (hf.contDiffAt).comp a hy_smooth
      exact (hnum_smooth.div hden_smooth hden_ne).congr_of_eventuallyEq h_ev
  have hF_cs : HasCompactSupport F := by
    obtain ⟨M0, hM0⟩ := hfC.isCompact.isBounded.subset_closedBall (0 : ℝ)
    let M : ℝ := max M0 1 + 1
    have hM_pos : 0 < M := by positivity
    have hf_van : ∀ y, M ≤ |y| → f y = 0 := by
      intro y hy
      by_contra hne
      have := hM0 (subset_tsupport f hne)
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
      linarith [le_max_left M0 1, le_max_right M0 1]
    let A : ℝ := max (Real.sqrt (1 + 2 * v₀) + 1) ((1 + 2 * v₀) * Real.exp M + 1)
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := 0) (b := A)) ?_
    intro a ha
    by_contra hnot
    simp only [mem_Icc, not_and_or, not_le] at hnot
    rcases hnot with ha_neg | ha_big
    · have : a ≤ a₀ := ha_neg.le.trans (le_trans (Real.sqrt_nonneg _) ha₀.le)
      exact ha (hF0 a this)
    · have ha_gt : Real.sqrt (1 + 2 * v₀) < a :=
        lt_of_le_of_lt (by linarith [le_max_left (Real.sqrt (1 + 2 * v₀) + 1) ((1 + 2 * v₀) * Real.exp M + 1)]) ha_big
      have ha_pos : 0 < a := (Real.sqrt_nonneg _).trans_lt ha_gt
      have ha_exp : (1 + 2 * v₀) * Real.exp M < a :=
        lt_of_le_of_lt (by linarith [le_max_right (Real.sqrt (1 + 2 * v₀) + 1) ((1 + 2 * v₀) * Real.exp M + 1)]) ha_big
      have h12v : 1 ≤ 1 + 2 * v₀ := by linarith
      have ha_exp1 : Real.exp M < a := lt_of_le_of_lt (le_mul_of_one_le_left (Real.exp_pos _).le h12v) ha_exp
      simp only [Function.mem_support, ne_eq, F, not_le.mpr ha_gt, ↓reduceIte] at ha
      cases sgn
      · simp only [Bool.false_eq_true, ↓reduceIte] at ha
        set s := Real.sqrt (a ^ 2 - (1 + 2 * v₀))
        have hsub : 0 < a ^ 2 - (1 + 2 * v₀) := by have := Real.lt_sq_of_sqrt_lt ha_gt; linarith
        have hs_pos : 0 < s := Real.sqrt_pos.mpr hsub
        have hs_lt : s < a := sqrt_sq_sub_lt_self hv₀.le ha_gt
        have hprod : (a + s) * (a - s) = 1 + 2 * v₀ := by
          have : s ^ 2 = a ^ 2 - (1 + 2 * v₀) := Real.sq_sqrt hsub.le
          nlinarith
        have harg_lt : a - s < Real.exp (-M) := by
          have h1 : a - s = (1 + 2 * v₀) / (a + s) := by
            field_simp [(by linarith : 0 < a + s).ne']; linarith [hprod]
          rw [h1, Real.exp_neg, ← one_div]
          rw [div_lt_div_iff₀ (by positivity) (Real.exp_pos _)]
          nlinarith [ha_exp, hs_pos]
        have hlog_lt : yMinus v₀ a < -M := by
          unfold yMinus
          rw [← Real.log_exp (-M)]
          exact Real.log_lt_log (sub_pos.mpr hs_lt) harg_lt
        have hf0 : f (yMinus v₀ a) = 0 := hf_van _ (by linarith [neg_le_abs (yMinus v₀ a)])
        simp [hf0] at ha
      · simp only [↓reduceIte] at ha
        have hs_nn : 0 ≤ Real.sqrt (a ^ 2 - (1 + 2 * v₀)) := Real.sqrt_nonneg _
        have harg_gt : Real.exp M < a + Real.sqrt (a ^ 2 - (1 + 2 * v₀)) := by linarith
        have hlog_gt : M < yPlus v₀ a := by
          unfold yPlus
          rw [← Real.log_exp M]
          exact Real.log_lt_log (Real.exp_pos _) harg_gt
        have hf0 : f (yPlus v₀ a) = 0 := hf_van _ (le_trans hlog_gt.le (le_abs_self _))
        simp [hf0] at ha
  have hh_eq : ∀ y, hBranch sgn F v₀ y = f y := by
    intro y
    cases sgn
    · simp only [Bool.false_eq_true, ↓reduceIte] at hc ⊢
      by_cases hy : y < yCrit v₀
      · have hgt : Real.sqrt (1 + 2 * v₀) < charA v₀ y := by
          rw [← charA_yCrit hv₀.le]
          exact charA_strictAntiOn hv₀.le hy.le le_rfl hy
        have hnot : ¬ (charA v₀ y ≤ Real.sqrt (1 + 2 * v₀)) := not_le.mpr hgt
        have hd_neg : Real.sinh y - v₀ * Real.exp (-y) < 0 :=
          (charA_deriv_neg_iff hv₀.le y).mpr hy
        have hsqrt : Real.sqrt (charA v₀ y ^ 2 - (1 + 2 * v₀)) = -(Real.sinh y - v₀ * Real.exp (-y)) := by
          rw [charA_sq_sub, Real.sqrt_sq_eq_abs, abs_of_neg hd_neg]
        simp only [hBranch, hy, Bool.false_eq_true, ↓reduceIte, F, hnot, yMinus_charA hv₀.le hy, hsqrt]
        have hne : Real.sinh y - v₀ * Real.exp (-y) ≠ 0 := hd_neg.ne
        field_simp [hne]
      · have hge : c ≤ y := hc.1.le.trans (not_lt.mp hy)
        simp [hBranch, hy, hc.2 y hge]
    · simp only [↓reduceIte] at hc ⊢
      by_cases hy : yCrit v₀ < y
      · have hgt : Real.sqrt (1 + 2 * v₀) < charA v₀ y := by
          rw [← charA_yCrit hv₀.le]
          exact charA_strictMonoOn hv₀.le le_rfl hy.le hy
        have hnot : ¬ (charA v₀ y ≤ Real.sqrt (1 + 2 * v₀)) := not_le.mpr hgt
        have hd_pos : 0 < Real.sinh y - v₀ * Real.exp (-y) :=
          (charA_deriv_pos_iff hv₀.le y).mpr hy
        have hsqrt : Real.sqrt (charA v₀ y ^ 2 - (1 + 2 * v₀)) = Real.sinh y - v₀ * Real.exp (-y) := by
          rw [charA_sq_sub, Real.sqrt_sq hd_pos.le]
        simp only [hBranch, hy, ↓reduceIte, F, hnot, yPlus_charA hv₀.le hy, hsqrt]
        have hne : Real.sinh y - v₀ * Real.exp (-y) ≠ 0 := hd_pos.ne'
        field_simp [hne]
      · have hle : y ≤ c := (not_lt.mp hy).trans hc.1.le
        simp [hBranch, hy, hc.2 y hle]
  have htr := transport_branch_eq W hW t ht hv₀ ha₀ hF_smooth hF_cs hF0 sgn
  have hev := branch_eval_zero W hW t ht hv₀ ha₀ hF_smooth hF_cs hF0 sgn
  simp_rw [hh_eq] at htr hev
  rw [htr, hev]
  cases sgn <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [← integral_indicator measurableSet_Iio]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    by_cases hy : y < yCrit v₀
    · simp [hy]
    · simp only [Bool.false_eq_true, ↓reduceIte] at hc
      have hge : c ≤ y := hc.1.le.trans (not_lt.mp hy)
      simp [hy, hc.2 y hge]
  · rw [← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    by_cases hy : yCrit v₀ < y
    · simp [hy]
    · simp only [↓reduceIte] at hc
      have hle : y ≤ c := (not_lt.mp hy).trans hc.1.le
      simp [hy, hc.2 y hle]

/-- `1/x`-Laplace inversion on `(expInt W 2 0 t, W t)` for `f ∈ C_c^3(ℝ)`. -/
theorem jointLaw_two_laplace_inv_contDiff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W)
    (t : ℝ≥0) (ht : 0 < t) {v₀ : ℝ} (hv₀ : 0 < v₀)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) (hfC : HasCompactSupport f) :
    ∫ ω, f (W t ω) * Real.exp (-v₀ / expInt W 2 0 t ω) ∂P =
      ∫ y : ℝ, f y * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)) := by
  let B : ℝ≥0 → Ω → ℝ := hW.toIsPreBrownianReal.mk W
  have hBmeas : ∀ s, Measurable (B s) := hW.toIsPreBrownianReal.measurable_mk
  have hBcont : ∀ ω, Continuous (B · ω) := hW.toIsPreBrownianReal.continuous_mk
  have hBpre : IsPreBrownianReal B P :=
    hW.toIsPreBrownianReal.isBrownianReal_mk.toIsPreBrownianReal
  have hBbm : IsBM P B := ⟨hBpre, Eventually.of_forall hBcont⟩
  have hBW : ∀ᵐ ω ∂P, ∀ s, B s ω = W s ω := hW.mk_ae_forall_eq
  have hBW_int : ∫ ω, f (W t ω) * Real.exp (-v₀ / expInt W 2 0 t ω) ∂P =
      ∫ ω, f (B t ω) * Real.exp (-v₀ / expInt B 2 0 t ω) ∂P := by
    refine integral_congr_ae (hBW.mono fun ω hω => ?_)
    dsimp only
    have hX : expInt W 2 0 t ω = expInt B 2 0 t ω := by
      simp only [expInt]; exact intervalIntegral.integral_congr fun s _ => by rw [hω s.toNNReal]
    rw [hX, ← hω t]
  rw [hBW_int]
  have hXpos := expInt_two_pos_ae B hBbm t ht
  have hXmeas : Measurable (expInt B 2 0 t) := measurable_expInt_bm hBmeas hBcont 2 t
  have hfcont : Continuous f := hf.continuous
  obtain ⟨Cf, _, hCf0, _, _, hf_bdd, _, _, _⟩ := contDiff_three_compactSupport_bounds hf hfC
  let χp : ℕ → ℝ → ℝ := fun n y =>
    smoothStepRight (yCrit v₀ + 1 / (2 * ((n : ℝ) + 1))) (yCrit v₀ + 1 / ((n : ℝ) + 1)) y
  let χm : ℕ → ℝ → ℝ := fun n y =>
    smoothStepLeft (yCrit v₀ - 1 / ((n : ℝ) + 1)) (yCrit v₀ - 1 / (2 * ((n : ℝ) + 1))) y
  have hχ_eq : ∀ n : ℕ,
      ∫ ω, (f (B t ω) * χp n (B t ω) + f (B t ω) * χm n (B t ω)) *
          Real.exp (-v₀ / expInt B 2 0 t ω) ∂P =
        ∫ y : ℝ, (f y * χp n y + f y * χm n y) *
          gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)) := by
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hp_cd : ContDiff ℝ 3 (fun y => f y * χp n y) :=
      hf.mul (smoothStepRight_contDiff _ _)
    have hm_cd : ContDiff ℝ 3 (fun y => f y * χm n y) :=
      hf.mul (smoothStepLeft_contDiff _ _)
    have hp_cs : HasCompactSupport (fun y => f y * χp n y) := hfC.mul_right
    have hm_cs : HasCompactSupport (fun y => f y * χm n y) := hfC.mul_right
    have hp_van : ∃ c, yCrit v₀ < c ∧ ∀ y ≤ c, f y * χp n y = 0 := by
      refine ⟨yCrit v₀ + 1 / (2 * ((n : ℝ) + 1)), by linarith [show (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) by positivity], fun y hy => ?_⟩
      have hlt : yCrit v₀ + 1 / (2 * ((n : ℝ) + 1)) < yCrit v₀ + 1 / ((n : ℝ) + 1) := by
        have : 1 / (2 * ((n : ℝ) + 1)) < 1 / ((n : ℝ) + 1) :=
          one_div_lt_one_div_of_lt (by positivity) (by linarith)
        linarith
      dsimp only [χp]
      rw [smoothStepRight_zero_of_le hlt hy, mul_zero]
    have hm_van : ∃ c, c < yCrit v₀ ∧ ∀ y ≥ c, f y * χm n y = 0 := by
      refine ⟨yCrit v₀ - 1 / (2 * ((n : ℝ) + 1)), by linarith [show (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) by positivity],
        fun y hy => ?_⟩
      have hlt : yCrit v₀ - 1 / ((n : ℝ) + 1) < yCrit v₀ - 1 / (2 * ((n : ℝ) + 1)) := by
        have : 1 / (2 * ((n : ℝ) + 1)) < 1 / ((n : ℝ) + 1) :=
          one_div_lt_one_div_of_lt (by positivity) (by linarith)
        linarith
      dsimp only [χm]
      rw [smoothStepLeft_zero_of_le hlt hy, mul_zero]
    have hp_id := jointLaw_two_laplace_inv_branch B hBbm t ht hv₀ hp_cd hp_cs true hp_van
    have hm_id := jointLaw_two_laplace_inv_branch B hBbm t ht hv₀ hm_cd hm_cs false hm_van
    have hp_intL : Integrable (fun ω => (f (B t ω) * χp n (B t ω)) * Real.exp (-v₀ / expInt B 2 0 t ω)) P := by
      refine (integrable_const Cf).mono' ?_ ?_
      · have hc : Continuous (fun y => f y * χp n y) := hp_cd.continuous
        exact ((hc.measurable.comp (hBmeas t)).mul
          (Real.continuous_exp.measurable.comp (measurable_const.div hXmeas))).aestronglyMeasurable
      · filter_upwards [hXpos] with ω hω
        have hle := (smoothStepRight_mem_Icc (yCrit v₀ + 1 / (2 * ((n : ℝ) + 1)))
          (yCrit v₀ + 1 / ((n : ℝ) + 1)) (B t ω))
        have hexp : Real.exp (-v₀ / expInt B 2 0 t ω) ≤ 1 :=
          Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hv₀.le) hω.le)
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hle.1]
        calc |f (B t ω)| * χp n (B t ω) * Real.exp (-v₀ / expInt B 2 0 t ω)
            ≤ Cf * 1 * 1 :=
              mul_le_mul (mul_le_mul (hf_bdd _) hle.2 hle.1 hCf0) hexp (Real.exp_pos _).le (by positivity)
          _ = Cf := by ring
    have hm_intL : Integrable (fun ω => (f (B t ω) * χm n (B t ω)) * Real.exp (-v₀ / expInt B 2 0 t ω)) P := by
      refine (integrable_const Cf).mono' ?_ ?_
      · have hc : Continuous (fun y => f y * χm n y) := hm_cd.continuous
        exact ((hc.measurable.comp (hBmeas t)).mul
          (Real.continuous_exp.measurable.comp (measurable_const.div hXmeas))).aestronglyMeasurable
      · filter_upwards [hXpos] with ω hω
        have hle := (smoothStepLeft_mem_Icc (yCrit v₀ - 1 / ((n : ℝ) + 1))
          (yCrit v₀ - 1 / (2 * ((n : ℝ) + 1))) (B t ω))
        have hexp : Real.exp (-v₀ / expInt B 2 0 t ω) ≤ 1 :=
          Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hv₀.le) hω.le)
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hle.1]
        calc |f (B t ω)| * χm n (B t ω) * Real.exp (-v₀ / expInt B 2 0 t ω)
            ≤ Cf * 1 * 1 :=
              mul_le_mul (mul_le_mul (hf_bdd _) hle.2 hle.1 hCf0) hexp (Real.exp_pos _).le (by positivity)
          _ = Cf := by ring
    have hp_intR : Integrable (fun y => (f y * χp n y) * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y))) := by
      have h_cs : HasCompactSupport (fun y => (f y * χp n y) * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y))) :=
        hp_cs.mul_right
      have h_cont : Continuous (fun y => (f y * χp n y) * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y))) := by
        have hc1 := hp_cd.continuous
        have hg : Continuous (gaussianPDFReal 0 t) := by rw [gaussianPDFReal_def]; fun_prop
        have ha := continuous_arcosh_charA hv₀.le
        exact hc1.mul (hg.comp ha)
      exact h_cont.integrable_of_hasCompactSupport h_cs
    have hm_intR : Integrable (fun y => (f y * χm n y) * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y))) := by
      have h_cs : HasCompactSupport (fun y => (f y * χm n y) * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y))) :=
        hm_cs.mul_right
      have h_cont : Continuous (fun y => (f y * χm n y) * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y))) := by
        have hc1 := hm_cd.continuous
        have hg : Continuous (gaussianPDFReal 0 t) := by rw [gaussianPDFReal_def]; fun_prop
        have ha := continuous_arcosh_charA hv₀.le
        exact hc1.mul (hg.comp ha)
      exact h_cont.integrable_of_hasCompactSupport h_cs
    have hsplitL : (fun ω => (f (B t ω) * χp n (B t ω) + f (B t ω) * χm n (B t ω)) *
          Real.exp (-v₀ / expInt B 2 0 t ω)) =
        fun ω => (f (B t ω) * χp n (B t ω)) * Real.exp (-v₀ / expInt B 2 0 t ω) +
          (f (B t ω) * χm n (B t ω)) * Real.exp (-v₀ / expInt B 2 0 t ω) := by
      funext ω; ring
    have hsplitR : (fun y => (f y * χp n y + f y * χm n y) *
          gaussianPDFReal 0 t (Real.arcosh (charA v₀ y))) =
        fun y => (f y * χp n y) * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)) +
          (f y * χm n y) * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)) := by
      funext y; ring
    rw [hsplitL, hsplitR, integral_add hp_intL hm_intL, integral_add hp_intR hm_intR, hp_id, hm_id]
  have hP_crit : ∀ᵐ ω ∂P, B t ω ≠ yCrit v₀ := by
    have hlaw : HasLaw (B t) (gaussianReal 0 t) P := hBbm.hasLaw_eval t
    have hnull : P {ω | B t ω = yCrit v₀} = 0 := by
      change P (B t ⁻¹' {yCrit v₀}) = 0
      rw [← Measure.map_apply (hBmeas t) (measurableSet_singleton _), hlaw.map_eq,
        gaussianReal_of_var_ne_zero _ ht.ne', withDensity_apply _ (measurableSet_singleton _)]
      simp
    exact ae_iff.mpr (by simpa using hnull)
  have hχ_tendsto : ∀ y ≠ yCrit v₀, Tendsto (fun n => χp n y + χm n y) atTop (nhds 1) := by
    intro y hy
    rcases lt_or_gt_of_ne hy with hlt | hgt
    · have h_ev : ∀ᶠ n : ℕ in atTop, χp n y + χm n y = 1 := by
        obtain ⟨N, hN⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
        refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
        have hn1 : 1 / ((n : ℝ) + 1) < yCrit v₀ - y :=
          lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)) hN
        have hlt1 : yCrit v₀ + 1 / (2 * ((n : ℝ) + 1)) < yCrit v₀ + 1 / ((n : ℝ) + 1) := by
          have : 1 / (2 * ((n : ℝ) + 1)) < 1 / ((n : ℝ) + 1) :=
            one_div_lt_one_div_of_lt (by positivity) (by linarith)
          linarith
        have hlt2 : yCrit v₀ - 1 / ((n : ℝ) + 1) < yCrit v₀ - 1 / (2 * ((n : ℝ) + 1)) := by
          have : 1 / (2 * ((n : ℝ) + 1)) < 1 / ((n : ℝ) + 1) :=
            one_div_lt_one_div_of_lt (by positivity) (by linarith)
          linarith
        have hpos2 : (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) := by positivity
        have hp0 : χp n y = 0 := smoothStepRight_zero_of_le hlt1 (by linarith)
        have hm1 : χm n y = 1 := smoothStepLeft_one_of_le hlt2 (by linarith)
        rw [hp0, hm1, zero_add]
      exact tendsto_const_nhds.congr' (h_ev.mono fun n hn => hn.symm)
    · have h_ev : ∀ᶠ n : ℕ in atTop, χp n y + χm n y = 1 := by
        obtain ⟨N, hN⟩ := exists_nat_one_div_lt (sub_pos.mpr hgt)
        refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
        have hn1 : 1 / ((n : ℝ) + 1) < y - yCrit v₀ :=
          lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)) hN
        have hlt1 : yCrit v₀ + 1 / (2 * ((n : ℝ) + 1)) < yCrit v₀ + 1 / ((n : ℝ) + 1) := by
          have : 1 / (2 * ((n : ℝ) + 1)) < 1 / ((n : ℝ) + 1) :=
            one_div_lt_one_div_of_lt (by positivity) (by linarith)
          linarith
        have hlt2 : yCrit v₀ - 1 / ((n : ℝ) + 1) < yCrit v₀ - 1 / (2 * ((n : ℝ) + 1)) := by
          have : 1 / (2 * ((n : ℝ) + 1)) < 1 / ((n : ℝ) + 1) :=
            one_div_lt_one_div_of_lt (by positivity) (by linarith)
          linarith
        have hpos2 : (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) := by positivity
        have hp1 : χp n y = 1 := smoothStepRight_one_of_le hlt1 (by linarith)
        have hm0 : χm n y = 0 := smoothStepLeft_zero_of_le hlt2 (by linarith)
        rw [hp1, hm0, add_zero]
      exact tendsto_const_nhds.congr' (h_ev.mono fun n hn => hn.symm)
  have hχ_bdd : ∀ n y, 0 ≤ χp n y + χm n y ∧ χp n y + χm n y ≤ 2 := fun n y =>
    ⟨add_nonneg (smoothStepRight_mem_Icc _ _ _).1 (smoothStepLeft_mem_Icc _ _ _).1,
     (add_le_add (smoothStepRight_mem_Icc _ _ _).2 (smoothStepLeft_mem_Icc _ _ _).2).trans
       (by norm_num)⟩
  have hL_tendsto : Tendsto (fun n : ℕ => ∫ ω, (f (B t ω) * χp n (B t ω) + f (B t ω) * χm n (B t ω)) *
        Real.exp (-v₀ / expInt B 2 0 t ω) ∂P)
      atTop (nhds (∫ ω, f (B t ω) * Real.exp (-v₀ / expInt B 2 0 t ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => 2 * Cf) ?_ (integrable_const _) ?_ ?_
    · intro n
      have hc : Continuous (fun y => f y * χp n y + f y * χm n y) :=
        (hfcont.mul (smoothStepRight_contDiff _ _ (n := 0)).continuous).add
          (hfcont.mul (smoothStepLeft_contDiff _ _ (n := 0)).continuous)
      exact ((hc.measurable.comp (hBmeas t)).mul
        (Real.continuous_exp.measurable.comp (measurable_const.div hXmeas))).aestronglyMeasurable
    · intro n
      filter_upwards [hXpos] with ω hω
      have hexp : Real.exp (-v₀ / expInt B 2 0 t ω) ≤ 1 :=
        Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hv₀.le) hω.le)
      have hb := hχ_bdd n (B t ω)
      rw [Real.norm_eq_abs, show (f (B t ω) * χp n (B t ω) + f (B t ω) * χm n (B t ω)) *
            Real.exp (-v₀ / expInt B 2 0 t ω) =
          f (B t ω) * (χp n (B t ω) + χm n (B t ω)) * Real.exp (-v₀ / expInt B 2 0 t ω) by ring,
        abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hb.1]
      calc |f (B t ω)| * (χp n (B t ω) + χm n (B t ω)) * Real.exp (-v₀ / expInt B 2 0 t ω)
          ≤ Cf * 2 * 1 :=
            mul_le_mul (mul_le_mul (hf_bdd _) hb.2 hb.1 hCf0) hexp (Real.exp_pos _).le (by positivity)
        _ = 2 * Cf := by ring
    · filter_upwards [hP_crit] with ω hω
      have h1 := (hχ_tendsto (B t ω) hω).const_mul (f (B t ω))
      have h2 := h1.mul_const (Real.exp (-v₀ / expInt B 2 0 t ω))
      have h3 : (fun n : ℕ => (f (B t ω) * χp n (B t ω) + f (B t ω) * χm n (B t ω)) *
            Real.exp (-v₀ / expInt B 2 0 t ω)) =
          fun n : ℕ => f (B t ω) * (χp n (B t ω) + χm n (B t ω)) * Real.exp (-v₀ / expInt B 2 0 t ω) := by
        funext n; ring
      rw [h3]
      simpa [mul_one] using h2
  have hR_tendsto : Tendsto (fun n : ℕ => ∫ y : ℝ, (f y * χp n y + f y * χm n y) *
        gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)))
      atTop (nhds (∫ y : ℝ, f y * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)))) := by
    let boundR : ℝ → ℝ := fun y => 2 * |f y| * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y))
    have hbound_int : Integrable boundR := by
      have hc : Continuous boundR := by
        have hg : Continuous (gaussianPDFReal 0 t) := by rw [gaussianPDFReal_def]; fun_prop
        have ha := continuous_arcosh_charA hv₀.le
        exact (continuous_const.mul hfcont.abs).mul (hg.comp ha)
      have hcs : HasCompactSupport boundR :=
        (hfC.abs.comp_left (mul_zero _)).mul_right
      exact hc.integrable_of_hasCompactSupport hcs
    refine tendsto_integral_of_dominated_convergence boundR ?_ hbound_int ?_ ?_
    · intro n
      have hc : Continuous (fun y => (f y * χp n y + f y * χm n y) *
          gaussianPDFReal 0 t (Real.arcosh (charA v₀ y))) := by
        have hc1 : Continuous (fun y => f y * χp n y + f y * χm n y) :=
          (hfcont.mul (smoothStepRight_contDiff _ _ (n := 0)).continuous).add
            (hfcont.mul (smoothStepLeft_contDiff _ _ (n := 0)).continuous)
        have hg : Continuous (gaussianPDFReal 0 t) := by rw [gaussianPDFReal_def]; fun_prop
        have ha := continuous_arcosh_charA hv₀.le
        exact hc1.mul (hg.comp ha)
      exact hc.aestronglyMeasurable
    · intro n
      filter_upwards with y
      have hb := hχ_bdd n y
      have hgp : 0 ≤ gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)) :=
        gaussianPDFReal_nonneg _ _ _
      rw [Real.norm_eq_abs, show (f y * χp n y + f y * χm n y) *
            gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)) =
          f y * (χp n y + χm n y) * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)) by ring,
        abs_mul, abs_mul, abs_of_nonneg hb.1, abs_of_nonneg hgp]
      dsimp [boundR]
      calc |f y| * (χp n y + χm n y) * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y))
          ≤ |f y| * 2 * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)) := by gcongr; exact hb.2
        _ = 2 * |f y| * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)) := by ring
    · have hne : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ yCrit v₀ :=
        ae_iff.mpr (by simp [measure_singleton])
      filter_upwards [hne] with y hy
      have h1 := (hχ_tendsto y hy).const_mul (f y)
      have h2 := h1.mul_const (gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)))
      have h3 : (fun n : ℕ => (f y * χp n y + f y * χm n y) *
            gaussianPDFReal 0 t (Real.arcosh (charA v₀ y))) =
          fun n : ℕ => f y * (χp n y + χm n y) * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)) := by
        funext n; ring
      rw [h3]
      simpa [mul_one] using h2
  have hL_eq : (fun n : ℕ => ∫ ω, (f (B t ω) * χp n (B t ω) + f (B t ω) * χm n (B t ω)) *
        Real.exp (-v₀ / expInt B 2 0 t ω) ∂P) =
      fun n : ℕ => ∫ y : ℝ, (f y * χp n y + f y * χm n y) *
        gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)) := funext hχ_eq
  rw [hL_eq] at hL_tendsto
  exact tendsto_nhds_unique hL_tendsto hR_tendsto

private lemma poly_contDiff (p : ℝ[X]) : ContDiff ℝ 3 (fun x : ℝ => p.eval x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [Polynomial.eval_add] using hp.add hq
  | monomial n a =>
      have h := (contDiff_const.mul (contDiff_id.pow n) : ContDiff ℝ 3 (fun x : ℝ => a * x ^ n))
      simpa only [Polynomial.eval_monomial] using h

/-- `1/x`-Laplace inversion on `(expInt W 2 0 t, W t)` for any `f ∈ C_c(ℝ)`. -/
theorem jointLaw_two_laplace_inv_compact {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W)
    (t : ℝ≥0) (ht : 0 < t) {v₀ : ℝ} (hv₀ : 0 < v₀)
    {f : ℝ → ℝ} (hf : Continuous f) (hfC : HasCompactSupport f) :
    ∫ ω, f (W t ω) * Real.exp (-v₀ / expInt W 2 0 t ω) ∂P =
      ∫ y : ℝ, f y * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)) := by
  let B : ℝ≥0 → Ω → ℝ := hW.toIsPreBrownianReal.mk W
  have hBmeas : ∀ s, Measurable (B s) := hW.toIsPreBrownianReal.measurable_mk
  have hBcont : ∀ ω, Continuous (B · ω) := hW.toIsPreBrownianReal.continuous_mk
  have hBpre : IsPreBrownianReal B P :=
    hW.toIsPreBrownianReal.isBrownianReal_mk.toIsPreBrownianReal
  have hBbm : IsBM P B := ⟨hBpre, Eventually.of_forall hBcont⟩
  have hBW : ∀ᵐ ω ∂P, ∀ s, B s ω = W s ω := hW.mk_ae_forall_eq
  have hBW_int : ∫ ω, f (W t ω) * Real.exp (-v₀ / expInt W 2 0 t ω) ∂P =
      ∫ ω, f (B t ω) * Real.exp (-v₀ / expInt B 2 0 t ω) ∂P := by
    refine integral_congr_ae (hBW.mono fun ω hω => ?_)
    dsimp only
    have hX : expInt W 2 0 t ω = expInt B 2 0 t ω := by
      simp only [expInt]; exact intervalIntegral.integral_congr fun s _ => by rw [hω s.toNNReal]
    rw [hX, ← hω t]
  rw [hBW_int]
  have hXpos := expInt_two_pos_ae B hBbm t ht
  have hXmeas : Measurable (expInt B 2 0 t) := measurable_expInt_bm hBmeas hBcont 2 t
  obtain ⟨M0, hM0⟩ := hfC.isCompact.isBounded.subset_closedBall (0 : ℝ)
  let R : ℝ := max M0 1 + 1
  have hR_pos : 0 < R := by positivity
  have hf_van : ∀ y, R ≤ |y| → f y = 0 := by
    intro y hy
    by_contra hne
    have := hM0 (subset_tsupport f hne)
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    linarith [le_max_left M0 1, le_max_right M0 1]
  let χ : ℝ → ℝ := smoothBump (-R - 1) (-R) R (R + 1)
  have hχ_cd : ContDiff ℝ 3 χ := smoothBump_contDiff _ _ _ _
  have hχ_cs : HasCompactSupport χ := smoothBump_hasCompactSupport (by linarith) (by linarith)
  have hχ_mem : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1 := smoothBump_mem_Icc _ _ _ _
  have hχ_one : ∀ y, |y| ≤ R → χ y = 1 := fun y hy =>
    smoothBump_one_of_mem (by linarith) (by linarith) (neg_le.mp (neg_le_abs y |>.trans hy))
      ((le_abs_self y).trans hy)
  have h_approx : ∀ n : ℕ, ∃ p : ℝ[X], ∀ y ∈ Icc (-R - 1) (R + 1),
      |p.eval y - f y| < 1 / ((n : ℝ) + 1) := fun n =>
    exists_polynomial_near_of_continuousOn (-R - 1) (R + 1) f hf.continuousOn
      (1 / ((n : ℝ) + 1)) (by positivity)
  choose p hp using h_approx
  let g : ℕ → ℝ → ℝ := fun n y => (p n).eval y * χ y
  have hg_cd : ∀ n, ContDiff ℝ 3 (g n) := fun n =>
    (poly_contDiff (p n)).mul hχ_cd
  have hg_cs : ∀ n, HasCompactSupport (g n) := fun n => hχ_cs.mul_left
  have hg_close : ∀ n y, |g n y - f y| ≤ 1 / ((n : ℝ) + 1) := by
    intro n y
    by_cases hyR : |y| ≤ R
    · rw [show g n y = (p n).eval y * χ y from rfl, hχ_one y hyR, mul_one]
      have hyI : y ∈ Icc (-R - 1) (R + 1) := ⟨by linarith [neg_le_abs y], by linarith [le_abs_self y]⟩
      exact (hp n y hyI).le
    · have hf0 : f y = 0 := hf_van y (not_le.mp hyR).le
      rw [hf0, sub_zero]
      by_cases hyI : y ∈ Icc (-R - 1) (R + 1)
      · have hmem := hχ_mem y
        rw [show g n y = (p n).eval y * χ y from rfl, abs_mul, abs_of_nonneg hmem.1]
        have hpy : |(p n).eval y| ≤ 1 / ((n : ℝ) + 1) := by
          simpa [hf0] using (hp n y hyI).le
        exact (mul_le_of_le_one_right (abs_nonneg _) hmem.2).trans hpy
      · simp only [mem_Icc, not_and_or, not_le] at hyI
        have hχ0 : χ y = 0 := smoothBump_zero_of_not_mem (by linarith) (by linarith)
          (hyI.imp le_of_lt le_of_lt)
        simp [g, hχ0]; positivity
  have hg_eq : ∀ n,
      ∫ ω, g n (B t ω) * Real.exp (-v₀ / expInt B 2 0 t ω) ∂P =
        ∫ y : ℝ, g n y * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)) := fun n =>
    jointLaw_two_laplace_inv_contDiff B hBbm t ht hv₀ (hg_cd n) (hg_cs n)
  obtain ⟨Cf, hCf0, hCf⟩ : ∃ Cf ≥ 0, ∀ y, |f y| ≤ Cf := by
    have hK' := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn hf.continuousOn
    obtain ⟨K, hK⟩ := hK'
    refine ⟨max K 0, le_max_right K 0, fun y => ?_⟩
    by_cases hy : |y| ≤ R
    · have hyI : y ∈ Icc (-R) R := ⟨by linarith [neg_le_abs y], by linarith [le_abs_self y]⟩
      exact (Real.norm_eq_abs (f y) ▸ hK y hyI).trans (le_max_left K 0)
    · rw [hf_van y (not_le.mp hy).le, abs_zero]; exact le_max_right K 0
  have hL_tendsto : Tendsto (fun n : ℕ => ∫ ω, g n (B t ω) * Real.exp (-v₀ / expInt B 2 0 t ω) ∂P)
      atTop (nhds (∫ ω, f (B t ω) * Real.exp (-v₀ / expInt B 2 0 t ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => Cf + 1) ?_ (integrable_const _) ?_ ?_
    · intro n
      have hc : Continuous (g n) := (hg_cd n).continuous
      exact ((hc.measurable.comp (hBmeas t)).mul
        (Real.continuous_exp.measurable.comp (measurable_const.div hXmeas))).aestronglyMeasurable
    · intro n
      filter_upwards [hXpos] with ω hω
      have hexp : Real.exp (-v₀ / expInt B 2 0 t ω) ≤ 1 :=
        Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hv₀.le) hω.le)
      have hgn : |g n (B t ω)| ≤ Cf + 1 := by
        have h1 := hg_close n (B t ω)
        have h2 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
        have htri := abs_sub_abs_le_abs_sub (g n (B t ω)) (f (B t ω))
        linarith [hCf (B t ω)]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_of_le_one_right (abs_nonneg _) hexp).trans hgn
    · filter_upwards with ω
      have hlim : Tendsto (fun n => g n (B t ω)) atTop (nhds (f (B t ω))) := by
        rw [Metric.tendsto_atTop]
        intro ε hε
        obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
        refine ⟨N, fun n hn => ?_⟩
        rw [Real.dist_eq]
        have hn' : (1 : ℝ) / ((n : ℝ) + 1) < ε :=
          lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) (by norm_cast; omega)) hN
        exact lt_of_le_of_lt (hg_close n (B t ω)) hn'
      exact hlim.mul_const _
  have hR_tendsto : Tendsto (fun n : ℕ => ∫ y : ℝ, g n y * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)))
      atTop (nhds (∫ y : ℝ, f y * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)))) := by
    let χ1 : ℝ → ℝ := smoothBump (-R - 2) (-R - 1) (R + 1) (R + 2)
    have hχ1_one : ∀ y, |y| ≤ R + 1 → χ1 y = 1 := fun y hy =>
      smoothBump_one_of_mem (by linarith) (by linarith) (by linarith [neg_le_abs y]) (by linarith [le_abs_self y])
    let boundR : ℝ → ℝ := fun y => (Cf + 1) * χ1 y * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y))
    have hbound_int : Integrable boundR := by
      have hc : Continuous boundR := by
        have hχc : Continuous χ1 := (smoothBump_contDiff (-R - 2) (-R - 1) (R + 1) (R + 2) (n := 0)).continuous
        have hg : Continuous (gaussianPDFReal 0 t) := by rw [gaussianPDFReal_def]; fun_prop
        have ha : Continuous (fun y => Real.arcosh (charA v₀ y)) := continuous_arcosh_charA hv₀.le
        exact (continuous_const.mul hχc).mul (hg.comp ha)
      have hcs1 : HasCompactSupport (fun y => (Cf + 1) * χ1 y) :=
        (smoothBump_hasCompactSupport (a := -R - 2) (b := -R - 1) (c := R + 1) (d := R + 2)
          (by linarith) (by linarith)).comp_left (mul_zero _)
      have hcs : HasCompactSupport boundR := hcs1.mul_right
      exact hc.integrable_of_hasCompactSupport hcs
    refine tendsto_integral_of_dominated_convergence boundR ?_ hbound_int ?_ ?_
    · intro n
      have hc : Continuous (fun y => g n y * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y))) := by
        have hc1 : Continuous (g n) := (hg_cd n).continuous
        have hg : Continuous (gaussianPDFReal 0 t) := by rw [gaussianPDFReal_def]; fun_prop
        have ha : Continuous (fun y => Real.arcosh (charA v₀ y)) := continuous_arcosh_charA hv₀.le
        exact hc1.mul (hg.comp ha)
      exact hc.aestronglyMeasurable
    · intro n
      filter_upwards with y
      have hgp : 0 ≤ gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)) :=
        gaussianPDFReal_nonneg _ _ _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hgp]
      by_cases hy : |y| ≤ R + 1
      · have hgn : |g n y| ≤ Cf + 1 := by
          have h1 := hg_close n y
          have h2 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
          have htri := abs_sub_abs_le_abs_sub (g n y) (f y)
          linarith [hCf y]
        dsimp [boundR]
        rw [hχ1_one y hy, mul_one]
        exact mul_le_mul_of_nonneg_right hgn hgp
      · have hy' : R + 1 < |y| := not_le.mp hy
        have hχ0 : χ y = 0 := by
          rcases le_or_gt 0 y with h0 | h0
          · rw [abs_of_nonneg h0] at hy'
            exact smoothBump_zero_of_not_mem (by linarith) (by linarith) (Or.inr hy'.le)
          · rw [abs_of_neg h0] at hy'
            exact smoothBump_zero_of_not_mem (by linarith) (by linarith) (Or.inl (by linarith))
        have hg0 : g n y = 0 := by simp [g, hχ0]
        rw [hg0, abs_zero, zero_mul]
        dsimp [boundR]
        have hχ1_nn : 0 ≤ χ1 y := (smoothBump_mem_Icc _ _ _ _ y).1
        positivity
    · filter_upwards with y
      have hlim : Tendsto (fun n => g n y) atTop (nhds (f y)) := by
        rw [Metric.tendsto_atTop]
        intro ε hε
        obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
        refine ⟨N, fun n hn => ?_⟩
        rw [Real.dist_eq]
        have hn' : (1 : ℝ) / ((n : ℝ) + 1) < ε :=
          lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) (by norm_cast; omega)) hN
        exact lt_of_le_of_lt (hg_close n y) hn'
      exact hlim.mul_const _
  have heq : (fun n : ℕ => ∫ ω, g n (B t ω) * Real.exp (-v₀ / expInt B 2 0 t ω) ∂P) =
      fun n : ℕ => ∫ y : ℝ, g n y * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)) := funext hg_eq
  rw [heq] at hL_tendsto
  exact tendsto_nhds_unique hL_tendsto hR_tendsto

/-- `1/x`-Laplace inversion on `(expInt W 2 0 t, W t)` for any bounded continuous `f`. -/
theorem jointLaw_two_laplace_inv {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W)
    (t : ℝ≥0) (ht : 0 < t) {v₀ : ℝ} (hv₀ : 0 < v₀)
    {f : ℝ → ℝ} (hf : Continuous f) (hf_bdd : ∃ C, ∀ y, |f y| ≤ C) :
    ∫ ω, f (W t ω) * Real.exp (-v₀ / expInt W 2 0 t ω) ∂P =
      ∫ y : ℝ, f y * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)) := by
  obtain ⟨C, hC⟩ := hf_bdd
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  let B : ℝ≥0 → Ω → ℝ := hW.toIsPreBrownianReal.mk W
  have hBmeas : ∀ s, Measurable (B s) := hW.toIsPreBrownianReal.measurable_mk
  have hBcont : ∀ ω, Continuous (B · ω) := hW.toIsPreBrownianReal.continuous_mk
  have hBpre : IsPreBrownianReal B P :=
    hW.toIsPreBrownianReal.isBrownianReal_mk.toIsPreBrownianReal
  have hBbm : IsBM P B := ⟨hBpre, Eventually.of_forall hBcont⟩
  have hBW : ∀ᵐ ω ∂P, ∀ s, B s ω = W s ω := hW.mk_ae_forall_eq
  have hBW_int : ∫ ω, f (W t ω) * Real.exp (-v₀ / expInt W 2 0 t ω) ∂P =
      ∫ ω, f (B t ω) * Real.exp (-v₀ / expInt B 2 0 t ω) ∂P := by
    refine integral_congr_ae (hBW.mono fun ω hω => ?_)
    dsimp only
    have hX : expInt W 2 0 t ω = expInt B 2 0 t ω := by
      simp only [expInt]; exact intervalIntegral.integral_congr fun s _ => by rw [hω s.toNNReal]
    rw [hX, ← hω t]
  rw [hBW_int]
  have hXpos := expInt_two_pos_ae B hBbm t ht
  have hXmeas : Measurable (expInt B 2 0 t) := measurable_expInt_bm hBmeas hBcont 2 t
  let χ : ℕ → ℝ → ℝ := fun n y =>
    smoothBump (-((n : ℝ) + 2)) (-((n : ℝ) + 1)) ((n : ℝ) + 1) ((n : ℝ) + 2) y
  have hχ_eq : ∀ n : ℕ,
      ∫ ω, (f (B t ω) * χ n (B t ω)) * Real.exp (-v₀ / expInt B 2 0 t ω) ∂P =
        ∫ y : ℝ, (f y * χ n y) * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)) := fun n =>
    jointLaw_two_laplace_inv_compact B hBbm t ht hv₀
      (hf.mul (smoothBump_contDiff _ _ _ _ (n := 0)).continuous)
      ((smoothBump_hasCompactSupport (by linarith : -((n : ℝ) + 2) < -((n : ℝ) + 1))
        (by linarith : (n : ℝ) + 1 < (n : ℝ) + 2)).mul_left)
  have hχ_lim : ∀ y : ℝ, Tendsto (fun n : ℕ => χ n y) atTop (nhds 1) := by
    intro y
    have h_ev : ∀ᶠ n : ℕ in atTop, χ n y = 1 := by
      obtain ⟨N, hN⟩ := exists_nat_gt |y|
      refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
      have hny : |y| ≤ (n : ℝ) + 1 := by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      exact smoothBump_one_of_mem (by linarith) (by linarith)
        (by linarith [neg_le_abs y]) (by linarith [le_abs_self y])
    exact tendsto_const_nhds.congr' (h_ev.mono fun n hn => hn.symm)
  have hL_tendsto : Tendsto (fun n : ℕ => ∫ ω, (f (B t ω) * χ n (B t ω)) * Real.exp (-v₀ / expInt B 2 0 t ω) ∂P)
      atTop (nhds (∫ ω, f (B t ω) * Real.exp (-v₀ / expInt B 2 0 t ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C) ?_ (integrable_const _) ?_ ?_
    · intro n
      have hc : Continuous (fun y => f y * χ n y) :=
        hf.mul (smoothBump_contDiff _ _ _ _ (n := 0)).continuous
      exact ((hc.measurable.comp (hBmeas t)).mul
        (Real.continuous_exp.measurable.comp (measurable_const.div hXmeas))).aestronglyMeasurable
    · intro n
      filter_upwards [hXpos] with ω hω
      have hexp : Real.exp (-v₀ / expInt B 2 0 t ω) ≤ 1 :=
        Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hv₀.le) hω.le)
      have hmem := smoothBump_mem_Icc (-((n : ℝ) + 2)) (-((n : ℝ) + 1)) ((n : ℝ) + 1) ((n : ℝ) + 2) (B t ω)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hmem.1]
      calc |f (B t ω)| * χ n (B t ω) * Real.exp (-v₀ / expInt B 2 0 t ω)
          ≤ C * 1 * 1 := by
            refine mul_le_mul (mul_le_mul (hC _) hmem.2 hmem.1 hC0) hexp (Real.exp_pos _).le (by positivity)
        _ = C := by ring
    · filter_upwards with ω
      have h1 := ((hχ_lim (B t ω)).const_mul (f (B t ω))).mul_const (Real.exp (-v₀ / expInt B 2 0 t ω))
      simpa using h1
  have hR_bound : ∀ y : ℝ,
      gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)) ≤ gaussianPDFReal 0 t y := by
    intro y
    have h1 : Real.cosh |y| ≤ charA v₀ y := by
      rw [Real.cosh_abs]
      unfold charA
      linarith [mul_nonneg hv₀.le (Real.exp_pos (-y)).le]
    have h2 : |y| ≤ Real.arcosh (charA v₀ y) := by
      rw [← Real.arcosh_cosh (abs_nonneg y)]
      exact (Real.arcosh_le_arcosh (lt_of_lt_of_le zero_lt_one (Real.one_le_cosh _))
        (lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one (Real.one_le_cosh _)) h1)).mpr h1
    have h3 : y ^ 2 ≤ Real.arcosh (charA v₀ y) ^ 2 := by
      have : |y| ^ 2 ≤ Real.arcosh (charA v₀ y) ^ 2 := by nlinarith [abs_nonneg y]
      simpa [sq_abs] using this
    simp only [gaussianPDFReal_def, sub_zero]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    exact div_le_div_of_nonneg_right (neg_le_neg h3) (by positivity)
  have hgauss_int : Integrable (fun y : ℝ => C * gaussianPDFReal 0 t y) := by
    have h1 : Integrable (gaussianPDFReal 0 t) := integrable_gaussianPDFReal 0 t
    exact h1.const_mul C
  have hR_tendsto : Tendsto (fun n : ℕ => ∫ y : ℝ, (f y * χ n y) * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)))
      atTop (nhds (∫ y : ℝ, f y * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)))) := by
    refine tendsto_integral_of_dominated_convergence (fun y => C * gaussianPDFReal 0 t y) ?_
      hgauss_int ?_ ?_
    · intro n
      have hc1 : Continuous (fun y => f y * χ n y) :=
        hf.mul (smoothBump_contDiff _ _ _ _ (n := 0)).continuous
      have hg : Continuous (gaussianPDFReal 0 t) := by rw [gaussianPDFReal_def]; fun_prop
      have ha : Continuous (fun y => Real.arcosh (charA v₀ y)) := continuous_arcosh_charA hv₀.le
      exact (hc1.mul (hg.comp ha)).aestronglyMeasurable
    · intro n
      filter_upwards with y
      have hmem := smoothBump_mem_Icc (-((n : ℝ) + 2)) (-((n : ℝ) + 1)) ((n : ℝ) + 1) ((n : ℝ) + 2) y
      have hgp : 0 ≤ gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)) := gaussianPDFReal_nonneg _ _ _
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hmem.1, abs_of_nonneg hgp]
      calc |f y| * χ n y * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y))
          ≤ C * 1 * gaussianPDFReal 0 t y := by
            refine mul_le_mul (mul_le_mul (hC y) hmem.2 hmem.1 hC0) (hR_bound y) hgp (by positivity)
        _ = C * gaussianPDFReal 0 t y := by ring
    · filter_upwards with y
      have h1 := ((hχ_lim y).const_mul (f y)).mul_const (gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)))
      simpa using h1
  have heq : (fun n : ℕ => ∫ ω, (f (B t ω) * χ n (B t ω)) * Real.exp (-v₀ / expInt B 2 0 t ω) ∂P) =
      fun n : ℕ => ∫ y : ℝ, (f y * χ n y) * gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)) := funext hχ_eq
  rw [heq] at hL_tendsto
  exact tendsto_nhds_unique hL_tendsto hR_tendsto

end LaplaceInversion

end Lyasoff2016
