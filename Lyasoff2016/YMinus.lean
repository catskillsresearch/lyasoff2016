/-
Lower inverse branch `y_-(v, a)` of the characteristic `A`.
-/
module

public import Lyasoff2016.CharA
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv


@[expose] public section

open Set Filter Topology
open scoped Real

noncomputable section
namespace Lyasoff2016

/-- Lower inverse branch `y_-(v, a) = log(a - √(a² - (1 + 2v)))`. -/
def yMinus (v a : ℝ) : ℝ := Real.log (a - Real.sqrt (a ^ 2 - (1 + 2 * v)))

/-- Helper: on the branch domain, `√(a² - (1+2v)) < a`. -/
lemma sqrt_sq_sub_lt_self {v a : ℝ} (hv : 0 ≤ v) (ha : Real.sqrt (1 + 2 * v) < a) :
    Real.sqrt (a ^ 2 - (1 + 2 * v)) < a := by
  have ha0 : 0 < a := (Real.sqrt_nonneg _).trans_lt ha
  have h12v : 0 < 1 + 2 * v := by linarith
  rw [Real.sqrt_lt' ha0]
  linarith

namespace yMinus

theorem contDiffOn {v : ℝ} (hv : 0 ≤ v) {n : ℕ∞} :
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

end yMinus

namespace charA

theorem yMinus {v a : ℝ} (hv : 0 ≤ v) (ha : Real.sqrt (1 + 2 * v) < a) :
    Lyasoff2016.yMinus v a < Lyasoff2016.yCrit v ∧
      charA v (Lyasoff2016.yMinus v a) = a := by
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
  have hy : Lyasoff2016.yMinus v a < Lyasoff2016.yCrit v := by
    have h2 : (a - s) ^ 2 < 1 + 2 * v := by
      have : a - s < a + s := by linarith
      nlinarith [hprod, harg_pos]
    have hexp : Real.exp (2 * Lyasoff2016.yMinus v a) < Real.exp (2 * Lyasoff2016.yCrit v) := by
      rw [Lyasoff2016.yCrit.exp_two_mul hv, Lyasoff2016.yMinus,
        show 2 * Real.log (a - s) = Real.log ((a - s) ^ 2) by
          rw [Real.log_pow]; ring]
      rw [Real.exp_log (by positivity)]
      exact h2
    linarith [Real.exp_lt_exp.mp hexp]
  refine ⟨hy, ?_⟩
  rw [eq, Lyasoff2016.yMinus, Real.exp_log harg_pos, Real.exp_neg, Real.exp_log harg_pos]
  have hinv : (1 + 2 * v) * (a - s)⁻¹ = a + s := by
    field_simp [harg_pos.ne']
    linarith [hprod]
  rw [hinv]
  ring

theorem image_Iio_yCrit {v : ℝ} (hv : 0 ≤ v) :
    charA v '' Iio (Lyasoff2016.yCrit v) = Ioi (Real.sqrt (1 + 2 * v)) := by
  ext a
  simp only [mem_image, mem_Ioi]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← yCrit hv]
    exact strictAntiOn hv hy.le le_rfl hy
  · intro ha
    obtain ⟨hy, hchar⟩ := yMinus hv ha
    exact ⟨Lyasoff2016.yMinus v a, hy, hchar⟩

end charA

namespace yMinus

theorem charA {v y : ℝ} (hv : 0 ≤ v) (hy : y < yCrit v) :
    yMinus v (Lyasoff2016.charA v y) = y := by
  have ha : Real.sqrt (1 + 2 * v) < Lyasoff2016.charA v y := by
    rw [← Lyasoff2016.charA.yCrit hv]
    exact Lyasoff2016.charA.strictAntiOn hv hy.le le_rfl hy
  obtain ⟨hy', hchar⟩ := Lyasoff2016.charA.yMinus hv ha
  exact (Lyasoff2016.charA.strictAntiOn hv).injOn hy'.le hy.le hchar

end yMinus

end Lyasoff2016
