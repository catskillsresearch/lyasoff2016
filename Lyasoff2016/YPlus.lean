/-
Upper inverse branch `y_+(v, a)` of the characteristic `A`.
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

/-- Upper inverse branch `y_+(v, a) = log(a + √(a² - (1 + 2v)))`. -/
def yPlus (v a : ℝ) : ℝ := Real.log (a + Real.sqrt (a ^ 2 - (1 + 2 * v)))

namespace yPlus

theorem contDiffOn {v : ℝ} (_hv : 0 ≤ v) {n : ℕ∞} :
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

end yPlus

namespace charA

theorem yPlus {v a : ℝ} (hv : 0 ≤ v) (ha : Real.sqrt (1 + 2 * v) < a) :
    Lyasoff2016.yCrit v < Lyasoff2016.yPlus v a ∧
      charA v (Lyasoff2016.yPlus v a) = a := by
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
  have hy : Lyasoff2016.yCrit v < Lyasoff2016.yPlus v a := by
    have h2 : 1 + 2 * v < (a + s) ^ 2 := by
      nlinarith [Real.lt_sq_of_sqrt_lt ha, hs_pos]
    have hexp : Real.exp (2 * Lyasoff2016.yCrit v) < Real.exp (2 * Lyasoff2016.yPlus v a) := by
      rw [Lyasoff2016.yCrit.exp_two_mul hv, Lyasoff2016.yPlus,
        show 2 * Real.log (a + s) = Real.log ((a + s) ^ 2) by
          rw [Real.log_pow]; ring]
      rw [Real.exp_log (by positivity)]
      exact h2
    linarith [Real.exp_lt_exp.mp hexp]
  refine ⟨hy, ?_⟩
  rw [eq, Lyasoff2016.yPlus, Real.exp_log harg_pos, Real.exp_neg, Real.exp_log harg_pos]
  have hinv : (1 + 2 * v) * (a + s)⁻¹ = a - s := by
    field_simp [harg_pos.ne']
    linarith [hprod]
  rw [hinv]
  ring

theorem image_Ioi_yCrit {v : ℝ} (hv : 0 ≤ v) :
    charA v '' Ioi (Lyasoff2016.yCrit v) = Ioi (Real.sqrt (1 + 2 * v)) := by
  ext a
  simp only [mem_image, mem_Ioi]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← yCrit hv]
    exact strictMonoOn hv le_rfl hy.le hy
  · intro ha
    obtain ⟨hy, hchar⟩ := yPlus hv ha
    exact ⟨Lyasoff2016.yPlus v a, hy, hchar⟩

end charA

namespace yPlus

theorem charA {v y : ℝ} (hv : 0 ≤ v) (hy : yCrit v < y) :
    yPlus v (Lyasoff2016.charA v y) = y := by
  have ha : Real.sqrt (1 + 2 * v) < Lyasoff2016.charA v y := by
    rw [← Lyasoff2016.charA.yCrit hv]
    exact Lyasoff2016.charA.strictMonoOn hv le_rfl hy.le hy
  obtain ⟨hy', hchar⟩ := Lyasoff2016.charA.yPlus hv ha
  exact (Lyasoff2016.charA.strictMonoOn hv).injOn hy'.le hy.le hchar

end yPlus

end Lyasoff2016
