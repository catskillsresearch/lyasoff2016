/-
Real Asian inner integral `S_{k,p}(α)` and closed forms (p. 1091).
-/
module

public import Lyasoff2016.UpperGamma


@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

def Sfun (k p : ℕ) (α : ℝ) : ℝ :=
  ∫ v in Ioi (0 : ℝ), max (v - (k : ℝ)) 0 * v ^ (-(p : ℤ)) * Real.exp (-α / v)

/-- The Gamma integrand `u ^ (s - 1) * exp (-u)` is integrable on `(0, ∞)` for `s > 0`. -/
private lemma integrableOn_rpow_mul_exp_neg {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun u : ℝ => u ^ (s - 1) * Real.exp (-u)) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent hs
  have heq : (fun u : ℝ => u ^ (s - 1) * Real.exp (-u)) =
      fun u : ℝ => Real.exp (-u) * u ^ (s - 1) := by
    funext u; ring
  rw [heq]
  exact h

/-- Lower incomplete Gamma integral: `∫₀^c u^{s-1} e^{-u} du = Γ(s) − Γ(s, c)`. -/
private lemma integral_Ioc_rpow_mul_exp_neg {s c : ℝ} (hs : 0 < s) (hc : 0 ≤ c) :
    ∫ u in Ioc 0 c, u ^ (s - 1) * Real.exp (-u) = Real.Gamma s - upperGamma s c := by
  have hint := integrableOn_rpow_mul_exp_neg hs
  have hunion := setIntegral_union (μ := volume)
    (f := fun u : ℝ => u ^ (s - 1) * Real.exp (-u))
    (Ioc_disjoint_Ioi (le_refl c)) measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hc))
  rw [Ioc_union_Ioi_eq_Ioi hc] at hunion
  have hΓ : Real.Gamma s = ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * Real.exp (-u) := by
    rw [Real.Gamma_eq_integral hs]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    ring
  rw [hΓ, upperGamma, hunion]
  ring

namespace Sfun

/- Paper: p. 1091, closed forms for S.
   Plain recap: S_{0,p}(A) = ∫₀^∞ e^{-A/x} x^{1-p} dx = A^{-(p-2)} Γ(p-2) for p ≥ 3. -/
theorem zero (p : ℕ) (α : ℝ) (hp : 3 ≤ p) (hα : 0 < α) :
    Sfun 0 p α = α ^ (-((p : ℝ) - 2)) * Real.Gamma ((p : ℝ) - 2) := by
  have hp2 : 0 < (p : ℝ) - 2 := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hsubst := integral_comp_rpow_Ioi
    (g := fun y : ℝ => y ^ ((p : ℝ) - 3) * Real.exp (-(α * y)))
    (p := (-1 : ℝ)) (by norm_num)
  have hpoint :
      ∀ x ∈ Ioi (0 : ℝ),
        max (x - (0 : ℝ)) 0 * x ^ (-(p : ℤ)) * Real.exp (-α / x) =
          ((|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) *
            ((x ^ (-1 : ℝ)) ^ ((p : ℝ) - 3) *
              Real.exp (-(α * x ^ (-1 : ℝ))))) := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    rw [max_eq_left (by simpa using hx.le), sub_zero]
    rw [abs_neg, abs_one, one_mul]
    have hz : x ^ (-(p : ℤ)) = x ^ (-(p : ℝ)) := by
      rw [zpow_neg, zpow_natCast, ← Real.rpow_natCast,
        ← Real.rpow_neg (le_of_lt hx)]
    rw [hz]
    nth_rewrite 1 [show x = x ^ (1 : ℝ) by simp]
    rw [← Real.rpow_add hx, ← Real.rpow_mul hx.le]
    rw [show (-1 : ℝ) * ((p : ℝ) - 3) = 3 - p by ring]
    rw [Real.rpow_neg_one]
    rw [← mul_assoc, ← Real.rpow_add hx]
    congr 2
    · ring
    · field_simp
  simp only [Sfun, Nat.cast_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint]
  have hsubst' : (∫ x in Ioi (0 : ℝ),
      |(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1) *
        ((x ^ (-1 : ℝ)) ^ ((p : ℝ) - 3) * Real.exp (-(α * x ^ (-1 : ℝ)))) =
      ∫ y in Ioi (0 : ℝ), y ^ ((p : ℝ) - 3) * Real.exp (-(α * y))) := by
    simpa only [smul_eq_mul] using hsubst
  rw [hsubst']
  rw [show (p : ℝ) - 3 = ((p : ℝ) - 2) - 1 by ring]
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hp2 hα]
  congr 1
  rw [one_div, ← Real.rpow_neg_eq_inv_rpow]

/- Paper: p. 1091, closed form for S_{k,p}.
   Plain recap: after the substitution v = A/x,
   S_{k,p}(A) = k A^{-(p-1)} Γ(p-1, A/k) − A^{-(p-2)} Γ(p-2, A/k)
                − k A^{-(p-1)} Γ(p-1) + A^{-(p-2)} Γ(p-2). -/
theorem closed_form (k p : ℕ) (α : ℝ) (hk : 0 < (k : ℝ)) (hp : 3 ≤ p) (hα : 0 < α) :
    Sfun k p α =
      (k : ℝ) * α ^ (-((p : ℝ) - 1)) * upperGamma ((p : ℝ) - 1) (α / k) -
        α ^ (-((p : ℝ) - 2)) * upperGamma ((p : ℝ) - 2) (α / k) -
        (k : ℝ) * α ^ (-((p : ℝ) - 1)) * Real.Gamma ((p : ℝ) - 1) +
        α ^ (-((p : ℝ) - 2)) * Real.Gamma ((p : ℝ) - 2) := by
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp2 : 0 < (p : ℝ) - 2 := by linarith
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  have hα0 : α ≠ 0 := hα.ne'
  have hk0 : (k : ℝ) ≠ 0 := hk.ne'
  have hc : 0 < α / k := div_pos hα hk
  set a : ℝ := α ^ ((p : ℝ) - 2) with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos hα _
  have ha0 : a ≠ 0 := ha.ne'
  have hα2 : α ^ (-((p : ℝ) - 2)) = a⁻¹ := Real.rpow_neg hα.le _
  have hα1 : α ^ (-((p : ℝ) - 1)) = (a * α)⁻¹ := by
    rw [Real.rpow_neg hα.le, ha_def, ← Real.rpow_add_one hα0]
    congr 2
    ring
  let F : ℝ → ℝ := fun u =>
    max (α / u - (k : ℝ)) 0 * (u / α) ^ ((p : ℝ) - 2) * Real.exp (-u)
  let F' : ℝ → ℝ := fun u =>
    α / a * (u ^ ((p : ℝ) - 2 - 1) * Real.exp (-u)) -
      (k : ℝ) * a⁻¹ * (u ^ ((p : ℝ) - 1 - 1) * Real.exp (-u))
  have hpoint :
      ∀ x ∈ Ioi (0 : ℝ),
        max (x - (k : ℝ)) 0 * x ^ (-(p : ℤ)) * Real.exp (-α / x) =
          (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) * F (α * x ^ (-1 : ℝ)) := by
    intro x hx
    have hx' : 0 < x := hx
    have hx0 : x ≠ 0 := hx'.ne'
    have hz : x ^ (-(p : ℤ)) = x ^ (-(p : ℝ)) := by
      rw [zpow_neg, zpow_natCast, ← Real.rpow_natCast, ← Real.rpow_neg hx'.le]
    have h1 : α / (α * x⁻¹) = x := by field_simp
    have h2 : α * x⁻¹ / α = x⁻¹ := by field_simp
    have h3 : x ^ (-(p : ℝ)) = x ^ ((-1 : ℝ) - 1) * (x⁻¹) ^ ((p : ℝ) - 2) := by
      rw [Real.inv_rpow hx'.le, ← Real.rpow_neg hx'.le, ← Real.rpow_add hx']
      congr 1
      ring
    have h4 : -α / x = -(α * x⁻¹) := by field_simp
    simp only [F]
    rw [abs_neg, abs_one, one_mul, Real.rpow_neg_one, h1, h2, hz, h3, h4]
    ring
  have hsubst := integral_comp_rpow_Ioi (g := fun y : ℝ => F (α * y))
    (p := (-1 : ℝ)) (by norm_num)
  have hsubst' : (∫ x in Ioi (0 : ℝ),
      |(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1) * F (α * x ^ (-1 : ℝ))) =
      ∫ y in Ioi (0 : ℝ), F (α * y) := by
    simpa only [smul_eq_mul] using hsubst
  have hscale : (∫ y in Ioi (0 : ℝ), F (α * y)) = α⁻¹ * ∫ u in Ioi (0 : ℝ), F u := by
    have h := integral_comp_mul_left_Ioi F 0 hα
    rwa [mul_zero, smul_eq_mul] at h
  have hF : ∀ u ∈ Ioi (0 : ℝ), F u = (Iic (α / k)).indicator F' u := by
    intro u hu
    have hu' : 0 < u := hu
    have hu0 : u ≠ 0 := hu'.ne'
    by_cases huc : u ≤ α / k
    · rw [indicator_of_mem (mem_Iic.mpr huc)]
      have hku : (k : ℝ) ≤ α / u := by
        rw [le_div_iff₀ hu']
        have := (le_div_iff₀ hk).mp huc
        linarith
      have hpow2 : u ^ ((p : ℝ) - 2) = u ^ ((p : ℝ) - 2 - 1) * u := by
        rw [← Real.rpow_add_one hu0]
        congr 1
        ring
      have hpow1 : u ^ ((p : ℝ) - 1 - 1) = u ^ ((p : ℝ) - 2 - 1) * u := by
        rw [← Real.rpow_add_one hu0]
        congr 1
        ring
      simp only [F, F']
      rw [max_eq_left (sub_nonneg.mpr hku), Real.div_rpow hu'.le hα.le, ← ha_def, hpow2, hpow1]
      field_simp
    · rw [indicator_of_notMem (by simpa using huc)]
      have hku : α / u ≤ (k : ℝ) := by
        rw [div_le_iff₀ hu']
        have := (div_lt_iff₀ hk).mp (not_le.mp huc)
        linarith
      simp only [F]
      rw [max_eq_right (sub_nonpos.mpr hku)]
      ring
  have hset : Ioi (0 : ℝ) ∩ Iic (α / k) = Ioc 0 (α / k) := by
    ext u
    simp [mem_Ioc]
  have hi2 : IntegrableOn (fun u : ℝ => u ^ ((p : ℝ) - 2 - 1) * Real.exp (-u))
      (Ioc 0 (α / k)) :=
    (integrableOn_rpow_mul_exp_neg hp2).mono_set Ioc_subset_Ioi_self
  have hi1 : IntegrableOn (fun u : ℝ => u ^ ((p : ℝ) - 1 - 1) * Real.exp (-u))
      (Ioc 0 (α / k)) :=
    (integrableOn_rpow_mul_exp_neg hp1).mono_set Ioc_subset_Ioi_self
  have hF' : (∫ u in Ioc 0 (α / k), F' u) =
      α / a * (Real.Gamma ((p : ℝ) - 2) - upperGamma ((p : ℝ) - 2) (α / k)) -
        (k : ℝ) * a⁻¹ * (Real.Gamma ((p : ℝ) - 1) - upperGamma ((p : ℝ) - 1) (α / k)) := by
    simp only [F']
    rw [integral_sub (hi2.const_mul _) (hi1.const_mul _), integral_const_mul,
      integral_const_mul, integral_Ioc_rpow_mul_exp_neg hp2 hc.le,
      integral_Ioc_rpow_mul_exp_neg hp1 hc.le]
  simp only [Sfun]
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint, hsubst', hscale,
    setIntegral_congr_fun measurableSet_Ioi hF, setIntegral_indicator measurableSet_Iic,
    hset, hF', hα2, hα1]
  field_simp
  ring

end Sfun

end Lyasoff2016