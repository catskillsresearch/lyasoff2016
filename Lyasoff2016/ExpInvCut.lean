/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Smooth cutoff `expInvCut u x = if 0 < x then exp(-u / x) else 0` and its derivatives/bounds,
plus compactly supported `C^3` function bounds.
-/
module

public import Mathlib
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.Algebra.Support

@[expose] public section

open Set Filter Topology
open scoped NNReal Real

noncomputable section
namespace Lyasoff2016

section ExpInvCutoff

/-- Smooth cutoff at `0`: `φ_u(x) = exp(-u / x)` for `x > 0` and `0` for `x ≤ 0`. -/
def expInvCut (u x : ℝ) : ℝ := if 0 < x then Real.exp (-u / x) else 0

/-- Derivative of `expInvCut u`: `(u / x^2) * exp(-u / x)` for `x > 0`. -/
def expInvCut₁ (u x : ℝ) : ℝ := if 0 < x then (u / x ^ 2) * Real.exp (-u / x) else 0

/-- Second derivative of `expInvCut u`: `(-2 u / x^3 + u^2 / x^4) * exp(-u / x)` for `x > 0`. -/
def expInvCut₂ (u x : ℝ) : ℝ :=
  if 0 < x then (-2 * u / x ^ 3 + u ^ 2 / x ^ 4) * Real.exp (-u / x) else 0

/-- Third derivative of `expInvCut u`: `(6 u / x^4 - 6 u^2 / x^5 + u^3 / x^6) * exp(-u / x)`. -/
def expInvCut₃ (u x : ℝ) : ℝ :=
  if 0 < x then (6 * u / x ^ 4 - 6 * u ^ 2 / x ^ 5 + u ^ 3 / x ^ 6) * Real.exp (-u / x) else 0

/-- For `u > 0`, `k : ℕ`, and `x > 0`, `x^(-k) * exp(-u / x) ≤ k! / u^k`. -/
lemma inv_pow_mul_exp_neg_div_le {u : ℝ} (hu : 0 < u) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    x ^ (-(k : ℤ)) * Real.exp (-u / x) ≤ (k.factorial : ℝ) / u ^ k := by
  have hy : 0 < u / x := div_pos hu hx
  have hfac := Real.pow_div_factorial_le_exp (u / x) hy.le k
  have hpow : x ^ (-(k : ℤ)) = (u / x) ^ k / u ^ k := by
    rw [zpow_neg, zpow_natCast, div_pow]
    field_simp [hu.ne', hx.ne']
  rw [hpow, show -u / x = -(u / x) by ring, Real.exp_neg]
  have h1 : (u / x) ^ k ≤ (k.factorial : ℝ) * Real.exp (u / x) := by
    rw [mul_comm]; exact (div_le_iff₀ (by positivity)).mp hfac
  calc (u / x) ^ k / u ^ k * (Real.exp (u / x))⁻¹
      ≤ ((k.factorial : ℝ) * Real.exp (u / x)) / u ^ k * (Real.exp (u / x))⁻¹ := by gcongr
    _ = (k.factorial : ℝ) / u ^ k := by
        have he : Real.exp (u / x) ≠ 0 := Real.exp_ne_zero _
        field_simp

/-- For `u > 0` and `k : ℕ`, `x^(-k) * exp(-u/x) → 0` as `x → 0⁺`. -/
lemma tendsto_inv_pow_mul_exp_neg_div_zero {u : ℝ} (hu : 0 < u) (k : ℕ) :
    Tendsto (fun x : ℝ => x ^ (-(k : ℤ)) * Real.exp (-u / x)) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hbd : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ x ^ (-(k : ℤ)) * Real.exp (-u / x) ∧
      x ^ (-(k : ℤ)) * Real.exp (-u / x) ≤ ((k + 1).factorial : ℝ) / u ^ (k + 1) * x := by
    intro x hx
    refine ⟨mul_nonneg (zpow_nonneg hx.le _) (Real.exp_pos _).le, ?_⟩
    have h1 := inv_pow_mul_exp_neg_div_le hu (k + 1) hx
    have heq : x ^ (-((k + 1 : ℕ) : ℤ)) = x ^ (-(k : ℤ)) * x⁻¹ := by
      rw [Nat.cast_add, Nat.cast_one, neg_add, zpow_add₀ hx.ne', zpow_neg_one]
    rw [heq] at h1
    have hx0 : 0 ≤ x := hx.le
    calc x ^ (-(k : ℤ)) * Real.exp (-u / x)
        = (x ^ (-(k : ℤ)) * x⁻¹ * Real.exp (-u / x)) * x := by field_simp [hx.ne']
      _ ≤ (((k + 1).factorial : ℝ) / u ^ (k + 1)) * x :=
          mul_le_mul_of_nonneg_right (by simpa [mul_assoc] using h1) hx0
  have hlim : Tendsto (fun x : ℝ => ((k + 1).factorial : ℝ) / u ^ (k + 1) * x)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hc : Continuous (fun x : ℝ => ((k + 1).factorial : ℝ) / u ^ (k + 1) * x) :=
      continuous_const.mul continuous_id
    have h0 := (hc.continuousAt (x := 0)).tendsto
    simpa using h0.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (eventually_nhdsWithin_of_forall fun x hx => (hbd x hx).1)
    (eventually_nhdsWithin_of_forall fun x hx => (hbd x hx).2)

private lemma hasDerivAt_zero_of_eq_zero_nonpos {f : ℝ → ℝ} (hf0 : ∀ x ≤ 0, f x = 0)
    (hlim : Tendsto (fun x => x⁻¹ * f x) (nhdsWithin 0 (Ioi 0)) (nhds 0)) :
    HasDerivAt f 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have h0 : f 0 = 0 := hf0 0 le_rfl
  have heq : slope f 0 = fun x => x⁻¹ * f x := by
    funext x; simp [slope_def_field, h0, div_eq_inv_mul]
  rw [heq]
  have hleft : Tendsto (fun x : ℝ => x⁻¹ * f x) (nhdsWithin 0 (Iio 0)) (nhds 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp [hf0 x (le_of_lt hx)]
  have hsplit : nhdsWithin (0 : ℝ) {0}ᶜ = nhdsWithin 0 (Iio 0) ⊔ nhdsWithin 0 (Ioi 0) := by
    rw [← nhdsWithin_union, Iio_union_Ioi]
  rw [hsplit]
  exact hleft.sup hlim

private lemma hasDerivAt_exp_neg_div {u x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y => Real.exp (-u / y)) (Real.exp (-u / x) * (u / x ^ 2)) x := by
  have h := (hasDerivAt_inv hx).const_mul (-u)
  convert h.exp using 1
  · funext y; simp [div_eq_mul_inv]
  · field_simp

lemma hasDerivAt_expInvCut {u : ℝ} (hu : 0 < u) (x : ℝ) :
    HasDerivAt (expInvCut u) (expInvCut₁ u x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hev : expInvCut u =ᶠ[nhds x] fun _ => 0 :=
      (eventually_lt_nhds hx).mono fun y hy => by simp [expInvCut, hy.le]
    have hxle : ¬ 0 < x := not_lt.mpr hx.le
    simpa [expInvCut₁, hxle] using (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev
  · simp only [expInvCut₁, lt_irrefl, ↓reduceIte]
    refine hasDerivAt_zero_of_eq_zero_nonpos (fun y hy => by simp [expInvCut, hy]) ?_
    refine (tendsto_inv_pow_mul_exp_neg_div_zero hu 1).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp [expInvCut, mem_Ioi.mp hy]
  · have hev : expInvCut u =ᶠ[nhds x] fun y => Real.exp (-u / y) :=
      (eventually_gt_nhds hx).mono fun y hy => by simp [expInvCut, hy]
    have hd := (hasDerivAt_exp_neg_div hx.ne').congr_of_eventuallyEq hev
    convert hd using 1
    simp [expInvCut₁, hx]; ring

lemma hasDerivAt_expInvCut₁ {u : ℝ} (hu : 0 < u) (x : ℝ) :
    HasDerivAt (expInvCut₁ u) (expInvCut₂ u x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hev : expInvCut₁ u =ᶠ[nhds x] fun _ => 0 :=
      (eventually_lt_nhds hx).mono fun y hy => by simp [expInvCut₁, hy.le]
    have hxle : ¬ 0 < x := not_lt.mpr hx.le
    simpa [expInvCut₂, hxle] using (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev
  · simp only [expInvCut₂, lt_irrefl, ↓reduceIte]
    refine hasDerivAt_zero_of_eq_zero_nonpos (fun y hy => by simp [expInvCut₁, hy]) ?_
    have hlim : Tendsto (fun y : ℝ => u * (y ^ (-(3 : ℤ)) * Real.exp (-u / y)))
        (nhdsWithin 0 (Ioi 0)) (nhds (u * 0)) :=
      tendsto_const_nhds.mul (tendsto_inv_pow_mul_exp_neg_div_zero hu 3)
    rw [mul_zero] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : (0 : ℝ) < y := hy
    simp only [expInvCut₁, hy0, ↓reduceIte]
    have hz : y ^ (-3 : ℤ) = (y ^ 3)⁻¹ := by rw [← zpow_natCast]; exact zpow_neg y 3
    rw [hz]
    field_simp [hy0.ne']
  · have hev : expInvCut₁ u =ᶠ[nhds x] fun y => (u / y ^ 2) * Real.exp (-u / y) :=
      (eventually_gt_nhds hx).mono fun y hy => by simp [expInvCut₁, hy]
    have hd1 : HasDerivAt (fun y => u / y ^ 2) (-2 * u / x ^ 3) x := by
      have h := (((hasDerivAt_pow 2 x).inv (pow_ne_zero 2 hx.ne')).const_mul u)
      convert h using 1
      · funext y; simp [div_eq_mul_inv]
      · simp only [Nat.cast_ofNat]; field_simp [hx.ne']; ring
    have hd := (hd1.mul (hasDerivAt_exp_neg_div hx.ne')).congr_of_eventuallyEq hev
    convert hd using 1
    simp only [expInvCut₂, hx, ↓reduceIte]
    field_simp [hx.ne']

lemma hasDerivAt_expInvCut₂ {u : ℝ} (hu : 0 < u) (x : ℝ) :
    HasDerivAt (expInvCut₂ u) (expInvCut₃ u x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hev : expInvCut₂ u =ᶠ[nhds x] fun _ => 0 :=
      (eventually_lt_nhds hx).mono fun y hy => by simp [expInvCut₂, hy.le]
    have hxle : ¬ 0 < x := not_lt.mpr hx.le
    simpa [expInvCut₃, hxle] using (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev
  · simp only [expInvCut₃, lt_irrefl, ↓reduceIte]
    refine hasDerivAt_zero_of_eq_zero_nonpos (fun y hy => by simp [expInvCut₂, hy]) ?_
    have h1 := tendsto_const_nhds.mul (tendsto_inv_pow_mul_exp_neg_div_zero hu 4)
      (a := (-2 * u))
    have h2 := tendsto_const_nhds.mul (tendsto_inv_pow_mul_exp_neg_div_zero hu 5)
      (a := u ^ 2)
    have hsum : Tendsto (fun y : ℝ =>
        (-2 * u) * (y ^ (-(4 : ℤ)) * Real.exp (-u / y)) +
          u ^ 2 * (y ^ (-(5 : ℤ)) * Real.exp (-u / y)))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      simpa using h1.add h2
    refine hsum.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : (0 : ℝ) < y := hy
    simp only [expInvCut₂, hy0, ↓reduceIte]
    have hz4 : y ^ (-4 : ℤ) = (y ^ 4)⁻¹ := by rw [← zpow_natCast]; exact zpow_neg y 4
    have hz5 : y ^ (-5 : ℤ) = (y ^ 5)⁻¹ := by rw [← zpow_natCast]; exact zpow_neg y 5
    rw [hz4, hz5]
    field_simp [hy0.ne']
  · have hev : expInvCut₂ u =ᶠ[nhds x] fun y => (-2 * u / y ^ 3 + u ^ 2 / y ^ 4) * Real.exp (-u / y) :=
      (eventually_gt_nhds hx).mono fun y hy => by simp [expInvCut₂, hy]
    have hd1 : HasDerivAt (fun y => -2 * u / y ^ 3 + u ^ 2 / y ^ 4)
        (6 * u / x ^ 4 - 4 * u ^ 2 / x ^ 5) x := by
      have ha := (((hasDerivAt_pow 3 x).inv (pow_ne_zero 3 hx.ne')).const_mul (-2 * u))
      have hb := (((hasDerivAt_pow 4 x).inv (pow_ne_zero 4 hx.ne')).const_mul (u ^ 2))
      convert ha.add hb using 1
      · funext y; simp [div_eq_mul_inv]
      · simp only [Nat.cast_ofNat]; field_simp [hx.ne']; ring
    have hd := (hd1.mul (hasDerivAt_exp_neg_div hx.ne')).congr_of_eventuallyEq hev
    convert hd using 1
    simp only [expInvCut₃, hx, ↓reduceIte]
    field_simp [hx.ne']; ring

/-- Bounds on `expInvCut` and its first 3 derivatives on all of `ℝ` for `u > 0`. -/
lemma expInvCut_bounds {u : ℝ} (hu : 0 < u) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ x, |expInvCut u x| ≤ C) ∧
      (∀ x, |expInvCut₁ u x| ≤ C) ∧
      (∀ x, |expInvCut₂ u x| ≤ C) ∧
      (∀ x, |expInvCut₃ u x| ≤ C) := by
  let C0 : ℝ := 1
  let C1 : ℝ := u * (2 / u ^ 2)
  let C2 : ℝ := 2 * u * (6 / u ^ 3) + u ^ 2 * (24 / u ^ 4)
  let C3 : ℝ := 6 * u * (24 / u ^ 4) + 6 * u ^ 2 * (120 / u ^ 5) + u ^ 3 * (720 / u ^ 6)
  refine ⟨max C0 (max C1 (max C2 C3)), le_trans (by positivity) (le_max_left _ _), ?_, ?_, ?_, ?_⟩
  · intro x
    refine le_trans ?_ (le_max_left _ _)
    by_cases hx : 0 < x
    · simp only [expInvCut, hx, ↓reduceIte, abs_of_pos (Real.exp_pos _)]
      exact (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu.le) hx.le))
    · simp [expInvCut, hx, C0]
  · intro x
    refine le_trans ?_ (le_trans (le_max_left _ _) (le_max_right _ _))
    by_cases hx : 0 < x
    · simp only [expInvCut₁, hx, ↓reduceIte, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_of_pos (div_pos hu (pow_pos hx 2))]
      have h2 := inv_pow_mul_exp_neg_div_le hu 2 hx
      rw [zpow_neg, zpow_natCast] at h2
      calc u / x ^ 2 * Real.exp (-u / x)
          = u * ((x ^ 2)⁻¹ * Real.exp (-u / x)) := by ring
        _ ≤ u * ((Nat.factorial 2 : ℝ) / u ^ 2) := mul_le_mul_of_nonneg_left h2 hu.le
        _ = C1 := by norm_num [C1]
    · simp [expInvCut₁, hx]; positivity
  · intro x
    refine le_trans ?_ (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _))
    by_cases hx : 0 < x
    · simp only [expInvCut₂, hx, ↓reduceIte, abs_mul, abs_of_pos (Real.exp_pos _)]
      have h3 := inv_pow_mul_exp_neg_div_le hu 3 hx
      have h4 := inv_pow_mul_exp_neg_div_le hu 4 hx
      rw [zpow_neg, zpow_natCast] at h3 h4
      have htri : |-2 * u / x ^ 3 + u ^ 2 / x ^ 4| ≤ 2 * u * (x ^ 3)⁻¹ + u ^ 2 * (x ^ 4)⁻¹ := by
        calc |-2 * u / x ^ 3 + u ^ 2 / x ^ 4|
            ≤ |-2 * u / x ^ 3| + |u ^ 2 / x ^ 4| := abs_add_le _ _
          _ = 2 * u * (x ^ 3)⁻¹ + u ^ 2 * (x ^ 4)⁻¹ := by
              rw [abs_div, abs_div, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
                abs_of_pos hu, abs_of_pos (pow_pos hx 3), abs_of_pos (sq_pos_of_pos hu),
                abs_of_pos (pow_pos hx 4), div_eq_mul_inv, div_eq_mul_inv]
      calc |-2 * u / x ^ 3 + u ^ 2 / x ^ 4| * Real.exp (-u / x)
          ≤ (2 * u * (x ^ 3)⁻¹ + u ^ 2 * (x ^ 4)⁻¹) * Real.exp (-u / x) :=
            mul_le_mul_of_nonneg_right htri (Real.exp_pos _).le
        _ = 2 * u * ((x ^ 3)⁻¹ * Real.exp (-u / x)) + u ^ 2 * ((x ^ 4)⁻¹ * Real.exp (-u / x)) := by ring
        _ ≤ 2 * u * ((Nat.factorial 3 : ℝ) / u ^ 3) + u ^ 2 * ((Nat.factorial 4 : ℝ) / u ^ 4) := by
            gcongr
        _ = C2 := by norm_num [C2]
    · simp [expInvCut₂, hx]; positivity
  · intro x
    refine le_trans ?_ (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _))
    by_cases hx : 0 < x
    · simp only [expInvCut₃, hx, ↓reduceIte, abs_mul, abs_of_pos (Real.exp_pos _)]
      have h4 := inv_pow_mul_exp_neg_div_le hu 4 hx
      have h5 := inv_pow_mul_exp_neg_div_le hu 5 hx
      have h6 := inv_pow_mul_exp_neg_div_le hu 6 hx
      rw [zpow_neg, zpow_natCast] at h4 h5 h6
      have htri : |6 * u / x ^ 4 - 6 * u ^ 2 / x ^ 5 + u ^ 3 / x ^ 6| ≤
          6 * u * (x ^ 4)⁻¹ + 6 * u ^ 2 * (x ^ 5)⁻¹ + u ^ 3 * (x ^ 6)⁻¹ := by
        calc |6 * u / x ^ 4 - 6 * u ^ 2 / x ^ 5 + u ^ 3 / x ^ 6|
            ≤ |6 * u / x ^ 4 - 6 * u ^ 2 / x ^ 5| + |u ^ 3 / x ^ 6| := abs_add_le _ _
          _ ≤ (|6 * u / x ^ 4| + |6 * u ^ 2 / x ^ 5|) + |u ^ 3 / x ^ 6| := by
              gcongr; exact abs_sub _ _
          _ = 6 * u * (x ^ 4)⁻¹ + 6 * u ^ 2 * (x ^ 5)⁻¹ + u ^ 3 * (x ^ 6)⁻¹ := by
              rw [abs_div, abs_div, abs_div, abs_of_pos (by positivity : 0 < 6 * u),
                abs_of_pos (pow_pos hx 4), abs_of_pos (by positivity : 0 < 6 * u ^ 2),
                abs_of_pos (pow_pos hx 5), abs_of_pos (pow_pos hu 3),
                abs_of_pos (pow_pos hx 6), div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
      calc |6 * u / x ^ 4 - 6 * u ^ 2 / x ^ 5 + u ^ 3 / x ^ 6| * Real.exp (-u / x)
          ≤ (6 * u * (x ^ 4)⁻¹ + 6 * u ^ 2 * (x ^ 5)⁻¹ + u ^ 3 * (x ^ 6)⁻¹) * Real.exp (-u / x) :=
            mul_le_mul_of_nonneg_right htri (Real.exp_pos _).le
        _ = 6 * u * ((x ^ 4)⁻¹ * Real.exp (-u / x)) +
              6 * u ^ 2 * ((x ^ 5)⁻¹ * Real.exp (-u / x)) +
              u ^ 3 * ((x ^ 6)⁻¹ * Real.exp (-u / x)) := by ring
        _ ≤ 6 * u * ((Nat.factorial 4 : ℝ) / u ^ 4) +
              6 * u ^ 2 * ((Nat.factorial 5 : ℝ) / u ^ 5) +
              u ^ 3 * ((Nat.factorial 6 : ℝ) / u ^ 6) := by
            gcongr
        _ = C3 := by norm_num [C3]
    · simp [expInvCut₃, hx]; positivity

/-- Uniform-in-`u` bounds on `x * expInvCut₁ u x`, `x^2 * expInvCut₂ u x`, `x^3 * expInvCut₃ u x`. -/
lemma mul_expInvCut_bounds {u : ℝ} (hu : 0 < u) :
    (∀ x, |x * expInvCut₁ u x| ≤ 1) ∧
    (∀ x, |x ^ 2 * expInvCut₂ u x| ≤ 4) ∧
    (∀ x, |x ^ 3 * expInvCut₃ u x| ≤ 30) := by
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_⟩
  · by_cases hx : 0 < x
    · simp only [expInvCut₁, hx, ↓reduceIte]
      have h1 := inv_pow_mul_exp_neg_div_le hu 1 hx
      simp only [Nat.cast_one, zpow_neg_one] at h1
      have heq : x * (u / x ^ 2 * Real.exp (-u / x)) = u * (x⁻¹ * Real.exp (-u / x)) := by
        field_simp [hx.ne']
      rw [heq, abs_of_nonneg (mul_nonneg hu.le (mul_nonneg (inv_nonneg.mpr hx.le) (Real.exp_pos _).le))]
      calc u * (x⁻¹ * Real.exp (-u / x)) ≤ u * ((Nat.factorial 1 : ℝ) / u ^ 1) :=
            mul_le_mul_of_nonneg_left h1 hu.le
        _ = 1 := by simp [hu.ne']
    · simp [expInvCut₁, hx]
  · by_cases hx : 0 < x
    · simp only [expInvCut₂, hx, ↓reduceIte]
      have h1 := inv_pow_mul_exp_neg_div_le hu 1 hx
      have h2 := inv_pow_mul_exp_neg_div_le hu 2 hx
      simp only [Nat.cast_one, zpow_neg_one] at h1
      have hz2 : x ^ (-((2 : ℕ) : ℤ)) = (x ^ 2)⁻¹ := by rw [zpow_neg, zpow_natCast]
      rw [hz2] at h2
      have heq : x ^ 2 * ((-2 * u / x ^ 3 + u ^ 2 / x ^ 4) * Real.exp (-u / x)) =
          -2 * u * (x⁻¹ * Real.exp (-u / x)) + u ^ 2 * ((x ^ 2)⁻¹ * Real.exp (-u / x)) := by
        field_simp [hx.ne']
      rw [heq]
      calc |-2 * u * (x⁻¹ * Real.exp (-u / x)) + u ^ 2 * ((x ^ 2)⁻¹ * Real.exp (-u / x))|
          ≤ 2 * u * (x⁻¹ * Real.exp (-u / x)) + u ^ 2 * ((x ^ 2)⁻¹ * Real.exp (-u / x)) := by
            refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
            · rw [abs_mul, abs_mul, abs_neg, abs_of_pos two_pos, abs_of_pos hu,
                abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hx.le) (Real.exp_pos _).le)]
            · rw [abs_mul, abs_of_pos (sq_pos_of_pos hu),
                abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (sq_nonneg x)) (Real.exp_pos _).le)]
        _ ≤ 2 * u * ((Nat.factorial 1 : ℝ) / u ^ 1) + u ^ 2 * ((Nat.factorial 2 : ℝ) / u ^ 2) := by
            gcongr
        _ = 4 := by norm_num; field_simp [hu.ne']; ring
    · simp [expInvCut₂, hx]
  · by_cases hx : 0 < x
    · simp only [expInvCut₃, hx, ↓reduceIte]
      have h1 := inv_pow_mul_exp_neg_div_le hu 1 hx
      have h2 := inv_pow_mul_exp_neg_div_le hu 2 hx
      have h3 := inv_pow_mul_exp_neg_div_le hu 3 hx
      simp only [Nat.cast_one, zpow_neg_one] at h1
      have hz2 : x ^ (-((2 : ℕ) : ℤ)) = (x ^ 2)⁻¹ := by rw [zpow_neg, zpow_natCast]
      have hz3 : x ^ (-((3 : ℕ) : ℤ)) = (x ^ 3)⁻¹ := by rw [zpow_neg, zpow_natCast]
      rw [hz2] at h2
      rw [hz3] at h3
      have heq : x ^ 3 * ((6 * u / x ^ 4 - 6 * u ^ 2 / x ^ 5 + u ^ 3 / x ^ 6) * Real.exp (-u / x)) =
          6 * u * (x⁻¹ * Real.exp (-u / x)) - 6 * u ^ 2 * ((x ^ 2)⁻¹ * Real.exp (-u / x)) +
            u ^ 3 * ((x ^ 3)⁻¹ * Real.exp (-u / x)) := by
        field_simp [hx.ne']
      rw [heq]
      calc |6 * u * (x⁻¹ * Real.exp (-u / x)) - 6 * u ^ 2 * ((x ^ 2)⁻¹ * Real.exp (-u / x)) +
              u ^ 3 * ((x ^ 3)⁻¹ * Real.exp (-u / x))|
          ≤ 6 * u * (x⁻¹ * Real.exp (-u / x)) + 6 * u ^ 2 * ((x ^ 2)⁻¹ * Real.exp (-u / x)) +
              u ^ 3 * ((x ^ 3)⁻¹ * Real.exp (-u / x)) := by
            refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add ?_ ?_)) ?_)
            · rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6), abs_of_pos hu,
                abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hx.le) (Real.exp_pos _).le)]
            · rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6),
                abs_of_pos (sq_pos_of_pos hu),
                abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (sq_nonneg x)) (Real.exp_pos _).le)]
            · rw [abs_mul, abs_of_pos (pow_pos hu 3),
                abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (pow_nonneg hx.le 3)) (Real.exp_pos _).le)]
        _ ≤ 6 * u * ((Nat.factorial 1 : ℝ) / u ^ 1) + 6 * u ^ 2 * ((Nat.factorial 2 : ℝ) / u ^ 2) +
              u ^ 3 * ((Nat.factorial 3 : ℝ) / u ^ 3) := by
            gcongr
        _ ≤ 30 := by
            have hfac1 : (Nat.factorial 1 : ℝ) = 1 := by norm_num
            have hfac2 : (Nat.factorial 2 : ℝ) = 2 := by norm_num
            have hfac3 : (Nat.factorial 3 : ℝ) = 6 := by norm_num
            rw [hfac1, hfac2, hfac3]
            have : 6 * u * (1 / u ^ 1) + 6 * u ^ 2 * (2 / u ^ 2) + u ^ 3 * (6 / u ^ 3) = 24 := by
              field_simp [hu.ne']; ring
            linarith
    · simp [expInvCut₃, hx]

lemma continuous_expInvCut {u : ℝ} (hu : 0 < u) :
    Continuous (expInvCut u) ∧ Continuous (expInvCut₁ u) ∧ Continuous (expInvCut₂ u) :=
  ⟨continuous_iff_continuousAt.mpr fun x => (hasDerivAt_expInvCut hu x).continuousAt,
   continuous_iff_continuousAt.mpr fun x => (hasDerivAt_expInvCut₁ hu x).continuousAt,
   continuous_iff_continuousAt.mpr fun x => (hasDerivAt_expInvCut₂ hu x).continuousAt⟩

/-- Compactly supported `C^3` functions on `ℝ` have global bounds on `ψ, ψ', ψ'', ψ'''`. -/
lemma contDiff_three_compactSupport_bounds {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 3 ψ)
    (hψC : HasCompactSupport ψ) :
    ∃ C R : ℝ, 0 ≤ C ∧ 0 < R ∧
      (∀ y, R ≤ |y| → ψ y = 0 ∧ deriv ψ y = 0 ∧
        deriv (deriv ψ) y = 0 ∧ deriv (deriv (deriv ψ)) y = 0) ∧
      (∀ y, |ψ y| ≤ C) ∧ (∀ y, |deriv ψ y| ≤ C) ∧
      (∀ y, |deriv (deriv ψ) y| ≤ C) ∧ (∀ y, |deriv (deriv (deriv ψ)) y| ≤ C) := by
  have hd1 : ContDiff ℝ 2 (deriv ψ) := ((contDiff_succ_iff_deriv (n := 2)).mp hψ).2.2
  have hd2 : ContDiff ℝ 1 (deriv (deriv ψ)) := ((contDiff_succ_iff_deriv (n := 1)).mp hd1).2.2
  have hc0 : Continuous ψ := hψ.continuous
  have hc1 : Continuous (deriv ψ) := hd1.continuous
  have hc2 : Continuous (deriv (deriv ψ)) := hd2.continuous
  have hc3 : Continuous (deriv (deriv (deriv ψ))) := ContDiff.continuous_deriv_one hd2
  obtain ⟨A0, hA0⟩ := hc0.bounded_above_of_compact_support hψC
  obtain ⟨A1, hA1⟩ := hc1.bounded_above_of_compact_support hψC.deriv
  obtain ⟨A2, hA2⟩ := hc2.bounded_above_of_compact_support hψC.deriv.deriv
  obtain ⟨A3, hA3⟩ := hc3.bounded_above_of_compact_support hψC.deriv.deriv.deriv
  obtain ⟨R₁, hR₁⟩ := (hψC.isCompact.image continuous_abs).bddAbove
  refine ⟨max A0 (max A1 (max A2 A3)), max R₁ 0 + 1,
    le_trans (abs_nonneg (ψ 0)) (le_trans (by simpa [Real.norm_eq_abs] using hA0 0) (le_max_left _ _)),
    by positivity, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have hnot : y ∉ tsupport ψ := fun hmem => by
      have : |y| ≤ R₁ := hR₁ (mem_image_of_mem _ hmem)
      linarith [le_max_left R₁ 0]
    have hev0 : ψ =ᶠ[nhds y] 0 := notMem_tsupport_iff_eventuallyEq.mp hnot
    have hev1 : deriv ψ =ᶠ[nhds y] 0 := by simpa [deriv_const'] using hev0.deriv
    have hev2 : deriv (deriv ψ) =ᶠ[nhds y] 0 := by simpa [deriv_const'] using hev1.deriv
    have hev3 : deriv (deriv (deriv ψ)) =ᶠ[nhds y] 0 := by simpa [deriv_const'] using hev2.deriv
    exact ⟨hev0.eq_of_nhds, hev1.eq_of_nhds, hev2.eq_of_nhds, hev3.eq_of_nhds⟩
  · intro y; exact le_trans (by simpa [Real.norm_eq_abs] using hA0 y) (le_max_left _ _)
  · intro y; exact le_trans (by simpa [Real.norm_eq_abs] using hA1 y)
      (le_trans (le_max_left _ _) (le_max_right _ _))
  · intro y; exact le_trans (by simpa [Real.norm_eq_abs] using hA2 y)
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _))
  · intro y; exact le_trans (by simpa [Real.norm_eq_abs] using hA3 y)
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _))

end ExpInvCutoff

end Lyasoff2016
