/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Analytic regularity (`C^∞` on `(0, ∞) × ℝ`), boundary limits at `0⁺` and `∞`,
Gaussian-weighted `L¹` moment bounds for all mixed partials `pd m n`,
and scaling to arbitrary `σ > 0` for Yor's conditional density, yielding a
constructive, axiom-free proof of `prop_2_2`.
-/
module

public import Lyasoff2016.YorKernel
public import Lyasoff2016.BrownianScaling
public import Lyasoff2016.YorDensity

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real Nat

noncomputable section
namespace Lyasoff2016

section CondDensityDef

/-- Explicit conditional density `φc(x, y) = yorDensity τ x y / gaussianPDFReal 0 τ y`
for `σ = 2` and `τ > 0`, extended by `0` on `x ≤ 0`. -/
def yorCondDensity (τ x y : ℝ) : ℝ :=
  if 0 < x then
    (Real.exp (Real.pi ^ 2 / (2 * τ)) / Real.pi) *
      Real.exp (y ^ 2 / (2 * τ) - (1 + Real.exp (2 * y)) / (2 * x) + y) *
      x ^ (-2 : ℤ) * Jm τ 0 (Real.exp y / x)
  else 0

lemma gaussianPDFReal_mul_yorCondDensity {τ : ℝ≥0} (hτ : 0 < τ) (x y : ℝ) :
    gaussianPDFReal 0 τ y * yorCondDensity (τ : ℝ) x y = yorDensity (τ : ℝ) x y := by
  have hτR : (0 : ℝ) < τ := hτ
  by_cases hx : 0 < x
  · have hx0 : x ≠ 0 := hx.ne'
    have hpi : 0 < Real.pi := Real.pi_pos
    have hsqrt_eq : Real.sqrt (2 * Real.pi ^ 3 * τ) = Real.pi * Real.sqrt (2 * Real.pi * τ) := by
      rw [show 2 * Real.pi ^ 3 * (τ : ℝ) = Real.pi ^ 2 * (2 * Real.pi * τ) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hpi.le]
    have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi * τ) := Real.sqrt_pos.mpr (by positivity)
    let I := ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * (τ : ℝ))) *
      Real.exp (-(Real.exp y / x) * Real.cosh u) * Real.sinh u * Real.sin (Real.pi * u / τ)
    have hJm0 : Jm (τ : ℝ) 0 (Real.exp y / x) = I := by
      unfold Jm
      simp only [pow_zero, one_mul, I]
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      rw [← Real.exp_add, sub_eq_add_neg, neg_mul]
    rw [gaussianPDFReal_def]
    simp only [sub_zero, yorCondDensity, hx, ↓reduceIte, yorDensity, theta, hJm0, hsqrt_eq]
    have hexp_comb :
        Real.exp (-y ^ 2 / (2 * (τ : ℝ))) *
          Real.exp (y ^ 2 / (2 * (τ : ℝ)) - (1 + Real.exp (2 * y)) / (2 * x) + y) =
        Real.exp (-(1 + Real.exp (2 * y)) / (2 * x)) * Real.exp y := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    have hpre : (Real.sqrt (2 * Real.pi * τ))⁻¹ * Real.pi⁻¹ * (x ^ 2)⁻¹ *
          Real.exp (Real.pi ^ 2 / (2 * (τ : ℝ))) *
          (Real.exp (-(1 + Real.exp (2 * y)) / (2 * x)) * Real.exp y) =
        1 / x * Real.exp (-(1 + Real.exp (2 * y)) / (2 * x)) *
          (Real.exp y / x / (Real.pi * Real.sqrt (2 * Real.pi * τ)) *
            Real.exp (Real.pi ^ 2 / (2 * (τ : ℝ)))) := by
      field_simp [hpi.ne', hsqrt_pos.ne', hx0]
    show (Real.sqrt (2 * Real.pi * τ))⁻¹ * Real.exp (-y ^ 2 / (2 * (τ : ℝ))) *
          ((Real.exp (Real.pi ^ 2 / (2 * (τ : ℝ))) / Real.pi) *
            Real.exp (y ^ 2 / (2 * (τ : ℝ)) - (1 + Real.exp (2 * y)) / (2 * x) + y) *
            (x ^ 2)⁻¹ * I) =
        1 / x * Real.exp (-(1 + Real.exp (2 * y)) / (2 * x)) *
          (Real.exp y / x / (Real.pi * Real.sqrt (2 * Real.pi * τ)) *
            Real.exp (Real.pi ^ 2 / (2 * (τ : ℝ))) * I)
    calc (Real.sqrt (2 * Real.pi * τ))⁻¹ * Real.exp (-y ^ 2 / (2 * (τ : ℝ))) *
          ((Real.exp (Real.pi ^ 2 / (2 * (τ : ℝ))) / Real.pi) *
            Real.exp (y ^ 2 / (2 * (τ : ℝ)) - (1 + Real.exp (2 * y)) / (2 * x) + y) *
            (x ^ 2)⁻¹ * I)
        = ((Real.sqrt (2 * Real.pi * τ))⁻¹ * Real.pi⁻¹ * (x ^ 2)⁻¹ *
            Real.exp (Real.pi ^ 2 / (2 * (τ : ℝ))) *
            (Real.exp (-y ^ 2 / (2 * (τ : ℝ))) *
              Real.exp (y ^ 2 / (2 * (τ : ℝ)) - (1 + Real.exp (2 * y)) / (2 * x) + y))) * I := by ring
      _ = ((Real.sqrt (2 * Real.pi * τ))⁻¹ * Real.pi⁻¹ * (x ^ 2)⁻¹ *
            Real.exp (Real.pi ^ 2 / (2 * (τ : ℝ))) *
            (Real.exp (-(1 + Real.exp (2 * y)) / (2 * x)) * Real.exp y)) * I := by rw [hexp_comb]
      _ = (1 / x * Real.exp (-(1 + Real.exp (2 * y)) / (2 * x)) *
            (Real.exp y / x / (Real.pi * Real.sqrt (2 * Real.pi * τ)) *
              Real.exp (Real.pi ^ 2 / (2 * (τ : ℝ))))) * I := by rw [hpre]
      _ = _ := by ring
  · simp only [yorCondDensity, hx, ↓reduceIte, mul_zero,
      yorDensity_zero_of_nonpos hτR (not_lt.mp hx) y]

lemma yor_cond_density {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (τ : ℝ≥0) (hτ : 0 < τ) :
    IsCondDensity P W 2 τ (yorCondDensity (τ : ℝ)) := by
  unfold IsCondDensity
  have h := yor_joint_density P W hW τ hτ
  simpa only [gaussianPDFReal_mul_yorCondDensity hτ] using h

/-- `yorCondDensity τ` is `C^∞` on `(0, ∞) × ℝ` for every `τ > 0`. -/
lemma yorCondDensity_contDiffOn {τ : ℝ} (hτ : 0 < τ) (N : ℕ) :
    ContDiffOn ℝ N (Function.uncurry (yorCondDensity τ)) (Ioi (0 : ℝ) ×ˢ univ) := by
  let g : ℝ × ℝ → ℝ := fun p =>
    (Real.exp (Real.pi ^ 2 / (2 * τ)) / Real.pi) *
      Real.exp (p.2 ^ 2 / (2 * τ) - (1 + Real.exp (2 * p.2)) / (2 * p.1) + p.2) *
      (p.1 ^ 2)⁻¹ * Jm τ 0 (Real.exp p.2 / p.1)
  have hg_eq : EqOn (Function.uncurry (yorCondDensity τ)) g (Ioi (0 : ℝ) ×ˢ univ) := by
    intro p hp
    have hx : 0 < p.1 := hp.1
    simp [Function.uncurry, yorCondDensity, hx, g]
  refine ContDiffOn.congr ?_ hg_eq
  have h1 : ContDiffOn ℝ N (fun p : ℝ × ℝ =>
      p.2 ^ 2 / (2 * τ) - (1 + Real.exp (2 * p.2)) / (2 * p.1) + p.2) (Ioi (0 : ℝ) ×ˢ univ) := by
    refine (((contDiffOn_snd.pow 2).div_const (2 * τ)).sub ?_).add contDiffOn_snd
    refine (contDiffOn_const.add ((contDiffOn_const.mul contDiffOn_snd).exp)).div
      (contDiffOn_const.mul contDiffOn_fst)
      (fun p (hp : p ∈ Ioi (0 : ℝ) ×ˢ univ) => mul_ne_zero two_ne_zero (ne_of_gt hp.1))
  have h2 : ContDiffOn ℝ N (fun p : ℝ × ℝ => (p.1 ^ 2)⁻¹) (Ioi (0 : ℝ) ×ˢ univ) :=
    (contDiffOn_fst.pow 2).inv (fun p (hp : p ∈ Ioi (0 : ℝ) ×ˢ univ) => pow_ne_zero 2 (ne_of_gt hp.1))
  have h3 : ContDiffOn ℝ N (fun p : ℝ × ℝ => Jm τ 0 (Real.exp p.2 / p.1)) (Ioi (0 : ℝ) ×ˢ univ) :=
    (Jm_contDiffOn hτ N 0).comp
      ((contDiffOn_snd.exp).div contDiffOn_fst
        (fun p (hp : p ∈ Ioi (0 : ℝ) ×ˢ univ) => ne_of_gt hp.1))
      (fun p (hp : p ∈ Ioi (0 : ℝ) ×ˢ univ) => div_pos (Real.exp_pos _) hp.1)
  exact (((contDiffOn_const.mul h1.exp).mul h2).mul h3)

end CondDensityDef

section DerivativeFamily

/-- Basis term for all mixed partial derivatives `pd m n (yorCondDensity τ)` on `(0, ∞) × ℝ`. -/
def yorTerm (τ : ℝ) (a b d k : ℕ) (x y : ℝ) : ℝ :=
  y ^ a * Real.exp (b * y) * x ^ (-(d : ℤ)) *
    Real.exp (y ^ 2 / (2 * τ) - (1 + Real.exp (2 * y)) / (2 * x)) *
    Jm τ k (Real.exp y / x)

abbrev YorCoeff := ℝ × ℕ × ℕ × ℕ × ℕ

def evalYorSum (τ : ℝ) (L : List YorCoeff) (x y : ℝ) : ℝ :=
  (L.map fun q => q.1 * yorTerm τ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 x y).sum

lemma evalYorSum_nil (τ x y : ℝ) : evalYorSum τ [] x y = 0 := by simp [evalYorSum]

lemma evalYorSum_cons (τ : ℝ) (q : YorCoeff) (L : List YorCoeff) (x y : ℝ) :
    evalYorSum τ (q :: L) x y =
      q.1 * yorTerm τ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 x y + evalYorSum τ L x y := by
  simp [evalYorSum]

lemma evalYorSum_append (τ : ℝ) (L₁ L₂ : List YorCoeff) (x y : ℝ) :
    evalYorSum τ (L₁ ++ L₂) x y = evalYorSum τ L₁ x y + evalYorSum τ L₂ x y := by
  simp [evalYorSum, List.map_append, List.sum_append]

lemma evalYorSum_scale (τ c : ℝ) (L : List YorCoeff) (x y : ℝ) :
    evalYorSum τ (L.map fun q => (c * q.1, q.2)) x y = c * evalYorSum τ L x y := by
  induction L with
  | nil => simp [evalYorSum]
  | cons q L ih =>
      simp only [List.map_cons, evalYorSum_cons] at ih ⊢
      rw [ih]; ring

lemma yorTerm_contDiffOn_x {τ : ℝ} (hτ : 0 < τ) (a b d k N : ℕ) (y : ℝ) :
    ContDiffOn ℝ N (fun x => yorTerm τ a b d k x y) (Ioi 0) := by
  have h_eq : EqOn (fun x => yorTerm τ a b d k x y)
      (fun x => y ^ a * Real.exp (b * y) * (x ^ d)⁻¹ *
        Real.exp (y ^ 2 / (2 * τ) - (1 + Real.exp (2 * y)) / (2 * x)) *
        Jm τ k (Real.exp y / x)) (Ioi 0) := fun x _ => by
    simp only [yorTerm, zpow_neg, zpow_natCast]
  refine ContDiffOn.congr ?_ h_eq
  have h1 : ContDiffOn ℝ N (fun x : ℝ => (x ^ d)⁻¹) (Ioi 0) :=
    (contDiffOn_id.pow d).inv (fun x (hx : x ∈ Ioi (0 : ℝ)) => pow_ne_zero d (ne_of_gt hx))
  have h2 : ContDiffOn ℝ N
      (fun x : ℝ => Real.exp (y ^ 2 / (2 * τ) - (1 + Real.exp (2 * y)) / (2 * x))) (Ioi 0) :=
    (contDiffOn_const.sub (contDiffOn_const.div (contDiffOn_const.mul contDiffOn_id)
      (fun x (hx : x ∈ Ioi (0 : ℝ)) => mul_ne_zero two_ne_zero (ne_of_gt hx)))).exp
  have h3 : ContDiffOn ℝ N (fun x : ℝ => Jm τ k (Real.exp y / x)) (Ioi 0) :=
    (Jm_contDiffOn hτ N k).comp
      (contDiffOn_const.div contDiffOn_id (fun x (hx : x ∈ Ioi (0 : ℝ)) => ne_of_gt hx))
      (fun x (hx : x ∈ Ioi (0 : ℝ)) => div_pos (Real.exp_pos y) hx)
  exact (((contDiffOn_const.mul h1).mul h2).mul h3)

lemma evalYorSum_contDiffOn_x {τ : ℝ} (hτ : 0 < τ) (L : List YorCoeff) (N : ℕ) (y : ℝ) :
    ContDiffOn ℝ N (fun x => evalYorSum τ L x y) (Ioi 0) := by
  induction L with
  | nil => simpa [evalYorSum] using contDiffOn_const
  | cons q L ih =>
      have h_eq : (fun x => evalYorSum τ (q :: L) x y) =
          fun x => q.1 * yorTerm τ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 x y + evalYorSum τ L x y := by
        funext x; exact evalYorSum_cons τ q L x y
      rw [h_eq]
      exact (contDiffOn_const.mul (yorTerm_contDiffOn_x hτ _ _ _ _ N y)).add ih

def dYorTermY (τ : ℝ) (a b d k : ℕ) : List YorCoeff :=
  [ ((a : ℝ), a - 1, b, d, k),
    ((b : ℝ), a, b, d, k),
    (τ⁻¹, a + 1, b, d, k),
    (-1, a, b + 2, d + 1, k),
    (1, a, b + 1, d + 1, k + 1) ]

def dYorTermX (a b d k : ℕ) : List YorCoeff :=
  [ (-(d : ℝ), a, b, d + 1, k),
    (1 / 2, a, b, d + 2, k),
    (1 / 2, a, b + 2, d + 2, k),
    (-1, a, b + 1, d + 2, k + 1) ]

def dEvalYorSumY (τ : ℝ) (L : List YorCoeff) : List YorCoeff :=
  L.flatMap fun q => (dYorTermY τ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2).map fun r => (q.1 * r.1, r.2)

def dEvalYorSumX (L : List YorCoeff) : List YorCoeff :=
  L.flatMap fun q => (dYorTermX q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2).map fun r => (q.1 * r.1, r.2)

private lemma hasDerivAt_zpow_neg_nat (d : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun x' : ℝ => x' ^ (-(d : ℤ))) (-(d : ℝ) * x ^ (-((d + 1 : ℕ) : ℤ))) x := by
  have heq : (fun x' : ℝ => x' ^ (-(d : ℤ))) = fun x' => (x' ^ d)⁻¹ := by
    funext x'; rw [zpow_neg, zpow_natCast]
  rw [heq]
  have hd : HasDerivAt (fun x' : ℝ => (x' ^ d)⁻¹) (-((d : ℝ) * x ^ (d - 1)) / (x ^ d) ^ 2) x :=
    (hasDerivAt_pow d x).inv (pow_ne_zero d hx)
  convert hd using 1
  rw [zpow_neg, zpow_natCast]
  cases d with
  | zero => simp
  | succ k =>
      have hk : k + 1 - 1 = k := by omega
      rw [hk, pow_succ, pow_succ]
      field_simp [hx]

lemma yorTerm_hasDerivAt_y {τ : ℝ} (hτ : 0 < τ) (a b d k : ℕ) {x : ℝ} (hx : 0 < x) (y : ℝ) :
    HasDerivAt (fun y' => yorTerm τ a b d k x y')
      (evalYorSum τ (dYorTermY τ a b d k) x y) y := by
  have hτ0 : τ ≠ 0 := hτ.ne'
  have hx0 : x ≠ 0 := hx.ne'
  have hf1 : HasDerivAt (fun y' : ℝ => y' ^ a) ((a : ℝ) * y ^ (a - 1)) y := hasDerivAt_pow a y
  have hf2 : HasDerivAt (fun y' : ℝ => Real.exp ((b : ℝ) * y')) (Real.exp ((b : ℝ) * y) * b) y := by
    simpa using ((hasDerivAt_id' y).const_mul (b : ℝ)).exp
  have hf3 : HasDerivAt (fun y' : ℝ => Real.exp (y' ^ 2 / (2 * τ) - (1 + Real.exp (2 * y')) / (2 * x)))
      (Real.exp (y ^ 2 / (2 * τ) - (1 + Real.exp (2 * y)) / (2 * x)) *
        (y / τ - Real.exp (2 * y) / x)) y := by
    have ha : HasDerivAt (fun y' : ℝ => y' ^ 2 / (2 * τ)) (y / τ) y := by
      have h := (hasDerivAt_pow 2 y).div_const (2 * τ)
      convert h using 1; field_simp; ring
    have hb : HasDerivAt (fun y' : ℝ => (1 + Real.exp (2 * y')) / (2 * x))
        (Real.exp (2 * y) / x) y := by
      have h := (hasDerivAt_const y (1 : ℝ)).add (((hasDerivAt_id' y).const_mul (2 : ℝ)).exp)
      convert h.div_const (2 * x) using 1; simp; ring
    exact (ha.sub hb).exp
  have hf4 : HasDerivAt (fun y' : ℝ => Jm τ k (Real.exp y' / x))
      (Jm τ (k + 1) (Real.exp y / x) * (Real.exp y / x)) y := by
    have harg : HasDerivAt (fun y' : ℝ => Real.exp y' / x) (Real.exp y / x) y :=
      (Real.hasDerivAt_exp y).div_const x
    have hJm := Jm_hasDerivAt hτ k (div_pos (Real.exp_pos y) hx)
    simpa only [Function.comp_def] using hJm.comp y harg
  have hprod := (((hf1.mul hf2).mul_const (x ^ (-(d : ℤ)))).mul hf3).mul hf4
  refine hprod.congr_deriv ?_
  simp only [Pi.mul_apply, evalYorSum, dYorTermY, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, yorTerm]
  have hy1 : y ^ a * y = y ^ (a + 1) := by rw [pow_succ]
  have he1 : Real.exp ((b : ℝ) * y) * Real.exp (2 * y) = Real.exp (((b + 2 : ℕ) : ℝ) * y) := by
    rw [← Real.exp_add]; congr 1; push_cast; ring
  have he2 : Real.exp ((b : ℝ) * y) * Real.exp y = Real.exp (((b + 1 : ℕ) : ℝ) * y) := by
    rw [← Real.exp_add]; congr 1; push_cast; ring
  have hx1 : x ^ (-(d : ℤ)) * x⁻¹ = x ^ (-((d + 1 : ℕ) : ℤ)) := by
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, pow_succ]; ring
  rw [← hy1, ← he1, ← he2, ← hx1]
  field_simp [hτ0, hx0]; ring

lemma yorTerm_hasDerivAt_x {τ : ℝ} (hτ : 0 < τ) (a b d k : ℕ) {x : ℝ} (hx : 0 < x) (y : ℝ) :
    HasDerivAt (fun x' => yorTerm τ a b d k x' y)
      (evalYorSum τ (dYorTermX a b d k) x y) x := by
  have hx0 : x ≠ 0 := hx.ne'
  have hg1 : HasDerivAt (fun x' : ℝ => x' ^ (-(d : ℤ)))
      (-(d : ℝ) * x ^ (-((d + 1 : ℕ) : ℤ))) x := hasDerivAt_zpow_neg_nat d hx0
  have hg2 : HasDerivAt (fun x' : ℝ => Real.exp (y ^ 2 / (2 * τ) - (1 + Real.exp (2 * y)) / (2 * x')))
      (Real.exp (y ^ 2 / (2 * τ) - (1 + Real.exp (2 * y)) / (2 * x)) *
        ((1 + Real.exp (2 * y)) / (2 * x ^ 2))) x := by
    have hinv : HasDerivAt (fun x' : ℝ => (1 + Real.exp (2 * y)) / (2 * x'))
        (-((1 + Real.exp (2 * y)) / (2 * x ^ 2))) x := by
      have h := ((hasDerivAt_inv hx0).const_mul ((1 + Real.exp (2 * y)) / 2))
      convert h using 1
      · funext x'; ring
      · ring
    have hsub := (hasDerivAt_const x (y ^ 2 / (2 * τ))).sub hinv
    simpa only [Pi.sub_apply, zero_sub, neg_neg] using hsub.exp
  have hg3 : HasDerivAt (fun x' : ℝ => Jm τ k (Real.exp y / x'))
      (Jm τ (k + 1) (Real.exp y / x) * (-(Real.exp y) / x ^ 2)) x := by
    have harg : HasDerivAt (fun x' : ℝ => Real.exp y / x') (-(Real.exp y) / x ^ 2) x := by
      have h := (hasDerivAt_inv hx0).const_mul (Real.exp y)
      convert h using 1
      · funext x'; ring
      · ring
    have hJm := Jm_hasDerivAt hτ k (div_pos (Real.exp_pos y) hx)
    simpa only [Function.comp_def] using hJm.comp x harg
  have hprod := (((hg1.const_mul (y ^ a * Real.exp (b * y))).mul hg2).mul hg3)
  refine hprod.congr_deriv ?_
  simp only [Pi.mul_apply, evalYorSum, dYorTermX, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, yorTerm]
  have hx2 : x ^ (-(d : ℤ)) * (x ^ 2)⁻¹ = x ^ (-((d + 2 : ℕ) : ℤ)) := by
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, pow_add]; ring
  have he1 : Real.exp ((b : ℝ) * y) * Real.exp (2 * y) = Real.exp (((b + 2 : ℕ) : ℝ) * y) := by
    rw [← Real.exp_add]; congr 1; push_cast; ring
  have he2 : Real.exp ((b : ℝ) * y) * Real.exp y = Real.exp (((b + 1 : ℕ) : ℝ) * y) := by
    rw [← Real.exp_add]; congr 1; push_cast; ring
  rw [← hx2, ← he1, ← he2]
  field_simp [hx0]; ring

lemma evalYorSum_hasDerivAt_y {τ : ℝ} (hτ : 0 < τ) (L : List YorCoeff) {x : ℝ} (hx : 0 < x)
    (y : ℝ) :
    HasDerivAt (fun y' => evalYorSum τ L x y') (evalYorSum τ (dEvalYorSumY τ L) x y) y := by
  induction L with
  | nil => simpa [evalYorSum, dEvalYorSumY] using hasDerivAt_const y (0 : ℝ)
  | cons q L ih =>
      simp only [dEvalYorSumY, List.flatMap_cons]
      have hhead : HasDerivAt (fun y' => q.1 * yorTerm τ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 x y')
          (evalYorSum τ ((dYorTermY τ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2).map fun r => (q.1 * r.1, r.2)) x y)
          y := by
        rw [evalYorSum_scale]
        exact (yorTerm_hasDerivAt_y hτ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 hx y).const_mul q.1
      have hadd := hhead.add ih
      refine (hadd.congr_of_eventuallyEq (Eventually.of_forall fun y' =>
        (evalYorSum_cons τ q L x y').symm)).congr_deriv ?_
      exact (evalYorSum_append τ _ _ x y).symm

lemma evalYorSum_hasDerivAt_x {τ : ℝ} (hτ : 0 < τ) (L : List YorCoeff) {x : ℝ} (hx : 0 < x)
    (y : ℝ) :
    HasDerivAt (fun x' => evalYorSum τ L x' y) (evalYorSum τ (dEvalYorSumX L) x y) x := by
  induction L with
  | nil => simpa [evalYorSum, dEvalYorSumX] using hasDerivAt_const x (0 : ℝ)
  | cons q L ih =>
      simp only [dEvalYorSumX, List.flatMap_cons]
      have hhead : HasDerivAt (fun x' => q.1 * yorTerm τ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 x' y)
          (evalYorSum τ ((dYorTermX q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2).map fun r => (q.1 * r.1, r.2)) x y)
          x := by
        rw [evalYorSum_scale]
        exact (yorTerm_hasDerivAt_x hτ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 hx y).const_mul q.1
      have hadd := hhead.add ih
      refine (hadd.congr_of_eventuallyEq (Eventually.of_forall fun x' =>
        (evalYorSum_cons τ q L x' y).symm)).congr_deriv ?_
      exact (evalYorSum_append τ _ _ x y).symm

/-- Explicit coefficient list representing `pd m n (yorCondDensity τ)` on `(0, ∞) × ℝ`. -/
def yorPdList (τ : ℝ) (m n : ℕ) : List YorCoeff :=
  Nat.recOn m
    (Nat.recOn n [(Real.exp (Real.pi ^ 2 / (2 * τ)) / Real.pi, 0, 1, 2, 0)]
      fun _ L => dEvalYorSumY τ L)
    fun _ L => dEvalYorSumX L

lemma iteratedDeriv_y_yorCondDensity {τ : ℝ} (hτ : 0 < τ) (n : ℕ) {x : ℝ} (hx : 0 < x) (y : ℝ) :
    iteratedDeriv n (fun y' => yorCondDensity τ x y') y = evalYorSum τ (yorPdList τ 0 n) x y := by
  induction n generalizing y with
  | zero =>
      have hlist : yorPdList τ 0 0 = [(Real.exp (Real.pi ^ 2 / (2 * τ)) / Real.pi, 0, 1, 2, 0)] := rfl
      rw [hlist]
      simp only [iteratedDeriv_zero, evalYorSum, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, yorCondDensity, hx, ↓reduceIte, yorTerm, pow_zero,
        one_mul, Nat.cast_one, Int.reduceNeg, zpow_neg, zpow_natCast]
      rw [show y ^ 2 / (2 * τ) - (1 + Real.exp (2 * y)) / (2 * x) + y =
          y + (y ^ 2 / (2 * τ) - (1 + Real.exp (2 * y)) / (2 * x)) by ring, Real.exp_add]
      field_simp [hx.ne']
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv n (fun y' => yorCondDensity τ x y') =
          fun y' => evalYorSum τ (yorPdList τ 0 n) x y' := funext ih
      rw [hfun]
      exact (evalYorSum_hasDerivAt_y hτ (yorPdList τ 0 n) hx y).deriv

lemma pd_yorCondDensity_eq_evalYorSum {τ : ℝ} (hτ : 0 < τ) (m n : ℕ) {x : ℝ} (hx : 0 < x)
    (y : ℝ) :
    pd m n (yorCondDensity τ) x y = evalYorSum τ (yorPdList τ m n) x y := by
  induction m generalizing x with
  | zero =>
      simpa [pd, iteratedDeriv_zero] using iteratedDeriv_y_yorCondDensity hτ n hx y
  | succ m ih =>
      unfold pd
      rw [iteratedDeriv_succ]
      have h_ev : (iteratedDeriv m (fun x' => iteratedDeriv n (fun y' => yorCondDensity τ x' y') y)) =ᶠ[𝓝 x]
          (fun x' => evalYorSum τ (yorPdList τ m n) x' y) := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with x' hx'
        exact ih hx'
      rw [h_ev.deriv_eq]
      exact (evalYorSum_hasDerivAt_x hτ (yorPdList τ m n) hx y).deriv

end DerivativeFamily

section TermLimitsAndMoments

private lemma yorTerm_bound {τ : ℝ} (hτ : 0 < τ) (a b d k N : ℕ) :
    ∃ C ≥ 0, ∀ {x : ℝ}, 0 < x → ∀ y : ℝ,
      |yorTerm τ a b d k x y| ≤
        C * |y| ^ a * Real.exp (((b + N : ℕ) : ℝ) * y + y ^ 2 / (2 * τ)) *
          x ^ (-((d + N : ℕ) : ℤ)) * Real.exp (-(1 + Real.exp (2 * y) + Real.exp y) / (2 * x)) := by
  obtain ⟨C, hC0, hC⟩ := Jm_bound hτ k N
  refine ⟨C, hC0, fun {x} hx y => ?_⟩
  have hJm := hC (Real.exp y / x) (div_pos (Real.exp_pos y) hx).le
  unfold yorTerm
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_pow,
    abs_of_pos (Real.exp_pos _), abs_of_pos (zpow_pos hx _), abs_of_pos (Real.exp_pos _)]
  have hpow : (Real.exp y / x) ^ N = Real.exp ((N : ℝ) * y) * x ^ (-(N : ℤ)) := by
    rw [div_pow, ← Real.exp_nat_mul, zpow_neg, zpow_natCast, div_eq_mul_inv]
  have hexp_y : Real.exp ((b : ℝ) * y) * Real.exp (y ^ 2 / (2 * τ) - (1 + Real.exp (2 * y)) / (2 * x)) *
      (Real.exp ((N : ℝ) * y) * Real.exp (-(Real.exp y / x) / 2)) =
      Real.exp (((b + N : ℕ) : ℝ) * y + y ^ 2 / (2 * τ)) *
        Real.exp (-(1 + Real.exp (2 * y) + Real.exp y) / (2 * x)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1; push_cast; ring
  have hx_zpow : x ^ (-(d : ℤ)) * x ^ (-(N : ℤ)) = x ^ (-((d + N : ℕ) : ℤ)) := by
    rw [← zpow_add₀ hx.ne']; congr 1; push_cast; ring
  calc |y| ^ a * Real.exp (↑b * y) * x ^ (-(d : ℤ)) *
          Real.exp (y ^ 2 / (2 * τ) - (1 + Real.exp (2 * y)) / (2 * x)) * |Jm τ k (Real.exp y / x)|
      ≤ |y| ^ a * Real.exp (↑b * y) * x ^ (-(d : ℤ)) *
          Real.exp (y ^ 2 / (2 * τ) - (1 + Real.exp (2 * y)) / (2 * x)) *
          (C * (Real.exp y / x) ^ N * Real.exp (-(Real.exp y / x) / 2)) := by
        gcongr
    _ = C * |y| ^ a * (x ^ (-(d : ℤ)) * x ^ (-(N : ℤ))) *
          (Real.exp (↑b * y) * Real.exp (y ^ 2 / (2 * τ) - (1 + Real.exp (2 * y)) / (2 * x)) *
            (Real.exp ((N : ℝ) * y) * Real.exp (-(Real.exp y / x) / 2))) := by
        rw [hpow]; ring
    _ = _ := by rw [hx_zpow, hexp_y]; ring

lemma yorTerm_tendsto_zero_right {τ : ℝ} (hτ : 0 < τ) (a b d k : ℕ) (y : ℝ) :
    Tendsto (fun x => yorTerm τ a b d k x y) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  obtain ⟨C, _, hC⟩ := yorTerm_bound hτ a b d k 0
  let Ky : ℝ := C * |y| ^ a * Real.exp ((b : ℝ) * y + y ^ 2 / (2 * τ)) * 2 ^ d
  have hlim_inv : Tendsto (fun x : ℝ => (2 * x)⁻¹) (nhdsWithin 0 (Ioi 0)) atTop := by
    refine Tendsto.inv_tendsto_nhdsGT_zero ?_
    have h0 : Tendsto (fun x : ℝ => 2 * x) (nhdsWithin 0 (Ioi 0)) (nhds (2 * 0)) :=
      (continuous_const.mul continuous_id).continuousWithinAt.tendsto
    rw [mul_zero] at h0
    refine tendsto_nhdsWithin_iff.mpr ⟨h0, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_pos two_pos hx
  have hlim_zero : Tendsto (fun x : ℝ => Ky * (((2 * x)⁻¹) ^ d * Real.exp (-((2 * x)⁻¹))))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa [mul_zero] using ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero d).comp hlim_inv).const_mul Ky
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ hlim_zero
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : 0 < x := hx
  rw [Real.norm_eq_abs]
  have h1 : Real.exp (-(1 + Real.exp (2 * y) + Real.exp y) / (2 * x)) ≤
      Real.exp (-((2 * x)⁻¹)) := by
    refine Real.exp_le_exp.mpr ?_
    have hexp_nn : 0 ≤ Real.exp (2 * y) + Real.exp y := by positivity
    rw [neg_div, neg_le_neg_iff, inv_eq_one_div]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have h2 : x ^ (-((d + 0 : ℕ) : ℤ)) = 2 ^ d * ((2 * x)⁻¹) ^ d := by
    simp only [add_zero, zpow_neg, zpow_natCast, mul_inv, mul_pow, inv_pow]
    have : (2 : ℝ) ^ d * (2 ^ d)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero d two_ne_zero)
    calc (x ^ d)⁻¹ = 1 * (x ^ d)⁻¹ := (one_mul _).symm
      _ = ((2 : ℝ) ^ d * (2 ^ d)⁻¹) * (x ^ d)⁻¹ := by rw [this]
      _ = (2 : ℝ) ^ d * ((2 ^ d)⁻¹ * (x ^ d)⁻¹) := by ring
  calc |yorTerm τ a b d k x y|
      ≤ C * |y| ^ a * Real.exp (((b + 0 : ℕ) : ℝ) * y + y ^ 2 / (2 * τ)) *
          x ^ (-((d + 0 : ℕ) : ℤ)) * Real.exp (-(1 + Real.exp (2 * y) + Real.exp y) / (2 * x)) :=
        hC hx0 y
    _ ≤ C * |y| ^ a * Real.exp ((b : ℝ) * y + y ^ 2 / (2 * τ)) *
          (2 ^ d * ((2 * x)⁻¹) ^ d) * Real.exp (-((2 * x)⁻¹)) := by
        simp only [add_zero] at h2 ⊢
        rw [h2]
        gcongr
    _ = Ky * (((2 * x)⁻¹) ^ d * Real.exp (-((2 * x)⁻¹))) := by dsimp only [Ky]; ring

lemma yorTerm_tendsto_zero_atTop {τ : ℝ} (hτ : 0 < τ) (a b d k : ℕ) (y : ℝ) :
    Tendsto (fun x => yorTerm τ a b d k x y) atTop (nhds 0) := by
  obtain ⟨C, _, hC⟩ := yorTerm_bound hτ a b d k 1
  let Ky : ℝ := C * |y| ^ a * Real.exp (((b + 1 : ℕ) : ℝ) * y + y ^ 2 / (2 * τ))
  have hlim_zero : Tendsto (fun x : ℝ => Ky * (x ^ (d + 1))⁻¹) atTop (nhds 0) := by
    simpa [mul_zero] using (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (Nat.succ_ne_zero d))).const_mul Ky
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ hlim_zero
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.norm_eq_abs]
  have hexp_le : Real.exp (-(1 + Real.exp (2 * y) + Real.exp y) / (2 * x)) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [Real.exp_pos (2 * y), Real.exp_pos y]) (by positivity)
  calc |yorTerm τ a b d k x y|
      ≤ C * |y| ^ a * Real.exp (((b + 1 : ℕ) : ℝ) * y + y ^ 2 / (2 * τ)) *
          x ^ (-((d + 1 : ℕ) : ℤ)) * Real.exp (-(1 + Real.exp (2 * y) + Real.exp y) / (2 * x)) :=
        hC hx y
    _ ≤ Ky * x ^ (-((d + 1 : ℕ) : ℤ)) * 1 := by
        dsimp only [Ky]; gcongr
    _ = Ky * (x ^ (d + 1))⁻¹ := by rw [zpow_neg, zpow_natCast, mul_one]

private lemma integrableOn_exp_neg_mul' {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun s : ℝ => Real.exp (-c * s)) (Ioi 0) :=
  (exp_neg_integrableOn_Ioi 0 hc).congr_fun (fun s _ => by ring_nf) measurableSet_Ioi

private lemma integrableOn_pow_mul_exp_neg (k : ℕ) :
    IntegrableOn (fun u : ℝ => u ^ k * Real.exp (-u)) (Ioi 0) := by
  have hdom : IntegrableOn (fun u : ℝ => (2 ^ k * (Nat.factorial k : ℝ)) * Real.exp (-(1 / 2) * u)) (Ioi 0) :=
    (integrableOn_exp_neg_mul' (by positivity : (0 : ℝ) < 1 / 2)).const_mul _
  refine hdom.mono' (by fun_prop) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
  have hu0 : 0 ≤ u := hu.out.le
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hu0 k), abs_of_pos (Real.exp_pos _)]
  have hsum : (u / 2) ^ k / (Nat.factorial k : ℝ) ≤ Real.exp (u / 2) := by
    have hmem : k ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_self k)
    calc (u / 2) ^ k / (Nat.factorial k : ℝ)
        ≤ ∑ i ∈ Finset.range (k + 1), (u / 2) ^ i / (Nat.factorial i : ℝ) :=
          Finset.single_le_sum (f := fun i => (u / 2) ^ i / (Nat.factorial i : ℝ))
            (fun i _ => by positivity) hmem
      _ ≤ Real.exp (u / 2) := Real.sum_le_exp_of_nonneg (by positivity) (k + 1)
  have hpow : u ^ k ≤ 2 ^ k * (Nat.factorial k : ℝ) * Real.exp (u / 2) := by
    have hk : (0 : ℝ) < Nat.factorial k := Nat.cast_pos.mpr (Nat.factorial_pos k)
    rw [div_pow, div_le_iff₀ hk] at hsum
    calc u ^ k = (2 ^ k) * (u ^ k / 2 ^ k) := by field_simp
      _ ≤ 2 ^ k * (Real.exp (u / 2) * (Nat.factorial k : ℝ)) := by gcongr
      _ = 2 ^ k * (Nat.factorial k : ℝ) * Real.exp (u / 2) := by ring
  calc u ^ k * Real.exp (-u)
      ≤ (2 ^ k * (Nat.factorial k : ℝ) * Real.exp (u / 2)) * Real.exp (-u) := by gcongr
    _ = (2 ^ k * (Nat.factorial k : ℝ)) * Real.exp (-(1 / 2) * u) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

private lemma integral_Ioi_zpow_neg_mul_exp_neg_div {A : ℝ} (hA : 0 < A) (k : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ (-((k + 2 : ℕ) : ℤ)) * Real.exp (-A / (2 * x))) (Ioi 0) ∧
    ∫ x in Ioi (0 : ℝ), x ^ (-((k + 2 : ℕ) : ℤ)) * Real.exp (-A / (2 * x)) =
      (2 / A) ^ (k + 1) * ∫ u in Ioi (0 : ℝ), u ^ k * Real.exp (-u) := by
  let c : ℝ := A / 2
  have hc : 0 < c := by positivity
  have h_inv_img : (Inv.inv '' Ioi (0 : ℝ)) = Ioi (0 : ℝ) := by
    ext x; simp only [mem_image, mem_Ioi]
    exact ⟨fun ⟨s, hs, h⟩ => h ▸ inv_pos.mpr hs, fun hx => ⟨x⁻¹, inv_pos.mpr hx, inv_inv x⟩⟩
  have h_inv_deriv : ∀ s ∈ Ioi (0 : ℝ), HasDerivWithinAt Inv.inv (-(s ^ 2)⁻¹) (Ioi 0) s := fun s hs =>
    (hasDerivAt_inv hs.ne').hasDerivWithinAt
  have h_inv_inj : InjOn Inv.inv (Ioi (0 : ℝ)) := fun _ _ _ _ h => inv_injective h
  have h_rel : ∀ s ∈ Ioi (0 : ℝ),
      |-(s ^ 2)⁻¹| • (s⁻¹ ^ (-((k + 2 : ℕ) : ℤ)) * Real.exp (-A / (2 * s⁻¹))) =
        s ^ k * Real.exp (-c * s) := fun s hs => by
    have hs0 : s ≠ 0 := hs.out.ne'
    rw [smul_eq_mul, abs_neg, abs_of_pos (inv_pos.mpr (sq_pos_of_ne_zero hs0)),
      zpow_neg, zpow_natCast, inv_pow, inv_inv]
    have hexp : -A / (2 * s⁻¹) = -c * s := by dsimp only [c]; field_simp [hs0]
    rw [hexp, pow_add, pow_two]
    field_simp [hs0]
  have h_mul_img : ((fun u : ℝ => c⁻¹ * u) '' Ioi (0 : ℝ)) = Ioi (0 : ℝ) := by
    ext s; simp only [mem_image, mem_Ioi]
    exact ⟨fun ⟨u, hu, h⟩ => h ▸ mul_pos (inv_pos.mpr hc) hu,
      fun hs => ⟨c * s, mul_pos hc hs, by field_simp [hc.ne']⟩⟩
  have h_mul_deriv : ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun u' : ℝ => c⁻¹ * u') c⁻¹ (Ioi 0) u :=
    fun u _ => by simpa using ((hasDerivAt_id' u).const_mul c⁻¹).hasDerivWithinAt
  have h_mul_inj : InjOn (fun u : ℝ => c⁻¹ * u) (Ioi (0 : ℝ)) :=
    fun _ _ _ _ h => mul_left_cancel₀ (inv_ne_zero hc.ne') h
  have h_rel2 : ∀ u ∈ Ioi (0 : ℝ),
      |c⁻¹| • ((c⁻¹ * u) ^ k * Real.exp (-c * (c⁻¹ * u))) =
        (2 / A) ^ (k + 1) * (u ^ k * Real.exp (-u)) := fun u _ => by
    rw [smul_eq_mul, abs_of_pos (inv_pos.mpr hc), mul_pow,
      show -c * (c⁻¹ * u) = -u by field_simp [hc.ne'],
      show c⁻¹ = 2 / A by dsimp only [c]; field_simp [hA.ne'], pow_succ]
    ring
  have h_s_int : IntegrableOn (fun s : ℝ => s ^ k * Real.exp (-c * s)) (Ioi 0) := by
    rw [← h_mul_img, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      h_mul_deriv h_mul_inj]
    exact ((integrableOn_pow_mul_exp_neg k).const_mul ((2 / A) ^ (k + 1))).congr
      (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => (h_rel2 u hu).symm)
  have h_x_int : IntegrableOn (fun x : ℝ => x ^ (-((k + 2 : ℕ) : ℤ)) * Real.exp (-A / (2 * x))) (Ioi 0) := by
    rw [← h_inv_img, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      h_inv_deriv h_inv_inj]
    exact h_s_int.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => (h_rel s hs).symm)
  refine ⟨h_x_int, ?_⟩
  have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi h_inv_deriv h_inv_inj
    (fun x : ℝ => x ^ (-((k + 2 : ℕ) : ℤ)) * Real.exp (-A / (2 * x)))
  rw [h_inv_img] at hcov
  rw [hcov, setIntegral_congr_fun measurableSet_Ioi h_rel]
  have hcov2 := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi h_mul_deriv h_mul_inj
    (fun s : ℝ => s ^ k * Real.exp (-c * s))
  rw [h_mul_img] at hcov2
  rw [hcov2, setIntegral_congr_fun measurableSet_Ioi h_rel2, integral_const_mul]

private lemma integrable_abs_pow_mul_exp_neg_abs (a : ℕ) :
    Integrable (fun y : ℝ => |y| ^ a * Real.exp (-|y|)) := by
  have hexp_int : Integrable (fun y : ℝ => Real.exp (-|y| / 2)) := by
    have hIci : IntegrableOn (fun y : ℝ => Real.exp (-y / 2)) (Ici 0) :=
      (integrableOn_exp_neg_mul' (by positivity : (0 : ℝ) < 1 / 2) |>.congr_fun
        (fun y _ => by ring_nf) measurableSet_Ioi).congr_set_ae Ioi_ae_eq_Ici.symm
    have hIio : IntegrableOn (fun y : ℝ => Real.exp (y / 2)) (Iio 0) := by
      have h_neg_img : (Neg.neg '' Ioi (0 : ℝ)) = Iio 0 := by
        ext u; simp only [mem_image, mem_Ioi, mem_Iio]
        exact ⟨fun ⟨v, hv, h⟩ => by linarith, fun hu => ⟨-u, by linarith, neg_neg u⟩⟩
      rw [← h_neg_img, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
        (fun u _ => (hasDerivAt_neg u).hasDerivWithinAt) neg_injective.injOn]
      exact (integrableOn_exp_neg_mul' (by positivity : (0 : ℝ) < 1 / 2)).congr_fun
        (fun u _ => by simp only [smul_eq_mul, abs_neg, abs_one, one_mul]; ring_nf)
        measurableSet_Ioi
    have h_split : IntegrableOn (fun y : ℝ => Real.exp (-|y| / 2)) (Iio 0 ∪ Ici 0) := by
      refine IntegrableOn.union ?_ ?_
      · refine hIio.congr_fun (fun y hy => ?_) measurableSet_Iio
        rw [abs_of_neg hy.out]; ring_nf
      · refine hIci.congr_fun (fun y hy => ?_) measurableSet_Ici
        rw [abs_of_nonneg hy.out]
    rwa [Iio_union_Ici, integrableOn_univ] at h_split
  refine (hexp_int.const_mul (2 ^ a * (Nat.factorial a : ℝ))).mono' (by fun_prop) (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (abs_nonneg y) a),
    abs_of_pos (Real.exp_pos _)]
  have hsum : (|y| / 2) ^ a / (Nat.factorial a : ℝ) ≤ Real.exp (|y| / 2) := by
    have hmem : a ∈ Finset.range (a + 1) := Finset.mem_range.mpr (Nat.lt_succ_self a)
    calc (|y| / 2) ^ a / (Nat.factorial a : ℝ)
        ≤ ∑ i ∈ Finset.range (a + 1), (|y| / 2) ^ i / (Nat.factorial i : ℝ) :=
          Finset.single_le_sum (f := fun i => (|y| / 2) ^ i / (Nat.factorial i : ℝ))
            (fun i _ => by positivity) hmem
      _ ≤ Real.exp (|y| / 2) := Real.sum_le_exp_of_nonneg (by positivity) (a + 1)
  have hpow : |y| ^ a ≤ 2 ^ a * (Nat.factorial a : ℝ) * Real.exp (|y| / 2) := by
    have ha : (0 : ℝ) < Nat.factorial a := Nat.cast_pos.mpr (Nat.factorial_pos a)
    rw [div_pow, div_le_iff₀ ha] at hsum
    calc |y| ^ a = 2 ^ a * (|y| ^ a / 2 ^ a) := by field_simp
      _ ≤ 2 ^ a * (Real.exp (|y| / 2) * (Nat.factorial a : ℝ)) := by gcongr
      _ = 2 ^ a * (Nat.factorial a : ℝ) * Real.exp (|y| / 2) := by ring
  calc |y| ^ a * Real.exp (-|y|)
      ≤ (2 ^ a * (Nat.factorial a : ℝ) * Real.exp (|y| / 2)) * Real.exp (-|y|) := by gcongr
    _ = (2 ^ a * (Nat.factorial a : ℝ)) * Real.exp (-|y| / 2) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- Gaussian-weighted `L¹` moment majorant for a single `yorTerm` with `x^s` (`s ≤ p`). -/
lemma yorTerm_moment_majorant {τ : ℝ} (hτ : 0 < τ) (a b d k p : ℕ) {s : ℤ} (hs : s ≤ p) :
    ∃ g : ℝ → ℝ, Integrable g ∧ (∀ y, 0 ≤ g y) ∧
      ∀ y : ℝ, ENNReal.ofReal (Real.exp (-y ^ 2 / (2 * τ))) *
        (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |x ^ s * yorTerm τ a b d k x y|) ≤ ENNReal.ofReal (g y) := by
  let N : ℕ := b + 2 * p + 3
  let K : ℕ := ((d : ℤ) + N - s - 2).toNat
  have hK_eq : (K + 2 : ℤ) = (d : ℤ) + N - s := by
    dsimp only [K, N]; omega
  have h2K : (b + N : ℤ) + 1 ≤ 2 * (K + 1 : ℤ) := by
    dsimp only [K, N]; omega
  obtain ⟨C, hC0, hC⟩ := yorTerm_bound hτ a b d k N
  have h_pt : ∀ {x : ℝ}, 0 < x → ∀ y : ℝ,
      |x ^ s * yorTerm τ a b d k x y| ≤
        C * |y| ^ a * Real.exp (((b + N : ℕ) : ℝ) * y + y ^ 2 / (2 * τ)) *
          x ^ (-((K + 2 : ℕ) : ℤ)) * Real.exp (-(1 + Real.exp (2 * y) + Real.exp y) / (2 * x)) := by
    intro x hx y
    rw [abs_mul, abs_of_pos (zpow_pos hx s)]
    have hpow : x ^ s * x ^ (-((d + N : ℕ) : ℤ)) = x ^ (-((K + 2 : ℕ) : ℤ)) := by
      rw [← zpow_add₀ hx.ne']; congr 1; omega
    calc x ^ s * |yorTerm τ a b d k x y|
        ≤ x ^ s * (C * |y| ^ a * Real.exp (((b + N : ℕ) : ℝ) * y + y ^ 2 / (2 * τ)) *
            x ^ (-((d + N : ℕ) : ℤ)) * Real.exp (-(1 + Real.exp (2 * y) + Real.exp y) / (2 * x))) :=
          mul_le_mul_of_nonneg_left (hC hx y) (zpow_pos hx s).le
      _ = C * |y| ^ a * Real.exp (((b + N : ℕ) : ℝ) * y + y ^ 2 / (2 * τ)) *
            (x ^ s * x ^ (-((d + N : ℕ) : ℤ))) *
            Real.exp (-(1 + Real.exp (2 * y) + Real.exp y) / (2 * x)) := by ring
      _ = _ := by rw [hpow]
  let I_K : ℝ := ∫ u in Ioi (0 : ℝ), u ^ K * Real.exp (-u)
  have hIK_nn : 0 ≤ I_K := setIntegral_nonneg measurableSet_Ioi fun u hu =>
    mul_nonneg (pow_nonneg hu.out.le K) (Real.exp_pos _).le
  let M_out : ℝ := C * 2 ^ (K + 1) * I_K
  have hM_nn : 0 ≤ M_out := by positivity
  refine ⟨fun y => M_out * (|y| ^ a * Real.exp (-|y|)),
    (integrable_abs_pow_mul_exp_neg_abs a).const_mul M_out,
    fun y => by positivity, fun y => ?_⟩
  let A : ℝ := 1 + Real.exp (2 * y) + Real.exp y
  have hA : 0 < A := by positivity
  let Cy : ℝ := C * |y| ^ a * Real.exp (((b + N : ℕ) : ℝ) * y + y ^ 2 / (2 * τ))
  have hCy_nn : 0 ≤ Cy := by positivity
  obtain ⟨h_xint, h_xval⟩ := integral_Ioi_zpow_neg_mul_exp_neg_div hA K
  have h_inner_mono :
      (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |x ^ s * yorTerm τ a b d k x y|) ≤
      ENNReal.ofReal (Cy * ((2 / A) ^ (K + 1) * I_K)) := by
    calc (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |x ^ s * yorTerm τ a b d k x y|)
        ≤ ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (Cy * (x ^ (-((K + 2 : ℕ) : ℤ)) * Real.exp (-A / (2 * x)))) := by
          refine setLIntegral_mono' measurableSet_Ioi fun x hx => ENNReal.ofReal_le_ofReal ?_
          simpa only [Cy, A, mul_assoc] using h_pt hx y
      _ = ENNReal.ofReal (∫ x in Ioi (0 : ℝ), Cy * (x ^ (-((K + 2 : ℕ) : ℤ)) * Real.exp (-A / (2 * x)))) := by
          refine (ofReal_integral_eq_lintegral_ofReal (h_xint.const_mul Cy)
            (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_)).symm
          exact mul_nonneg hCy_nn (mul_nonneg (zpow_nonneg hx.out.le _) (Real.exp_pos _).le)
      _ = ENNReal.ofReal (Cy * ((2 / A) ^ (K + 1) * I_K)) := by
          rw [integral_const_mul, h_xval]
  have h_y_exp : Real.exp (-y ^ 2 / (2 * τ)) * Cy * (2 / A) ^ (K + 1) ≤
      C * 2 ^ (K + 1) * (|y| ^ a * Real.exp (-|y|)) := by
    have hcancel : Real.exp (-y ^ 2 / (2 * τ)) * Cy =
        C * |y| ^ a * Real.exp (((b + N : ℕ) : ℝ) * y) := by
      dsimp only [Cy]
      rw [← mul_assoc, mul_comm (Real.exp (-y ^ 2 / (2 * τ))) (C * |y| ^ a), mul_assoc,
        ← Real.exp_add]
      congr 2; ring
    rw [hcancel]
    have h_Ay : Real.exp (((b + N : ℕ) : ℝ) * y) * (2 / A) ^ (K + 1) ≤
        2 ^ (K + 1) * Real.exp (-|y|) := by
      rw [div_pow]
      by_cases hy : 0 ≤ y
      · rw [abs_of_nonneg hy]
        have hA_ge : Real.exp (2 * y) ≤ A := by dsimp only [A]; linarith [Real.exp_pos y]
        have hA_pow : (Real.exp (2 * y)) ^ (K + 1) ≤ A ^ (K + 1) :=
          pow_le_pow_left₀ (Real.exp_pos _).le hA_ge (K + 1)
        have hA_inv : (A ^ (K + 1))⁻¹ ≤ (Real.exp (((2 * (K + 1) : ℕ) : ℝ) * y))⁻¹ := by
          rw [← Real.exp_nat_mul] at hA_pow
          have hpow_eq : Real.exp ((K + 1 : ℕ) * (2 * y)) = Real.exp (((2 * (K + 1) : ℕ) : ℝ) * y) := by
            congr 1; push_cast; ring
          rw [hpow_eq] at hA_pow
          exact inv_anti₀ (Real.exp_pos _) hA_pow
        calc Real.exp (((b + N : ℕ) : ℝ) * y) * (2 ^ (K + 1) / A ^ (K + 1))
            = 2 ^ (K + 1) * (Real.exp (((b + N : ℕ) : ℝ) * y) * (A ^ (K + 1))⁻¹) := by ring
          _ ≤ 2 ^ (K + 1) * (Real.exp (((b + N : ℕ) : ℝ) * y) *
                (Real.exp (((2 * (K + 1) : ℕ) : ℝ) * y))⁻¹) := by gcongr
          _ = 2 ^ (K + 1) * Real.exp ((((b + N : ℤ) - 2 * (K + 1 : ℤ) : ℤ) : ℝ) * y) := by
              rw [← Real.exp_neg, ← Real.exp_add]; congr 2; push_cast; ring
          _ ≤ 2 ^ (K + 1) * Real.exp (-y) := by
              gcongr
              have h_le : (((b + N : ℤ) - 2 * (K + 1 : ℤ) : ℤ) : ℝ) ≤ -1 := by
                exact_mod_cast (by omega : (b + N : ℤ) - 2 * (K + 1 : ℤ) ≤ -1)
              nlinarith
      · have hy_neg : y < 0 := lt_of_not_ge hy
        rw [abs_of_neg hy_neg, neg_neg]
        have hA_ge1 : 1 ≤ A := by dsimp only [A]; linarith [Real.exp_pos (2 * y), Real.exp_pos y]
        have hA_inv : (A ^ (K + 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hA_ge1)
        have hbN : (1 : ℝ) ≤ (b + N : ℕ) := by
          dsimp only [N]; exact_mod_cast (by omega : 1 ≤ b + (b + 2 * p + 3))
        calc Real.exp (((b + N : ℕ) : ℝ) * y) * (2 ^ (K + 1) / A ^ (K + 1))
            = 2 ^ (K + 1) * (Real.exp (((b + N : ℕ) : ℝ) * y) * (A ^ (K + 1))⁻¹) := by ring
          _ ≤ 2 ^ (K + 1) * (Real.exp (((b + N : ℕ) : ℝ) * y) * 1) := by gcongr
          _ ≤ 2 ^ (K + 1) * Real.exp y := by
              rw [mul_one]; gcongr; nlinarith
    calc C * |y| ^ a * Real.exp (((b + N : ℕ) : ℝ) * y) * (2 / A) ^ (K + 1)
        = C * |y| ^ a * (Real.exp (((b + N : ℕ) : ℝ) * y) * (2 / A) ^ (K + 1)) := by ring
      _ ≤ C * |y| ^ a * (2 ^ (K + 1) * Real.exp (-|y|)) := by gcongr
      _ = C * 2 ^ (K + 1) * (|y| ^ a * Real.exp (-|y|)) := by ring
  calc ENNReal.ofReal (Real.exp (-y ^ 2 / (2 * τ))) *
        (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |x ^ s * yorTerm τ a b d k x y|)
      ≤ ENNReal.ofReal (Real.exp (-y ^ 2 / (2 * τ))) *
          ENNReal.ofReal (Cy * ((2 / A) ^ (K + 1) * I_K)) := by gcongr
    _ = ENNReal.ofReal (Real.exp (-y ^ 2 / (2 * τ)) * (Cy * ((2 / A) ^ (K + 1) * I_K))) :=
        (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
    _ ≤ ENNReal.ofReal (M_out * (|y| ^ a * Real.exp (-|y|))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc Real.exp (-y ^ 2 / (2 * τ)) * (Cy * ((2 / A) ^ (K + 1) * I_K))
            = (Real.exp (-y ^ 2 / (2 * τ)) * Cy * (2 / A) ^ (K + 1)) * I_K := by ring
          _ ≤ (C * 2 ^ (K + 1) * (|y| ^ a * Real.exp (-|y|))) * I_K :=
              mul_le_mul_of_nonneg_right h_y_exp hIK_nn
          _ = M_out * (|y| ^ a * Real.exp (-|y|)) := by dsimp only [M_out]; ring

end TermLimitsAndMoments

section EvalSumAndScaling

lemma evalYorSum_tendsto_zero_right {τ : ℝ} (hτ : 0 < τ) (L : List YorCoeff) (y : ℝ) :
    Tendsto (fun x => evalYorSum τ L x y) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  induction L with
  | nil => simp [evalYorSum]
  | cons q L ih =>
      have h_eq : (fun x => evalYorSum τ (q :: L) x y) =
          fun x => q.1 * yorTerm τ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 x y + evalYorSum τ L x y := by
        funext x; exact evalYorSum_cons τ q L x y
      rw [h_eq]
      simpa [mul_zero, add_zero] using
        ((yorTerm_tendsto_zero_right hτ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 y).const_mul q.1).add ih

lemma evalYorSum_tendsto_zero_atTop {τ : ℝ} (hτ : 0 < τ) (L : List YorCoeff) (y : ℝ) :
    Tendsto (fun x => evalYorSum τ L x y) atTop (nhds 0) := by
  induction L with
  | nil => simp [evalYorSum]
  | cons q L ih =>
      have h_eq : (fun x => evalYorSum τ (q :: L) x y) =
          fun x => q.1 * yorTerm τ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 x y + evalYorSum τ L x y := by
        funext x; exact evalYorSum_cons τ q L x y
      rw [h_eq]
      simpa [mul_zero, add_zero] using
        ((yorTerm_tendsto_zero_atTop hτ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 y).const_mul q.1).add ih

lemma evalYorSum_moment_majorant {τ : ℝ} (hτ : 0 < τ) (L : List YorCoeff) (p : ℕ) {s : ℤ}
    (hs : s ≤ p) :
    ∃ g : ℝ → ℝ, Integrable g ∧ (∀ y, 0 ≤ g y) ∧
      ∀ y : ℝ, ENNReal.ofReal (Real.exp (-y ^ 2 / (2 * τ))) *
        (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |x ^ s * evalYorSum τ L x y|) ≤ ENNReal.ofReal (g y) := by
  induction L with
  | nil =>
      refine ⟨fun _ => 0, integrable_zero _ _ _, fun _ => le_rfl, fun y => ?_⟩
      simp [evalYorSum_nil]
  | cons q L ih =>
      obtain ⟨gq, hgq_int, hgq_nn, hgq⟩ :=
        yorTerm_moment_majorant hτ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 p hs
      obtain ⟨gL, hgL_int, hgL_nn, hgL⟩ := ih
      refine ⟨fun y => |q.1| * gq y + gL y, (hgq_int.const_mul _).add hgL_int,
        fun y => add_nonneg (mul_nonneg (abs_nonneg _) (hgq_nn y)) (hgL_nn y), fun y => ?_⟩
      have hm1 : AEMeasurable
          (fun x : ℝ => ENNReal.ofReal |x ^ s * yorTerm τ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 x y|)
          (volume.restrict (Ioi 0)) := by
        have hcont : ContinuousOn
            (fun x : ℝ => ENNReal.ofReal |x ^ s * yorTerm τ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 x y|)
            (Ioi 0) := by
          refine ENNReal.continuous_ofReal.comp_continuousOn ?_
          refine ContinuousOn.abs ?_
          refine ContinuousOn.mul ?_ (yorTerm_contDiffOn_x hτ _ _ _ _ 0 y).continuousOn
          exact continuousOn_id.zpow₀ s (fun x hx => Or.inl hx.ne')
        exact hcont.aemeasurable measurableSet_Ioi
      have h_in : (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |x ^ s * evalYorSum τ (q :: L) x y|) ≤
          ENNReal.ofReal |q.1| *
            (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |x ^ s * yorTerm τ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 x y|) +
          ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |x ^ s * evalYorSum τ L x y| := by
        calc (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |x ^ s * evalYorSum τ (q :: L) x y|)
            ≤ ∫⁻ x in Ioi (0 : ℝ),
                (ENNReal.ofReal |q.1| * ENNReal.ofReal |x ^ s * yorTerm τ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 x y| +
                 ENNReal.ofReal |x ^ s * evalYorSum τ L x y|) := by
              refine lintegral_mono fun x => ?_
              rw [evalYorSum_cons, mul_add, ← ENNReal.ofReal_mul (abs_nonneg _),
                ← ENNReal.ofReal_add (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)]
              refine ENNReal.ofReal_le_ofReal ?_
              calc |x ^ s * (q.1 * yorTerm τ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 x y) +
                      x ^ s * evalYorSum τ L x y|
                  ≤ |x ^ s * (q.1 * yorTerm τ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 x y)| +
                      |x ^ s * evalYorSum τ L x y| := abs_add_le _ _
                _ = |q.1| * |x ^ s * yorTerm τ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 x y| +
                      |x ^ s * evalYorSum τ L x y| := by
                    rw [show x ^ s * (q.1 * yorTerm τ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 x y) =
                      q.1 * (x ^ s * yorTerm τ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 x y) by ring, abs_mul]
          _ = (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |q.1| *
                  ENNReal.ofReal |x ^ s * yorTerm τ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 x y|) +
                ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |x ^ s * evalYorSum τ L x y| :=
              lintegral_add_left' (hm1.const_mul _) _
          _ = ENNReal.ofReal |q.1| *
                  (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |x ^ s * yorTerm τ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 x y|) +
                ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |x ^ s * evalYorSum τ L x y| := by
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      calc ENNReal.ofReal (Real.exp (-y ^ 2 / (2 * τ))) *
            (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |x ^ s * evalYorSum τ (q :: L) x y|)
          ≤ ENNReal.ofReal (Real.exp (-y ^ 2 / (2 * τ))) *
              (ENNReal.ofReal |q.1| *
                (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |x ^ s * yorTerm τ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 x y|) +
               ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |x ^ s * evalYorSum τ L x y|) := by gcongr
        _ = ENNReal.ofReal |q.1| * (ENNReal.ofReal (Real.exp (-y ^ 2 / (2 * τ))) *
                ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |x ^ s * yorTerm τ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 x y|) +
              ENNReal.ofReal (Real.exp (-y ^ 2 / (2 * τ))) *
                ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |x ^ s * evalYorSum τ L x y| := by
            rw [mul_add]; congr 1; ring
        _ ≤ ENNReal.ofReal |q.1| * ENNReal.ofReal (gq y) + ENNReal.ofReal (gL y) := by
            gcongr; exact hgq y; exact hgL y
        _ = ENNReal.ofReal (|q.1| * gq y + gL y) := by
            rw [← ENNReal.ofReal_mul (abs_nonneg _),
              ← ENNReal.ofReal_add (mul_nonneg (abs_nonneg _) (hgq_nn y)) (hgL_nn y)]

private lemma pd_yorCondDensity_scaled {τ : ℝ} (hτ : 0 < τ) {α : ℝ} (hα : 0 < α)
    (m n : ℕ) {x : ℝ} (hx : 0 < x) (y : ℝ) :
    pd m n (fun x' y' => α ^ 2 * yorCondDensity τ (α ^ 2 * x') (α * y')) x y =
      α ^ (2 + 2 * m + n) * pd m n (yorCondDensity τ) (α ^ 2 * x) (α * y) := by
  have h_y : ∀ x' > 0, iteratedDeriv n (fun y' => α ^ 2 * yorCondDensity τ (α ^ 2 * x') (α * y')) y =
      α ^ 2 * α ^ n * evalYorSum τ (yorPdList τ 0 n) (α ^ 2 * x') (α * y) := by
    intro x' hx'
    have hcont_y : ContDiff ℝ n (fun y' => yorCondDensity τ (α ^ 2 * x') y') := by
      have hmap : MapsTo (fun y' : ℝ => (α ^ 2 * x', y')) univ (Ioi (0 : ℝ) ×ˢ univ) :=
        fun _ _ => ⟨mul_pos (sq_pos_of_pos hα) hx', trivial⟩
      exact contDiffOn_univ.mp ((yorCondDensity_contDiffOn hτ n).comp
        (contDiffOn_const.prodMk contDiffOn_id) hmap)
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_const_mul hcont_y α]
    dsimp only
    rw [iteratedDeriv_y_yorCondDensity hτ n (mul_pos (sq_pos_of_pos hα) hx') (α * y)]
    ring
  let g : ℝ → ℝ := fun z => evalYorSum τ (yorPdList τ 0 n) z (α * y)
  have hg_cd : ContDiffOn ℝ m g (Ioi 0) :=
    evalYorSum_contDiffOn_x hτ (yorPdList τ 0 n) m (α * y)
  have h_eqOn : EqOn (fun x' => iteratedDeriv n (fun y' => α ^ 2 * yorCondDensity τ (α ^ 2 * x') (α * y')) y)
      (fun x' => α ^ 2 * α ^ n * g (α ^ 2 * x')) (Ioi 0) :=
    fun x' hx' => h_y x' hx'
  have h_comp_cd : ContDiffOn ℝ m (fun x' => g (α ^ 2 * x')) (Ioi 0) :=
    hg_cd.comp (contDiffOn_const.mul contDiffOn_id) (fun _ hx' => mul_pos (sq_pos_of_pos hα) hx')
  have h_lhs_cd : ContDiffAt ℝ m
      (fun x' => iteratedDeriv n (fun y' => α ^ 2 * yorCondDensity τ (α ^ 2 * x') (α * y')) y) x :=
    ((contDiffOn_const.mul h_comp_cd).congr h_eqOn).contDiffAt (isOpen_Ioi.mem_nhds hx)
  have h_within :
      pd m n (fun x' y' => α ^ 2 * yorCondDensity τ (α ^ 2 * x') (α * y')) x y =
      iteratedDerivWithin m (fun x' => α ^ 2 * α ^ n * g (α ^ 2 * x')) (Ioi 0) x := by
    unfold pd
    rw [← iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0) h_lhs_cd hx]
    exact iteratedDerivWithin_congr h_eqOn hx
  have h_const_out :
      iteratedDerivWithin m (fun x' => α ^ 2 * α ^ n * g (α ^ 2 * x')) (Ioi 0) x =
      α ^ 2 * α ^ n * iteratedDerivWithin m (fun x' => g (α ^ 2 * x')) (Ioi 0) x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0)
        ((contDiffOn_const.mul h_comp_cd).contDiffAt (isOpen_Ioi.mem_nhds hx)) hx,
      iteratedDeriv_const_mul_field,
      ← iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0)
        (h_comp_cd.contDiffAt (isOpen_Ioi.mem_nhds hx)) hx]
  have h_comp_scale :
      iteratedDerivWithin m (fun x' => g (α ^ 2 * x')) (Ioi 0) x =
      (α ^ 2) ^ m * iteratedDerivWithin m g (Ioi 0) (α ^ 2 * x) := by
    simpa [smul_eq_mul] using
      iteratedDerivWithin_comp_const_smul hx (uniqueDiffOn_Ioi 0) hg_cd (α ^ 2)
        (fun _ hx' => mul_pos (sq_pos_of_pos hα) hx')
  have h_g_eq_pd : iteratedDerivWithin m g (Ioi 0) (α ^ 2 * x) =
      pd m n (yorCondDensity τ) (α ^ 2 * x) (α * y) := by
    have hax : 0 < α ^ 2 * x := mul_pos (sq_pos_of_pos hα) hx
    have h_eq_on2 : EqOn g (fun z => iteratedDeriv n (fun y' => yorCondDensity τ z y') (α * y)) (Ioi 0) :=
      fun z hz => (iteratedDeriv_y_yorCondDensity hτ n hz (α * y)).symm
    have h_pd_cd : ContDiffAt ℝ m
        (fun z => iteratedDeriv n (fun y' => yorCondDensity τ z y') (α * y)) (α ^ 2 * x) :=
      (hg_cd.congr h_eq_on2.symm).contDiffAt (isOpen_Ioi.mem_nhds hax)
    rw [iteratedDerivWithin_congr h_eq_on2 hax,
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0) h_pd_cd hax]
    rfl
  rw [h_within, h_const_out, h_comp_scale, h_g_eq_pd]
  have hpow : α ^ 2 * α ^ n * (α ^ 2) ^ m = α ^ (2 + 2 * m + n) := by ring
  rw [← mul_assoc, hpow]

private lemma lintegral_Ioi_comp_mul_left {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ≥0∞}
    (hf : AEMeasurable f (volume.restrict (Ioi 0))) :
    ∫⁻ x in Ioi (0 : ℝ), f (a * x) = ENNReal.ofReal a⁻¹ * ∫⁻ u in Ioi (0 : ℝ), f u := by
  have hmap : (volume : Measure ℝ).map (fun x => a * x) = ENNReal.ofReal a⁻¹ • volume := by
    rw [Real.map_volume_mul_left ha.ne', abs_of_pos (inv_pos.mpr ha)]
  have hpre : (fun x => a * x) ⁻¹' Ioi 0 = Ioi 0 := by
    ext x; simp [mul_pos_iff_of_pos_left ha]
  have hr : ((volume : Measure ℝ).restrict (Ioi 0)).map (fun x => a * x) =
      ENNReal.ofReal a⁻¹ • (volume.restrict (Ioi 0)) := by
    conv_lhs => rw [← hpre]
    rw [← Measure.restrict_map (by fun_prop) measurableSet_Ioi, hmap, Measure.restrict_smul]
  have hf' : AEMeasurable f (((volume : Measure ℝ).restrict (Ioi 0)).map (fun x => a * x)) := by
    rw [hr]
    exact hf.smul_measure _
  rw [← lintegral_map' hf' (by fun_prop), hr, lintegral_smul_measure, smul_eq_mul]

/-- Constructive, axiom-free proof of Lyasoff Prop. 2.2. -/
theorem prop_2_2_constructive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (hσ : 0 < σ) (ht : 0 < t) :
    ∃ φc : ℝ → ℝ → ℝ, IsCondDensity P W σ t φc ∧
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry φc) (Ioi (0 : ℝ) ×ˢ univ)) ∧
      (∀ y, Tendsto (fun x => φc x y) (nhdsWithin 0 (Ioi 0)) (nhds 0)) ∧
      (∀ m n y, Tendsto (fun x => pd m n φc x y) atTop (nhds 0)) ∧
      (∀ m n y, ∃ l, Tendsto (fun x => pd m n φc x y) (nhdsWithin 0 (Ioi 0)) (nhds l)) ∧
      (∀ m n p : ℕ,
        (∫⁻ y, ENNReal.ofReal (Real.exp (-y ^ 2 / (2 * (t : ℝ)))) *
          ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |(x : ℝ) ^ (p : ℤ) * pd m n φc x y|) < ∞ ∧
        (∫⁻ y, ENNReal.ofReal (Real.exp (-y ^ 2 / (2 * (t : ℝ)))) *
          ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |(x : ℝ) ^ (-(p : ℤ)) * pd m n φc x y|) < ∞) := by
  let α : ℝ := σ / 2
  have hα : 0 < α := by positivity
  let τ : ℝ≥0 := (α ^ 2 * (t : ℝ)).toNNReal
  have hτ : 0 < τ := Real.toNNReal_pos.mpr (by positivity)
  have hτR : (τ : ℝ) = α ^ 2 * (t : ℝ) := Real.coe_toNNReal _ (by positivity)
  let φc : ℝ → ℝ → ℝ := fun x y => α ^ 2 * yorCondDensity (τ : ℝ) (α ^ 2 * x) (α * y)
  refine ⟨φc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 1. `IsCondDensity P W σ t φc`
    unfold IsCondDensity
    let t₁ : ℝ≥0 := (σ ^ 2 * (t : ℝ)).toNNReal
    have ht₁R : (t₁ : ℝ) = σ ^ 2 * (t : ℝ) := Real.coe_toNNReal _ (by positivity)
    have ht₁_div2 : ((t₁ : ℝ) / (2 : ℝ) ^ 2).toNNReal = τ := by
      ext
      rw [Real.coe_toNNReal _ (by positivity), hτR, ht₁R]
      dsimp only [α]; ring
    have ht₁_divσ : ((t₁ : ℝ) / σ ^ 2).toNNReal = t := by
      ext
      rw [Real.coe_toNNReal _ (by positivity), ht₁R]
      field_simp [hσ.ne']
    have h2 := jointLaw_scaling P W hW (by positivity : (0 : ℝ) < 2) t₁
    have hσs := jointLaw_scaling P W hW hσ t₁
    rw [ht₁_div2] at h2
    rw [ht₁_divσ] at hσs
    have h_eq_map : (jointLaw P W σ 0 t).map (fun p : ℝ × ℝ => (σ ^ 2 * p.1, σ * p.2)) =
        (jointLaw P W 2 0 τ).map (fun p : ℝ × ℝ => ((2 : ℝ) ^ 2 * p.1, 2 * p.2)) :=
      hσs.symm.trans h2
    let invσ : ℝ × ℝ → ℝ × ℝ := fun p => ((σ ^ 2)⁻¹ * p.1, σ⁻¹ * p.2)
    have h_inv_meas : Measurable invσ := by fun_prop
    have h_law_map : jointLaw P W σ 0 t =
        (jointLaw P W 2 0 τ).map (fun p : ℝ × ℝ => ((α ^ 2)⁻¹ * p.1, α⁻¹ * p.2)) := by
      have h1 := congrArg (Measure.map invσ) h_eq_map
      have h_id : (invσ ∘ fun p : ℝ × ℝ => (σ ^ 2 * p.1, σ * p.2)) = id := by
        funext p; dsimp only [invσ, Function.comp_apply, id_def]
        ext <;> field_simp [hσ.ne']
      have h_comp : (invσ ∘ fun p : ℝ × ℝ => ((2 : ℝ) ^ 2 * p.1, 2 * p.2)) =
          fun p : ℝ × ℝ => ((α ^ 2)⁻¹ * p.1, α⁻¹ * p.2) := by
        funext p; dsimp only [invσ, Function.comp_apply, α]
        ext <;> field_simp [hσ.ne']
      rw [Measure.map_map h_inv_meas (by fun_prop), h_id, Measure.map_id,
        Measure.map_map h_inv_meas (by fun_prop), h_comp] at h1
      exact h1
    have hc2 := yor_cond_density P W hW τ hτ
    unfold IsCondDensity IsJointDensity at hc2
    unfold IsJointDensity
    rw [h_law_map, hc2]
    have h_meas_f : Measurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal (gaussianPDFReal 0 τ p.2 * yorCondDensity (τ : ℝ) p.1 p.2)) := by
      have h_yc_meas : Measurable (Function.uncurry (yorCondDensity (τ : ℝ))) := by
        have h_pw : Function.uncurry (yorCondDensity (τ : ℝ)) =
            Set.piecewise (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))
              (Function.uncurry (yorCondDensity (τ : ℝ))) (fun _ => 0) := by
          ext p
          by_cases hp : p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)
          · simp [Set.piecewise, hp]
          · have hle : ¬ (0 < p.1) := fun h => hp ⟨h, trivial⟩
            simp [Set.piecewise, hp, Function.uncurry, yorCondDensity, hle]
        rw [h_pw]
        exact (yorCondDensity_contDiffOn (by exact_mod_cast hτ) 0).continuousOn.measurable_piecewise
          continuousOn_const (measurableSet_Ioi.prod MeasurableSet.univ)
      have hg_meas : Measurable (gaussianPDFReal 0 τ) := by
        rw [gaussianPDFReal_def]
        fun_prop
      exact ((hg_meas.comp measurable_snd).mul h_yc_meas).ennreal_ofReal
    rw [map_prod_mul_withDensity (inv_ne_zero (pow_ne_zero 2 hα.ne')) (inv_ne_zero hα.ne') _ h_meas_f]
    congr 1
    funext p
    simp only [inv_inv, abs_of_pos hα, abs_of_pos (sq_pos_of_pos hα)]
    have h_gpdf : α * gaussianPDFReal 0 τ (α * p.2) = gaussianPDFReal 0 t p.2 := by
      have htR : (0 : ℝ) < t := ht
      have hsqrt : Real.sqrt (2 * Real.pi * (τ : ℝ)) = α * Real.sqrt (2 * Real.pi * (t : ℝ)) := by
        rw [hτR, show 2 * Real.pi * (α ^ 2 * (t : ℝ)) = α ^ 2 * (2 * Real.pi * t) by ring,
          Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hα.le]
      have hexp : -(α * p.2 - 0) ^ 2 / (2 * (τ : ℝ)) = -(p.2 - 0) ^ 2 / (2 * (t : ℝ)) := by
        rw [hτR]; field_simp [hα.ne', htR.ne']; ring
      simp only [gaussianPDFReal_def, hsqrt, hexp]
      have hne : Real.sqrt (2 * Real.pi * (t : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
      field_simp [hα.ne', hne]
    rw [← ENNReal.ofReal_mul hα.le, ← ENNReal.ofReal_mul (mul_nonneg hα.le (sq_nonneg α))]
    congr 1
    dsimp only [φc]
    rw [← h_gpdf]
    ring
  · -- 2. `ContDiffOn`
    intro n
    have hmap : MapsTo (fun p : ℝ × ℝ => (α ^ 2 * p.1, α * p.2))
        (Ioi (0 : ℝ) ×ˢ univ) (Ioi (0 : ℝ) ×ˢ univ) :=
      fun p hp => ⟨mul_pos (sq_pos_of_pos hα) hp.1, trivial⟩
    have hcd := (yorCondDensity_contDiffOn (by exact_mod_cast hτ) n).comp
      ((contDiffOn_const.mul contDiffOn_fst).prodMk (contDiffOn_const.mul contDiffOn_snd)) hmap
    exact contDiffOn_const.mul hcd
  · -- 3. `φc x y → 0` as `x → 0⁺`
    intro y
    have h_lim_x : Tendsto (fun x => α ^ 2 * x) (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Ioi 0)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have h0 : Tendsto (fun x : ℝ => α ^ 2 * x) (nhdsWithin 0 (Ioi 0)) (nhds (α ^ 2 * 0)) :=
          (continuous_const.mul continuous_id).continuousWithinAt.tendsto
        simpa [mul_zero] using h0
      · filter_upwards [self_mem_nhdsWithin] with x hx
        exact mul_pos (sq_pos_of_pos hα) hx
    have h_eq : (fun x => φc x y) =ᶠ[nhdsWithin 0 (Ioi 0)]
        fun x => α ^ 2 * evalYorSum (τ : ℝ) (yorPdList (τ : ℝ) 0 0) (α ^ 2 * x) (α * y) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hpd := pd_yorCondDensity_eq_evalYorSum (by exact_mod_cast hτ : (0 : ℝ) < τ) 0 0
        (mul_pos (sq_pos_of_pos hα) hx) (α * y)
      dsimp only [φc]
      rw [← hpd]
      simp [pd, iteratedDeriv_zero]
    refine Tendsto.congr' h_eq.symm ?_
    simpa [mul_zero] using
      ((evalYorSum_tendsto_zero_right (by exact_mod_cast hτ : (0 : ℝ) < τ)
        (yorPdList (τ : ℝ) 0 0) (α * y)).comp h_lim_x).const_mul (α ^ 2)
  · -- 4. `pd m n φc x y → 0` as `x → ∞`
    intro m n y
    have h_lim_x : Tendsto (fun x => α ^ 2 * x) atTop atTop :=
      tendsto_id.const_mul_atTop (sq_pos_of_pos hα)
    have h_eq : (fun x => pd m n φc x y) =ᶠ[atTop]
        fun x => α ^ (2 + 2 * m + n) *
          evalYorSum (τ : ℝ) (yorPdList (τ : ℝ) m n) (α ^ 2 * x) (α * y) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [pd_yorCondDensity_scaled (by exact_mod_cast hτ : (0 : ℝ) < τ) hα m n hx y,
        pd_yorCondDensity_eq_evalYorSum (by exact_mod_cast hτ : (0 : ℝ) < τ) m n
          (mul_pos (sq_pos_of_pos hα) hx) (α * y)]
    refine Tendsto.congr' h_eq.symm ?_
    simpa [mul_zero] using
      ((evalYorSum_tendsto_zero_atTop (by exact_mod_cast hτ : (0 : ℝ) < τ)
        (yorPdList (τ : ℝ) m n) (α * y)).comp h_lim_x).const_mul (α ^ (2 + 2 * m + n))
  · -- 5. `∃ l, pd m n φc x y → l` as `x → 0⁺` (with `l = 0`)
    intro m n y
    refine ⟨0, ?_⟩
    have h_lim_x : Tendsto (fun x => α ^ 2 * x) (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Ioi 0)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have h0 : Tendsto (fun x : ℝ => α ^ 2 * x) (nhdsWithin 0 (Ioi 0)) (nhds (α ^ 2 * 0)) :=
          (continuous_const.mul continuous_id).continuousWithinAt.tendsto
        simpa [mul_zero] using h0
      · filter_upwards [self_mem_nhdsWithin] with x hx
        exact mul_pos (sq_pos_of_pos hα) hx
    have h_eq : (fun x => pd m n φc x y) =ᶠ[nhdsWithin 0 (Ioi 0)]
        fun x => α ^ (2 + 2 * m + n) *
          evalYorSum (τ : ℝ) (yorPdList (τ : ℝ) m n) (α ^ 2 * x) (α * y) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [pd_yorCondDensity_scaled (by exact_mod_cast hτ : (0 : ℝ) < τ) hα m n hx y,
        pd_yorCondDensity_eq_evalYorSum (by exact_mod_cast hτ : (0 : ℝ) < τ) m n
          (mul_pos (sq_pos_of_pos hα) hx) (α * y)]
    refine Tendsto.congr' h_eq.symm ?_
    simpa [mul_zero] using
      ((evalYorSum_tendsto_zero_right (by exact_mod_cast hτ : (0 : ℝ) < τ)
        (yorPdList (τ : ℝ) m n) (α * y)).comp h_lim_x).const_mul (α ^ (2 + 2 * m + n))
  · -- 6. Gaussian-weighted `L¹` moment bounds
    intro m n p
    have h_moment_s : ∀ s : ℤ, s ≤ (p : ℤ) →
        (∫⁻ y, ENNReal.ofReal (Real.exp (-y ^ 2 / (2 * (t : ℝ)))) *
          ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |(x : ℝ) ^ s * pd m n φc x y|) < ∞ := by
      intro s hs
      obtain ⟨g, hg_int, hg_nn, hg⟩ := evalYorSum_moment_majorant
        (by exact_mod_cast hτ : (0 : ℝ) < τ) (yorPdList (τ : ℝ) m n) p hs
      let Cs : ℝ := (α ^ 2) ^ (-s) * α ^ (2 + 2 * m + n)
      have hCs_nn : 0 ≤ Cs := by positivity
      have h_le_y : ∀ y : ℝ,
          ENNReal.ofReal (Real.exp (-y ^ 2 / (2 * (t : ℝ)))) *
            (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |(x : ℝ) ^ s * pd m n φc x y|) ≤
          ENNReal.ofReal (Cs * (α ^ 2)⁻¹ * g (α * y)) := by
        intro y
        have h_eq_x : Set.EqOn
            (fun x : ℝ => ENNReal.ofReal |(x : ℝ) ^ s * pd m n φc x y|)
            (fun x : ℝ => ENNReal.ofReal Cs *
              ENNReal.ofReal |(α ^ 2 * x) ^ s *
                evalYorSum (τ : ℝ) (yorPdList (τ : ℝ) m n) (α ^ 2 * x) (α * y)|)
            (Ioi 0) := by
          intro x hx
          have hx0 : 0 < x := hx
          dsimp only
          rw [← ENNReal.ofReal_mul hCs_nn]
          congr 1
          rw [pd_yorCondDensity_scaled (by exact_mod_cast hτ : (0 : ℝ) < τ) hα m n hx0 y,
            pd_yorCondDensity_eq_evalYorSum (by exact_mod_cast hτ : (0 : ℝ) < τ) m n
              (mul_pos (sq_pos_of_pos hα) hx0) (α * y)]
          have hpow : x ^ s = (α ^ 2) ^ (-s) * (α ^ 2 * x) ^ s := by
            rw [mul_zpow, ← mul_assoc, ← zpow_add₀ (pow_ne_zero 2 hα.ne'), neg_add_cancel,
              zpow_zero, one_mul]
          rw [hpow, show ((α ^ 2) ^ (-s) * (α ^ 2 * x) ^ s) *
              (α ^ (2 + 2 * m + n) * evalYorSum (τ : ℝ) (yorPdList (τ : ℝ) m n) (α ^ 2 * x) (α * y)) =
              Cs * ((α ^ 2 * x) ^ s * evalYorSum (τ : ℝ) (yorPdList (τ : ℝ) m n) (α ^ 2 * x) (α * y)) by
                dsimp only [Cs]; ring, abs_mul, abs_of_nonneg hCs_nn]
        have hm_u : AEMeasurable
            (fun u : ℝ => ENNReal.ofReal |u ^ s *
              evalYorSum (τ : ℝ) (yorPdList (τ : ℝ) m n) u (α * y)|)
            (volume.restrict (Ioi 0)) := by
          have hcont : ContinuousOn
              (fun u : ℝ => ENNReal.ofReal |u ^ s *
                evalYorSum (τ : ℝ) (yorPdList (τ : ℝ) m n) u (α * y)|) (Ioi 0) := by
            refine ENNReal.continuous_ofReal.comp_continuousOn ?_
            refine ContinuousOn.abs (ContinuousOn.mul ?_
              (evalYorSum_contDiffOn_x (by exact_mod_cast hτ : (0 : ℝ) < τ)
                (yorPdList (τ : ℝ) m n) 0 (α * y)).continuousOn)
            exact continuousOn_id.zpow₀ s (fun u hu => Or.inl hu.ne')
          exact hcont.aemeasurable measurableSet_Ioi
        have h_in_eq :
            (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |(x : ℝ) ^ s * pd m n φc x y|) =
            ENNReal.ofReal (Cs * (α ^ 2)⁻¹) *
              ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal |u ^ s *
                evalYorSum (τ : ℝ) (yorPdList (τ : ℝ) m n) u (α * y)| := by
          rw [setLIntegral_congr_fun measurableSet_Ioi h_eq_x,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_Ioi_comp_mul_left (sq_pos_of_pos hα) hm_u, ← mul_assoc,
            ← ENNReal.ofReal_mul hCs_nn]
        have hexp_y : Real.exp (-y ^ 2 / (2 * (t : ℝ))) =
            Real.exp (-(α * y) ^ 2 / (2 * (τ : ℝ))) := by
          have htR : (0 : ℝ) < t := ht
          rw [hτR]; congr 1; field_simp [hα.ne', htR.ne']
        rw [h_in_eq, hexp_y]
        calc ENNReal.ofReal (Real.exp (-(α * y) ^ 2 / (2 * (τ : ℝ)))) *
              (ENNReal.ofReal (Cs * (α ^ 2)⁻¹) *
                ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal |u ^ s *
                  evalYorSum (τ : ℝ) (yorPdList (τ : ℝ) m n) u (α * y)|)
            = ENNReal.ofReal (Cs * (α ^ 2)⁻¹) *
                (ENNReal.ofReal (Real.exp (-(α * y) ^ 2 / (2 * (τ : ℝ)))) *
                  ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal |u ^ s *
                    evalYorSum (τ : ℝ) (yorPdList (τ : ℝ) m n) u (α * y)|) := by ring
          _ ≤ ENNReal.ofReal (Cs * (α ^ 2)⁻¹) * ENNReal.ofReal (g (α * y)) := by
              gcongr; exact hg (α * y)
          _ = ENNReal.ofReal (Cs * (α ^ 2)⁻¹ * g (α * y)) :=
              (ENNReal.ofReal_mul (mul_nonneg hCs_nn (inv_nonneg.mpr (sq_nonneg α)))).symm
      have hg_scaled : Integrable (fun y : ℝ => Cs * (α ^ 2)⁻¹ * g (α * y)) :=
        (hg_int.comp_mul_left' hα.ne').const_mul _
      calc (∫⁻ y, ENNReal.ofReal (Real.exp (-y ^ 2 / (2 * (t : ℝ)))) *
              ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |(x : ℝ) ^ s * pd m n φc x y|)
          ≤ ∫⁻ y, ENNReal.ofReal (Cs * (α ^ 2)⁻¹ * g (α * y)) := lintegral_mono h_le_y
        _ < ∞ := hg_scaled.lintegral_lt_top
    exact ⟨h_moment_s (p : ℤ) le_rfl, h_moment_s (-(p : ℤ)) (by omega)⟩

end EvalSumAndScaling

end Lyasoff2016

