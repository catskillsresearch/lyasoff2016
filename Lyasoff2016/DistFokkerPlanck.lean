/-
Distributional Fokker–Planck equation and inverse-argument Laplace transform for `(∫₀ᵗ e^{2 W_s} ds, W_t)`.
-/
module

public import Lyasoff2016.ExpectedIto
public import Lyasoff2016.ExpInvCut

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

open MathFin ItoIntegralL2

section DistFokkerPlanck

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma measurable_expInt_bm
    {B : ℝ≥0 → Ω → ℝ} (hBmeas : ∀ s, Measurable (B s)) (hBcont : ∀ ω, Continuous (B · ω))
    (c : ℝ) (s : ℝ≥0) :
    Measurable (expInt B c 0 s) := by
  have heq : expInt B c 0 s = fun ω => ∫ r in (0 : ℝ)..(s : ℝ), Real.exp (c * B r.toNNReal ω) := by
    funext ω; simp [expInt]
  rw [heq]
  exact (measurable_pathIntegral_natFiltration hBmeas hBcont
    (by fun_prop : Continuous fun y => Real.exp (c * y)) s).mono
    ((natFiltration hBmeas).le s) le_rfl

omit [MeasurableSpace Ω] in
private lemma continuous_expInt_bm
    {B : ℝ≥0 → Ω → ℝ} (hBcont : ∀ ω, Continuous (B · ω)) (c : ℝ) (ω : Ω) :
    Continuous fun r : ℝ => expInt B c 0 r.toNNReal ω := by
  have heq : (fun r : ℝ => expInt B c 0 r.toNNReal ω) =
      fun r : ℝ => ∫ s in (0 : ℝ)..(r.toNNReal : ℝ), Real.exp (c * B s.toNNReal ω) := by
    funext r; simp [expInt]
  rw [heq]
  exact (continuous_pathIntegral_nnreal (Real.continuous_exp.comp
    (continuous_const.mul (hBcont ω)))).comp continuous_real_toNNReal

private lemma continuous_expectation_expInt_aux
    {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (hBmeas : ∀ s, Measurable (B s)) (hBcont : ∀ ω, Continuous (B · ω))
    (c : ℝ) (H : ℝ → ℝ → ℝ) (hH : Continuous (Function.uncurry H))
    {M : ℝ} (hM : ∀ (r : ℝ) (ω : Ω), |H (expInt B c 0 r.toNNReal ω) (B r.toNNReal ω)| ≤ M) :
    Continuous fun r : ℝ => ∫ ω, H (expInt B c 0 r.toNNReal ω) (B r.toNNReal ω) ∂P := by
  rw [continuous_iff_seqContinuous]
  intro rn r₀ hrn
  refine tendsto_integral_of_dominated_convergence (fun _ => M) ?_ (integrable_const M) ?_ ?_
  · intro k
    exact (hH.measurable.comp ((measurable_expInt_bm hBmeas hBcont c (rn k).toNNReal).prodMk
      (hBmeas _))).aestronglyMeasurable
  · intro k
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact hM (rn k) ω
  · filter_upwards with ω
    have hcont : Continuous fun r : ℝ =>
        H (expInt B c 0 r.toNNReal ω) (B r.toNNReal ω) :=
      hH.comp ((continuous_expInt_bm hBcont c ω).prodMk ((hBcont ω).comp continuous_real_toNNReal))
    exact hcont.continuousAt.tendsto.comp hrn

/-- Fixed-`u` distributional Fokker–Planck identity for `(expInt W 2 0 t, W t)`:
for every `t > 0`, `u > 0`, and `ψ ∈ C_c^3(ℝ)`,
`E[(2 X_t² φ_u''(X_t) + (1 + 2 X_t - e^{2 W_t}) φ_u'(X_t)) ψ(W_t) + 2 X_t φ_u'(X_t) ψ'(W_t)] = 0`. -/
theorem jointLaw_two_fp_u (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W)
    (t : ℝ≥0) (ht : 0 < t) {u : ℝ} (hu : 0 < u)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 3 ψ) (hψC : HasCompactSupport ψ) :
    ∫ ω, (2 * expInt W 2 0 t ω ^ 2 * expInvCut₂ u (expInt W 2 0 t ω) * ψ (W t ω) +
        2 * expInt W 2 0 t ω * expInvCut₁ u (expInt W 2 0 t ω) * deriv ψ (W t ω) +
        (1 + 2 * expInt W 2 0 t ω - Real.exp (2 * W t ω)) *
          expInvCut₁ u (expInt W 2 0 t ω) * ψ (W t ω)) ∂P = 0 := by
  let B : ℝ≥0 → Ω → ℝ := hW.toIsPreBrownianReal.mk W
  have hBmeas : ∀ s, Measurable (B s) := hW.toIsPreBrownianReal.measurable_mk
  have hBcont : ∀ ω, Continuous (B · ω) := hW.toIsPreBrownianReal.continuous_mk
  have hBpre : IsPreBrownianReal B P :=
    hW.toIsPreBrownianReal.isBrownianReal_mk.toIsPreBrownianReal
  have hB0 : ∀ᵐ ω ∂P, B 0 ω = 0 :=
    (hW.toIsPreBrownianReal.isBrownianReal_mk).eval_zero_ae_eq_zero
  have hBW : ∀ᵐ ω ∂P, ∀ s, B s ω = W s ω := hW.mk_ae_forall_eq
  have hBW_int : ∫ ω, (2 * expInt W 2 0 t ω ^ 2 * expInvCut₂ u (expInt W 2 0 t ω) * ψ (W t ω) +
        2 * expInt W 2 0 t ω * expInvCut₁ u (expInt W 2 0 t ω) * deriv ψ (W t ω) +
        (1 + 2 * expInt W 2 0 t ω - Real.exp (2 * W t ω)) *
          expInvCut₁ u (expInt W 2 0 t ω) * ψ (W t ω)) ∂P =
      ∫ ω, (2 * expInt B 2 0 t ω ^ 2 * expInvCut₂ u (expInt B 2 0 t ω) * ψ (B t ω) +
        2 * expInt B 2 0 t ω * expInvCut₁ u (expInt B 2 0 t ω) * deriv ψ (B t ω) +
        (1 + 2 * expInt B 2 0 t ω - Real.exp (2 * B t ω)) *
          expInvCut₁ u (expInt B 2 0 t ω) * ψ (B t ω)) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hBW] with ω hω
    have hX : expInt W 2 0 t ω = expInt B 2 0 t ω := by
      simp only [expInt]
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [hω s.toNNReal]
    rw [hX, hω t]
  rw [hBW_int]
  obtain ⟨Ccut, hCcut0, hcut0, hcut1, hcut2, hcut3⟩ := expInvCut_bounds hu
  obtain ⟨hm1, hm2, hm3⟩ := mul_expInvCut_bounds hu
  obtain ⟨Cψ, R, hCψ0, _, hsupp, hψ0, hψ1, hψ2, hψ3⟩ :=
    contDiff_three_compactSupport_bounds hψ hψC
  obtain ⟨hc_cut0, hc_cut1, hc_cut2⟩ := continuous_expInvCut hu
  have hψ_deriv1 : ∀ y, HasDerivAt ψ (deriv ψ y) y := fun y =>
    ((hψ.of_le (by decide : (1 : WithTop ℕ∞) ≤ 3)).differentiable (by decide)).differentiableAt.hasDerivAt
  have hψ_deriv2 : ∀ y, HasDerivAt (deriv ψ) (deriv (deriv ψ) y) y := fun y =>
    (((contDiff_succ_iff_deriv (n := 2)).mp hψ).2.2.of_le
      (by decide : (1 : WithTop ℕ∞) ≤ 2)).differentiable (by decide) |>.differentiableAt.hasDerivAt
  have hψ_deriv3 : ∀ y, HasDerivAt (deriv (deriv ψ)) (deriv (deriv (deriv ψ)) y) y := fun y =>
    (((contDiff_succ_iff_deriv (n := 1)).mp
      ((contDiff_succ_iff_deriv (n := 2)).mp hψ).2.2).2.2).differentiable (by decide)
      |>.differentiableAt.hasDerivAt
  have hcψ0 : Continuous ψ := hψ.continuous
  have hcψ1 : Continuous (deriv ψ) := ((contDiff_succ_iff_deriv (n := 2)).mp hψ).2.2.continuous
  have hcψ2 : Continuous (deriv (deriv ψ)) :=
    ((contDiff_succ_iff_deriv (n := 1)).mp
      ((contDiff_succ_iff_deriv (n := 2)).mp hψ).2.2).2.2.continuous
  let F₁ : ℝ → ℝ → ℝ := fun x y => expInvCut u x * ψ y
  let F₁_x : ℝ → ℝ → ℝ := fun x y => expInvCut₁ u x * ψ y
  let F₁_y : ℝ → ℝ → ℝ := fun x y => expInvCut u x * deriv ψ y
  let F₁_xx : ℝ → ℝ → ℝ := fun x y => expInvCut₂ u x * ψ y
  let F₁_xy : ℝ → ℝ → ℝ := fun x y => expInvCut₁ u x * deriv ψ y
  let F₁_yy : ℝ → ℝ → ℝ := fun x y => expInvCut u x * deriv (deriv ψ) y
  let F₁_yyy : ℝ → ℝ → ℝ := fun x y => expInvCut u x * deriv (deriv (deriv ψ)) y
  let M₁ : ℝ := Ccut * Cψ
  have hM₁ : 0 ≤ M₁ := mul_nonneg hCcut0 hCψ0
  let F₂ : ℝ → ℝ → ℝ := fun z y => expInvCut u (Real.exp (2 * y) * z) * ψ y
  let F₂_z : ℝ → ℝ → ℝ := fun z y => Real.exp (2 * y) * expInvCut₁ u (Real.exp (2 * y) * z) * ψ y
  let F₂_zz : ℝ → ℝ → ℝ := fun z y => Real.exp (4 * y) * expInvCut₂ u (Real.exp (2 * y) * z) * ψ y
  let F₂_y : ℝ → ℝ → ℝ := fun z y =>
    2 * (Real.exp (2 * y) * z) * expInvCut₁ u (Real.exp (2 * y) * z) * ψ y +
      expInvCut u (Real.exp (2 * y) * z) * deriv ψ y
  let F₂_zy : ℝ → ℝ → ℝ := fun z y =>
    (2 * Real.exp (2 * y) * expInvCut₁ u (Real.exp (2 * y) * z) +
      2 * Real.exp (2 * y) * (Real.exp (2 * y) * z) * expInvCut₂ u (Real.exp (2 * y) * z)) * ψ y +
      Real.exp (2 * y) * expInvCut₁ u (Real.exp (2 * y) * z) * deriv ψ y
  let F₂_yy : ℝ → ℝ → ℝ := fun z y =>
    (4 * (Real.exp (2 * y) * z) * expInvCut₁ u (Real.exp (2 * y) * z) +
      4 * (Real.exp (2 * y) * z) ^ 2 * expInvCut₂ u (Real.exp (2 * y) * z)) * ψ y +
      4 * (Real.exp (2 * y) * z) * expInvCut₁ u (Real.exp (2 * y) * z) * deriv ψ y +
      expInvCut u (Real.exp (2 * y) * z) * deriv (deriv ψ) y
  let F₂_yyy : ℝ → ℝ → ℝ := fun z y =>
    (8 * (Real.exp (2 * y) * z) * expInvCut₁ u (Real.exp (2 * y) * z) +
      24 * (Real.exp (2 * y) * z) ^ 2 * expInvCut₂ u (Real.exp (2 * y) * z) +
      8 * (Real.exp (2 * y) * z) ^ 3 * expInvCut₃ u (Real.exp (2 * y) * z)) * ψ y +
      (12 * (Real.exp (2 * y) * z) * expInvCut₁ u (Real.exp (2 * y) * z) +
        12 * (Real.exp (2 * y) * z) ^ 2 * expInvCut₂ u (Real.exp (2 * y) * z)) * deriv ψ y +
      6 * (Real.exp (2 * y) * z) * expInvCut₁ u (Real.exp (2 * y) * z) * deriv (deriv ψ) y +
      expInvCut u (Real.exp (2 * y) * z) * deriv (deriv (deriv ψ)) y
  have hexp_ψ : ∀ (k : ℕ) (y : ℝ),
      (Real.exp ((k : ℝ) * y) * |ψ y| ≤ Real.exp ((k : ℝ) * R) * Cψ) ∧
      (Real.exp ((k : ℝ) * y) * |deriv ψ y| ≤ Real.exp ((k : ℝ) * R) * Cψ) ∧
      (Real.exp ((k : ℝ) * y) * |deriv (deriv ψ) y| ≤ Real.exp ((k : ℝ) * R) * Cψ) ∧
      (Real.exp ((k : ℝ) * y) * |deriv (deriv (deriv ψ)) y| ≤ Real.exp ((k : ℝ) * R) * Cψ) := by
    intro k y
    by_cases hy : R ≤ |y|
    · obtain ⟨h0, h1, h2, h3⟩ := hsupp y hy
      simp only [h0, h1, h2, h3, abs_zero, mul_zero]
      exact ⟨mul_nonneg (Real.exp_pos _).le hCψ0, mul_nonneg (Real.exp_pos _).le hCψ0,
        mul_nonneg (Real.exp_pos _).le hCψ0, mul_nonneg (Real.exp_pos _).le hCψ0⟩
    · have hylt : y ≤ R := (le_abs_self y).trans (not_le.mp hy).le
      have hexp : Real.exp ((k : ℝ) * y) ≤ Real.exp ((k : ℝ) * R) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hylt (Nat.cast_nonneg k))
      refine ⟨mul_le_mul hexp (hψ0 y) (abs_nonneg _) (Real.exp_pos _).le,
        mul_le_mul hexp (hψ1 y) (abs_nonneg _) (Real.exp_pos _).le,
        mul_le_mul hexp (hψ2 y) (abs_nonneg _) (Real.exp_pos _).le,
        mul_le_mul hexp (hψ3 y) (abs_nonneg _) (Real.exp_pos _).le⟩
  let E4 := Real.exp (4 * R)
  have hE1 : Real.exp (2 * R) ≤ E4 := Real.exp_le_exp.mpr (by linarith)
  have hE0 : 1 ≤ E4 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
  let M₂ : ℝ := 10 * (E4 * (Ccut + 1) + 400) * (Ccut + Cψ + 10)
  have hM₂ : 0 ≤ M₂ := by positivity
  have hd_ez : ∀ z y, HasDerivAt (fun y' => Real.exp (2 * y') * z) (2 * (Real.exp (2 * y) * z)) y := by
    intro z y
    have h1 : HasDerivAt (fun y' : ℝ => 2 * y') 2 y := by
      have h := (hasDerivAt_id' y).const_mul (2 : ℝ)
      simpa using h
    have h2 : HasDerivAt (fun y' : ℝ => Real.exp (2 * y')) (Real.exp (2 * y) * 2) y := h1.exp
    have h3 : HasDerivAt (fun y' : ℝ => Real.exp (2 * y') * z) ((Real.exp (2 * y) * 2) * z) y :=
      h2.mul_const z
    rwa [show (Real.exp (2 * y) * 2) * z = 2 * (Real.exp (2 * y) * z) by ring] at h3
  have hF₂_z : ∀ z y, HasDerivAt (fun z' => F₂ z' y) (F₂_z z y) z := by
    intro z y
    have h1 : HasDerivAt (fun z' : ℝ => Real.exp (2 * y) * z') (Real.exp (2 * y)) z := by
      have h := (hasDerivAt_id' z).const_mul (Real.exp (2 * y))
      simpa using h
    have h2 : HasDerivAt (fun z' => expInvCut u (Real.exp (2 * y) * z'))
        (expInvCut₁ u (Real.exp (2 * y) * z) * Real.exp (2 * y)) z :=
      (hasDerivAt_expInvCut hu (Real.exp (2 * y) * z)).comp z h1
    have h3 := h2.mul_const (ψ y)
    rwa [show expInvCut₁ u (Real.exp (2 * y) * z) * Real.exp (2 * y) * ψ y = F₂_z z y by
      simp only [F₂_z]; ring] at h3
  have hF₂_zz : ∀ z y, HasDerivAt (fun z' => F₂_z z' y) (F₂_zz z y) z := by
    intro z y
    have h1 : HasDerivAt (fun z' : ℝ => Real.exp (2 * y) * z') (Real.exp (2 * y)) z := by
      have h := (hasDerivAt_id' z).const_mul (Real.exp (2 * y))
      simpa using h
    have h2 : HasDerivAt (fun z' => expInvCut₁ u (Real.exp (2 * y) * z'))
        (expInvCut₂ u (Real.exp (2 * y) * z) * Real.exp (2 * y)) z :=
      (hasDerivAt_expInvCut₁ hu (Real.exp (2 * y) * z)).comp z h1
    have h3 := (h2.const_mul (Real.exp (2 * y))).mul_const (ψ y)
    have hfun : (fun z' => Real.exp (2 * y) * expInvCut₁ u (Real.exp (2 * y) * z') * ψ y) =
        fun z' => F₂_z z' y := rfl
    have hder : Real.exp (2 * y) * (expInvCut₂ u (Real.exp (2 * y) * z) * Real.exp (2 * y)) * ψ y =
        F₂_zz z y := by
      simp only [F₂_zz]
      rw [show Real.exp (2 * y) * (expInvCut₂ u (Real.exp (2 * y) * z) * Real.exp (2 * y)) * ψ y =
          (Real.exp (2 * y) * Real.exp (2 * y)) * expInvCut₂ u (Real.exp (2 * y) * z) * ψ y by ring,
        ← Real.exp_add, show 2 * y + 2 * y = 4 * y by ring]
    rw [hfun, hder] at h3
    exact h3
  have hF₂_zy : ∀ z y, HasDerivAt (fun y' => F₂_z z y') (F₂_zy z y) y := by
    intro z y
    have he2 : HasDerivAt (fun y' : ℝ => Real.exp (2 * y')) (Real.exp (2 * y) * 2) y := by
      have h1 : HasDerivAt (fun y' : ℝ => 2 * y') 2 y := by
        have h := (hasDerivAt_id' y).const_mul (2 : ℝ)
        simpa using h
      exact h1.exp
    have hc1 : HasDerivAt (fun y' => expInvCut₁ u (Real.exp (2 * y') * z))
        (expInvCut₂ u (Real.exp (2 * y) * z) * (2 * (Real.exp (2 * y) * z))) y := by
      simpa [Function.comp_def] using (hasDerivAt_expInvCut₁ hu (Real.exp (2 * y) * z)).comp y (hd_ez z y)
    have hp := (he2.mul hc1).mul (hψ_deriv1 y)
    have hfun : (((fun y' : ℝ => Real.exp (2 * y')) *
        fun y' => expInvCut₁ u (Real.exp (2 * y') * z)) * ψ) = fun y' => F₂_z z y' := rfl
    have hder : (Real.exp (2 * y) * 2 * expInvCut₁ u (Real.exp (2 * y) * z) +
          Real.exp (2 * y) * (expInvCut₂ u (Real.exp (2 * y) * z) * (2 * (Real.exp (2 * y) * z)))) *
        ψ y + (Real.exp (2 * y) * expInvCut₁ u (Real.exp (2 * y) * z)) * deriv ψ y = F₂_zy z y := by
      simp only [F₂_zy]; ring
    rw [hfun] at hp
    exact hp.congr_deriv hder
  have hF₂_y : ∀ z y, HasDerivAt (fun y' => F₂ z y') (F₂_y z y) y := by
    intro z y
    have hc0 : HasDerivAt (fun y' => expInvCut u (Real.exp (2 * y') * z))
        (expInvCut₁ u (Real.exp (2 * y) * z) * (2 * (Real.exp (2 * y) * z))) y := by
      simpa [Function.comp_def] using (hasDerivAt_expInvCut hu (Real.exp (2 * y) * z)).comp y (hd_ez z y)
    have hp := hc0.mul (hψ_deriv1 y)
    have hfun : ((fun y' => expInvCut u (Real.exp (2 * y') * z)) * ψ) = fun y' => F₂ z y' := rfl
    have hder : expInvCut₁ u (Real.exp (2 * y) * z) * (2 * (Real.exp (2 * y) * z)) * ψ y +
        expInvCut u (Real.exp (2 * y) * z) * deriv ψ y = F₂_y z y := by
      simp only [F₂_y]; ring
    rw [hfun] at hp
    exact hp.congr_deriv hder
  have hF₂_yy : ∀ z y, HasDerivAt (fun y' => F₂_y z y') (F₂_yy z y) y := by
    intro z y
    have hc1 : HasDerivAt (fun y' => expInvCut₁ u (Real.exp (2 * y') * z))
        (expInvCut₂ u (Real.exp (2 * y) * z) * (2 * (Real.exp (2 * y) * z))) y := by
      simpa [Function.comp_def] using (hasDerivAt_expInvCut₁ hu (Real.exp (2 * y) * z)).comp y (hd_ez z y)
    have hxc1 : HasDerivAt (fun y' => (Real.exp (2 * y') * z) * expInvCut₁ u (Real.exp (2 * y') * z))
        (2 * (Real.exp (2 * y) * z) * expInvCut₁ u (Real.exp (2 * y) * z) +
          (Real.exp (2 * y) * z) * (expInvCut₂ u (Real.exp (2 * y) * z) * (2 * (Real.exp (2 * y) * z)))) y :=
      (hd_ez z y).fun_mul hc1
    have hc0 : HasDerivAt (fun y' => expInvCut u (Real.exp (2 * y') * z))
        (expInvCut₁ u (Real.exp (2 * y) * z) * (2 * (Real.exp (2 * y) * z))) y := by
      simpa [Function.comp_def] using (hasDerivAt_expInvCut hu (Real.exp (2 * y) * z)).comp y (hd_ez z y)
    have hA := (hxc1.const_mul 2).fun_mul (hψ_deriv1 y)
    have hB := hc0.fun_mul (hψ_deriv2 y)
    have hAB := hA.fun_add hB
    have hfun : (fun y' => 2 * ((Real.exp (2 * y') * z) * expInvCut₁ u (Real.exp (2 * y') * z)) * ψ y' +
        expInvCut u (Real.exp (2 * y') * z) * deriv ψ y') = fun y' => F₂_y z y' := by
      funext y'; simp only [F₂_y]; ring
    rw [hfun] at hAB
    exact hAB.congr_deriv (by simp only [F₂_yy]; ring)
  have hF₂_yyy : ∀ z y, HasDerivAt (fun y' => F₂_yy z y') (F₂_yyy z y) y := by
    intro z y
    have hc1 : HasDerivAt (fun y' => expInvCut₁ u (Real.exp (2 * y') * z))
        (expInvCut₂ u (Real.exp (2 * y) * z) * (2 * (Real.exp (2 * y) * z))) y := by
      simpa [Function.comp_def] using (hasDerivAt_expInvCut₁ hu (Real.exp (2 * y) * z)).comp y (hd_ez z y)
    have hxc1 : HasDerivAt (fun y' => (Real.exp (2 * y') * z) * expInvCut₁ u (Real.exp (2 * y') * z))
        (2 * (Real.exp (2 * y) * z) * expInvCut₁ u (Real.exp (2 * y) * z) +
          (Real.exp (2 * y) * z) * (expInvCut₂ u (Real.exp (2 * y) * z) * (2 * (Real.exp (2 * y) * z)))) y :=
      (hd_ez z y).fun_mul hc1
    have hx2 : HasDerivAt (fun y' => (Real.exp (2 * y') * z) ^ 2)
        (2 * (Real.exp (2 * y) * z) * (2 * (Real.exp (2 * y) * z))) y := by
      have h := (hasDerivAt_pow 2 (Real.exp (2 * y) * z)).comp y (hd_ez z y)
      simpa [Function.comp_def] using h
    have hc2 : HasDerivAt (fun y' => expInvCut₂ u (Real.exp (2 * y') * z))
        (expInvCut₃ u (Real.exp (2 * y) * z) * (2 * (Real.exp (2 * y) * z))) y := by
      simpa [Function.comp_def] using (hasDerivAt_expInvCut₂ hu (Real.exp (2 * y) * z)).comp y (hd_ez z y)
    have hx2c2 : HasDerivAt (fun y' => (Real.exp (2 * y') * z) ^ 2 * expInvCut₂ u (Real.exp (2 * y') * z))
        (2 * (Real.exp (2 * y) * z) * (2 * (Real.exp (2 * y) * z)) *
            expInvCut₂ u (Real.exp (2 * y) * z) +
          (Real.exp (2 * y) * z) ^ 2 *
            (expInvCut₃ u (Real.exp (2 * y) * z) * (2 * (Real.exp (2 * y) * z)))) y :=
      hx2.fun_mul hc2
    have hc0 : HasDerivAt (fun y' => expInvCut u (Real.exp (2 * y') * z))
        (expInvCut₁ u (Real.exp (2 * y) * z) * (2 * (Real.exp (2 * y) * z))) y := by
      simpa [Function.comp_def] using (hasDerivAt_expInvCut hu (Real.exp (2 * y) * z)).comp y (hd_ez z y)
    have hT1 := ((hxc1.const_mul 4).fun_add (hx2c2.const_mul 4)).fun_mul (hψ_deriv1 y)
    have hT2 := (hxc1.const_mul 4).fun_mul (hψ_deriv2 y)
    have hT3 := hc0.fun_mul (hψ_deriv3 y)
    have hT := (hT1.fun_add hT2).fun_add hT3
    have hfun : (fun y' =>
        (4 * ((Real.exp (2 * y') * z) * expInvCut₁ u (Real.exp (2 * y') * z)) +
          4 * ((Real.exp (2 * y') * z) ^ 2 * expInvCut₂ u (Real.exp (2 * y') * z))) * ψ y' +
          4 * ((Real.exp (2 * y') * z) * expInvCut₁ u (Real.exp (2 * y') * z)) * deriv ψ y' +
          expInvCut u (Real.exp (2 * y') * z) * deriv (deriv ψ) y') = fun y' => F₂_yy z y' := by
      funext y'; simp only [F₂_yy]; ring
    rw [hfun] at hT
    exact hT.congr_deriv (by simp only [F₂_yyy]; ring)
  have hF₂_yy_cont : Continuous (Function.uncurry F₂_yy) := by
    have harg : Continuous (fun p : ℝ × ℝ => Real.exp (2 * p.2) * p.1) := by fun_prop
    have hc1 := hc_cut1.comp harg
    have hc2 := hc_cut2.comp harg
    have hc0 := hc_cut0.comp harg
    exact (((((continuous_const.mul harg).mul hc1).add
      ((continuous_const.mul (harg.pow 2)).mul hc2)).mul (hcψ0.comp continuous_snd)).add
      (((continuous_const.mul harg).mul hc1).mul (hcψ1.comp continuous_snd))).add
      (hc0.mul (hcψ2.comp continuous_snd))
  have hm_x2 : ∀ x : ℝ, |x * expInvCut₂ u x| ≤ Ccut + 4 := fun x => by
    have h1 : |x| ≤ 1 + x ^ 2 := by
      rcases le_or_gt 0 x with hx | hx
      · rw [abs_of_nonneg hx]; nlinarith [sq_nonneg (x - 1 / 2)]
      · rw [abs_of_neg hx]; nlinarith [sq_nonneg (x + 1 / 2)]
    calc |x * expInvCut₂ u x| = |x| * |expInvCut₂ u x| := abs_mul _ _
      _ ≤ (1 + x ^ 2) * |expInvCut₂ u x| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = |expInvCut₂ u x| + |x ^ 2 * expInvCut₂ u x| := by
          rw [add_mul, one_mul, abs_mul, abs_sq x]
      _ ≤ Ccut + 4 := add_le_add (hcut2 x) (hm2 x)
  have hbd₂ : (∀ z y, |F₂ z y| ≤ M₂) ∧ (∀ z y, |F₂_z z y| ≤ M₂) ∧
      (∀ z y, |F₂_y z y| ≤ M₂) ∧ (∀ z y, |F₂_zz z y| ≤ M₂) ∧
      (∀ z y, |F₂_zy z y| ≤ M₂) ∧ (∀ z y, |F₂_yy z y| ≤ M₂) ∧
      (∀ z y, |F₂_yyy z y| ≤ M₂) := by
    have h1_le_M : ∀ A B : ℝ, 0 ≤ A → 0 ≤ B → A ≤ 10 * (E4 * (Ccut + 1) + 400) →
        B ≤ Ccut + Cψ + 10 → A * B ≤ M₂ := fun A B _ hB hA' hB' => by
      simp only [M₂]; exact mul_le_mul hA' hB' hB (by positivity)
    have b0 : ∀ z y, |F₂ z y| ≤ M₂ := fun z y => by
      rw [show F₂ z y = expInvCut u (Real.exp (2 * y) * z) * ψ y from rfl, abs_mul]
      calc |expInvCut u (Real.exp (2 * y) * z)| * |ψ y| ≤ Ccut * Cψ :=
            mul_le_mul (hcut0 _) (hψ0 _) (abs_nonneg _) hCcut0
        _ ≤ M₂ := h1_le_M Ccut Cψ hCcut0 hCψ0 (by nlinarith [hE0, hCcut0]) (by linarith [hCcut0])
    have b1 : ∀ z y, |F₂_z z y| ≤ M₂ := fun z y => by
      have h2 := (hexp_ψ 2 y).1
      rw [show ((2 : ℕ) : ℝ) = 2 by norm_num] at h2
      have h2' : Real.exp (2 * y) * |ψ y| ≤ E4 * Cψ :=
        h2.trans (mul_le_mul_of_nonneg_right hE1 hCψ0)
      calc |F₂_z z y| = |expInvCut₁ u (Real.exp (2 * y) * z)| * (Real.exp (2 * y) * |ψ y|) := by
            simp only [F₂_z, abs_mul, abs_of_pos (Real.exp_pos _)]; ring
        _ ≤ Ccut * (E4 * Cψ) := mul_le_mul (hcut1 _) h2' (by positivity) hCcut0
        _ = (E4 * Ccut) * Cψ := by ring
        _ ≤ M₂ := h1_le_M (E4 * Ccut) Cψ (by positivity) hCψ0 (by nlinarith [hE0, hCcut0])
            (by linarith [hCcut0])
    have b2 : ∀ z y, |F₂_y z y| ≤ M₂ := fun z y => by
      set x := Real.exp (2 * y) * z
      have h_eq : F₂_y z y = 2 * (x * expInvCut₁ u x) * ψ y + expInvCut u x * deriv ψ y := by
        simp only [F₂_y]; ring
      calc |F₂_y z y|
          = |2 * (x * expInvCut₁ u x) * ψ y + expInvCut u x * deriv ψ y| := by rw [h_eq]
        _ ≤ 2 * |x * expInvCut₁ u x| * |ψ y| + |expInvCut u x| * |deriv ψ y| := by
            refine (abs_add_le _ _).trans (add_le_add ?_ (by rw [abs_mul]))
            rw [abs_mul, abs_mul, abs_of_pos two_pos]
        _ ≤ 2 * 1 * Cψ + Ccut * Cψ := by gcongr; exact hm1 x; exact hψ0 y; exact hcut0 x; exact hψ1 y
        _ = (2 + Ccut) * Cψ := by ring
        _ ≤ M₂ := h1_le_M (2 + Ccut) Cψ (by positivity) hCψ0 (by nlinarith [hE0, hCcut0])
            (by linarith [hCcut0])
    have b3 : ∀ z y, |F₂_zz z y| ≤ M₂ := fun z y => by
      have h4 := (hexp_ψ 4 y).1
      have h4' : Real.exp (4 * y) * |ψ y| ≤ E4 * Cψ := by simpa [E4] using h4
      calc |F₂_zz z y| = |expInvCut₂ u (Real.exp (2 * y) * z)| * (Real.exp (4 * y) * |ψ y|) := by
            simp only [F₂_zz, abs_mul, abs_of_pos (Real.exp_pos _)]; ring
        _ ≤ Ccut * (E4 * Cψ) := mul_le_mul (hcut2 _) h4' (by positivity) hCcut0
        _ = (E4 * Ccut) * Cψ := by ring
        _ ≤ M₂ := h1_le_M (E4 * Ccut) Cψ (by positivity) hCψ0 (by nlinarith [hE0, hCcut0])
            (by linarith [hCcut0])
    have b4 : ∀ z y, |F₂_zy z y| ≤ M₂ := fun z y => by
      set x := Real.exp (2 * y) * z
      have h20 : Real.exp (2 * y) * |ψ y| ≤ E4 * Cψ := by
        simpa using ((hexp_ψ 2 y).1).trans (mul_le_mul_of_nonneg_right hE1 hCψ0)
      have h21 : Real.exp (2 * y) * |deriv ψ y| ≤ E4 * Cψ := by
        simpa using ((hexp_ψ 2 y).2.1).trans (mul_le_mul_of_nonneg_right hE1 hCψ0)
      have htri : |(2 * Real.exp (2 * y) * expInvCut₁ u x +
            2 * Real.exp (2 * y) * x * expInvCut₂ u x) * ψ y| ≤
          (2 * Ccut + 2 * (Ccut + 4)) * (Real.exp (2 * y) * |ψ y|) := by
        rw [abs_mul]
        calc |2 * Real.exp (2 * y) * expInvCut₁ u x + 2 * Real.exp (2 * y) * x * expInvCut₂ u x| * |ψ y|
            ≤ (2 * Real.exp (2 * y) * |expInvCut₁ u x| +
                2 * Real.exp (2 * y) * |x * expInvCut₂ u x|) * |ψ y| := by
              refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
              refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
              · rw [abs_mul, abs_mul, abs_of_pos two_pos, abs_of_pos (Real.exp_pos _)]
              · rw [show 2 * Real.exp (2 * y) * x * expInvCut₂ u x =
                    2 * Real.exp (2 * y) * (x * expInvCut₂ u x) by ring,
                  abs_mul, abs_mul, abs_of_pos two_pos, abs_of_pos (Real.exp_pos _)]
          _ ≤ (2 * Real.exp (2 * y) * Ccut + 2 * Real.exp (2 * y) * (Ccut + 4)) * |ψ y| := by
              have h1 := hcut1 x
              have h2 := hm_x2 x
              gcongr
          _ = (2 * Ccut + 2 * (Ccut + 4)) * (Real.exp (2 * y) * |ψ y|) := by ring
      calc |F₂_zy z y|
          ≤ |(2 * Real.exp (2 * y) * expInvCut₁ u x +
                2 * Real.exp (2 * y) * x * expInvCut₂ u x) * ψ y| +
              |Real.exp (2 * y) * expInvCut₁ u x * deriv ψ y| := abs_add_le _ _
        _ ≤ (2 * Ccut + 2 * (Ccut + 4)) * (Real.exp (2 * y) * |ψ y|) +
              |expInvCut₁ u x| * (Real.exp (2 * y) * |deriv ψ y|) := by
              gcongr
              rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]; ring_nf; rfl
        _ ≤ (2 * Ccut + 2 * (Ccut + 4)) * (E4 * Cψ) + Ccut * (E4 * Cψ) := by
              gcongr; exact hcut1 x
        _ = (5 * Ccut + 8) * (E4 * Cψ) := by ring
        _ ≤ M₂ := by
            have h1 : 10 * E4 * (Ccut + 1) ≥ 0 := by positivity
            calc (5 * Ccut + 8) * (E4 * Cψ)
                ≤ (10 * (Ccut + 1)) * (E4 * Cψ) := by gcongr; linarith [hCcut0]
              _ = (10 * E4 * (Ccut + 1)) * Cψ := by ring
              _ ≤ M₂ := h1_le_M (10 * E4 * (Ccut + 1)) Cψ h1 hCψ0 (by linarith) (by linarith [hCcut0])
    have b5 : ∀ z y, |F₂_yy z y| ≤ M₂ := fun z y => by
      set x := Real.exp (2 * y) * z
      have hp1 : |4 * (x * expInvCut₁ u x) + 4 * (x ^ 2 * expInvCut₂ u x)| ≤ 4 * 1 + 4 * 4 := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
          exact mul_le_mul_of_nonneg_left (hm1 x) (by norm_num)
        · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
          exact mul_le_mul_of_nonneg_left (hm2 x) (by norm_num)
      have h_eq : F₂_yy z y = (4 * (x * expInvCut₁ u x) + 4 * (x ^ 2 * expInvCut₂ u x)) * ψ y +
          4 * (x * expInvCut₁ u x) * deriv ψ y + expInvCut u x * deriv (deriv ψ) y := by
        simp only [F₂_yy]; ring
      calc |F₂_yy z y|
          = |(4 * (x * expInvCut₁ u x) + 4 * (x ^ 2 * expInvCut₂ u x)) * ψ y +
              4 * (x * expInvCut₁ u x) * deriv ψ y + expInvCut u x * deriv (deriv ψ) y| := by
              rw [h_eq]
        _ ≤ (4 * 1 + 4 * 4) * Cψ + 4 * 1 * Cψ + Ccut * Cψ := by
              refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
              · rw [abs_mul]; exact mul_le_mul hp1 (hψ0 y) (abs_nonneg _) (by norm_num)
              · rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
                exact mul_le_mul (mul_le_mul_of_nonneg_left (hm1 x) (by norm_num)) (hψ1 y)
                  (abs_nonneg _) (by norm_num)
              · rw [abs_mul]; exact mul_le_mul (hcut0 x) (hψ2 y) (abs_nonneg _) hCcut0
        _ = (24 + Ccut) * Cψ := by ring
        _ ≤ M₂ := h1_le_M (24 + Ccut) Cψ (by positivity) hCψ0 (by nlinarith [hE0, hCcut0])
            (by linarith [hCcut0])
    have b6 : ∀ z y, |F₂_yyy z y| ≤ M₂ := fun z y => by
      set x := Real.exp (2 * y) * z
      have hp1 : |8 * (x * expInvCut₁ u x) + 24 * (x ^ 2 * expInvCut₂ u x) +
            8 * (x ^ 3 * expInvCut₃ u x)| ≤ 8 * 1 + 24 * 4 + 8 * 30 := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
        · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
          exact mul_le_mul_of_nonneg_left (hm1 x) (by norm_num)
        · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 24)]
          exact mul_le_mul_of_nonneg_left (hm2 x) (by norm_num)
        · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
          exact mul_le_mul_of_nonneg_left (hm3 x) (by norm_num)
      have hp2 : |12 * (x * expInvCut₁ u x) + 12 * (x ^ 2 * expInvCut₂ u x)| ≤ 12 * 1 + 12 * 4 := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 12)]
          exact mul_le_mul_of_nonneg_left (hm1 x) (by norm_num)
        · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 12)]
          exact mul_le_mul_of_nonneg_left (hm2 x) (by norm_num)
      have h_eq : F₂_yyy z y = (8 * (x * expInvCut₁ u x) + 24 * (x ^ 2 * expInvCut₂ u x) +
            8 * (x ^ 3 * expInvCut₃ u x)) * ψ y +
          (12 * (x * expInvCut₁ u x) + 12 * (x ^ 2 * expInvCut₂ u x)) * deriv ψ y +
          6 * (x * expInvCut₁ u x) * deriv (deriv ψ) y +
          expInvCut u x * deriv (deriv (deriv ψ)) y := by
        simp only [F₂_yyy]; ring
      calc |F₂_yyy z y|
          = |(8 * (x * expInvCut₁ u x) + 24 * (x ^ 2 * expInvCut₂ u x) +
                8 * (x ^ 3 * expInvCut₃ u x)) * ψ y +
              (12 * (x * expInvCut₁ u x) + 12 * (x ^ 2 * expInvCut₂ u x)) * deriv ψ y +
              6 * (x * expInvCut₁ u x) * deriv (deriv ψ) y +
              expInvCut u x * deriv (deriv (deriv ψ)) y| := by rw [h_eq]
        _ ≤ (8 * 1 + 24 * 4 + 8 * 30) * Cψ + (12 * 1 + 12 * 4) * Cψ + 6 * 1 * Cψ + Ccut * Cψ := by
              refine (abs_add_le _ _).trans (add_le_add
                ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)) ?_)
              · rw [abs_mul]; exact mul_le_mul hp1 (hψ0 y) (abs_nonneg _) (by norm_num)
              · rw [abs_mul]; exact mul_le_mul hp2 (hψ1 y) (abs_nonneg _) (by norm_num)
              · rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
                exact mul_le_mul (mul_le_mul_of_nonneg_left (hm1 x) (by norm_num)) (hψ2 y)
                  (abs_nonneg _) (by norm_num)
              · rw [abs_mul]; exact mul_le_mul (hcut0 x) (hψ3 y) (abs_nonneg _) hCcut0
        _ = (410 + Ccut) * Cψ := by ring
        _ ≤ M₂ := h1_le_M (410 + Ccut) Cψ (by positivity) hCψ0 (by nlinarith [hE0, hCcut0])
            (by linarith [hCcut0])
    exact ⟨b0, b1, b2, b3, b4, b5, b6⟩
  have hIto₂ : ∀ s ≤ t + 1,
      ∫ ω, F₂ (expInt B (-2) 0 s ω) (B s ω) ∂P - F₂ 0 0 =
        ∫ r in (0 : ℝ)..(s : ℝ),
          ∫ ω, (F₂_z (expInt B (-2) 0 r.toNNReal ω) (B r.toNNReal ω) * Real.exp (-2 * B r.toNNReal ω) +
            (1 / 2 : ℝ) * F₂_yy (expInt B (-2) 0 r.toNNReal ω) (B r.toNNReal ω)) ∂P := by
    intro s hs
    have h := expected_ito_integral_path
      B hBpre hBmeas hBcont hB0 (fun y => Real.exp (-2 * y)) (by fun_prop)
      (t + 1) (integrable_sq_iSup_exp_preBrownian B hBpre hBmeas hBcont (-2) (t + 1))
      F₂ F₂_z F₂_y F₂_zz F₂_zy F₂_yy F₂_yyy
      hF₂_z hF₂_zz hF₂_zy hF₂_y hF₂_yy hF₂_yyy hF₂_yy_cont hM₂
      hbd₂.1 hbd₂.2.1 hbd₂.2.2.1 hbd₂.2.2.2.1 hbd₂.2.2.2.2.1 hbd₂.2.2.2.2.2.1 hbd₂.2.2.2.2.2.2
      s hs
    have hL : ∫ ω, F₂ (expInt B (-2) 0 s ω) (B s ω) ∂P - F₂ 0 0 =
        ∫ ω, F₂ (∫ r in (0 : ℝ)..(s : ℝ), Real.exp (-2 * B r.toNNReal ω)) (B s ω) ∂P - F₂ 0 0 := by
      simp [expInt]
    rw [hL, h]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le s.coe_nonneg] at hr
    simp only [expInt, zero_mul, add_zero, Real.coe_toNNReal r hr.1]
  have hIto₁' : ∀ s ≤ t + 1,
      ∫ ω, F₁ (expInt B 2 0 s ω) (B s ω) ∂P - F₁ 0 0 =
        ∫ r in (0 : ℝ)..(s : ℝ),
          ∫ ω, (F₁_x (expInt B 2 0 r.toNNReal ω) (B r.toNNReal ω) * Real.exp (2 * B r.toNNReal ω) +
            (1 / 2 : ℝ) * F₁_yy (expInt B 2 0 r.toNNReal ω) (B r.toNNReal ω)) ∂P := by
    intro s hs
    have h := expected_ito_integral_path
      B hBpre hBmeas hBcont hB0 (fun y => Real.exp (2 * y)) (by fun_prop)
      (t + 1) (integrable_sq_iSup_exp_preBrownian B hBpre hBmeas hBcont 2 (t + 1))
      F₁ F₁_x F₁_y F₁_xx F₁_xy F₁_yy F₁_yyy
      (fun x y => (hasDerivAt_expInvCut hu x).mul_const (ψ y))
      (fun x y => (hasDerivAt_expInvCut₁ hu x).mul_const (ψ y))
      (fun x y => (hψ_deriv1 y).const_mul (expInvCut₁ u x))
      (fun x y => (hψ_deriv1 y).const_mul (expInvCut u x))
      (fun x y => (hψ_deriv2 y).const_mul (expInvCut u x))
      (fun x y => (hψ_deriv3 y).const_mul (expInvCut u x))
      ((hc_cut0.comp continuous_fst).mul (hcψ2.comp continuous_snd))
      hM₁
      (fun x y => by rw [abs_mul]; exact mul_le_mul (hcut0 x) (hψ0 y) (abs_nonneg _) hCcut0)
      (fun x y => by rw [abs_mul]; exact mul_le_mul (hcut1 x) (hψ0 y) (abs_nonneg _) hCcut0)
      (fun x y => by rw [abs_mul]; exact mul_le_mul (hcut0 x) (hψ1 y) (abs_nonneg _) hCcut0)
      (fun x y => by rw [abs_mul]; exact mul_le_mul (hcut2 x) (hψ0 y) (abs_nonneg _) hCcut0)
      (fun x y => by rw [abs_mul]; exact mul_le_mul (hcut1 x) (hψ1 y) (abs_nonneg _) hCcut0)
      (fun x y => by rw [abs_mul]; exact mul_le_mul (hcut0 x) (hψ2 y) (abs_nonneg _) hCcut0)
      (fun x y => by rw [abs_mul]; exact mul_le_mul (hcut0 x) (hψ3 y) (abs_nonneg _) hCcut0)
      s hs
    have hL : ∫ ω, F₁ (expInt B 2 0 s ω) (B s ω) ∂P - F₁ 0 0 =
        ∫ ω, F₁ (∫ r in (0 : ℝ)..(s : ℝ), Real.exp (2 * B r.toNNReal ω)) (B s ω) ∂P - F₁ 0 0 := by
      simp [expInt]
    rw [hL, h]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le s.coe_nonneg] at hr
    simp only [expInt, zero_mul, add_zero, Real.coe_toNNReal r hr.1]
  have hBbm : IsBM P B := ⟨hBpre, Eventually.of_forall hBcont⟩
  have htr_law : ∀ r : ℝ≥0,
      P.map (fun ω => (expInt B 2 0 r ω, B r ω)) =
        P.map (fun ω => (Real.exp (2 * B r ω) * expInt B (-2) 0 r ω, B r ω)) := by
    intro r
    let V : Fin 1 → ℝ → ℝ → ℝ := fun _ _ b => Real.exp (2 * b)
    have hV : ∀ i, Continuous (Function.uncurry (V i)) := fun _ => by simp [V]; fun_prop
    have htr := time_reversal P B hBbm 1 V hV r
    let pr : (Fin 1 → ℝ) × ℝ → ℝ × ℝ := fun p => (p.1 0, p.2)
    have hpr : Measurable pr := ((measurable_pi_apply 0).comp measurable_fst).prodMk measurable_snd
    have hmp := congrArg (Measure.map pr) htr
    have hm1 : Measurable (fun ω => (fun _ : Fin 1 =>
        ∫ s in (0 : ℝ)..(r : ℝ), V 0 s (B s.toNNReal ω), B r ω)) :=
      Measurable.prodMk (measurable_pi_iff.2 fun _ => by
        have : (fun ω => ∫ s in (0 : ℝ)..(r : ℝ), V 0 s (B s.toNNReal ω)) = expInt B 2 0 r := by
          funext ω; simp [V, expInt]
        rw [this]
        exact measurable_expInt_bm hBmeas hBcont 2 r) (hBmeas r)
    have hm2 : Measurable (fun ω => (fun _ : Fin 1 =>
        ∫ s in (0 : ℝ)..(r : ℝ), V 0 ((r : ℝ) - s) (B r ω - B s.toNNReal ω), B r ω)) := by
      refine Measurable.prodMk (measurable_pi_iff.2 fun _ => ?_) (hBmeas r)
      have heq : (fun ω => ∫ s in (0 : ℝ)..(r : ℝ),
          V 0 ((r : ℝ) - s) (B r ω - B s.toNNReal ω)) =
          fun ω => Real.exp (2 * B r ω) * expInt B (-2) 0 r ω := by
        funext ω
        simp only [V, expInt, zero_mul, add_zero, ← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun s _ => ?_
        rw [← Real.exp_add]; congr 1; ring
      rw [heq]
      exact (Real.measurable_exp.comp ((hBmeas r).const_mul 2)).mul
        (measurable_expInt_bm hBmeas hBcont (-2) r)
    rw [Measure.map_map hpr hm1, Measure.map_map hpr hm2] at hmp
    have hmp' : P.map (fun ω => (expInt B 2 0 r ω, B r ω)) =
        P.map (fun ω => (∫ s in (0 : ℝ)..(r : ℝ), V 0 ((r : ℝ) - s) (B r ω - B s.toNNReal ω), B r ω)) := by
      simpa only [Function.comp_def, pr, V, expInt, zero_mul, add_zero] using hmp
    refine hmp'.trans (congrArg (fun f => P.map f) ?_)
    funext ω
    refine Prod.ext ?_ rfl
    simp only [V, expInt, zero_mul, add_zero, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [← Real.exp_add]; congr 1; ring
  let G_FP : ℝ → ℝ → ℝ := fun x y =>
    2 * x ^ 2 * expInvCut₂ u x * ψ y + 2 * x * expInvCut₁ u x * deriv ψ y +
      (1 + 2 * x - Real.exp (2 * y)) * expInvCut₁ u x * ψ y
  have hG_FP_cont : Continuous (Function.uncurry G_FP) := by
    have hc_prod : Continuous (fun p : ℝ × ℝ => expInvCut₁ u p.1) := hc_cut1.comp continuous_fst
    have hc_prod2 : Continuous (fun p : ℝ × ℝ => expInvCut₂ u p.1) := hc_cut2.comp continuous_fst
    exact (((((continuous_const.mul (continuous_fst.pow 2)).mul hc_prod2).mul
      (hcψ0.comp continuous_snd)).add
      (((continuous_const.mul continuous_fst).mul hc_prod).mul (hcψ1.comp continuous_snd))).add
      ((((continuous_const.add (continuous_const.mul continuous_fst)).sub
        (Real.continuous_exp.comp (continuous_const.mul continuous_snd))).mul hc_prod).mul
        (hcψ0.comp continuous_snd)))
  have hG_FP_bd : ∃ MG : ℝ, 0 ≤ MG ∧ ∀ x y, |G_FP x y| ≤ MG := by
    have h20 : ∀ y, Real.exp (2 * y) * |ψ y| ≤ E4 * Cψ := fun y =>
      (hexp_ψ 2 y).1.trans (mul_le_mul_of_nonneg_right hE1 hCψ0)
    refine ⟨8 * Cψ + 2 * Cψ + (Ccut + 2 + E4 * Ccut) * Cψ + 1, by positivity, fun x y => ?_⟩
    have ht1 : |2 * x ^ 2 * expInvCut₂ u x * ψ y| ≤ 8 * Cψ := by
      rw [show 2 * x ^ 2 * expInvCut₂ u x * ψ y = 2 * (x ^ 2 * expInvCut₂ u x) * ψ y by ring,
        abs_mul, abs_mul, abs_of_pos two_pos]
      calc 2 * |x ^ 2 * expInvCut₂ u x| * |ψ y| ≤ 2 * 4 * Cψ := by gcongr; exact hm2 x; exact hψ0 y
        _ = 8 * Cψ := by ring
    have ht2 : |2 * x * expInvCut₁ u x * deriv ψ y| ≤ 2 * Cψ := by
      rw [show 2 * x * expInvCut₁ u x * deriv ψ y = 2 * (x * expInvCut₁ u x) * deriv ψ y by ring,
        abs_mul, abs_mul, abs_of_pos two_pos]
      calc 2 * |x * expInvCut₁ u x| * |deriv ψ y| ≤ 2 * 1 * Cψ := by gcongr; exact hm1 x; exact hψ1 y
        _ = 2 * Cψ := by ring
    have ht3 : |(1 + 2 * x - Real.exp (2 * y)) * expInvCut₁ u x * ψ y| ≤
        Ccut * Cψ + 2 * Cψ + E4 * Cψ * Ccut := by
      rw [show (1 + 2 * x - Real.exp (2 * y)) * expInvCut₁ u x * ψ y =
          expInvCut₁ u x * ψ y + 2 * (x * expInvCut₁ u x) * ψ y -
            expInvCut₁ u x * (Real.exp (2 * y) * ψ y) by ring]
      refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
      · rw [abs_mul]; exact mul_le_mul (hcut1 x) (hψ0 y) (abs_nonneg _) hCcut0
      · rw [abs_mul, abs_mul, abs_of_pos two_pos]
        calc 2 * |x * expInvCut₁ u x| * |ψ y| ≤ 2 * 1 * Cψ := by gcongr; exact hm1 x; exact hψ0 y
          _ = 2 * Cψ := by ring
      · rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
        have h := h20 y
        calc |expInvCut₁ u x| * (Real.exp (2 * y) * |ψ y|) ≤ Ccut * (E4 * Cψ) :=
              mul_le_mul (hcut1 x) h (by positivity) hCcut0
          _ = E4 * Cψ * Ccut := by ring
    calc |G_FP x y| ≤ |2 * x ^ 2 * expInvCut₂ u x * ψ y| + |2 * x * expInvCut₁ u x * deriv ψ y| +
          |(1 + 2 * x - Real.exp (2 * y)) * expInvCut₁ u x * ψ y| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ 8 * Cψ + 2 * Cψ + (Ccut * Cψ + 2 * Cψ + E4 * Cψ * Ccut) := by gcongr
      _ ≤ 8 * Cψ + 2 * Cψ + (Ccut + 2 + E4 * Ccut) * Cψ + 1 := by
          have : Ccut * Cψ + 2 * Cψ + E4 * Cψ * Ccut = (Ccut + 2 + E4 * Ccut) * Cψ := by ring
          linarith
  have h_int_zero : ∀ s ≤ t + 1,
      ∫ r in (0 : ℝ)..(s : ℝ),
        ∫ ω, G_FP (expInt B 2 0 r.toNNReal ω) (B r.toNNReal ω) ∂P = 0 := by
    intro s hs
    have hLHS_eq : ∫ ω, F₁ (expInt B 2 0 s ω) (B s ω) ∂P - F₁ 0 0 =
        ∫ ω, F₂ (expInt B (-2) 0 s ω) (B s ω) ∂P - F₂ 0 0 := by
      have hF0 : F₁ 0 0 = F₂ 0 0 := by simp [F₁, F₂]
      rw [hF0]
      congr 1
      have h1 : Measurable (fun ω => (expInt B 2 0 s ω, B s ω)) :=
        (measurable_expInt_bm hBmeas hBcont 2 s).prodMk (hBmeas s)
      have h2 : Measurable (fun ω => (Real.exp (2 * B s ω) * expInt B (-2) 0 s ω, B s ω)) :=
        ((Real.measurable_exp.comp ((hBmeas s).const_mul 2)).mul
          (measurable_expInt_bm hBmeas hBcont (-2) s)).prodMk (hBmeas s)
      have hm1 := (integral_map (μ := P) (f := fun p : ℝ × ℝ => expInvCut u p.1 * ψ p.2)
        h1.aemeasurable
        ((hc_cut0.comp continuous_fst).mul (hcψ0.comp continuous_snd)).aestronglyMeasurable).symm
      have hm2 := (integral_map (μ := P) (f := fun p : ℝ × ℝ => expInvCut u p.1 * ψ p.2)
        h2.aemeasurable
        ((hc_cut0.comp continuous_fst).mul (hcψ0.comp continuous_snd)).aestronglyMeasurable).symm
      calc ∫ ω, F₁ (expInt B 2 0 s ω) (B s ω) ∂P
          = ∫ p : ℝ × ℝ, expInvCut u p.1 * ψ p.2 ∂(P.map fun ω => (expInt B 2 0 s ω, B s ω)) := hm1
        _ = ∫ p : ℝ × ℝ, expInvCut u p.1 * ψ p.2
              ∂(P.map fun ω => (Real.exp (2 * B s ω) * expInt B (-2) 0 s ω, B s ω)) := by
            rw [htr_law s]
        _ = ∫ ω, F₂ (expInt B (-2) 0 s ω) (B s ω) ∂P := by
            simpa [F₂] using hm2.symm
    have hFx_cont : Continuous (Function.uncurry F₁_x) :=
      (hc_cut1.comp continuous_fst).mul (hcψ0.comp continuous_snd)
    have hRHS_eq : ∀ r ∈ uIcc (0 : ℝ) (s : ℝ),
        ∫ ω, (F₂_z (expInt B (-2) 0 r.toNNReal ω) (B r.toNNReal ω) * Real.exp (-2 * B r.toNNReal ω) +
          (1 / 2 : ℝ) * F₂_yy (expInt B (-2) 0 r.toNNReal ω) (B r.toNNReal ω)) ∂P -
        ∫ ω, (F₁_x (expInt B 2 0 r.toNNReal ω) (B r.toNNReal ω) * Real.exp (2 * B r.toNNReal ω) +
          (1 / 2 : ℝ) * F₁_yy (expInt B 2 0 r.toNNReal ω) (B r.toNNReal ω)) ∂P =
        ∫ ω, G_FP (expInt B 2 0 r.toNNReal ω) (B r.toNNReal ω) ∂P := by
      intro r _
      let K₂ : ℝ → ℝ → ℝ := fun x y =>
        2 * x ^ 2 * expInvCut₂ u x * ψ y + 2 * x * expInvCut₁ u x * deriv ψ y +
          (1 + 2 * x) * expInvCut₁ u x * ψ y + (1 / 2 : ℝ) * expInvCut u x * deriv (deriv ψ) y
      have hK₂_eq : ∀ z y,
          F₂_z z y * Real.exp (-2 * y) + (1 / 2 : ℝ) * F₂_yy z y = K₂ (Real.exp (2 * y) * z) y := by
        intro z y
        simp only [F₂_z, F₂_yy, K₂]
        have he : Real.exp (2 * y) * Real.exp (-2 * y) = 1 := by
          rw [← Real.exp_add]; simp
        calc Real.exp (2 * y) * expInvCut₁ u (Real.exp (2 * y) * z) * ψ y * Real.exp (-2 * y) +
              1 / 2 * ((4 * (Real.exp (2 * y) * z) * expInvCut₁ u (Real.exp (2 * y) * z) +
                4 * (Real.exp (2 * y) * z) ^ 2 * expInvCut₂ u (Real.exp (2 * y) * z)) * ψ y +
                4 * (Real.exp (2 * y) * z) * expInvCut₁ u (Real.exp (2 * y) * z) * deriv ψ y +
                expInvCut u (Real.exp (2 * y) * z) * deriv (deriv ψ) y)
            = (Real.exp (2 * y) * Real.exp (-2 * y)) * expInvCut₁ u (Real.exp (2 * y) * z) * ψ y +
                2 * (Real.exp (2 * y) * z) * expInvCut₁ u (Real.exp (2 * y) * z) * ψ y +
                2 * (Real.exp (2 * y) * z) ^ 2 * expInvCut₂ u (Real.exp (2 * y) * z) * ψ y +
                2 * (Real.exp (2 * y) * z) * expInvCut₁ u (Real.exp (2 * y) * z) * deriv ψ y +
                1 / 2 * expInvCut u (Real.exp (2 * y) * z) * deriv (deriv ψ) y := by ring
          _ = _ := by rw [he]; ring
      have hK₂_cont : Continuous (Function.uncurry K₂) := by
        have hfst : Continuous (fun p : ℝ × ℝ => p.1) := continuous_fst
        have hsnd : Continuous (fun p : ℝ × ℝ => p.2) := continuous_snd
        have hc1 := hc_cut1.comp hfst
        have hc2 := hc_cut2.comp hfst
        have hc0 := hc_cut0.comp hfst
        exact (((((continuous_const.mul (hfst.pow 2)).mul hc2).mul (hcψ0.comp hsnd)).add
          (((continuous_const.mul hfst).mul hc1).mul (hcψ1.comp hsnd))).add
          (((continuous_const.add (continuous_const.mul hfst)).mul hc1).mul
            (hcψ0.comp hsnd))).add
          ((continuous_const.mul hc0).mul (hcψ2.comp hsnd))
      have hK₂_law : ∫ ω, K₂ (Real.exp (2 * B r.toNNReal ω) * expInt B (-2) 0 r.toNNReal ω) (B r.toNNReal ω) ∂P =
          ∫ ω, K₂ (expInt B 2 0 r.toNNReal ω) (B r.toNNReal ω) ∂P := by
        have h1 : Measurable (fun ω => (expInt B 2 0 r.toNNReal ω, B r.toNNReal ω)) :=
          (measurable_expInt_bm hBmeas hBcont 2 r.toNNReal).prodMk (hBmeas _)
        have h2 : Measurable (fun ω => (Real.exp (2 * B r.toNNReal ω) * expInt B (-2) 0 r.toNNReal ω, B r.toNNReal ω)) :=
          ((Real.measurable_exp.comp ((hBmeas _).const_mul 2)).mul
            (measurable_expInt_bm hBmeas hBcont (-2) r.toNNReal)).prodMk (hBmeas _)
        have hm1 := (integral_map (μ := P) (f := Function.uncurry K₂)
          h1.aemeasurable hK₂_cont.aestronglyMeasurable).symm
        have hm2 := (integral_map (μ := P) (f := Function.uncurry K₂)
          h2.aemeasurable hK₂_cont.aestronglyMeasurable).symm
        calc ∫ ω, K₂ (Real.exp (2 * B r.toNNReal ω) * expInt B (-2) 0 r.toNNReal ω) (B r.toNNReal ω) ∂P
            = ∫ p : ℝ × ℝ, K₂ p.1 p.2 ∂(P.map fun ω =>
                (Real.exp (2 * B r.toNNReal ω) * expInt B (-2) 0 r.toNNReal ω, B r.toNNReal ω)) := hm2
          _ = ∫ p : ℝ × ℝ, K₂ p.1 p.2 ∂(P.map fun ω => (expInt B 2 0 r.toNNReal ω, B r.toNNReal ω)) := by
              rw [← htr_law r.toNNReal]
          _ = ∫ ω, K₂ (expInt B 2 0 r.toNNReal ω) (B r.toNNReal ω) ∂P := hm1.symm
      have hK₂_rw : (fun ω => F₂_z (expInt B (-2) 0 r.toNNReal ω) (B r.toNNReal ω) *
            Real.exp (-2 * B r.toNNReal ω) +
            (1 / 2 : ℝ) * F₂_yy (expInt B (-2) 0 r.toNNReal ω) (B r.toNNReal ω)) =
          fun ω => K₂ (Real.exp (2 * B r.toNNReal ω) * expInt B (-2) 0 r.toNNReal ω) (B r.toNNReal ω) :=
        funext fun ω => hK₂_eq _ _
      rw [hK₂_rw, hK₂_law]
      have hK₂_bd : ∀ x y : ℝ, |K₂ x y| ≤ 8 * Cψ + 2 * Cψ + (Ccut + 2) * Cψ + (1 / 2) * Ccut * Cψ + 1 := by
        intro x y
        have ha1 : |2 * x ^ 2 * expInvCut₂ u x * ψ y| ≤ 8 * Cψ := by
          rw [show 2 * x ^ 2 * expInvCut₂ u x * ψ y = 2 * (x ^ 2 * expInvCut₂ u x) * ψ y by ring,
            abs_mul, abs_mul, abs_of_pos two_pos]
          calc 2 * |x ^ 2 * expInvCut₂ u x| * |ψ y| ≤ 2 * 4 * Cψ := by gcongr; exact hm2 x; exact hψ0 y
            _ = 8 * Cψ := by ring
        have ha2 : |2 * x * expInvCut₁ u x * deriv ψ y| ≤ 2 * Cψ := by
          rw [show 2 * x * expInvCut₁ u x * deriv ψ y = 2 * (x * expInvCut₁ u x) * deriv ψ y by ring,
            abs_mul, abs_mul, abs_of_pos two_pos]
          calc 2 * |x * expInvCut₁ u x| * |deriv ψ y| ≤ 2 * 1 * Cψ := by gcongr; exact hm1 x; exact hψ1 y
            _ = 2 * Cψ := by ring
        have ha3 : |(1 + 2 * x) * expInvCut₁ u x * ψ y| ≤ Ccut * Cψ + 2 * Cψ := by
          rw [show (1 + 2 * x) * expInvCut₁ u x * ψ y = expInvCut₁ u x * ψ y + 2 * (x * expInvCut₁ u x) * ψ y by ring]
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [abs_mul]; exact mul_le_mul (hcut1 x) (hψ0 y) (abs_nonneg _) hCcut0
          · rw [abs_mul, abs_mul, abs_of_pos two_pos]
            calc 2 * |x * expInvCut₁ u x| * |ψ y| ≤ 2 * 1 * Cψ := by gcongr; exact hm1 x; exact hψ0 y
              _ = 2 * Cψ := by ring
        have ha4 : |(1 / 2 : ℝ) * expInvCut u x * deriv (deriv ψ) y| ≤ (1 / 2) * Ccut * Cψ := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hcut0 x) (by norm_num)) (hψ2 y) (abs_nonneg _)
            (by positivity)
        have htri1 : |K₂ x y| ≤ |2 * x ^ 2 * expInvCut₂ u x * ψ y| +
            |2 * x * expInvCut₁ u x * deriv ψ y| + |(1 + 2 * x) * expInvCut₁ u x * ψ y| +
            |(1 / 2 : ℝ) * expInvCut u x * deriv (deriv ψ) y| := by
          simp only [K₂]
          exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
            (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
        have h_eq : Ccut * Cψ + 2 * Cψ = (Ccut + 2) * Cψ := by ring
        linarith [htri1, ha1, ha2, ha3, ha4, h_eq]
      have hI₁ : Integrable (fun ω => K₂ (expInt B 2 0 r.toNNReal ω) (B r.toNNReal ω)) P :=
        Integrable.of_bound
          (hK₂_cont.measurable.comp ((measurable_expInt_bm hBmeas hBcont 2 r.toNNReal).prodMk (hBmeas _))).aestronglyMeasurable
          (8 * Cψ + 2 * Cψ + (Ccut + 2) * Cψ + (1 / 2) * Ccut * Cψ + 1)
          (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hK₂_bd _ _)
      have hI₂ : Integrable (fun ω =>
          F₁_x (expInt B 2 0 r.toNNReal ω) (B r.toNNReal ω) * Real.exp (2 * B r.toNNReal ω) +
            (1 / 2 : ℝ) * F₁_yy (expInt B 2 0 r.toNNReal ω) (B r.toNNReal ω)) P := by
        refine Integrable.of_bound ?_ (E4 * Ccut * Cψ + (1 / 2) * Ccut * Cψ + 1) ?_
        · have hmX := measurable_expInt_bm hBmeas hBcont 2 r.toNNReal
          exact (((hFx_cont.measurable.comp (hmX.prodMk (hBmeas _))).mul
            (Real.measurable_exp.comp ((hBmeas _).const_mul 2))).add
            (measurable_const.mul ((hc_cut0.measurable.comp hmX).mul
              (hcψ2.measurable.comp (hBmeas _))))).aestronglyMeasurable
        · filter_upwards with ω
          rw [Real.norm_eq_abs]
          have h20 : Real.exp (2 * B r.toNNReal ω) * |ψ (B r.toNNReal ω)| ≤ E4 * Cψ :=
            (hexp_ψ 2 _).1.trans (mul_le_mul_of_nonneg_right hE1 hCψ0)
          have h1 : |F₁_x (expInt B 2 0 r.toNNReal ω) (B r.toNNReal ω) * Real.exp (2 * B r.toNNReal ω)| ≤
              E4 * Ccut * Cψ := by
            simp only [F₁_x, abs_mul, abs_of_pos (Real.exp_pos _)]
            calc |expInvCut₁ u _| * |ψ _| * Real.exp (2 * B r.toNNReal ω)
                = |expInvCut₁ u _| * (Real.exp (2 * B r.toNNReal ω) * |ψ _|) := by ring
              _ ≤ Ccut * (E4 * Cψ) := mul_le_mul (hcut1 _) h20 (by positivity) hCcut0
              _ = E4 * Ccut * Cψ := by ring
          have h2 : |(1 / 2 : ℝ) * F₁_yy (expInt B 2 0 r.toNNReal ω) (B r.toNNReal ω)| ≤
              (1 / 2) * Ccut * Cψ := by
            simp only [F₁_yy, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
            calc 1 / 2 * (|expInvCut u _| * |deriv (deriv ψ) _|)
                ≤ 1 / 2 * (Ccut * Cψ) := by gcongr; exact hcut0 _; exact hψ2 _
              _ = (1 / 2) * Ccut * Cψ := by ring
          exact (abs_add_le _ _).trans (by linarith [h1, h2])
      rw [← integral_sub hI₁ hI₂]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [K₂, F₁_x, F₁_yy, G_FP]
      ring
    have hdiff : ∫ r in (0 : ℝ)..(s : ℝ),
          ∫ ω, (F₂_z (expInt B (-2) 0 r.toNNReal ω) (B r.toNNReal ω) * Real.exp (-2 * B r.toNNReal ω) +
            (1 / 2 : ℝ) * F₂_yy (expInt B (-2) 0 r.toNNReal ω) (B r.toNNReal ω)) ∂P =
        ∫ r in (0 : ℝ)..(s : ℝ),
          ∫ ω, (F₁_x (expInt B 2 0 r.toNNReal ω) (B r.toNNReal ω) * Real.exp (2 * B r.toNNReal ω) +
            (1 / 2 : ℝ) * F₁_yy (expInt B 2 0 r.toNNReal ω) (B r.toNNReal ω)) ∂P :=
      (hIto₂ s hs).symm.trans (hLHS_eq.symm.trans (hIto₁' s hs))
    have hcont_I₁ : Continuous (fun r : ℝ =>
        ∫ ω, (F₁_x (expInt B 2 0 r.toNNReal ω) (B r.toNNReal ω) * Real.exp (2 * B r.toNNReal ω) +
          (1 / 2 : ℝ) * F₁_yy (expInt B 2 0 r.toNNReal ω) (B r.toNNReal ω)) ∂P) := by
      let H₁ : ℝ → ℝ → ℝ := fun x y => F₁_x x y * Real.exp (2 * y) + (1 / 2 : ℝ) * F₁_yy x y
      have hH₁ : Continuous (Function.uncurry H₁) :=
        ((hFx_cont.mul (Real.continuous_exp.comp (continuous_const.mul continuous_snd))).add
          (continuous_const.mul ((hc_cut0.comp continuous_fst).mul (hcψ2.comp continuous_snd))))
      refine continuous_expectation_expInt_aux hBmeas hBcont 2 H₁ hH₁
        (M := E4 * Ccut * Cψ + (1 / 2) * Ccut * Cψ + 1) ?_
      intro r ω
      have h20 : Real.exp (2 * B r.toNNReal ω) * |ψ (B r.toNNReal ω)| ≤ E4 * Cψ :=
        (hexp_ψ 2 _).1.trans (mul_le_mul_of_nonneg_right hE1 hCψ0)
      have h1 : |H₁ (expInt B 2 0 r.toNNReal ω) (B r.toNNReal ω)| ≤
          |F₁_x (expInt B 2 0 r.toNNReal ω) (B r.toNNReal ω) * Real.exp (2 * B r.toNNReal ω)| +
            |(1 / 2 : ℝ) * F₁_yy (expInt B 2 0 r.toNNReal ω) (B r.toNNReal ω)| :=
        abs_add_le _ _
      have ha : |F₁_x (expInt B 2 0 r.toNNReal ω) (B r.toNNReal ω) *
          Real.exp (2 * B r.toNNReal ω)| ≤ E4 * Ccut * Cψ := by
        simp only [F₁_x, abs_mul, abs_of_pos (Real.exp_pos _)]
        calc |expInvCut₁ u (expInt B 2 0 r.toNNReal ω)| * |ψ (B r.toNNReal ω)| *
              Real.exp (2 * B r.toNNReal ω)
            = |expInvCut₁ u (expInt B 2 0 r.toNNReal ω)| *
                (Real.exp (2 * B r.toNNReal ω) * |ψ (B r.toNNReal ω)|) := by ring
          _ ≤ Ccut * (E4 * Cψ) := mul_le_mul (hcut1 _) h20 (by positivity) hCcut0
          _ = E4 * Ccut * Cψ := by ring
      have hb : |(1 / 2 : ℝ) * F₁_yy (expInt B 2 0 r.toNNReal ω) (B r.toNNReal ω)| ≤
          (1 / 2) * Ccut * Cψ := by
        simp only [F₁_yy, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        calc 1 / 2 * (|expInvCut u (expInt B 2 0 r.toNNReal ω)| * |deriv (deriv ψ) (B r.toNNReal ω)|)
            ≤ 1 / 2 * (Ccut * Cψ) := by gcongr; exact hcut0 _; exact hψ2 _
          _ = (1 / 2) * Ccut * Cψ := by ring
      exact h1.trans ((add_le_add ha hb).trans (le_add_of_nonneg_right zero_le_one))
    have hcont_I₂ : Continuous (fun r : ℝ =>
        ∫ ω, (F₂_z (expInt B (-2) 0 r.toNNReal ω) (B r.toNNReal ω) * Real.exp (-2 * B r.toNNReal ω) +
          (1 / 2 : ℝ) * F₂_yy (expInt B (-2) 0 r.toNNReal ω) (B r.toNNReal ω)) ∂P) := by
      let H₂ : ℝ → ℝ → ℝ := fun z y => F₂_z z y * Real.exp (-2 * y) + (1 / 2 : ℝ) * F₂_yy z y
      have harg : Continuous (fun p : ℝ × ℝ => Real.exp (2 * p.2) * p.1) := by fun_prop
      have hcFz : Continuous (Function.uncurry F₂_z) :=
        ((Real.continuous_exp.comp (continuous_const.mul continuous_snd)).mul
          (hc_cut1.comp harg)).mul (hcψ0.comp continuous_snd)
      have hH₂ : Continuous (Function.uncurry H₂) :=
        (hcFz.mul (Real.continuous_exp.comp (continuous_const.mul continuous_snd))).add
          (continuous_const.mul hF₂_yy_cont)
      refine continuous_expectation_expInt_aux hBmeas hBcont (-2) H₂ hH₂
        (M := M₂ * Real.exp (2 * R) + (1 / 2) * M₂ + 1) ?_
      intro r ω
      have hFz_e : |F₂_z (expInt B (-2) 0 r.toNNReal ω) (B r.toNNReal ω) *
          Real.exp (-2 * B r.toNNReal ω)| ≤ M₂ * Real.exp (2 * R) := by
        set z := expInt B (-2) 0 r.toNNReal ω
        set y := B r.toNNReal ω
        by_cases hy : R ≤ |y|
        · obtain ⟨h0, _, _, _⟩ := hsupp y hy
          simp [F₂_z, h0]; positivity
        · have hy' : -y ≤ R := (neg_le_abs y).trans (not_le.mp hy).le
          have hexp : Real.exp (-2 * y) ≤ Real.exp (2 * R) :=
            Real.exp_le_exp.mpr (by linarith)
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul (hbd₂.2.1 z y) hexp (Real.exp_pos _).le hM₂
      have hFyy_e : |(1 / 2 : ℝ) * F₂_yy (expInt B (-2) 0 r.toNNReal ω) (B r.toNNReal ω)| ≤
          (1 / 2) * M₂ := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        exact mul_le_mul_of_nonneg_left (hbd₂.2.2.2.2.2.1 _ _) (by norm_num)
      have htri : |H₂ (expInt B (-2) 0 r.toNNReal ω) (B r.toNNReal ω)| ≤
          |F₂_z (expInt B (-2) 0 r.toNNReal ω) (B r.toNNReal ω) * Real.exp (-2 * B r.toNNReal ω)| +
            |(1 / 2 : ℝ) * F₂_yy (expInt B (-2) 0 r.toNNReal ω) (B r.toNNReal ω)| :=
        abs_add_le _ _
      exact htri.trans ((add_le_add hFz_e hFyy_e).trans (le_add_of_nonneg_right zero_le_one))
    have hsub_int : ∫ r in (0 : ℝ)..(s : ℝ),
        (∫ ω, (F₂_z (expInt B (-2) 0 r.toNNReal ω) (B r.toNNReal ω) * Real.exp (-2 * B r.toNNReal ω) +
          (1 / 2 : ℝ) * F₂_yy (expInt B (-2) 0 r.toNNReal ω) (B r.toNNReal ω)) ∂P -
         ∫ ω, (F₁_x (expInt B 2 0 r.toNNReal ω) (B r.toNNReal ω) * Real.exp (2 * B r.toNNReal ω) +
          (1 / 2 : ℝ) * F₁_yy (expInt B 2 0 r.toNNReal ω) (B r.toNNReal ω)) ∂P) = 0 := by
      rw [intervalIntegral.integral_sub (hcont_I₂.intervalIntegrable _ _) (hcont_I₁.intervalIntegrable _ _),
        hdiff, sub_self]
    exact (intervalIntegral.integral_congr fun r hr => (hRHS_eq r hr).symm).trans hsub_int
  let g_FP : ℝ → ℝ := fun r => ∫ ω, G_FP (expInt B 2 0 r.toNNReal ω) (B r.toNNReal ω) ∂P
  obtain ⟨MG, _, hMG⟩ := hG_FP_bd
  have hg_cont : Continuous g_FP :=
    continuous_expectation_expInt_aux hBmeas hBcont 2 G_FP hG_FP_cont (fun _ _ => hMG _ _)
  have hderiv_t : HasDerivAt (fun s : ℝ => ∫ r in (0 : ℝ)..s, g_FP r) (g_FP (t : ℝ)) (t : ℝ) :=
    intervalIntegral.integral_hasDerivAt_right (hg_cont.intervalIntegrable _ _)
      (hg_cont.stronglyMeasurableAtFilter volume (nhds (t : ℝ))) hg_cont.continuousAt
  have hzero_nhds : (fun s : ℝ => ∫ r in (0 : ℝ)..s, g_FP r) =ᶠ[nhds (t : ℝ)] fun _ => 0 := by
    have hmem : Ioo (0 : ℝ) ((t + 1 : ℝ≥0) : ℝ) ∈ nhds (t : ℝ) :=
      isOpen_Ioo.mem_nhds ⟨NNReal.coe_pos.mpr ht, by push_cast; linarith⟩
    filter_upwards [hmem] with s hs
    have hs_nn : s.toNNReal ≤ t + 1 := Real.toNNReal_le_iff_le_coe.mpr hs.2.le
    have hs_eq : (s.toNNReal : ℝ) = s := Real.coe_toNNReal s hs.1.le
    calc ∫ r in (0 : ℝ)..s, g_FP r
        = ∫ r in (0 : ℝ)..(s.toNNReal : ℝ), g_FP r := by rw [hs_eq]
      _ = 0 := h_int_zero s.toNNReal hs_nn
  have hderiv_0 : HasDerivAt (fun s : ℝ => ∫ r in (0 : ℝ)..s, g_FP r) 0 (t : ℝ) :=
    (hasDerivAt_const (t : ℝ) (0 : ℝ)).congr_of_eventuallyEq hzero_nhds
  have hgt : g_FP (t : ℝ) = 0 := hderiv_t.unique hderiv_0
  have ht_eq : ((t : ℝ).toNNReal) = t := Real.toNNReal_coe
  simpa only [g_FP, G_FP, ht_eq] using hgt

end DistFokkerPlanck

end Lyasoff2016
