/-
Gaussian decay of g_{t,p} along horizontal lines u ↦ u − ia, and the resulting absolute
integrability of `cosh u · |g_{t,p}(u − ia)|` (the Fubini hypothesis of the π/2-formula).
-/
module

public import Lyasoff2016.ContourRec


@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real Interval

noncomputable section
namespace Lyasoff2016

/- Paper: p. 1085–1086 (vision OCR p. 25), justification of the exchange of the two integrations
   for the contour ζ_{π/2}.
   Plain recap: on a horizontal line the two `cerf` terms of each pair in (5.8) tend to `+1`
   and `−1` respectively, at Gaussian rate, so the constants cancel and
     |g_{t,3}(u − ia)| ≤ C e^{−u²/t},   |g_{t,4}(u − ia)| ≤ C cosh u · e^{−u²/t}.
   Together with |g_{t,2}(u − ia)| = e^{2a²/t} e^{−2u²/t}/(4π) this makes
   `cosh u · |g_{t,p}(u − ia)|` integrable, since ∫ e^{−c u²} cosh² u du < ∞.
   (The bounds `ContourRec.norm_gFun_three_line_le`, `…four_line_le` only give `C`, `C cosh u`,
   which is enough for the contour equation but not for Fubini at a = π/2.) -/
namespace GFunDecay

open ContourTwo ContourRec

/-! ### `cerf` tends to `±1` at Gaussian rate along horizontal lines -/

lemma cerf_zero : cerf 0 = 0 := by simp [cerf]

lemma norm_two_div_sqrt_pi : ‖(2 / Real.sqrt Real.pi : ℂ)‖ = 2 / √π := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  simp

lemma hasDerivAt_cerf_line (β x : ℝ) :
    HasDerivAt (fun x : ℝ => cerf (x + β * I))
      ((2 / Real.sqrt Real.pi : ℂ) * cexp (-((x : ℂ) + β * I) ^ 2)) x := by
  have h := (cerf.hasDerivAt ((x : ℂ) + β * I)).comp_add_const (x : ℂ) (β * I)
  exact h.comp_ofReal

lemma norm_cerf_line_deriv (β s : ℝ) :
    ‖(2 / Real.sqrt Real.pi : ℂ) * cexp (-((s : ℂ) + β * I) ^ 2)‖ =
      2 / √π * Real.exp (β ^ 2) * Real.exp (-1 * s ^ 2) := by
  have hre : (-((s : ℂ) + β * I) ^ 2).re = β ^ 2 + -1 * s ^ 2 := by
    simp [pow_two]
    ring
  rw [norm_mul, norm_two_div_sqrt_pi, Complex.norm_exp, hre, Real.exp_add, mul_assoc]

lemma integrable_cerf_line_deriv (β : ℝ) :
    Integrable fun s : ℝ => (2 / Real.sqrt Real.pi : ℂ) * cexp (-((s : ℂ) + β * I) ^ 2) := by
  have hG : Integrable fun s : ℝ => 2 / √π * Real.exp (β ^ 2) * Real.exp (-1 * s ^ 2) :=
    (integrable_exp_neg_mul_sq one_pos).const_mul _
  refine hG.mono' (Continuous.aestronglyMeasurable (by fun_prop))
    (Eventually.of_forall fun s => ?_)
  rw [norm_cerf_line_deriv]

/-- `erf x → 1` as `x → +∞` along the real axis. -/
lemma tendsto_cerf_real : Tendsto (fun x : ℝ => cerf (x : ℂ)) atTop (𝓝 1) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => cerf (x : ℂ))
      ((2 / Real.sqrt Real.pi : ℂ) * cexp (-(x : ℂ) ^ 2)) x := by
    intro x
    simpa using hasDerivAt_cerf_line 0 x
  have hint : Integrable fun s : ℝ => (2 / Real.sqrt Real.pi : ℂ) * cexp (-(s : ℂ) ^ 2) := by
    simpa using integrable_cerf_line_deriv 0
  have hF : ∀ x : ℝ, (∫ s in (0 : ℝ)..x, (2 / Real.sqrt Real.pi : ℂ) * cexp (-(s : ℂ) ^ 2)) =
      cerf (x : ℂ) := by
    intro x
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
      (hint.intervalIntegrable)]
    simp [cerf_zero]
  have hlim := intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hint.integrableOn tendsto_id
  have hval : ∫ s in Ioi (0 : ℝ), (2 / Real.sqrt Real.pi : ℂ) * cexp (-(s : ℂ) ^ 2) = 1 := by
    have hcast : ∀ s : ℝ, (2 / Real.sqrt Real.pi : ℂ) * cexp (-(s : ℂ) ^ 2) =
        ((2 / √π * Real.exp (-1 * s ^ 2) : ℝ) : ℂ) := by
      intro s
      push_cast
      ring_nf
    simp_rw [hcast]
    rw [integral_complex_ofReal, integral_const_mul, integral_gaussian_Ioi, div_one]
    have hπ : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
    norm_cast
    field_simp
  simp only [id, hF] at hlim
  rwa [hval] at hlim

/-- Moving from the real axis to the line `ℑ = β` costs at most a Gaussian in `x`. -/
lemma norm_cerf_line_sub_real_le (β x : ℝ) :
    ‖cerf (x + β * I) - cerf (x : ℂ)‖ ≤
      2 / √π * Real.exp (β ^ 2) * Real.exp (-x ^ 2) * |β| := by
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => cerf ((x : ℂ) + s * I))
      ((2 / Real.sqrt Real.pi : ℂ) * cexp (-((x : ℂ) + s * I) ^ 2) * I) s := by
    intro s
    have hc : HasDerivAt (fun w : ℂ => cerf ((x : ℂ) + w * I))
        ((2 / Real.sqrt Real.pi : ℂ) * cexp (-((x : ℂ) + (s : ℂ) * I) ^ 2) * I) (s : ℂ) := by
      have hin : HasDerivAt (fun w : ℂ => (x : ℂ) + w * I) I (s : ℂ) := by
        simpa using ((hasDerivAt_id' (s : ℂ)).mul_const I).const_add (x : ℂ)
      exact (cerf.hasDerivAt _).comp (s : ℂ) hin
    exact hc.comp_ofReal
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := β)
    (fun s _ => hd s) (Continuous.intervalIntegrable (by fun_prop) _ _)
  have h0 : cerf ((x : ℂ) + ((0 : ℝ) : ℂ) * I) = cerf (x : ℂ) := by simp
  rw [h0] at hFTC
  rw [← hFTC]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := β)
    (C := 2 / √π * Real.exp (β ^ 2) * Real.exp (-x ^ 2))
    (f := fun s : ℝ => (2 / Real.sqrt Real.pi : ℂ) * cexp (-((x : ℂ) + s * I) ^ 2) * I) ?_
  · simpa using hb
  intro s hs
  have hsβ : s ^ 2 ≤ β ^ 2 := by
    rcases Set.mem_uIoc.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> nlinarith
  have hre : (-((x : ℂ) + s * I) ^ 2).re = s ^ 2 + -x ^ 2 := by
    simp [pow_two]
    ring
  rw [norm_mul, norm_mul, norm_two_div_sqrt_pi, Complex.norm_exp, hre, Complex.norm_I, mul_one,
    mul_assoc, ← Real.exp_add]
  have hπ : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  gcongr

/-- `erf(x + iβ) → 1` as `x → +∞`. -/
lemma tendsto_cerf_line (β : ℝ) : Tendsto (fun x : ℝ => cerf (x + β * I)) atTop (𝓝 1) := by
  have h0 : Tendsto (fun x : ℝ => cerf (x + β * I) - cerf (x : ℂ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (norm_cerf_line_sub_real_le β) ?_
    have hexp : Tendsto (fun x : ℝ => Real.exp (-x ^ 2)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop two_ne_zero))
    simpa using (hexp.const_mul (2 / √π * Real.exp (β ^ 2))).mul_const |β|
  simpa using h0.add tendsto_cerf_real

/-- Gaussian tail of the complementary error function on the line `ℑ = β`, for `x ≥ 0`. -/
lemma norm_cerf_line_sub_one_le (β : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    ‖cerf (x + β * I) - 1‖ ≤ 2 * Real.exp (β ^ 2) * Real.exp (-x ^ 2) := by
  have hint := integrable_cerf_line_deriv β
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto' (a := x)
    (fun s _ => hasDerivAt_cerf_line β s) hint.integrableOn (tendsto_cerf_line β)
  rw [← norm_neg, neg_sub, ← hFTC]
  have hG : Integrable fun s : ℝ => Real.exp (-1 * (s - x) ^ 2) :=
    (integrable_exp_neg_mul_sq one_pos).comp_sub_right x
  have hπ : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  calc ‖∫ s in Ioi x, (2 / Real.sqrt Real.pi : ℂ) * cexp (-((s : ℂ) + β * I) ^ 2)‖
      ≤ ∫ s in Ioi x, ‖(2 / Real.sqrt Real.pi : ℂ) * cexp (-((s : ℂ) + β * I) ^ 2)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ s in Ioi x, 2 / √π * Real.exp (β ^ 2) * Real.exp (-x ^ 2) *
          Real.exp (-1 * (s - x) ^ 2) := by
        refine setIntegral_mono_on hint.norm.integrableOn (hG.const_mul _).integrableOn
          measurableSet_Ioi fun s hs => ?_
        rw [norm_cerf_line_deriv, mul_assoc (2 / √π * Real.exp (β ^ 2)), ← Real.exp_add]
        gcongr
        nlinarith [mul_nonneg hx (sub_nonneg.2 (mem_Ioi.1 hs).le)]
    _ ≤ ∫ s : ℝ, 2 / √π * Real.exp (β ^ 2) * Real.exp (-x ^ 2) *
          Real.exp (-1 * (s - x) ^ 2) :=
        setIntegral_le_integral (hG.const_mul _) (Eventually.of_forall fun s => by positivity)
    _ = 2 * Real.exp (β ^ 2) * Real.exp (-x ^ 2) := by
        rw [integral_const_mul,
          integral_sub_right_eq_self (fun s : ℝ => Real.exp (-1 * s ^ 2)) x, integral_gaussian,
          div_one]
        field_simp

/-- `|erf(x + iβ) − 1| ≤ C e^{−x²}` on every half-line `x ≥ −K`. -/
lemma cerf_line_sub_one_gaussian (β K : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, -K ≤ x →
      ‖cerf (x + β * I) - 1‖ ≤ C * Real.exp (-x ^ 2) := by
  obtain ⟨M, hM⟩ := cerf_bdd_line β
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine ⟨2 * Real.exp (β ^ 2) + (M + 1) * Real.exp (K ^ 2), by positivity, fun x hx => ?_⟩
  rw [add_mul]
  rcases le_total 0 x with h | h
  · have h1 := norm_cerf_line_sub_one_le β h
    have h2 : 0 ≤ (M + 1) * Real.exp (K ^ 2) * Real.exp (-x ^ 2) := by positivity
    linarith
  · have hx2 : x ^ 2 ≤ K ^ 2 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ K + x) (by linarith : 0 ≤ K - x)]
    have h1 : ‖cerf (x + β * I) - 1‖ ≤ M + 1 := by
      calc _ ≤ ‖cerf (x + β * I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ M + 1 := by
          rw [norm_one]
          exact add_le_add (hM x) le_rfl
    have h2 : 1 ≤ Real.exp (K ^ 2) * Real.exp (-x ^ 2) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    have h3 : (M + 1) * 1 ≤ (M + 1) * (Real.exp (K ^ 2) * Real.exp (-x ^ 2)) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have h4 : 0 ≤ 2 * Real.exp (β ^ 2) * Real.exp (-x ^ 2) := by positivity
    linarith

/-- `|erf(x + iβ) + 1| ≤ C e^{−x²}` on every half-line `x ≤ K`. -/
lemma cerf_line_add_one_gaussian (β K : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, x ≤ K →
      ‖cerf (x + β * I) + 1‖ ≤ C * Real.exp (-x ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := cerf_line_sub_one_gaussian (-β) K
  refine ⟨C, hC0, fun x hx => ?_⟩
  have h := hC (-x) (by linarith)
  have e : cerf (x + β * I) + 1 = -(cerf (((-x : ℝ) : ℂ) + ((-β : ℝ) : ℂ) * I) - 1) := by
    rw [show (((-x : ℝ) : ℂ) + ((-β : ℝ) : ℂ) * I) = -((x : ℂ) + β * I) by push_cast; ring,
      cerf.neg]
    ring
  rw [e, norm_neg]
  simpa using h

/-! ### The sum of the two `cerf` terms of a pair decays like a Gaussian -/

private lemma cerf_pair_gaussian_nonneg {T m d : ℝ} (hT : 0 ≤ T) (hm : 0 < m) (hd : 0 < d)
    (a : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u →
      ‖cerf (((T : ℂ) + (m : ℂ) * (u - I * a)) / (d : ℂ)) +
        cerf (((T : ℂ) - (m : ℂ) * (u - I * a)) / (d : ℂ))‖ ≤
        C * Real.exp (-(m ^ 2 / (2 * d ^ 2)) * u ^ 2) := by
  obtain ⟨C1, hC10, hC1⟩ := cerf_line_sub_one_gaussian (-(m * a) / d) 0
  obtain ⟨C2, hC20, hC2⟩ := cerf_line_add_one_gaussian (m * a / d) (T / d)
  refine ⟨C1 + C2 * Real.exp (T ^ 2 / d ^ 2), by positivity, fun u hu => ?_⟩
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have e1 : ((T : ℂ) + (m : ℂ) * (u - I * a)) / (d : ℂ) =
      (((T + m * u) / d : ℝ) : ℂ) + ((-(m * a) / d : ℝ) : ℂ) * I := by
    push_cast; ring
  have e2 : ((T : ℂ) - (m : ℂ) * (u - I * a)) / (d : ℂ) =
      (((T - m * u) / d : ℝ) : ℂ) + ((m * a / d : ℝ) : ℂ) * I := by
    push_cast; ring
  have hmu : 0 ≤ m * u := mul_nonneg hm.le hu
  have hp : -(0 : ℝ) ≤ (T + m * u) / d := by
    rw [neg_zero]; positivity
  have hq : (T - m * u) / d ≤ T / d :=
    div_le_div_of_nonneg_right (by linarith) hd.le
  have h1 := hC1 _ hp
  have h2 := hC2 _ hq
  set D : ℝ := (d ^ 2)⁻¹ with hD
  have hD0 : 0 ≤ D := by positivity
  have hsq : ∀ r : ℝ, (r / d) ^ 2 = r ^ 2 * D := fun r => by
    rw [div_pow, div_eq_mul_inv]
  have hrate : m ^ 2 / (2 * d ^ 2) * u ^ 2 = (m * u) ^ 2 / 2 * D := by
    rw [hD]; field_simp
  have hT2 : T ^ 2 / d ^ 2 = T ^ 2 * D := div_eq_mul_inv _ _
  have hE1 : Real.exp (-((T + m * u) / d) ^ 2) ≤
      Real.exp (-(m ^ 2 / (2 * d ^ 2)) * u ^ 2) := by
    apply Real.exp_le_exp.2
    rw [neg_mul, hrate, hsq]
    have : 0 ≤ D * ((T + m * u) ^ 2 - (m * u) ^ 2 / 2) :=
      mul_nonneg hD0 (by nlinarith [mul_nonneg hT hmu, sq_nonneg T, sq_nonneg (m * u)])
    linarith
  have hE2 : Real.exp (-((T - m * u) / d) ^ 2) ≤
      Real.exp (T ^ 2 / d ^ 2) * Real.exp (-(m ^ 2 / (2 * d ^ 2)) * u ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    rw [neg_mul, hrate, hsq, hT2]
    have : 0 ≤ D * ((T - m * u) ^ 2 + T ^ 2 - (m * u) ^ 2 / 2) :=
      mul_nonneg hD0 (by nlinarith [sq_nonneg (T - m * u / 2)])
    linarith
  rw [e1, e2]
  have hsum : cerf ((((T + m * u) / d : ℝ) : ℂ) + ((-(m * a) / d : ℝ) : ℂ) * I) +
      cerf ((((T - m * u) / d : ℝ) : ℂ) + ((m * a / d : ℝ) : ℂ) * I) =
      (cerf ((((T + m * u) / d : ℝ) : ℂ) + ((-(m * a) / d : ℝ) : ℂ) * I) - 1) +
        (cerf ((((T - m * u) / d : ℝ) : ℂ) + ((m * a / d : ℝ) : ℂ) * I) + 1) := by ring
  rw [hsum]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ C1 * Real.exp (-((T + m * u) / d) ^ 2) + C2 * Real.exp (-((T - m * u) / d) ^ 2) :=
        add_le_add h1 h2
    _ ≤ C1 * Real.exp (-(m ^ 2 / (2 * d ^ 2)) * u ^ 2) +
          C2 * (Real.exp (T ^ 2 / d ^ 2) * Real.exp (-(m ^ 2 / (2 * d ^ 2)) * u ^ 2)) :=
        add_le_add (mul_le_mul_of_nonneg_left hE1 hC10) (mul_le_mul_of_nonneg_left hE2 hC20)
    _ = _ := by ring

/-- For `m, d > 0` the pair `erf((T + m z)/d) + erf((T − m z)/d)` is `O(e^{−m²u²/(2d²)})`
along `z = u − ia`. -/
lemma cerf_pair_gaussian {T m d : ℝ} (hT : 0 ≤ T) (hm : 0 < m) (hd : 0 < d) (a : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ,
      ‖cerf (((T : ℂ) + (m : ℂ) * (u - I * a)) / (d : ℂ)) +
        cerf (((T : ℂ) - (m : ℂ) * (u - I * a)) / (d : ℂ))‖ ≤
        C * Real.exp (-(m ^ 2 / (2 * d ^ 2)) * u ^ 2) := by
  obtain ⟨C1, hC10, hC1⟩ := cerf_pair_gaussian_nonneg hT hm hd a
  obtain ⟨C2, hC20, hC2⟩ := cerf_pair_gaussian_nonneg hT hm hd (-a)
  refine ⟨C1 + C2, by positivity, fun u => ?_⟩
  rw [add_mul]
  rcases le_total 0 u with hu | hu
  · have h := hC1 u hu
    have h2 : 0 ≤ C2 * Real.exp (-(m ^ 2 / (2 * d ^ 2)) * u ^ 2) := by positivity
    linarith
  · have h := hC2 (-u) (by linarith)
    have e : cerf (((T : ℂ) + (m : ℂ) * (u - I * a)) / (d : ℂ)) +
        cerf (((T : ℂ) - (m : ℂ) * (u - I * a)) / (d : ℂ)) =
        cerf (((T : ℂ) + (m : ℂ) * (((-u : ℝ) : ℂ) - I * ((-a : ℝ) : ℂ))) / (d : ℂ)) +
          cerf (((T : ℂ) - (m : ℂ) * (((-u : ℝ) : ℂ) - I * ((-a : ℝ) : ℂ))) / (d : ℂ)) := by
      rw [add_comm]
      congr 2 <;> push_cast <;> ring
    rw [e]
    rw [neg_sq] at h
    have h2 : 0 ≤ C1 * Real.exp (-(m ^ 2 / (2 * d ^ 2)) * u ^ 2) := by positivity
    linarith

/-! ### Gaussian bounds for `g_{t,p}` along the lower edge `u ↦ u − ia` -/

/-- `|g_{T,2}(u − ia)| ≤ C e^{−u²/T}` (in fact with rate `2/T`). -/
theorem norm_gFun_two_line_gaussian {T : ℝ} (hT : 0 < T) (a : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, ‖gFun 2 T (u - I * a)‖ ≤ C * Real.exp (-u ^ 2 / T) := by
  refine ⟨Real.exp (2 * a ^ 2 / T) / (4 * π), by positivity, fun u => ?_⟩
  rw [norm_gFun_two, line_re, line_im, div_mul_eq_mul_div, ← Real.exp_add]
  have h0 : 0 ≤ u ^ 2 / T := by positivity
  have he : -2 * (u ^ 2 - (-a) ^ 2) / T = 2 * a ^ 2 / T + -u ^ 2 / T - u ^ 2 / T := by
    field_simp
    ring
  gcongr
  linarith

/-- `|g_{T,3}(u − ia)| ≤ C e^{−u²/T}`: the constants `±1` of the two `cerf` terms cancel. -/
theorem norm_gFun_three_line_gaussian {T : ℝ} (hT : 0 < T) (a : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, ‖gFun 3 T (u - I * a)‖ ≤ C * Real.exp (-u ^ 2 / T) := by
  obtain ⟨C, hC0, hC⟩ := cerf_pair_gaussian hT.le (m := 4) (by norm_num)
    (d := 2 * √(2 * T)) (by positivity) a
  refine ⟨‖(Real.exp (T / 8) : ℂ) * (√T / (4 * I * √(2 * π)))‖ * C, by positivity, fun u => ?_⟩
  have hrate : -((4 : ℝ) ^ 2 / (2 * (2 * √(2 * T)) ^ 2)) * u ^ 2 = -u ^ 2 / T := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  have h := hC u
  rw [hrate] at h
  have e : cerf (((T : ℂ) + 4 * (u - I * a)) / (2 * √(2 * T))) +
      cerf (((T : ℂ) - 4 * (u - I * a)) / (2 * √(2 * T))) =
      cerf (((T : ℂ) + ((4 : ℝ) : ℂ) * (u - I * a)) / ((2 * √(2 * T) : ℝ) : ℂ)) +
        cerf (((T : ℂ) - ((4 : ℝ) : ℂ) * (u - I * a)) / ((2 * √(2 * T) : ℝ) : ℂ)) := by
    push_cast
    rfl
  rw [gFun.three_apply, norm_mul, e]
  calc _ ≤ ‖(Real.exp (T / 8) : ℂ) * (√T / (4 * I * √(2 * π)))‖ *
        (C * Real.exp (-u ^ 2 / T)) := mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = _ := by ring

/-- `|g_{T,4}(u − ia)| ≤ C cosh u · e^{−u²/T}`. -/
theorem norm_gFun_four_line_gaussian {T : ℝ} (hT : 0 < T) (a : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ,
      ‖gFun 4 T (u - I * a)‖ ≤ C * Real.cosh u * Real.exp (-u ^ 2 / T) := by
  obtain ⟨C3, hC30, hC3⟩ := norm_gFun_three_line_gaussian hT a
  obtain ⟨C, hC0, hC⟩ := cerf_pair_gaussian hT.le (m := 2) (by norm_num)
    (d := √(2 * T)) (by positivity) a
  refine ⟨‖(Real.exp (T / 2) : ℂ) * (√T / (2 * I * √(2 * π)))‖ * C + 4 * C3, by positivity,
    fun u => ?_⟩
  have hrate : -((2 : ℝ) ^ 2 / (2 * √(2 * T) ^ 2)) * u ^ 2 = -u ^ 2 / T := by
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have h := hC u
  rw [hrate] at h
  have e : cerf (((T : ℂ) + 2 * (u - I * a)) / √(2 * T)) +
      cerf (((T : ℂ) - 2 * (u - I * a)) / √(2 * T)) =
      cerf (((T : ℂ) + ((2 : ℝ) : ℂ) * (u - I * a)) / ((√(2 * T) : ℝ) : ℂ)) +
        cerf (((T : ℂ) - ((2 : ℝ) : ℂ) * (u - I * a)) / ((√(2 * T) : ℝ) : ℂ)) := by
    push_cast
    rfl
  have hone : 1 ≤ Real.cosh u := Real.one_le_cosh u
  have hE : 0 ≤ Real.exp (-u ^ 2 / T) := (Real.exp_pos _).le
  have hA : ‖(Real.exp (T / 2) : ℂ) * (√T / (2 * I * √(2 * π))) *
      (cerf (((T : ℂ) + 2 * (u - I * a)) / √(2 * T)) +
        cerf (((T : ℂ) - 2 * (u - I * a)) / √(2 * T)))‖ ≤
      ‖(Real.exp (T / 2) : ℂ) * (√T / (2 * I * √(2 * π)))‖ * (C * Real.exp (-u ^ 2 / T)) := by
    rw [norm_mul, e]
    exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
  have hB : ‖4 * Complex.cosh ((u : ℂ) - I * a) * gFun 3 T (u - I * a)‖ ≤
      4 * Real.cosh u * (C3 * Real.exp (-u ^ 2 / T)) := by
    rw [norm_mul, norm_mul]
    have h4 : ‖(4 : ℂ)‖ = 4 := by simp
    rw [h4]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (norm_cosh_line_le' u a) (by norm_num))
      (hC3 u) (norm_nonneg _) (by positivity)
  rw [gFun.four_eq]
  set K : ℝ := ‖(Real.exp (T / 2) : ℂ) * (√T / (2 * I * √(2 * π)))‖ with hK
  have hK0 : 0 ≤ K := norm_nonneg _
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ K * (C * Real.exp (-u ^ 2 / T)) + 4 * Real.cosh u * (C3 * Real.exp (-u ^ 2 / T)) :=
        add_le_add hA hB
    _ ≤ K * C * Real.cosh u * Real.exp (-u ^ 2 / T) +
          4 * Real.cosh u * (C3 * Real.exp (-u ^ 2 / T)) := by
        have h1 : K * C * Real.exp (-u ^ 2 / T) * 1 ≤
            K * C * Real.exp (-u ^ 2 / T) * Real.cosh u :=
          mul_le_mul_of_nonneg_left hone (by positivity)
        linarith
    _ = _ := by ring

/-- Uniform statement for the three paper orders:
`|g_{T,p}(u − ia)| ≤ C cosh u · e^{−u²/T}` (without the `cosh u` for `p = 2, 3`). -/
theorem norm_gFun_line_gaussian {p : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 4) {T : ℝ} (hT : 0 < T)
    (a : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ,
      ‖gFun p T (u - I * a)‖ ≤ C * Real.cosh u * Real.exp (-u ^ 2 / T) := by
  have hweak : ∀ {q : ℕ}, (∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ,
      ‖gFun q T (u - I * a)‖ ≤ C * Real.exp (-u ^ 2 / T)) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ,
        ‖gFun q T (u - I * a)‖ ≤ C * Real.cosh u * Real.exp (-u ^ 2 / T) := by
    rintro q ⟨C, hC0, hC⟩
    refine ⟨C, hC0, fun u => (hC u).trans ?_⟩
    have h1 : C * Real.exp (-u ^ 2 / T) * 1 ≤ C * Real.exp (-u ^ 2 / T) * Real.cosh u :=
      mul_le_mul_of_nonneg_left (Real.one_le_cosh u) (by positivity)
    linarith
  rcases hp with rfl | rfl | rfl
  · exact hweak (norm_gFun_two_line_gaussian hT a)
  · exact hweak (norm_gFun_three_line_gaussian hT a)
  · exact norm_gFun_four_line_gaussian hT a

/-! ### Absolute integrability of `cosh u · |g_{t,p}(u − ia)|` -/

/-- `∫ cosh² u · e^{−u²/T} du < ∞`. -/
lemma integrable_cosh_sq_mul_gaussian {T : ℝ} (hT : 0 < T) :
    Integrable fun u : ℝ => Real.cosh u ^ 2 * Real.exp (-u ^ 2 / T) := by
  have hb : 0 < 1 / T := by positivity
  have h0 := integrable_exp_neg_mul_sq hb
  have h1 := (h0.comp_sub_right T).const_mul (Real.exp T)
  have h2 := (h0.comp_sub_right (-T)).const_mul (Real.exp T)
  refine (h1.add h2).mono' (Continuous.aestronglyMeasurable (by fun_prop))
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hp : Real.exp T * Real.exp (-(1 / T) * (u - T) ^ 2) =
      Real.exp u ^ 2 * Real.exp (-u ^ 2 / T) := by
    rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  have hm : Real.exp T * Real.exp (-(1 / T) * (u - -T) ^ 2) =
      Real.exp (-u) ^ 2 * Real.exp (-u ^ 2 / T) := by
    rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  simp only [Pi.add_apply]
  rw [hp, hm, ← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  have he : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add]; simp
  rw [Real.cosh_eq]
  nlinarith [sq_nonneg (Real.exp u - Real.exp (-u)), sq_nonneg (Real.exp u),
    sq_nonneg (Real.exp (-u))]

/-- The Fubini hypothesis of the π/2-formula: `cosh u · |g_{T,p}(u − ia)|` is integrable
over `ℝ` for `p = 2, 3, 4` and every horizontal line. -/
theorem integrable_cosh_mul_norm_gFun_line {p : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 4) {T : ℝ}
    (hT : 0 < T) (a : ℝ) :
    Integrable fun u : ℝ => Real.cosh u * ‖gFun p T (u - I * a)‖ := by
  obtain ⟨C, hC0, hC⟩ := norm_gFun_line_gaussian hp hT a
  have hg : Continuous (gFun p T) := (gFun.contDiff p T).continuous
  have hcont : Continuous fun u : ℝ => Real.cosh u * ‖gFun p T (u - I * a)‖ :=
    Real.continuous_cosh.mul (hg.comp (by fun_prop)).norm
  refine ((integrable_cosh_sq_mul_gaussian hT).const_mul C).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc Real.cosh u * ‖gFun p T (u - I * a)‖
      ≤ Real.cosh u * (C * Real.cosh u * Real.exp (-u ^ 2 / T)) :=
        mul_le_mul_of_nonneg_left (hC u) (Real.cosh_pos u).le
    _ = C * (Real.cosh u ^ 2 * Real.exp (-u ^ 2 / T)) := by ring

/-- The same at the aperture `a = π/2` used by the π/2-formula. -/
theorem integrable_cosh_mul_norm_gFun_piHalf {p : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 4) {T : ℝ}
    (hT : 0 < T) :
    Integrable fun u : ℝ => Real.cosh u * ‖gFun p T (u - I * (π / 2))‖ := by
  have h := integrable_cosh_mul_norm_gFun_line hp hT (π / 2)
  refine h.congr (Eventually.of_forall fun u => ?_)
  simp only
  push_cast
  rfl

end GFunDecay

end Lyasoff2016
