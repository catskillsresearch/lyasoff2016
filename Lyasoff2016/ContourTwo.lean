/-
The contour equation (5.3) for p = 2: the residue computation on the strip {|ℑ z| ≤ a}.
-/
module

public import Lyasoff2016.GFun


@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real Interval ComplexConjugate

noncomputable section
namespace Lyasoff2016

/- Paper: p. 1082–1083, the residue computation behind (5.3)/(5.5) for p = 2.
   Plain recap: with A = (z − y)/2 and B = (z + y)/2,
     sinh z / (cosh z − cosh y) = (coth A + coth B)/2,
   so the integrand of (5.3) is (Φ_y + Φ_{−y})/2 with Φ_y(z) = g_{t,2}(z) coth((z − y)/2).
   Φ_y has a single simple pole in the strip {|ℑ z| ≤ a} (a < 2π), at z = y, with residue
   2 g_{t,2}(y).  Subtracting g_{t,2}(y)/sinh((z − y)/2) removes the pole; Cauchy's theorem on
   rectangles (vertical sides vanish by the Gaussian decay of g_{t,2}) shows that the two edges
   of the strip carry the same integral of the difference, and the edge integrals of
   1/sinh((z − y)/2) are computed in closed form (an arctangent).  The upper edge is minus the
   conjugate of the lower one, which leaves twice the real part. -/
namespace ContourTwo

/-! ### Real hyperbolic bounds -/

lemma one_add_sq_le_four_cosh (x : ℝ) : 1 + x ^ 2 ≤ 4 * Real.cosh x := by
  have h1 := Real.quadratic_le_exp_of_nonneg (abs_nonneg x)
  have h2 := Real.add_one_le_exp (-|x|)
  have h3 : Real.cosh x = (Real.exp |x| + Real.exp (-|x|)) / 2 := by
    rw [← Real.cosh_abs, Real.cosh_eq]
  rw [sq_abs] at h1
  linarith

lemma self_le_cosh (x : ℝ) : x ≤ Real.cosh x := by
  rcases le_or_gt 0 x with h | h
  · exact (Real.self_le_sinh_iff.2 h).trans (Real.sinh_lt_cosh x).le
  · exact h.le.trans (Real.cosh_pos x).le

lemma tendsto_cosh_atTop : Tendsto Real.cosh atTop atTop :=
  tendsto_atTop_mono self_le_cosh tendsto_id

lemma tendsto_cosh_atBot : Tendsto Real.cosh atBot atTop :=
  tendsto_atTop_mono (fun x => by simpa using self_le_cosh (-x)) tendsto_neg_atBot_atTop

lemma tendsto_inv_cosh_atTop : Tendsto (fun x : ℝ => (Real.cosh x)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_cosh_atTop

lemma tendsto_inv_cosh_atBot : Tendsto (fun x : ℝ => (Real.cosh x)⁻¹) atBot (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_cosh_atBot

lemma integrable_inv_cosh : Integrable fun x : ℝ => (Real.cosh x)⁻¹ := by
  refine (integrable_inv_one_add_sq.const_mul 4).mono'
    (Real.continuous_cosh.inv₀ fun x => (Real.cosh_pos x).ne').aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (Real.cosh_pos x)), ← div_eq_mul_inv,
    inv_eq_one_div, div_le_div_iff₀ (Real.cosh_pos x) (by positivity)]
  linarith [one_add_sq_le_four_cosh x]

lemma tendsto_sinh_atTop : Tendsto Real.sinh atTop atTop :=
  tendsto_atTop_mono' atTop
    ((eventually_ge_atTop (0 : ℝ)).mono fun _ hx => Real.self_le_sinh_iff.2 hx) tendsto_id

lemma tendsto_sinh_atBot : Tendsto Real.sinh atBot atBot :=
  tendsto_atBot_mono' atBot
    ((eventually_le_atBot (0 : ℝ)).mono fun _ hx => Real.sinh_le_self_iff.2 hx) tendsto_id

/-! ### Complex hyperbolic functions in terms of real and imaginary parts -/

lemma sinh_re_im (z : ℂ) :
    (Complex.sinh z).re = Real.sinh z.re * Real.cos z.im ∧
    (Complex.sinh z).im = Real.cosh z.re * Real.sin z.im := by
  have h : Complex.sinh z = Complex.sinh (z.re + z.im * I) := by rw [Complex.re_add_im]
  rw [h, Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  simp [← Complex.ofReal_cosh, ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma cosh_re_im (z : ℂ) :
    (Complex.cosh z).re = Real.cosh z.re * Real.cos z.im ∧
    (Complex.cosh z).im = Real.sinh z.re * Real.sin z.im := by
  have h : Complex.cosh z = Complex.cosh (z.re + z.im * I) := by rw [Complex.re_add_im]
  rw [h, Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  simp [← Complex.ofReal_cosh, ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma norm_sinh_sq (z : ℂ) :
    ‖Complex.sinh z‖ ^ 2 = Real.sinh z.re ^ 2 + Real.sin z.im ^ 2 := by
  obtain ⟨hre, him⟩ := sinh_re_im z
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
  have hsc : Real.cosh z.re ^ 2 - Real.sinh z.re ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq z.re
  have hcs : Real.sin z.im ^ 2 + Real.cos z.im ^ 2 = 1 := Real.sin_sq_add_cos_sq z.im
  linear_combination Real.sinh z.re ^ 2 * hcs + Real.sin z.im ^ 2 * hsc

lemma norm_cosh_sq (z : ℂ) :
    ‖Complex.cosh z‖ ^ 2 = Real.sinh z.re ^ 2 + Real.cos z.im ^ 2 := by
  obtain ⟨hre, him⟩ := cosh_re_im z
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
  have hsc : Real.cosh z.re ^ 2 - Real.sinh z.re ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq z.re
  have hcs : Real.sin z.im ^ 2 + Real.cos z.im ^ 2 = 1 := Real.sin_sq_add_cos_sq z.im
  linear_combination Real.sinh z.re ^ 2 * hcs + Real.cos z.im ^ 2 * hsc

lemma abs_sinh_le_norm_sinh (z : ℂ) : |Real.sinh z.re| ≤ ‖Complex.sinh z‖ :=
  abs_le_of_sq_le_sq (by rw [norm_sinh_sq]; nlinarith [sq_nonneg (Real.sin z.im)])
    (norm_nonneg _)

lemma sin_mul_cosh_le_norm_sinh (z : ℂ) :
    |Real.sin z.im| * Real.cosh z.re ≤ ‖Complex.sinh z‖ := by
  have h : |Real.sin z.im * Real.cosh z.re| ≤ ‖Complex.sinh z‖ := by
    refine abs_le_of_sq_le_sq ?_ (norm_nonneg _)
    rw [norm_sinh_sq]
    have hsc : Real.cosh z.re ^ 2 - Real.sinh z.re ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq z.re
    have hs1 : Real.sin z.im ^ 2 ≤ 1 := Real.sin_sq_le_one z.im
    nlinarith [sq_nonneg (Real.sinh z.re),
      mul_nonneg (sq_nonneg (Real.sinh z.re)) (sub_nonneg.2 hs1)]
  rwa [abs_mul, abs_of_pos (Real.cosh_pos _)] at h

lemma norm_cosh_le_cosh (z : ℂ) : ‖Complex.cosh z‖ ≤ Real.cosh z.re := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.cosh_pos _).le two_ne_zero).1 ?_
  rw [norm_cosh_sq]
  have hsc : Real.cosh z.re ^ 2 - Real.sinh z.re ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq z.re
  have hc1 : Real.cos z.im ^ 2 ≤ 1 := Real.cos_sq_le_one z.im
  linarith

lemma norm_sinh_le_cosh (z : ℂ) : ‖Complex.sinh z‖ ≤ Real.cosh z.re := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.cosh_pos _).le two_ne_zero).1 ?_
  rw [norm_sinh_sq]
  have hsc : Real.cosh z.re ^ 2 - Real.sinh z.re ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq z.re
  have hs1 : Real.sin z.im ^ 2 ≤ 1 := Real.sin_sq_le_one z.im
  linarith

lemma sinh_ne_zero_of_abs_im_lt {w : ℂ} (hw : w ≠ 0) (him : |w.im| < π) :
    Complex.sinh w ≠ 0 := by
  intro h
  have hsq : Real.sinh w.re ^ 2 + Real.sin w.im ^ 2 = 0 := by
    rw [← norm_sinh_sq, h, norm_zero]; norm_num
  have h1 : Real.sinh w.re ^ 2 = 0 := by
    nlinarith [sq_nonneg (Real.sinh w.re), sq_nonneg (Real.sin w.im)]
  have h2 : Real.sin w.im ^ 2 = 0 := by
    nlinarith [sq_nonneg (Real.sinh w.re), sq_nonneg (Real.sin w.im)]
  have hre : w.re = 0 := Real.sinh_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h1)
  have him0 : w.im = 0 :=
    (Real.sin_eq_zero_iff_of_lt_of_lt (abs_lt.1 him).1 (abs_lt.1 him).2).1
      ((pow_eq_zero_iff two_ne_zero).1 h2)
  exact hw (Complex.ext hre him0)

/-! ### Cauchy's theorem on a strip -/

/-- If `F` is holomorphic on the closed strip `{|ℑ z| ≤ a}`, integrable on both edges and
uniformly small on the vertical segments `ℜ z = ±R` as `R → ∞`, then the integrals over the two
edges agree. -/
lemma integral_strip_eq {F : ℂ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hF : DifferentiableOn ℂ F {z | |z.im| ≤ a})
    (hlo : Integrable fun u : ℝ => F (u + ((-a : ℝ) : ℂ) * I))
    (hhi : Integrable fun u : ℝ => F (u + (a : ℂ) * I))
    {B : ℝ → ℝ} (hB : Tendsto B atTop (𝓝 0))
    (hvert : ∀ᶠ R : ℝ in atTop, ∀ s ∈ Icc (-a) a,
      ‖F ((R : ℂ) + s * I)‖ ≤ B R ∧ ‖F (((-R : ℝ) : ℂ) + s * I)‖ ≤ B R) :
    ∫ u : ℝ, F (u + ((-a : ℝ) : ℂ) * I) = ∫ u : ℝ, F (u + (a : ℂ) * I) := by
  have hrect : ∀ R : ℝ,
      (∫ x : ℝ in (-R)..R, F (x + ((-a : ℝ) : ℂ) * I)) -
          (∫ x : ℝ in (-R)..R, F (x + (a : ℂ) * I)) +
        I • (∫ s : ℝ in (-a)..a, F ((R : ℂ) + s * I)) -
        I • (∫ s : ℝ in (-a)..a, F (((-R : ℝ) : ℂ) + s * I)) = 0 := by
    intro R
    refine integral_boundary_rect_eq_zero_of_differentiableOn F ⟨-R, -a⟩ ⟨R, a⟩ (hF.mono ?_)
    intro z hz
    have him : z.im ∈ [[-a, a]] := hz.2
    rw [uIcc_of_le (by linarith)] at him
    exact abs_le.2 him
  have hL : Tendsto (fun R : ℝ => ∫ x : ℝ in (-R)..R, F (x + ((-a : ℝ) : ℂ) * I)) atTop
      (𝓝 (∫ u : ℝ, F (u + ((-a : ℝ) : ℂ) * I))) :=
    intervalIntegral_tendsto_integral hlo tendsto_neg_atTop_atBot tendsto_id
  have hU : Tendsto (fun R : ℝ => ∫ x : ℝ in (-R)..R, F (x + (a : ℂ) * I)) atTop
      (𝓝 (∫ u : ℝ, F (u + (a : ℂ) * I))) :=
    intervalIntegral_tendsto_integral hhi tendsto_neg_atTop_atBot tendsto_id
  have hV : Tendsto (fun R : ℝ => I * (∫ s : ℝ in (-a)..a, F ((R : ℂ) + s * I)) -
        I * (∫ s : ℝ in (-a)..a, F (((-R : ℝ) : ℂ) + s * I))) atTop (𝓝 0) := by
    have hB' : Tendsto (fun R => B R * |a - -a| + B R * |a - -a|) atTop (𝓝 0) := by
      simpa using (hB.mul_const |a - -a|).add (hB.mul_const |a - -a|)
    refine squeeze_zero_norm' ?_ hB'
    filter_upwards [hvert] with R hR
    have hsub : ∀ s ∈ Ι (-a) a, s ∈ Icc (-a) a := fun s hs => by
      rw [uIoc_of_le (by linarith)] at hs
      exact Ioc_subset_Icc_self hs
    have h1 : ‖∫ s : ℝ in (-a)..a, F ((R : ℂ) + s * I)‖ ≤ B R * |a - -a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => (hR s (hsub s hs)).1
    have h2 : ‖∫ s : ℝ in (-a)..a, F (((-R : ℝ) : ℂ) + s * I)‖ ≤ B R * |a - -a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => (hR s (hsub s hs)).2
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]
    exact add_le_add h1 h2
  have hsum := (hL.sub hU).add hV
  have hconst : (fun R : ℝ => (∫ x : ℝ in (-R)..R, F (x + ((-a : ℝ) : ℂ) * I)) -
        (∫ x : ℝ in (-R)..R, F (x + (a : ℂ) * I)) +
      (I * (∫ s : ℝ in (-a)..a, F ((R : ℂ) + s * I)) -
        I * (∫ s : ℝ in (-a)..a, F (((-R : ℝ) : ℂ) + s * I)))) = fun _ => 0 := by
    funext R
    have := hrect R
    simp only [smul_eq_mul] at this
    linear_combination this
  rw [hconst] at hsum
  have h0 := tendsto_nhds_unique hsum tendsto_const_nhds
  linear_combination h0

/-! ### `g_{t,2}` -/

lemma gFun_two_apply (t : ℝ) (z : ℂ) :
    gFun 2 t z = cexp (-2 * z ^ 2 / t) / (4 * π * I) := rfl

lemma differentiable_gFun_two (t : ℝ) : Differentiable ℂ (gFun 2 t) := by
  have h : gFun 2 t = fun z : ℂ => cexp (-2 * z ^ 2 / t) / (4 * π * I) := rfl
  rw [h]
  fun_prop

lemma norm_gFun_two (t : ℝ) (z : ℂ) :
    ‖gFun 2 t z‖ = Real.exp (-2 * (z.re ^ 2 - z.im ^ 2) / t) / (4 * π) := by
  have h4 : ‖(4 * π * I : ℂ)‖ = 4 * π := by
    simp [abs_of_pos Real.pi_pos]
  have hre : (-2 * z ^ 2 / (t : ℂ)).re = -2 * (z.re ^ 2 - z.im ^ 2) / t := by
    rw [Complex.div_ofReal_re]
    simp [pow_two]
  rw [gFun_two_apply, norm_div, Complex.norm_exp, h4, hre]

lemma gFun_two_conj (t : ℝ) (z : ℂ) : gFun 2 t (conj z) = -conj (gFun 2 t z) := by
  simp only [gFun_two_apply, map_div₀, ← Complex.exp_conj, map_mul, map_neg, map_pow,
    Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  field_simp

lemma gFun_two_mul (t : ℝ) (y : ℝ) :
    gFun 2 t y * (4 * π * I) = ((Real.exp (-2 * y ^ 2 / t) : ℝ) : ℂ) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [gFun_two_apply]
  push_cast
  field_simp

/-! ### Points on horizontal lines -/

lemma half_line (u ε y : ℝ) :
    ((u : ℂ) + (ε : ℂ) * I - y) / 2 = (((u - y) / 2 : ℝ) : ℂ) + ((ε / 2 : ℝ) : ℂ) * I := by
  push_cast; ring

lemma re_line (x β : ℝ) : ((x : ℂ) + (β : ℂ) * I).re = x := by simp

lemma im_line (x β : ℝ) : ((x : ℂ) + (β : ℂ) * I).im = β := by simp

lemma norm_sinh_line_ge (u ε y : ℝ) :
    |Real.sin (ε / 2)| * Real.cosh ((u - y) / 2) ≤
      ‖Complex.sinh (((u : ℂ) + (ε : ℂ) * I - y) / 2)‖ := by
  have h := sin_mul_cosh_le_norm_sinh ((((u - y) / 2 : ℝ) : ℂ) + ((ε / 2 : ℝ) : ℂ) * I)
  rw [re_line, im_line] at h
  rwa [half_line]

lemma norm_cosh_line_le (u ε y : ℝ) :
    ‖Complex.cosh (((u : ℂ) + (ε : ℂ) * I - y) / 2)‖ ≤ Real.cosh ((u - y) / 2) := by
  have h := norm_cosh_le_cosh ((((u - y) / 2 : ℝ) : ℂ) + ((ε / 2 : ℝ) : ℂ) * I)
  rw [re_line] at h
  rwa [half_line]

lemma sinh_line_ne_zero (u y : ℝ) {ε : ℝ} (hε : Real.sin (ε / 2) ≠ 0) :
    Complex.sinh (((u : ℂ) + (ε : ℂ) * I - y) / 2) ≠ 0 := by
  have h := norm_sinh_line_ge u ε y
  have hpos : 0 < |Real.sin (ε / 2)| * Real.cosh ((u - y) / 2) :=
    mul_pos (abs_pos.2 hε) (Real.cosh_pos _)
  exact norm_pos_iff.1 (hpos.trans_le h)

/-! ### The functions `Φ_y`, `χ_y` and the regularised difference `Ψ_y` -/

/-- `Φ_y(z) = g_{t,2}(z) coth((z − y)/2)`. -/
def Phi (t y : ℝ) (z : ℂ) : ℂ :=
  gFun 2 t z * Complex.cosh ((z - y) / 2) / Complex.sinh ((z - y) / 2)

/-- `χ_y(z) = 1 / sinh((z − y)/2)`. -/
def Chi (y : ℝ) (z : ℂ) : ℂ := (Complex.sinh ((z - y) / 2))⁻¹

/-- Numerator of `Ψ_y`: an entire function vanishing at `z = y`. -/
def Nfun (t y : ℝ) (z : ℂ) : ℂ :=
  gFun 2 t z * Complex.cosh ((z - y) / 2) - gFun 2 t y

/-- `Ψ_y = Φ_y − g_{t,2}(y) χ_y`, with the removable singularity at `z = y` removed. -/
def Psi (t y : ℝ) (z : ℂ) : ℂ :=
  2 * dslope (Nfun t y) y z / dslope Complex.sinh 0 ((z - y) / 2)

lemma Psi_eq (t y : ℝ) {z : ℂ} (hz : z ≠ y) (hs : Complex.sinh ((z - y) / 2) ≠ 0) :
    Psi t y z = Phi t y z - gFun 2 t y * Chi y z := by
  have hz' : z - y ≠ 0 := sub_ne_zero.2 hz
  have hw : (z - y) / 2 ≠ 0 := div_ne_zero hz' two_ne_zero
  have hN : Nfun t y y = 0 := by simp [Nfun]
  unfold Psi Phi Chi
  rw [dslope_of_ne _ hz, dslope_of_ne _ hw, slope_def_field, slope_def_field, hN,
    Complex.sinh_zero]
  simp only [Nfun, sub_zero]
  field_simp

lemma differentiableOn_Psi (t y : ℝ) {a : ℝ} (ha2 : a < 2 * π) :
    DifferentiableOn ℂ (Psi t y) {z | |z.im| ≤ a} := by
  intro z hz
  have hNd : Differentiable ℂ (Nfun t y) := by
    unfold Nfun
    exact ((differentiable_gFun_two t).mul (by fun_prop)).sub_const _
  have h1 : AnalyticAt ℂ (dslope (Nfun t y) y) z := (hNd.analyticAt z).dslope _
  have h2 : AnalyticAt ℂ (fun z : ℂ => dslope Complex.sinh 0 ((z - y) / 2)) z := by
    have h : AnalyticAt ℂ (dslope Complex.sinh 0) ((z - y) / 2) :=
      (Complex.differentiable_sinh.analyticAt _).dslope _
    exact h.comp (f := fun z : ℂ => (z - y) / 2) (by fun_prop)
  have hne : dslope Complex.sinh 0 ((z - y) / 2) ≠ 0 := by
    by_cases hw : (z - y) / 2 = 0
    · rw [hw, dslope_same, Complex.deriv_sinh, Complex.cosh_zero]
      exact one_ne_zero
    · rw [dslope_of_ne _ hw, slope_def_field, Complex.sinh_zero, sub_zero, sub_zero]
      refine div_ne_zero (sinh_ne_zero_of_abs_im_lt hw ?_) hw
      have him : ((z - y) / 2).im = z.im / 2 := by simp
      rw [him, abs_div, abs_two]
      have hz' : |z.im| ≤ a := hz
      linarith
  exact ((analyticAt_const.mul h1).div h2 hne).differentiableAt.differentiableWithinAt

lemma Psi_line (t y u : ℝ) {ε : ℝ} (hε : Real.sin (ε / 2) ≠ 0) :
    Psi t y (u + (ε : ℂ) * I) =
      Phi t y (u + (ε : ℂ) * I) - gFun 2 t y * Chi y (u + (ε : ℂ) * I) := by
  refine Psi_eq t y (fun h => hε ?_) (sinh_line_ne_zero u y hε)
  have := congrArg Complex.im h
  rw [im_line, Complex.ofReal_im] at this
  rw [this]; simp

/-! ### Integrability on horizontal lines -/

lemma integrable_Phi_line {t : ℝ} (ht : 0 < t) (y : ℝ) {ε : ℝ} (hε : Real.sin (ε / 2) ≠ 0) :
    Integrable fun u : ℝ => Phi t y (u + (ε : ℂ) * I) := by
  have hσ : 0 < |Real.sin (ε / 2)| := abs_pos.2 hε
  have hcont : Continuous fun u : ℝ => Phi t y (u + (ε : ℂ) * I) := by
    unfold Phi
    refine Continuous.div ?_ (by fun_prop) (fun u => sinh_line_ne_zero u y hε)
    exact ((differentiable_gFun_two t).continuous.comp (by fun_prop)).mul (by fun_prop)
  refine Integrable.mono'
    (g := fun u : ℝ => Real.exp (2 * ε ^ 2 / t) / (4 * π * |Real.sin (ε / 2)|) *
      Real.exp (-(2 / t) * u ^ 2))
    ((integrable_exp_neg_mul_sq (by positivity)).const_mul _) hcont.aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  have hg : ‖gFun 2 t (u + (ε : ℂ) * I)‖ =
      Real.exp (2 * ε ^ 2 / t) * Real.exp (-(2 / t) * u ^ 2) / (4 * π) := by
    rw [norm_gFun_two, re_line, im_line, ← Real.exp_add]
    congr 2
    ring
  have hc := norm_cosh_line_le u ε y
  have hs := norm_sinh_line_ge u ε y
  have hC : 0 < Real.cosh ((u - y) / 2) := Real.cosh_pos _
  unfold Phi
  rw [norm_div, norm_mul, hg]
  calc Real.exp (2 * ε ^ 2 / t) * Real.exp (-(2 / t) * u ^ 2) / (4 * π) *
          ‖Complex.cosh (((u : ℂ) + (ε : ℂ) * I - y) / 2)‖ /
          ‖Complex.sinh (((u : ℂ) + (ε : ℂ) * I - y) / 2)‖
      ≤ Real.exp (2 * ε ^ 2 / t) * Real.exp (-(2 / t) * u ^ 2) / (4 * π) *
          Real.cosh ((u - y) / 2) / (|Real.sin (ε / 2)| * Real.cosh ((u - y) / 2)) := by
        gcongr
    _ = Real.exp (2 * ε ^ 2 / t) / (4 * π * |Real.sin (ε / 2)|) *
          Real.exp (-(2 / t) * u ^ 2) := by
        field_simp

lemma integrable_Chi_line (y : ℝ) {ε : ℝ} (hε : Real.sin (ε / 2) ≠ 0) :
    Integrable fun u : ℝ => Chi y (u + (ε : ℂ) * I) := by
  have hσ : 0 < |Real.sin (ε / 2)| := abs_pos.2 hε
  have hcont : Continuous fun u : ℝ => Chi y (u + (ε : ℂ) * I) := by
    unfold Chi
    exact Continuous.inv₀ (by fun_prop) (fun u => sinh_line_ne_zero u y hε)
  have hint : Integrable fun u : ℝ => |Real.sin (ε / 2)|⁻¹ * (Real.cosh ((u - y) / 2))⁻¹ :=
    ((integrable_inv_cosh.comp_div two_ne_zero).comp_sub_right y).const_mul _
  refine hint.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  have hs := norm_sinh_line_ge u ε y
  have hC : 0 < Real.cosh ((u - y) / 2) := Real.cosh_pos _
  unfold Chi
  rw [norm_inv, ← mul_inv]
  exact inv_anti₀ (by positivity) hs

/-! ### The jump of `χ_y` across the strip -/

lemma Chi_sub (y : ℝ) {a : ℝ} (hσ : 0 < Real.sin (a / 2)) (u : ℝ) :
    Chi y (u + ((-a : ℝ) : ℂ) * I) - Chi y (u + (a : ℂ) * I) =
      4 * I * ((Real.sin (a / 2) * Real.cosh ((u - y) / 2) / 2 /
        (Real.sin (a / 2) ^ 2 + Real.sinh ((u - y) / 2) ^ 2) : ℝ) : ℂ) := by
  have hσ' : Real.sin (-a / 2) ≠ 0 := by
    rw [neg_div, Real.sin_neg]; exact neg_ne_zero.2 hσ.ne'
  have hA := sinh_line_ne_zero u y hσ'
  have hB := sinh_line_ne_zero u y hσ.ne'
  unfold Chi
  have e1 : ((u : ℂ) + ((-a : ℝ) : ℂ) * I - y) / 2 =
      (((u - y) / 2 : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ) * I := by push_cast; ring
  have e2 : ((u : ℂ) + (a : ℂ) * I - y) / 2 =
      (((u - y) / 2 : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [e1] at hA ⊢
  rw [e2] at hB ⊢
  generalize (u - y) / 2 = x at hA hB ⊢
  generalize a / 2 = β at hσ hA hB ⊢
  have hX : Complex.cosh (x : ℂ) ^ 2 - Complex.sinh (x : ℂ) ^ 2 = 1 :=
    Complex.cosh_sq_sub_sinh_sq _
  have hW : Complex.cosh ((β : ℂ) * I) ^ 2 - Complex.sinh ((β : ℂ) * I) ^ 2 = 1 :=
    Complex.cosh_sq_sub_sinh_sq _
  have hprod : Complex.sinh ((x : ℂ) - (β : ℂ) * I) * Complex.sinh ((x : ℂ) + (β : ℂ) * I) =
      Complex.sinh (x : ℂ) ^ 2 - Complex.sinh ((β : ℂ) * I) ^ 2 := by
    rw [Complex.sinh_sub, Complex.sinh_add]
    linear_combination Complex.sinh (x : ℂ) ^ 2 * hW - Complex.sinh ((β : ℂ) * I) ^ 2 * hX
  have hdiff : Complex.sinh ((x : ℂ) + (β : ℂ) * I) - Complex.sinh ((x : ℂ) - (β : ℂ) * I) =
      2 * Complex.cosh (x : ℂ) * Complex.sinh ((β : ℂ) * I) := by
    rw [Complex.sinh_sub, Complex.sinh_add]; ring
  have hinv : (Complex.sinh ((x : ℂ) - (β : ℂ) * I))⁻¹ -
      (Complex.sinh ((x : ℂ) + (β : ℂ) * I))⁻¹ =
      2 * Complex.cosh (x : ℂ) * Complex.sinh ((β : ℂ) * I) /
        (Complex.sinh (x : ℂ) ^ 2 - Complex.sinh ((β : ℂ) * I) ^ 2) := by
    rw [← hprod, ← hdiff]
    field_simp
  rw [hinv, Complex.sinh_mul_I, mul_pow, Complex.I_sq, ← Complex.ofReal_sinh,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sin]
  have hd' : ((Real.sinh x : ℝ) : ℂ) ^ 2 - ((Real.sin β : ℝ) : ℂ) ^ 2 * -1 =
      ((Real.sin β : ℝ) : ℂ) ^ 2 + ((Real.sinh x : ℝ) : ℂ) ^ 2 := by ring
  rw [hd']
  push_cast
  ring

lemma integral_Chi_sub (y : ℝ) {a : ℝ} (ha : 0 < a) (ha2 : a < 2 * π) :
    ∫ u : ℝ, (Chi y (u + ((-a : ℝ) : ℂ) * I) - Chi y (u + (a : ℂ) * I)) = 4 * π * I := by
  have hσ : 0 < Real.sin (a / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  set σ := Real.sin (a / 2) with hσdef
  have hderiv : ∀ u : ℝ, HasDerivAt (fun u : ℝ => Real.arctan (Real.sinh ((u - y) / 2) / σ))
      (σ * Real.cosh ((u - y) / 2) / 2 / (σ ^ 2 + Real.sinh ((u - y) / 2) ^ 2)) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => Real.sinh ((u - y) / 2) / σ)
        (Real.cosh ((u - y) / 2) * (1 / 2) / σ) u :=
      ((Real.hasDerivAt_sinh _).comp u (((hasDerivAt_id u).sub_const y).div_const 2)).div_const σ
    refine h1.arctan.congr_deriv ?_
    field_simp
  have hint : Integrable fun u : ℝ =>
      σ * Real.cosh ((u - y) / 2) / 2 / (σ ^ 2 + Real.sinh ((u - y) / 2) ^ 2) := by
    have hbound : Integrable fun u : ℝ => (2 * σ)⁻¹ * (Real.cosh ((u - y) / 2))⁻¹ :=
      ((integrable_inv_cosh.comp_div two_ne_zero).comp_sub_right y).const_mul _
    refine hbound.mono' (Continuous.aestronglyMeasurable ?_) (Eventually.of_forall fun u => ?_)
    · refine Continuous.div (by fun_prop) (by fun_prop) fun u => ?_
      positivity
    · have hC : 0 < Real.cosh ((u - y) / 2) := Real.cosh_pos _
      have hsc : Real.cosh ((u - y) / 2) ^ 2 - Real.sinh ((u - y) / 2) ^ 2 = 1 :=
        Real.cosh_sq_sub_sinh_sq _
      have hσ1 : σ ≤ 1 := Real.sin_le_one _
      have hσ2 : σ ^ 2 ≤ 1 := by nlinarith
      have key : σ * Real.cosh ((u - y) / 2) / 2 * (2 * σ * Real.cosh ((u - y) / 2)) =
          σ ^ 2 + σ ^ 2 * Real.sinh ((u - y) / 2) ^ 2 := by
        have hC2 : Real.cosh ((u - y) / 2) ^ 2 = 1 + Real.sinh ((u - y) / 2) ^ 2 := by linarith
        calc σ * Real.cosh ((u - y) / 2) / 2 * (2 * σ * Real.cosh ((u - y) / 2))
            = σ ^ 2 * Real.cosh ((u - y) / 2) ^ 2 := by ring
          _ = _ := by rw [hC2]; ring
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_inv, ← one_div,
        div_le_div_iff₀ (by positivity) (by positivity), key]
      nlinarith [mul_nonneg (sq_nonneg (Real.sinh ((u - y) / 2))) (sub_nonneg.2 hσ2)]
  have hlin_top : Tendsto (fun u : ℝ => (u - y) / 2) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨2 * b + y, fun u hu => by linarith⟩
  have hlin_bot : Tendsto (fun u : ℝ => (u - y) / 2) atBot atBot :=
    tendsto_atBot_atBot.2 fun b => ⟨2 * b + y, fun u hu => by linarith⟩
  have htop : Tendsto (fun u : ℝ => Real.arctan (Real.sinh ((u - y) / 2) / σ)) atTop
      (𝓝 (π / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp
      ((tendsto_sinh_atTop.comp hlin_top).atTop_div_const hσ)
  have hbot : Tendsto (fun u : ℝ => Real.arctan (Real.sinh ((u - y) / 2) / σ)) atBot
      (𝓝 (-(π / 2))) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atBot).comp
      ((tendsto_sinh_atBot.comp hlin_bot).atBot_div_const hσ)
  have hreal := integral_of_hasDerivAt_of_tendsto hderiv hint hbot htop
  simp_rw [Chi_sub y hσ]
  rw [integral_const_mul, integral_complex_ofReal, hreal]
  push_cast
  ring

/-! ### The residue identity for `Φ_y` -/

lemma Phi_conj (t y : ℝ) (z : ℂ) : Phi t y (conj z) = -conj (Phi t y z) := by
  have h : (conj z - (y : ℂ)) / 2 = conj ((z - y) / 2) := by
    simp [map_div₀, map_sub, Complex.conj_ofReal, map_ofNat]
  unfold Phi
  rw [h, Complex.cosh_conj, Complex.sinh_conj, gFun_two_conj, map_div₀, map_mul]
  ring

lemma norm_Psi_le {t : ℝ} (ht : 0 < t) (y : ℝ) {a : ℝ} {z : ℂ}
    (hz : |z.im| ≤ a) (hre : |y| + 2 ≤ |z.re|) :
    ‖Psi t y z‖ ≤ 2 * (Real.exp (2 * a ^ 2 / t) / (4 * π)) * Real.exp (-(2 / t) * z.re ^ 2) +
      2 * ‖gFun 2 t y‖ / (|z.re| - |y|) := by
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = (z - y) / 2 := ⟨_, rfl⟩
  have hwre : w.re = (z.re - y) / 2 := by simp [hw]
  have hd : 0 < |z.re| - |y| := by linarith
  have hx : (|z.re| - |y|) / 2 ≤ |w.re| := by
    rw [hwre, abs_div, abs_two]
    have := abs_sub_abs_le_abs_sub z.re y
    linarith
  have hsx : |w.re| ≤ |Real.sinh w.re| := by
    rw [Real.abs_sinh]; exact Real.self_le_sinh_iff.2 (abs_nonneg _)
  have hsn : |Real.sinh w.re| ≤ ‖Complex.sinh w‖ := abs_sinh_le_norm_sinh w
  have hspos : 0 < ‖Complex.sinh w‖ := by linarith
  have hs0 : Complex.sinh w ≠ 0 := norm_pos_iff.1 hspos
  have hzy : z ≠ y := by
    intro h
    rw [h, Complex.ofReal_re] at hre
    linarith
  have hc : ‖Complex.cosh w‖ ≤ 2 * ‖Complex.sinh w‖ := by
    have h1 := norm_cosh_le_cosh w
    have h2 : Real.cosh w.re ≤ |Real.sinh w.re| + 1 := by
      refine (pow_le_pow_iff_left₀ (Real.cosh_pos _).le (by positivity) two_ne_zero).1 ?_
      have hsc : Real.cosh w.re ^ 2 - Real.sinh w.re ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq _
      nlinarith [abs_nonneg (Real.sinh w.re), sq_abs (Real.sinh w.re)]
    linarith
  have hg : ‖gFun 2 t z‖ ≤
      Real.exp (2 * a ^ 2 / t) / (4 * π) * Real.exp (-(2 / t) * z.re ^ 2) := by
    have him : z.im ^ 2 ≤ a ^ 2 := sq_le_sq' (by linarith [(abs_le.1 hz).1]) (abs_le.1 hz).2
    have e : -2 * (z.re ^ 2 - z.im ^ 2) / t = 2 * z.im ^ 2 / t + -(2 / t) * z.re ^ 2 := by ring
    rw [norm_gFun_two, div_mul_eq_mul_div, ← Real.exp_add, e]
    refine div_le_div_of_nonneg_right (Real.exp_le_exp.2 ?_) (by positivity)
    exact add_le_add_left (div_le_div_of_nonneg_right (by linarith) ht.le) _
  rw [hw] at hs0
  rw [Psi_eq t y hzy hs0]
  rw [← hw] at hs0
  refine (norm_sub_le _ _).trans ?_
  have hP : ‖Phi t y z‖ ≤
      2 * (Real.exp (2 * a ^ 2 / t) / (4 * π)) * Real.exp (-(2 / t) * z.re ^ 2) := by
    unfold Phi
    rw [← hw, norm_div, norm_mul, div_le_iff₀ hspos]
    calc ‖gFun 2 t z‖ * ‖Complex.cosh w‖
        ≤ (Real.exp (2 * a ^ 2 / t) / (4 * π) * Real.exp (-(2 / t) * z.re ^ 2)) *
            (2 * ‖Complex.sinh w‖) := mul_le_mul hg hc (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hQ : ‖gFun 2 t y * Chi y z‖ ≤ 2 * ‖gFun 2 t y‖ / (|z.re| - |y|) := by
    unfold Chi
    rw [← hw, norm_mul, norm_inv]
    have hinv : ‖Complex.sinh w‖⁻¹ ≤ 2 / (|z.re| - |y|) :=
      calc ‖Complex.sinh w‖⁻¹ ≤ ((|z.re| - |y|) / 2)⁻¹ :=
            inv_anti₀ (by positivity) (by linarith)
        _ = 2 / (|z.re| - |y|) := by rw [inv_div]
    calc ‖gFun 2 t y‖ * ‖Complex.sinh w‖⁻¹ ≤ ‖gFun 2 t y‖ * (2 / (|z.re| - |y|)) :=
          mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
      _ = _ := by ring
  exact add_le_add hP hQ

/-- The residue identity: the two edges of the strip differ by `2πi · Res_{z=y} Φ_y`. -/
lemma integral_Phi_sub {t : ℝ} (ht : 0 < t) (y : ℝ) {a : ℝ} (ha : 0 < a) (ha2 : a < 2 * π) :
    (∫ u : ℝ, Phi t y (u + ((-a : ℝ) : ℂ) * I)) - ∫ u : ℝ, Phi t y (u + (a : ℂ) * I) =
      ((Real.exp (-2 * y ^ 2 / t) : ℝ) : ℂ) := by
  have hσ : Real.sin (a / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have hσ' : Real.sin (-a / 2) ≠ 0 := by
    rw [neg_div, Real.sin_neg]; exact neg_ne_zero.2 hσ
  have hΦlo := integrable_Phi_line ht y hσ'
  have hΦhi := integrable_Phi_line ht y hσ
  have hχlo := integrable_Chi_line y hσ'
  have hχhi := integrable_Chi_line y hσ
  have hΨlo : Integrable fun u : ℝ => Psi t y (u + ((-a : ℝ) : ℂ) * I) :=
    (hΦlo.sub (hχlo.const_mul (gFun 2 t y))).congr
      (Eventually.of_forall fun u => (Psi_line t y u hσ').symm)
  have hΨhi : Integrable fun u : ℝ => Psi t y (u + (a : ℂ) * I) :=
    (hΦhi.sub (hχhi.const_mul (gFun 2 t y))).congr
      (Eventually.of_forall fun u => (Psi_line t y u hσ).symm)
  have hB : Tendsto (fun R : ℝ => 2 * (Real.exp (2 * a ^ 2 / t) / (4 * π)) *
      Real.exp (-(2 / t) * R ^ 2) + 2 * ‖gFun 2 t y‖ / (R - |y|)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => Real.exp (-(2 / t) * R ^ 2)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp
        ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by
          have : 0 < 2 / t := by positivity
          linarith))
    have h2 : Tendsto (fun R : ℝ => 2 * ‖gFun 2 t y‖ / (R - |y|)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_atTop.2 fun b => ⟨b + |y|, fun R hR => by linarith⟩)
    simpa using (h1.const_mul (2 * (Real.exp (2 * a ^ 2 / t) / (4 * π)))).add h2
  have hvert : ∀ᶠ R : ℝ in atTop, ∀ s ∈ Icc (-a) a,
      ‖Psi t y ((R : ℂ) + s * I)‖ ≤ 2 * (Real.exp (2 * a ^ 2 / t) / (4 * π)) *
          Real.exp (-(2 / t) * R ^ 2) + 2 * ‖gFun 2 t y‖ / (R - |y|) ∧
      ‖Psi t y (((-R : ℝ) : ℂ) + s * I)‖ ≤ 2 * (Real.exp (2 * a ^ 2 / t) / (4 * π)) *
          Real.exp (-(2 / t) * R ^ 2) + 2 * ‖gFun 2 t y‖ / (R - |y|) := by
    filter_upwards [eventually_ge_atTop (|y| + 2)] with R hR s hs
    have hR0 : 0 ≤ R := by linarith [abs_nonneg y]
    have hs' : |s| ≤ a := abs_le.2 hs
    constructor
    · have h := norm_Psi_le ht y (a := a) (z := (R : ℂ) + s * I)
        (by rw [im_line]; exact hs') (by rw [re_line, abs_of_nonneg hR0]; exact hR)
      rwa [re_line, abs_of_nonneg hR0] at h
    · have h := norm_Psi_le ht y (a := a) (z := ((-R : ℝ) : ℂ) + s * I)
        (by rw [im_line]; exact hs') (by rw [re_line, abs_neg, abs_of_nonneg hR0]; exact hR)
      rwa [re_line, abs_neg, abs_of_nonneg hR0, neg_sq] at h
  have hstrip := integral_strip_eq ha.le (differentiableOn_Psi t y ha2) hΨlo hΨhi hB hvert
  have hlo : ∫ u : ℝ, Psi t y (u + ((-a : ℝ) : ℂ) * I) =
      (∫ u : ℝ, Phi t y (u + ((-a : ℝ) : ℂ) * I)) -
        gFun 2 t y * ∫ u : ℝ, Chi y (u + ((-a : ℝ) : ℂ) * I) := by
    rw [integral_congr_ae (Eventually.of_forall fun u => Psi_line t y u hσ'),
      integral_sub hΦlo (hχlo.const_mul _), integral_const_mul]
  have hhi : ∫ u : ℝ, Psi t y (u + (a : ℂ) * I) =
      (∫ u : ℝ, Phi t y (u + (a : ℂ) * I)) -
        gFun 2 t y * ∫ u : ℝ, Chi y (u + (a : ℂ) * I) := by
    rw [integral_congr_ae (Eventually.of_forall fun u => Psi_line t y u hσ),
      integral_sub hΦhi (hχhi.const_mul _), integral_const_mul]
  have hχ := integral_Chi_sub y ha ha2
  rw [integral_sub hχlo hχhi] at hχ
  rw [hlo, hhi] at hstrip
  rw [← gFun_two_mul]
  linear_combination hstrip + gFun 2 t y * hχ

/-- Twice the real part of the lower-edge integral of `Φ_y`. -/
lemma two_re_integral_Phi {t : ℝ} (ht : 0 < t) (y : ℝ) {a : ℝ} (ha : 0 < a)
    (ha2 : a < 2 * π) :
    2 * (∫ u : ℝ, Phi t y (u + ((-a : ℝ) : ℂ) * I)).re = Real.exp (-2 * y ^ 2 / t) := by
  have hsub := integral_Phi_sub ht y ha ha2
  have hhi : ∫ u : ℝ, Phi t y (u + (a : ℂ) * I) =
      -conj (∫ u : ℝ, Phi t y (u + ((-a : ℝ) : ℂ) * I)) := by
    rw [← integral_conj, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only
    rw [← Phi_conj]
    congr 1
    simp [Complex.conj_ofReal]
  rw [hhi, sub_neg_eq_add, Complex.add_conj] at hsub
  exact_mod_cast hsub

/-! ### The contour equation for `p = 2` -/

lemma sinh_div_cosh_sub {A B : ℂ} (hA : Complex.sinh A ≠ 0) (hB : Complex.sinh B ≠ 0) :
    Complex.sinh (A + B) / (Complex.cosh (A + B) - Complex.cosh (B - A)) =
      (Complex.cosh A / Complex.sinh A + Complex.cosh B / Complex.sinh B) / 2 := by
  have h : Complex.cosh (A + B) - Complex.cosh (B - A) = 2 * Complex.sinh A * Complex.sinh B := by
    rw [Complex.cosh_add, Complex.cosh_sub]; ring
  rw [h, Complex.sinh_add]
  field_simp
  ring

lemma integrand_two_eq (t y : ℝ) {z : ℂ} (hA : Complex.sinh ((z - y) / 2) ≠ 0)
    (hB : Complex.sinh ((z - ((-y : ℝ) : ℂ)) / 2) ≠ 0) :
    gFun 2 t z * Complex.sinh z / (Complex.cosh z - Complex.cosh y) =
      (Phi t y z + Phi t (-y) z) / 2 := by
  have h := sinh_div_cosh_sub hA hB
  have e1 : (z - y) / 2 + (z - ((-y : ℝ) : ℂ)) / 2 = z := by push_cast; ring
  have e2 : (z - ((-y : ℝ) : ℂ)) / 2 - (z - y) / 2 = y := by push_cast; ring
  rw [e1, e2] at h
  unfold Phi
  rw [mul_div_assoc, h]
  ring

/-- The contour equation (5.3) for `p = 2`, on the lower edge `u ↦ u − ia`, `0 < a < 2π`. -/
theorem contour_two {t : ℝ} (ht : 0 < t) (y : ℝ) {a : ℝ} (ha : 0 < a) (ha2 : a < 2 * π) :
    Integrable (fun u : ℝ => gFun 2 t (u - I * a) * Complex.sinh (u - I * a) /
        (Complex.cosh (u - I * a) - Complex.cosh y)) ∧
      2 * (∫ u : ℝ, gFun 2 t (u - I * a) * Complex.sinh (u - I * a) /
        (Complex.cosh (u - I * a) - Complex.cosh y)).re = Real.exp (-2 * y ^ 2 / t) := by
  have hσ' : Real.sin (-a / 2) ≠ 0 := by
    rw [neg_div, Real.sin_neg]
    exact neg_ne_zero.2 (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have hz : ∀ u : ℝ, (u : ℂ) - I * a = u + ((-a : ℝ) : ℂ) * I := fun u => by push_cast; ring
  have hΦ1 := integrable_Phi_line ht y hσ'
  have hΦ2 := integrable_Phi_line ht (-y) hσ'
  have heq : ∀ u : ℝ, gFun 2 t (u - I * a) * Complex.sinh (u - I * a) /
        (Complex.cosh (u - I * a) - Complex.cosh y) =
      (Phi t y (u + ((-a : ℝ) : ℂ) * I) + Phi t (-y) (u + ((-a : ℝ) : ℂ) * I)) / 2 := by
    intro u
    rw [hz u]
    exact integrand_two_eq t y (sinh_line_ne_zero u y hσ') (sinh_line_ne_zero u (-y) hσ')
  simp_rw [heq]
  refine ⟨(hΦ1.add hΦ2).div_const 2, ?_⟩
  rw [integral_div, integral_add hΦ1 hΦ2]
  have h1 := two_re_integral_Phi ht y ha ha2
  have h2 := two_re_integral_Phi ht (-y) ha ha2
  rw [neg_sq] at h2
  have hre : ((∫ u : ℝ, Phi t y (u + ((-a : ℝ) : ℂ) * I)) +
      ∫ u : ℝ, Phi t (-y) (u + ((-a : ℝ) : ℂ) * I)) / 2 =
      ((1 / 2 : ℝ) : ℂ) * ((∫ u : ℝ, Phi t y (u + ((-a : ℝ) : ℂ) * I)) +
      ∫ u : ℝ, Phi t (-y) (u + ((-a : ℝ) : ℂ) * I)) := by push_cast; ring
  rw [hre, Complex.re_ofReal_mul, Complex.add_re]
  linarith

end ContourTwo

end Lyasoff2016
