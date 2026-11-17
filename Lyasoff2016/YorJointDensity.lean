/-
Evaluation of the `1/x`-Laplace transform of `yorDensity`, nonnegativity of `yorDensity`,
and the sorry-free proof of `IsJointDensity P W 2 0 t (yorDensity t)`.
-/
module

public import Lyasoff2016.YorLaplace
public import Lyasoff2016.YorDensity

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real Polynomial

noncomputable section
namespace Lyasoff2016

section YorIntegrability

/-- For `t > 0`, `u ↦ exp(-u²/(2t)) * sinh u` is integrable on `Ioi 0`. -/
lemma integrableOn_exp_neg_quad_mul_sinh {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun u : ℝ => Real.exp (-u ^ 2 / (2 * t)) * Real.sinh u) (Ioi 0) := by
  have hgauss : Integrable (fun u : ℝ => Real.exp (t / 2) * Real.exp (-(1 / (2 * t)) * (u - t) ^ 2)) :=
    ((integrable_exp_neg_mul_sq (by positivity : 0 < 1 / (2 * t))).comp_sub_right t).const_mul _
  refine hgauss.integrableOn.mono' (by fun_prop) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
  have hsinh_nn : 0 ≤ Real.sinh u := Real.sinh_nonneg_iff.mpr hu.out.le
  have hsinh_le : Real.sinh u ≤ Real.exp u := by
    rw [Real.sinh_eq]; linarith [Real.exp_pos (-u), Real.exp_pos u]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hsinh_nn]
  calc Real.exp (-u ^ 2 / (2 * t)) * Real.sinh u
      ≤ Real.exp (-u ^ 2 / (2 * t)) * Real.exp u :=
        mul_le_mul_of_nonneg_left hsinh_le (Real.exp_pos _).le
    _ = Real.exp (t / 2) * Real.exp (-(1 / (2 * t)) * (u - t) ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; field_simp [ht.ne']; ring

private lemma integral_Ioi_exp_neg_mul {c : ℝ} (hc : 0 < c) :
    ∫ s in Ioi (0 : ℝ), Real.exp (-s * c) = c⁻¹ := by
  have hderiv : ∀ s ∈ Ici (0 : ℝ),
      HasDerivAt (fun s' : ℝ => -c⁻¹ * Real.exp (-s' * c)) (Real.exp (-s * c)) s := by
    intro s _
    have hlin : HasDerivAt (fun s' : ℝ => -s' * c) (-c) s := by
      have h := ((hasDerivAt_id' s).neg).mul_const c
      simpa using h
    convert hlin.exp.const_mul (-c⁻¹) using 1
    field_simp [hc.ne']
  have hlim : Tendsto (fun s : ℝ => -c⁻¹ * Real.exp (-s * c)) atTop (nhds 0) := by
    have ht : Tendsto (fun s : ℝ => -s * c) atTop atBot := by
      rw [show (fun s : ℝ => -s * c) = fun s => (-c) * s by funext s; ring]
      exact Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_id
    simpa [Function.comp_def] using (Real.tendsto_exp_atBot.comp ht).const_mul (-c⁻¹)
  have hint := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hderiv
    (fun s _ => (Real.exp_pos _).le) hlim
  simpa [sub_neg_eq_add] using hint

private lemma sqrt_two_pi_cube_mul (t : ℝ) (_ht : 0 < t) :
    Real.pi / Real.sqrt (2 * Real.pi ^ 3 * t) = 1 / Real.sqrt (2 * Real.pi * t) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsq : 2 * Real.pi ^ 3 * t = Real.pi ^ 2 * (2 * Real.pi * t) := by ring
  rw [hsq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hpi.le]
  field_simp [hpi.ne']

/-- Exact `1/x`-Laplace transform of `yorDensity t · y` on `Ioi 0` for `t > 0, v₀ > 0`. -/
lemma yorDensity_laplace_x (t : ℝ≥0) (ht : 0 < t) {v₀ : ℝ} (hv₀ : 0 < v₀) (y : ℝ) :
    IntegrableOn (fun x => Real.exp (-v₀ / x) * yorDensity t x y) (Ioi 0) ∧
    ∫ x in Ioi (0 : ℝ), Real.exp (-v₀ / x) * yorDensity t x y =
      gaussianPDFReal 0 t (Real.arcosh (charA v₀ y)) := by
  have htR : (0 : ℝ) < t := ht
  let Cy : ℝ := v₀ + (1 + Real.exp (2 * y)) / 2
  let c : ℝ → ℝ := fun u => Cy + Real.exp y * Real.cosh u
  have hc_ge : ∀ u : ℝ, v₀ + Real.exp y ≤ c u := fun u => by
    have h1 : Real.exp y ≤ Real.exp y * Real.cosh u :=
      le_mul_of_one_le_right (Real.exp_pos y).le (Real.one_le_cosh u)
    have h2 : 0 ≤ (1 + Real.exp (2 * y)) / 2 := by positivity
    dsimp only [c, Cy]; linarith
  have hc_pos : ∀ u : ℝ, 0 < c u := fun u =>
    lt_of_lt_of_le (by positivity) (hc_ge u)
  let g : ℝ → ℝ → ℝ := fun s u =>
    Real.exp (-u ^ 2 / (2 * (t : ℝ))) * Real.sinh u * Real.sin (Real.pi * u / t) * Real.exp (-s * c u)
  have hg_sm : StronglyMeasurable (Function.uncurry g) := by
    have hc : Continuous (Function.uncurry g) := by
      unfold Function.uncurry; dsimp only [g, c, Cy]; fun_prop
    exact hc.stronglyMeasurable
  have hg_int_s : ∀ u ∈ Ioi (0 : ℝ),
      IntegrableOn (fun s => g s u) (Ioi 0) ∧
      ∫ s in Ioi (0 : ℝ), |g s u| ≤
        (Real.exp (-u ^ 2 / (2 * (t : ℝ))) * Real.sinh u) * (v₀ + Real.exp y)⁻¹ := by
    intro u hu
    have h1 : IntegrableOn (fun s => Real.exp (-s * c u)) (Ioi 0) := by
      have hi := integral_Ioi_exp_neg_mul (hc_pos u)
      by_contra H
      have : (c u)⁻¹ = 0 := by rw [← hi, integral_undef H]
      exact (inv_pos.mpr (hc_pos u)).ne' this
    have h2 : IntegrableOn (fun s => g s u) (Ioi 0) := by
      refine (h1.const_mul (Real.exp (-u ^ 2 / (2 * (t : ℝ))) * Real.sinh u *
        Real.sin (Real.pi * u / t))).congr (ae_of_all _ fun s => ?_)
      dsimp only [g]
    refine ⟨h2, ?_⟩
    have hsinh_nn : 0 ≤ Real.sinh u := Real.sinh_nonneg_iff.mpr hu.out.le
    have h_abs : (fun s => |g s u|) =
        fun s => (Real.exp (-u ^ 2 / (2 * (t : ℝ))) * Real.sinh u * |Real.sin (Real.pi * u / t)|) *
          Real.exp (-s * c u) := by
      funext s
      simp only [g, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hsinh_nn]
    rw [h_abs, integral_const_mul, integral_Ioi_exp_neg_mul (hc_pos u)]
    have hsin1 : |Real.sin (Real.pi * u / t)| ≤ 1 := Real.abs_sin_le_one _
    have hcinv : (c u)⁻¹ ≤ (v₀ + Real.exp y)⁻¹ :=
      inv_anti₀ (by positivity) (hc_ge u)
    calc Real.exp (-u ^ 2 / (2 * (t : ℝ))) * Real.sinh u * |Real.sin (Real.pi * u / t)| * (c u)⁻¹
        ≤ Real.exp (-u ^ 2 / (2 * (t : ℝ))) * Real.sinh u * 1 * (v₀ + Real.exp y)⁻¹ := by
          gcongr
      _ = (Real.exp (-u ^ 2 / (2 * (t : ℝ))) * Real.sinh u) * (v₀ + Real.exp y)⁻¹ := by ring
  have hg_prod_int : Integrable (Function.uncurry g)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [integrable_prod_iff' hg_sm.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => (hg_int_s u hu).1
    · have hdom : IntegrableOn (fun u => (Real.exp (-u ^ 2 / (2 * (t : ℝ))) * Real.sinh u) *
          (v₀ + Real.exp y)⁻¹) (Ioi 0) :=
        (integrableOn_exp_neg_quad_mul_sinh htR).mul_const _
      refine hdom.mono' (hg_sm.norm.integral_prod_left').aestronglyMeasurable ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      simpa [Real.norm_eq_abs] using (hg_int_s u hu).2
  have hswap := integral_integral_swap hg_prod_int
  have h_s_int : IntegrableOn (fun s => ∫ u in Ioi (0 : ℝ), g s u) (Ioi 0) :=
    hg_prod_int.integral_prod_left
  have h_u_rhs : ∫ u in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), g s u =
      ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * (t : ℝ))) * Real.sinh u * Real.sin (Real.pi * u / t) / c u := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    have heq : (fun s => g s u) =
        fun s => (Real.exp (-u ^ 2 / (2 * (t : ℝ))) * Real.sinh u * Real.sin (Real.pi * u / t)) *
          Real.exp (-s * c u) := by
      funext s; simp only [g]
    rw [heq, integral_const_mul, integral_Ioi_exp_neg_mul (hc_pos u), ← div_eq_mul_inv]
  let K : ℝ := Real.exp y / Real.sqrt (2 * Real.pi ^ 3 * t) * Real.exp (Real.pi ^ 2 / (2 * t))
  have h_rel_s : ∀ s ∈ Ioi (0 : ℝ),
      |-(s ^ 2)⁻¹| • (Real.exp (-v₀ / s⁻¹) * yorDensity t s⁻¹ y) = K * ∫ u in Ioi (0 : ℝ), g s u := by
    intro s hs
    have hs0 : 0 < s := hs
    have hpow : |-(s ^ 2)⁻¹| = s⁻¹ ^ 2 := by
      rw [abs_neg, abs_inv, abs_of_pos (sq_pos_of_pos hs0), inv_pow]
    rw [smul_eq_mul, hpow]
    have h_in : (fun u => g s u) = fun u =>
        Real.exp (-s * Cy) * (Real.exp (-u ^ 2 / (2 * (t : ℝ))) * Real.exp (-(Real.exp y / s⁻¹) * Real.cosh u) *
          Real.sinh u * Real.sin (Real.pi * u / t)) := by
      funext u
      dsimp only [g, c]
      rw [div_inv_eq_mul]
      rw [show (-s) * (Cy + Real.exp y * Real.cosh u) = -s * Cy + -(Real.exp y * s * Real.cosh u) by ring,
        Real.exp_add]
      ring_nf
    rw [h_in, integral_const_mul]
    simp only [yorDensity, theta]
    have hexp_mul : Real.exp (-v₀ / s⁻¹) * Real.exp (-(1 + Real.exp (2 * y)) / (2 * s⁻¹)) =
        Real.exp (-s * Cy) := by
      rw [← Real.exp_add]; congr 1
      dsimp only [Cy]
      field_simp [hs0.ne']; ring
    have hpref : s⁻¹ ^ 2 * (1 / s⁻¹ * (Real.exp y / s⁻¹ / Real.sqrt (2 * Real.pi ^ 3 * t) *
        Real.exp (Real.pi ^ 2 / (2 * t)))) = K := by
      dsimp only [K]
      field_simp [hs0.ne']
    calc s⁻¹ ^ 2 * (Real.exp (-v₀ / s⁻¹) * (1 / s⁻¹ * Real.exp (-(1 + Real.exp (2 * y)) / (2 * s⁻¹)) *
          (Real.exp y / s⁻¹ / Real.sqrt (2 * Real.pi ^ 3 * t) * Real.exp (Real.pi ^ 2 / (2 * t)) *
            ∫ u in Ioi 0, Real.exp (-u ^ 2 / (2 * (t : ℝ))) * Real.exp (-(Real.exp y / s⁻¹) * Real.cosh u) *
              Real.sinh u * Real.sin (Real.pi * u / t))))
        = (s⁻¹ ^ 2 * (1 / s⁻¹ * (Real.exp y / s⁻¹ / Real.sqrt (2 * Real.pi ^ 3 * t) *
              Real.exp (Real.pi ^ 2 / (2 * t))))) *
            ((Real.exp (-v₀ / s⁻¹) * Real.exp (-(1 + Real.exp (2 * y)) / (2 * s⁻¹))) *
              ∫ u in Ioi 0, Real.exp (-u ^ 2 / (2 * (t : ℝ))) * Real.exp (-(Real.exp y / s⁻¹) * Real.cosh u) *
                Real.sinh u * Real.sin (Real.pi * u / t)) := by ring
      _ = K * (Real.exp (-s * Cy) * ∫ u in Ioi 0, Real.exp (-u ^ 2 / (2 * (t : ℝ))) *
            Real.exp (-(Real.exp y / s⁻¹) * Real.cosh u) * Real.sinh u * Real.sin (Real.pi * u / t)) := by
          rw [hpref, hexp_mul]
  have h_inv_img : (Inv.inv '' Ioi (0 : ℝ)) = Ioi (0 : ℝ) := by
    ext x
    simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨s, hs, rfl⟩; exact inv_pos.mpr hs
    · intro hx; exact ⟨x⁻¹, inv_pos.mpr hx, inv_inv x⟩
  have h_inv_deriv : ∀ s ∈ Ioi (0 : ℝ), HasDerivWithinAt Inv.inv (-(s ^ 2)⁻¹) (Ioi 0) s := fun s hs =>
    (hasDerivAt_inv (ne_of_gt hs)).hasDerivWithinAt
  have h_inv_inj : InjOn Inv.inv (Ioi (0 : ℝ)) := fun _ _ _ _ h => inv_injective h
  have h_int_x : IntegrableOn (fun x => Real.exp (-v₀ / x) * yorDensity t x y) (Ioi 0) := by
    rw [← h_inv_img, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      h_inv_deriv h_inv_inj]
    exact (h_s_int.const_mul K).congr (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs =>
      (h_rel_s s hs).symm)
  have h_val_x : ∫ x in Ioi (0 : ℝ), Real.exp (-v₀ / x) * yorDensity t x y =
      K * ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * (t : ℝ))) * Real.sinh u * Real.sin (Real.pi * u / t) / c u := by
    have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      h_inv_deriv h_inv_inj (fun x => Real.exp (-v₀ / x) * yorDensity t x y)
    rw [h_inv_img] at hcov
    rw [hcov, setIntegral_congr_fun measurableSet_Ioi h_rel_s, integral_const_mul, hswap, h_u_rhs]
  refine ⟨h_int_x, ?_⟩
  rw [h_val_x]
  let α : ℝ := Real.arcosh (charA v₀ y)
  have hchar_gt : 1 < charA v₀ y := by
    have h1 : 1 ≤ Real.cosh y := Real.one_le_cosh y
    have h2 : 0 < v₀ * Real.exp (-y) := mul_pos hv₀ (Real.exp_pos (-y))
    unfold charA; linarith
  have hα_pos : 0 < α := by
    by_contra hle
    push Not at hle
    have h0 : α = 0 := le_antisymm hle (Real.arcosh_nonneg hchar_gt.le)
    have hcosh : Real.cosh α = charA v₀ y := Real.cosh_arcosh hchar_gt.le
    rw [h0, Real.cosh_zero] at hcosh
    linarith
  have hcosh_α : Real.cosh α = charA v₀ y := Real.cosh_arcosh hchar_gt.le
  have hc_factor : ∀ u : ℝ, c u = Real.exp y * (Real.cosh u + Real.cosh α) := fun u => by
    rw [hcosh_α]
    dsimp only [c, Cy]
    rw [charA.eq, mul_add]
    have hmul : Real.exp y * Real.exp (-y) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hexp2 : Real.exp (2 * y) = Real.exp y * Real.exp y := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hexp2]
    calc v₀ + (1 + Real.exp y * Real.exp y) / 2 + Real.exp y * Real.cosh u
        = Real.exp y * Real.cosh u + (Real.exp y * Real.exp y + (1 + 2 * v₀) * 1) / 2 := by ring
      _ = Real.exp y * Real.cosh u + (Real.exp y * Real.exp y + (1 + 2 * v₀) * (Real.exp y * Real.exp (-y))) / 2 := by
          rw [hmul]
      _ = Real.exp y * Real.cosh u + Real.exp y * ((Real.exp y + (1 + 2 * v₀) * Real.exp (-y)) / 2) := by ring
  have h_u_eq : (∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * (t : ℝ))) * Real.sinh u * Real.sin (Real.pi * u / t) / c u) =
      Real.exp (-y) * ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * (t : ℝ))) *
        (Real.sinh u * Real.sin (Real.pi * u / t) / (Real.cosh u + Real.cosh α)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [hc_factor u, div_eq_mul_inv, mul_inv, Real.exp_neg]
    ring
  rw [h_u_eq]
  have hcw := hartman_watson_contour htR hα_pos
  have hexp_y : Real.exp y * Real.exp (-y) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc K * (Real.exp (-y) * ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * (t : ℝ))) *
          (Real.sinh u * Real.sin (Real.pi * u / t) / (Real.cosh u + Real.cosh α)))
      = (Real.exp y * Real.exp (-y)) / Real.sqrt (2 * Real.pi ^ 3 * t) *
          (Real.exp (Real.pi ^ 2 / (2 * t)) * ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * (t : ℝ))) *
            (Real.sinh u * Real.sin (Real.pi * u / t) / (Real.cosh u + Real.cosh α))) := by
          dsimp only [K]; ring
    _ = (1 / Real.sqrt (2 * Real.pi ^ 3 * t)) * (Real.pi * Real.exp (-α ^ 2 / (2 * t))) := by
          rw [hexp_y, hcw]
    _ = (Real.pi / Real.sqrt (2 * Real.pi ^ 3 * t)) * Real.exp (-α ^ 2 / (2 * t)) := by ring
    _ = (1 / Real.sqrt (2 * Real.pi * t)) * Real.exp (-α ^ 2 / (2 * t)) := by
          rw [sqrt_two_pi_cube_mul t htR]
    _ = gaussianPDFReal 0 t α := by
          rw [gaussianPDFReal_def]
          simp only [sub_zero, one_div]

/-- Uniform `x`-integrable bound for `|yorDensity t x y|`, with `L¹` norm bounded by a constant
`M_t` independent of `y : ℝ`. -/
lemma yorDensity_abs_bound (t : ℝ≥0) (ht : 0 < t) :
    ∃ M ≥ 0, ∀ y,
      (∀ x > 0, |yorDensity t x y| ≤
        M * (1 / x) * (Real.exp y / x) * Real.exp (-(1 + Real.exp (2 * y)) / (2 * x))) ∧
      IntegrableOn (fun x => yorDensity t x y) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ), |yorDensity t x y| ≤ M := by
  have htR : (0 : ℝ) < t := ht
  let I₀ : ℝ := ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * (t : ℝ))) * Real.sinh u
  have hI₀_nn : 0 ≤ I₀ := setIntegral_nonneg measurableSet_Ioi fun u hu =>
    mul_nonneg (Real.exp_pos _).le (Real.sinh_nonneg_iff.mpr hu.out.le)
  let M : ℝ := (1 / Real.sqrt (2 * Real.pi ^ 3 * t) * Real.exp (Real.pi ^ 2 / (2 * t))) * I₀
  have hM0 : 0 ≤ M := by positivity
  refine ⟨M, hM0, fun y => ?_⟩
  have h_pt : ∀ x > 0, |yorDensity t x y| ≤
      M * (1 / x) * (Real.exp y / x) * Real.exp (-(1 + Real.exp (2 * y)) / (2 * x)) := by
    intro x hx
    have h_theta_bound : |theta (Real.exp y / x) t| ≤
        (Real.exp y / x / Real.sqrt (2 * Real.pi ^ 3 * t) * Real.exp (Real.pi ^ 2 / (2 * t))) * I₀ := by
      unfold theta
      rw [abs_mul, abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hint_norm : |∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * (t : ℝ))) *
            Real.exp (-(Real.exp y / x) * Real.cosh u) * Real.sinh u * Real.sin (Real.pi * u / t)| ≤
          ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * (t : ℝ))) * Real.sinh u := by
        rw [← Real.norm_eq_abs]
        calc ‖∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * (t : ℝ))) *
                Real.exp (-(Real.exp y / x) * Real.cosh u) * Real.sinh u * Real.sin (Real.pi * u / t)‖
            ≤ ∫ u in Ioi (0 : ℝ), ‖Real.exp (-u ^ 2 / (2 * (t : ℝ))) *
                Real.exp (-(Real.exp y / x) * Real.cosh u) * Real.sinh u * Real.sin (Real.pi * u / t)‖ :=
              norm_integral_le_integral_norm _
          _ ≤ ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * (t : ℝ))) * Real.sinh u := by
              refine setIntegral_mono_on ?_ (integrableOn_exp_neg_quad_mul_sinh htR) measurableSet_Ioi
                fun u hu => ?_
              · refine (integrableOn_exp_neg_quad_mul_sinh htR).mono' ?_ ?_
                · exact (by fun_prop : Continuous fun u => ‖Real.exp (-u ^ 2 / (2 * (t : ℝ))) *
                    Real.exp (-(Real.exp y / x) * Real.cosh u) * Real.sinh u *
                    Real.sin (Real.pi * u / t)‖).aestronglyMeasurable
                · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u' hu' => ?_
                  have h1 : Real.exp (-(Real.exp y / x) * Real.cosh u') ≤ 1 :=
                    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
                      (neg_nonpos.mpr (by positivity)) (Real.cosh_pos u').le)
                  have h2 : |Real.sin (Real.pi * u' / t)| ≤ 1 := Real.abs_sin_le_one _
                  have hs : 0 ≤ Real.sinh u' := Real.sinh_nonneg_iff.mpr hu'.out.le
                  rw [Real.norm_eq_abs, abs_norm, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
                    abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _), abs_of_nonneg hs]
                  calc Real.exp (-u' ^ 2 / (2 * (t : ℝ))) * Real.exp (-(Real.exp y / x) * Real.cosh u') *
                        Real.sinh u' * |Real.sin (Real.pi * u' / t)|
                      ≤ Real.exp (-u' ^ 2 / (2 * (t : ℝ))) * 1 * Real.sinh u' * 1 := by gcongr
                    _ = Real.exp (-u' ^ 2 / (2 * (t : ℝ))) * Real.sinh u' := by ring
              · have h1 : Real.exp (-(Real.exp y / x) * Real.cosh u) ≤ 1 :=
                  Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
                    (neg_nonpos.mpr (by positivity)) (Real.cosh_pos u).le)
                have h2 : |Real.sin (Real.pi * u / t)| ≤ 1 := Real.abs_sin_le_one _
                have hs : 0 ≤ Real.sinh u := Real.sinh_nonneg_iff.mpr hu.out.le
                rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
                  abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _), abs_of_nonneg hs]
                calc Real.exp (-u ^ 2 / (2 * (t : ℝ))) * Real.exp (-(Real.exp y / x) * Real.cosh u) *
                      Real.sinh u * |Real.sin (Real.pi * u / t)|
                    ≤ Real.exp (-u ^ 2 / (2 * (t : ℝ))) * 1 * Real.sinh u * 1 := by gcongr
                  _ = Real.exp (-u ^ 2 / (2 * (t : ℝ))) * Real.sinh u := by ring
      exact hint_norm
    dsimp only [yorDensity]
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc 1 / x * Real.exp (-(1 + Real.exp (2 * y)) / (2 * x)) * |theta (Real.exp y / x) t|
        ≤ 1 / x * Real.exp (-(1 + Real.exp (2 * y)) / (2 * x)) *
            ((Real.exp y / x / Real.sqrt (2 * Real.pi ^ 3 * t) * Real.exp (Real.pi ^ 2 / (2 * t))) * I₀) := by
          gcongr
      _ = M * (1 / x) * (Real.exp y / x) * Real.exp (-(1 + Real.exp (2 * y)) / (2 * x)) := by
          dsimp only [M]; ring
  let ay : ℝ := (1 + Real.exp (2 * y)) / 2
  have hay_pos : 0 < ay := by positivity
  have h_env_int : IntegrableOn (fun x => M * (1 / x) * (Real.exp y / x) *
      Real.exp (-(1 + Real.exp (2 * y)) / (2 * x))) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ), M * (1 / x) * (Real.exp y / x) *
        Real.exp (-(1 + Real.exp (2 * y)) / (2 * x)) = M * (Real.exp y / ay) := by
    have h_inv_img : (Inv.inv '' Ioi (0 : ℝ)) = Ioi (0 : ℝ) := by
      ext x; simp only [mem_image, mem_Ioi]
      exact ⟨fun ⟨s, hs, h⟩ => h ▸ inv_pos.mpr hs, fun hx => ⟨x⁻¹, inv_pos.mpr hx, inv_inv x⟩⟩
    have h_inv_deriv : ∀ s ∈ Ioi (0 : ℝ), HasDerivWithinAt Inv.inv (-(s ^ 2)⁻¹) (Ioi 0) s := fun s hs =>
      (hasDerivAt_inv (ne_of_gt hs)).hasDerivWithinAt
    have h_inv_inj : InjOn Inv.inv (Ioi (0 : ℝ)) := fun _ _ _ _ h => inv_injective h
    have hs_eq : ∀ s ∈ Ioi (0 : ℝ),
        |-(s ^ 2)⁻¹| • (M * (1 / s⁻¹) * (Real.exp y / s⁻¹) *
          Real.exp (-(1 + Real.exp (2 * y)) / (2 * s⁻¹))) =
          (M * Real.exp y) * Real.exp (-s * ay) := by
      intro s hs
      have hs0 : 0 < s := hs
      have hpow : |-(s ^ 2)⁻¹| = s⁻¹ ^ 2 := by
        rw [abs_neg, abs_inv, abs_of_pos (sq_pos_of_pos hs0), inv_pow]
      rw [smul_eq_mul, hpow]
      have hexp : -(1 + Real.exp (2 * y)) / (2 * s⁻¹) = -s * ay := by
        dsimp only [ay]; field_simp [hs0.ne']
      rw [hexp]
      field_simp [hs0.ne']
    have h_exp_int : IntegrableOn (fun s => (M * Real.exp y) * Real.exp (-s * ay)) (Ioi 0) := by
      have h1 : IntegrableOn (fun s => Real.exp (-s * ay)) (Ioi 0) := by
        have hi := integral_Ioi_exp_neg_mul hay_pos
        by_contra H; have : ay⁻¹ = 0 := by rw [← hi, integral_undef H]
        exact (inv_pos.mpr hay_pos).ne' this
      exact h1.const_mul _
    refine ⟨?_, ?_⟩
    · rw [← h_inv_img, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
        h_inv_deriv h_inv_inj]
      exact h_exp_int.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => (hs_eq s hs).symm)
    · rw [← h_inv_img, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
        h_inv_deriv h_inv_inj, setIntegral_congr_fun measurableSet_Ioi hs_eq,
        integral_const_mul, integral_Ioi_exp_neg_mul hay_pos]
      ring
  have h_yor_cont : ContinuousOn (fun x => yorDensity t x y) (Ioi 0) := by
    have h_theta_cont : ContinuousOn (fun r => theta r t) (Ioi 0) := by
      unfold theta
      refine ContinuousOn.mul (by fun_prop) ?_
      refine continuousOn_iff_continuous_domRestrict.mpr ?_
      have h_int_c : Continuous (fun r : Ioi (0 : ℝ) =>
          ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * (t : ℝ))) * Real.exp (-r.1 * Real.cosh u) *
            Real.sinh u * Real.sin (Real.pi * u / t)) := by
        refine continuous_of_dominated (bound := fun u => Real.exp (-u ^ 2 / (2 * (t : ℝ))) * Real.sinh u)
          ?_ ?_ (integrableOn_exp_neg_quad_mul_sinh htR) ?_
        · intro r; exact (by fun_prop : Continuous fun u => _).aestronglyMeasurable
        · intro r
          refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
          have h1 : Real.exp (-r.1 * Real.cosh u) ≤ 1 :=
            Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr r.2.le) (Real.cosh_pos u).le)
          have h2 : |Real.sin (Real.pi * u / t)| ≤ 1 := Real.abs_sin_le_one _
          have hs : 0 ≤ Real.sinh u := Real.sinh_nonneg_iff.mpr hu.out.le
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
            abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _), abs_of_nonneg hs]
          calc Real.exp (-u ^ 2 / (2 * (t : ℝ))) * Real.exp (-r.1 * Real.cosh u) * Real.sinh u *
                |Real.sin (Real.pi * u / t)|
              ≤ Real.exp (-u ^ 2 / (2 * (t : ℝ))) * 1 * Real.sinh u * 1 := by gcongr
            _ = Real.exp (-u ^ 2 / (2 * (t : ℝ))) * Real.sinh u := by ring
        · filter_upwards with u
          have hv : Continuous (fun r : Ioi (0 : ℝ) => r.1) := continuous_subtype_val
          fun_prop
      exact (continuous_iff_continuousAt.mpr fun r => h_int_c.continuousAt)
    intro x hx
    have h1 : ContinuousAt (fun x' => (1 / x') * Real.exp (-(1 + Real.exp (2 * y)) / (2 * x'))) x :=
      ((continuousAt_const.div continuousAt_id hx.ne').mul
        (Real.continuous_exp.continuousAt.comp
          (continuousAt_const.div (continuousAt_const.mul continuousAt_id)
            (mul_ne_zero two_ne_zero hx.ne'))))
    have h2 : ContinuousAt (fun x' => theta (Real.exp y / x') t) x :=
      (h_theta_cont.continuousAt (Ioi_mem_nhds (div_pos (Real.exp_pos y) hx))).comp
        (continuousAt_const.div continuousAt_id hx.ne')
    exact (h1.mul h2).continuousWithinAt
  have h_yor_int : IntegrableOn (fun x => yorDensity t x y) (Ioi 0) :=
    h_env_int.1.mono' (h_yor_cont.aestronglyMeasurable measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => by
        rw [Real.norm_eq_abs]; exact h_pt x hx)
  refine ⟨h_pt, h_yor_int, ?_⟩
  have h_amgm : Real.exp y / ay ≤ 1 := by
    rw [div_le_one hay_pos]
    dsimp only [ay]
    have h2 : Real.exp (2 * y) = Real.exp y ^ 2 := by
      rw [← Real.exp_nat_mul]; simp
    rw [h2]
    nlinarith [sq_nonneg (Real.exp y - 1)]
  calc ∫ x in Ioi (0 : ℝ), |yorDensity t x y|
      ≤ ∫ x in Ioi (0 : ℝ), M * (1 / x) * (Real.exp y / x) *
          Real.exp (-(1 + Real.exp (2 * y)) / (2 * x)) :=
        setIntegral_mono_on h_yor_int.abs h_env_int.1 measurableSet_Ioi h_pt
    _ = M * (Real.exp y / ay) := h_env_int.2
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left h_amgm hM0
    _ = M := mul_one _

/-- At `v₀ = 0`, `∫ x in Ioi 0, yorDensity t x y = gaussianPDFReal 0 t y`. -/
lemma yorDensity_integral_x_eq_gaussian (t : ℝ≥0) (ht : 0 < t) (y : ℝ) :
    ∫ x in Ioi (0 : ℝ), yorDensity t x y = gaussianPDFReal 0 t y := by
  obtain ⟨M, _, hM⟩ := yorDensity_abs_bound t ht
  obtain ⟨_, hy_int, _⟩ := hM y
  have hL : Tendsto (fun v : ℝ => ∫ x in Ioi (0 : ℝ), Real.exp (-v / x) * yorDensity t x y)
      (nhdsWithin 0 (Ioi 0)) (nhds (∫ x in Ioi (0 : ℝ), yorDensity t x y)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => |yorDensity t x y|) ?_ ?_
      hy_int.abs ?_
    · filter_upwards [self_mem_nhdsWithin] with v _
      have hm : ContinuousOn (fun x => Real.exp (-v / x)) (Ioi 0) := fun x hx =>
        (Real.continuous_exp.continuousAt.comp
          (continuousAt_const.div continuousAt_id hx.ne')).continuousWithinAt
      exact (hm.aestronglyMeasurable measurableSet_Ioi).mul hy_int.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with v hv
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
      have hexp : Real.exp (-v / x) ≤ 1 :=
        Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hv.le) hx.le)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_left (abs_nonneg _) hexp
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun x _ => ?_
      have h0 : Tendsto (fun v : ℝ => Real.exp (-v / x)) (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
        have hc : Continuous (fun v : ℝ => Real.exp (-v / x)) := by fun_prop
        have ht0 := hc.tendsto (0 : ℝ)
        simp only [neg_zero, zero_div, Real.exp_zero] at ht0
        exact ht0.mono_left nhdsWithin_le_nhds
      simpa using h0.mul_const (yorDensity t x y)
  have h_eq : (fun v : ℝ => ∫ x in Ioi (0 : ℝ), Real.exp (-v / x) * yorDensity t x y) =ᶠ[nhdsWithin 0 (Ioi 0)]
      fun v => gaussianPDFReal 0 t (Real.arcosh (charA v y)) := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact (yorDensity_laplace_x t ht hv y).2
  have hR : Tendsto (fun v : ℝ => gaussianPDFReal 0 t (Real.arcosh (charA v y)))
      (nhdsWithin 0 (Ioi 0)) (nhds (gaussianPDFReal 0 t y)) := by
    have hcontA : Continuous (fun v : ℝ => charA v y) := by unfold charA; fun_prop
    have harc : ContinuousOn Real.arcosh (Ici 1) := Real.continuousOn_arcosh
    have h_in : ∀ v ∈ Ici (0 : ℝ), 1 ≤ charA v y := fun v hv => by
      have h1 : (1 : ℝ) ≤ 1 + 2 * v := by linarith [mem_Ici.mp hv]
      exact (Real.sqrt_one ▸ Real.sqrt_le_sqrt h1).trans (charA.ge_sqrt hv y)
    have hc_on : ContinuousOn (fun v : ℝ => Real.arcosh (charA v y)) (Ici 0) :=
      harc.comp hcontA.continuousOn h_in
    have ht1 : Tendsto (fun v : ℝ => Real.arcosh (charA v y)) (nhdsWithin 0 (Ioi 0))
        (nhds (Real.arcosh (Real.cosh y))) := by
      have h_at := (hc_on 0 le_rfl).tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
      simpa [charA] using h_at
    have h_abs : Real.arcosh (Real.cosh y) = |y| := by
      rw [← Real.cosh_abs y]; exact Real.arcosh_cosh (abs_nonneg y)
    have hgp : Continuous (gaussianPDFReal 0 t) := by rw [gaussianPDFReal_def]; fun_prop
    have ht2 := hgp.continuousAt.tendsto.comp (h_abs ▸ ht1)
    have hgp_abs : gaussianPDFReal 0 t |y| = gaussianPDFReal 0 t y := by
      simp [gaussianPDFReal_def]
    rwa [hgp_abs] at ht2
  exact tendsto_nhds_unique (hL.congr' h_eq) hR

end YorIntegrability

section YorNonnegAndDensity

/-- Joint continuity of `yorDensity t` on `(0, ∞) × ℝ`. -/
lemma yorDensity_continuousOn (t : ℝ≥0) (ht : 0 < t) :
    ContinuousOn (Function.uncurry (yorDensity t)) (Ioi (0 : ℝ) ×ˢ univ) := by
  have htR : (0 : ℝ) < t := ht
  let U := Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)
  refine continuousOn_iff_continuous_domRestrict.mpr ?_
  have h_int_c : Continuous (fun p : U =>
      ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * (t : ℝ))) *
        Real.exp (-(Real.exp p.1.2 / p.1.1) * Real.cosh u) *
        Real.sinh u * Real.sin (Real.pi * u / t)) := by
    refine continuous_of_dominated (bound := fun u => Real.exp (-u ^ 2 / (2 * (t : ℝ))) * Real.sinh u)
      ?_ ?_ (integrableOn_exp_neg_quad_mul_sinh htR) ?_
    · intro p
      exact (by fun_prop : Continuous fun u => _).aestronglyMeasurable
    · intro p
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
      have hx : 0 < p.1.1 := p.2.1
      have h1 : Real.exp (-(Real.exp p.1.2 / p.1.1) * Real.cosh u) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (by positivity)) (Real.cosh_pos u).le)
      have h2 : |Real.sin (Real.pi * u / t)| ≤ 1 := Real.abs_sin_le_one _
      have hs : 0 ≤ Real.sinh u := Real.sinh_nonneg_iff.mpr hu.out.le
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
        abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _), abs_of_nonneg hs]
      calc Real.exp (-u ^ 2 / (2 * (t : ℝ))) *
            Real.exp (-(Real.exp p.1.2 / p.1.1) * Real.cosh u) *
            Real.sinh u * |Real.sin (Real.pi * u / t)|
          ≤ Real.exp (-u ^ 2 / (2 * (t : ℝ))) * 1 * Real.sinh u * 1 := by gcongr
        _ = Real.exp (-u ^ 2 / (2 * (t : ℝ))) * Real.sinh u := by ring
    · filter_upwards with u
      have hp1 : Continuous (fun p : U => p.1.1) := continuous_fst.comp continuous_subtype_val
      have hp2 : Continuous (fun p : U => p.1.2) := continuous_snd.comp continuous_subtype_val
      have hp1_ne : ∀ p : U, p.1.1 ≠ 0 := fun p => p.2.1.ne'
      have h_div : Continuous (fun p : U => Real.exp p.1.2 / p.1.1) :=
        (Real.continuous_exp.comp hp2).div hp1 hp1_ne
      fun_prop
  have hp1 : Continuous (fun p : U => p.1.1) := continuous_fst.comp continuous_subtype_val
  have hp2 : Continuous (fun p : U => p.1.2) := continuous_snd.comp continuous_subtype_val
  have hp1_ne : ∀ p : U, p.1.1 ≠ 0 := fun p => p.2.1.ne'
  have h1 : Continuous (fun p : U => 1 / p.1.1) := continuous_const.div hp1 hp1_ne
  have h2 : Continuous (fun p : U => Real.exp (-(1 + Real.exp (2 * p.1.2)) / (2 * p.1.1))) :=
    Real.continuous_exp.comp (((continuous_const.add (Real.continuous_exp.comp
      (continuous_const.mul hp2))).neg).div (continuous_const.mul hp1)
      fun p => mul_ne_zero two_ne_zero (hp1_ne p))
  have h3 : Continuous (fun p : U => (Real.exp p.1.2 / p.1.1) / Real.sqrt (2 * Real.pi ^ 3 * t) *
      Real.exp (Real.pi ^ 2 / (2 * t))) :=
    (((Real.continuous_exp.comp hp2).div hp1 hp1_ne).div_const _).mul continuous_const
  refine ((h1.mul h2).mul (h3.mul h_int_c)).congr fun p => ?_
  change (1 / p.1.1) * Real.exp (-(1 + Real.exp (2 * p.1.2)) / (2 * p.1.1)) *
      ((Real.exp p.1.2 / p.1.1) / Real.sqrt (2 * Real.pi ^ 3 * ↑t) * Real.exp (Real.pi ^ 2 / (2 * ↑t)) *
        ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * ↑t)) * Real.exp (-(Real.exp p.1.2 / p.1.1) * Real.cosh u) *
          Real.sinh u * Real.sin (Real.pi * u / ↑t)) =
      (1 / p.1.1) * Real.exp (-(1 + Real.exp (2 * p.1.2)) / (2 * p.1.1)) *
        ((Real.exp p.1.2 / p.1.1) / Real.sqrt (2 * Real.pi ^ 3 * ↑t) * Real.exp (Real.pi ^ 2 / (2 * ↑t)) *
          ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * ↑t)) * Real.exp (-(Real.exp p.1.2 / p.1.1) * Real.cosh u) *
            Real.sinh u * Real.sin (Real.pi * u / ↑t))
  rfl

private lemma yorDensity_ite_measurable (t : ℝ≥0) (ht : 0 < t) :
    Measurable (fun p : ℝ × ℝ => if 0 < p.1 then yorDensity t p.1 p.2 else 0) := by
  classical
  have h1 : Measurable (Set.piecewise (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))
      (Function.uncurry (yorDensity t)) (fun _ => (0 : ℝ))) :=
    (yorDensity_continuousOn t ht).measurable_piecewise continuousOn_const
      (measurableSet_Ioi.prod MeasurableSet.univ)
  have h_eq : (fun p : ℝ × ℝ => if 0 < p.1 then yorDensity t p.1 p.2 else 0) =
      Set.piecewise (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) (Function.uncurry (yorDensity t)) (fun _ => (0 : ℝ)) := by
    funext p
    by_cases hp : 0 < p.1
    · simp [Set.piecewise, hp]; rfl
    · simp [Set.piecewise, hp]
  rw [h_eq]
  exact h1

private lemma yorDensity_joint_integrable_mul_compact (t : ℝ≥0) (ht : 0 < t)
    {φ : ℝ → ℝ} (hφ : Continuous φ) (hφ_bdd : ∃ C, ∀ u, |φ u| ≤ C)
    {f : ℝ → ℝ} (hf : Continuous f) (hfC : HasCompactSupport f) :
    IntegrableOn (fun p : ℝ × ℝ => φ (Real.exp (-p.1⁻¹)) * f p.2 * yorDensity t p.1 p.2)
      (Ioi (0 : ℝ) ×ˢ univ) := by
  obtain ⟨C, hC⟩ := hφ_bdd
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  obtain ⟨M, hM0, hM⟩ := yorDensity_abs_bound t ht
  let g_m : ℝ × ℝ → ℝ := fun p =>
    φ (Real.exp (-p.1⁻¹)) * f p.2 * (if 0 < p.1 then yorDensity t p.1 p.2 else 0)
  have hg_sm : StronglyMeasurable g_m := by
    have hm1 : Measurable (fun p : ℝ × ℝ => φ (Real.exp (-p.1⁻¹))) :=
      hφ.measurable.comp (Real.continuous_exp.measurable.comp measurable_fst.inv.neg)
    have hm2 : Measurable (fun p : ℝ × ℝ => f p.2) := hf.measurable.comp measurable_snd
    exact ((hm1.mul hm2).mul (yorDensity_ite_measurable t ht)).stronglyMeasurable
  have h_eq_on : EqOn g_m (fun p : ℝ × ℝ => φ (Real.exp (-p.1⁻¹)) * f p.2 * yorDensity t p.1 p.2)
      (Ioi (0 : ℝ) ×ˢ univ) := fun p hp => by
    simp only [g_m, mem_prod, mem_Ioi, mem_univ, and_true] at hp ⊢
    simp [hp]
  have hf_int : Integrable (fun y => C * M * |f y|) :=
    (hf.integrable_of_hasCompactSupport hfC).abs.const_mul (C * M)
  have hg_int : Integrable g_m ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    rw [integrable_prod_iff' hg_sm.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards with y
      obtain ⟨_, hy_int, _⟩ := hM y
      refine Integrable.mono' (hy_int.abs.const_mul (C * |f y|)) ?_ ?_
      · exact (hg_sm.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      · refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
        have hx0 : 0 < x := hx
        simp only [g_m, hx0, ↓reduceIte]
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        have hC' : |φ (Real.exp (-x⁻¹))| ≤ C := hC _
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC' (abs_nonneg _)) (abs_nonneg _)
    · refine hf_int.mono' (hg_sm.norm.integral_prod_left').aestronglyMeasurable ?_
      filter_upwards with y
      obtain ⟨_, hy_int, hy_M⟩ := hM y
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      have h1 : ∀ x ∈ Ioi (0 : ℝ), ‖g_m (x, y)‖ ≤ (C * |f y|) * |yorDensity t x y| := fun x hx => by
        have hx0 : 0 < x := hx
        simp only [g_m, hx0, ↓reduceIte]
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hC _) (abs_nonneg _)) (abs_nonneg _)
      have h_norm_int : IntegrableOn (fun x => ‖g_m (x, y)‖) (Ioi 0) :=
        (hy_int.abs.const_mul (C * |f y|)).mono'
          ((hg_sm.norm.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
          (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => by
            rw [Real.norm_eq_abs, abs_norm]
            exact h1 x hx)
      calc ∫ x in Ioi (0 : ℝ), ‖g_m (x, y)‖
          ≤ ∫ x in Ioi (0 : ℝ), (C * |f y|) * |yorDensity t x y| :=
            setIntegral_mono_on h_norm_int (hy_int.abs.const_mul _) measurableSet_Ioi h1
        _ = (C * |f y|) * ∫ x in Ioi (0 : ℝ), |yorDensity t x y| := integral_const_mul _ _
        _ ≤ (C * |f y|) * M := mul_le_mul_of_nonneg_left hy_M (by positivity)
        _ = C * M * |f y| := by ring
  have hg_on : IntegrableOn g_m (Ioi (0 : ℝ) ×ˢ univ) := by
    unfold IntegrableOn
    rwa [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  exact hg_on.congr_fun h_eq_on (measurableSet_Ioi.prod MeasurableSet.univ)

private lemma yorDensity_integrable_y_slice (t : ℝ≥0) (ht : 0 < t)
    {φ : ℝ → ℝ} (hφ : Continuous φ) (hφ_bdd : ∃ C, ∀ u, |φ u| ≤ C)
    {f : ℝ → ℝ} (hf : Continuous f) (hfC : HasCompactSupport f) :
    Integrable (fun y : ℝ => ∫ x in Ioi (0 : ℝ), φ (Real.exp (-x⁻¹)) * f y * yorDensity t x y) := by
  have hj := yorDensity_joint_integrable_mul_compact t ht hφ hφ_bdd hf hfC
  unfold IntegrableOn at hj
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ] at hj
  exact hj.integral_prod_right

/-- For every `φ ∈ C([0, 1], ℝ)` and `f ∈ C_c(ℝ)`, the `φ(e^{-1/x}) f(y)` integral
against `jointLaw P W 2 0 t` equals the integral against `yorDensity t` on `(0, ∞) × ℝ`. -/
lemma jointLaw_two_eq_yorDensity_test {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W)
    (t : ℝ≥0) (ht : 0 < t) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc 0 1))
    {f : ℝ → ℝ} (hf : Continuous f) (hfC : HasCompactSupport f) :
    ∫ ω, φ (Real.exp (-(expInt W 2 0 t ω)⁻¹)) * f (W t ω) ∂P =
      ∫ y : ℝ, ∫ x in Ioi (0 : ℝ), φ (Real.exp (-x⁻¹)) * f y * yorDensity t x y := by
  let φExt : ℝ → ℝ := fun u => φ (max 0 (min 1 u))
  have h_clamp : ∀ u : ℝ, max (0 : ℝ) (min 1 u) ∈ Icc (0 : ℝ) 1 := fun u =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hφExt_cont : Continuous φExt :=
    hφ.comp_continuous (continuous_const.max (continuous_const.min continuous_id)) h_clamp
  have hφExt_eq : ∀ u ∈ Icc (0 : ℝ) 1, φExt u = φ u := fun u hu => by
    simp [φExt, min_eq_right hu.2, max_eq_right hu.1]
  have h_in01 : ∀ x : ℝ, 0 < x → Real.exp (-x⁻¹) ∈ Icc (0 : ℝ) 1 := fun x hx =>
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr (inv_nonneg.mpr hx.le))⟩
  let B : ℝ≥0 → Ω → ℝ := hW.toIsPreBrownianReal.mk W
  have hBmeas : ∀ s, Measurable (B s) := hW.toIsPreBrownianReal.measurable_mk
  have hBcont : ∀ ω, Continuous (B · ω) := hW.toIsPreBrownianReal.continuous_mk
  have hBbm : IsBM P B := ⟨hW.toIsPreBrownianReal.isBrownianReal_mk.toIsPreBrownianReal,
    Eventually.of_forall hBcont⟩
  have hBW : ∀ᵐ ω ∂P, ∀ s, B s ω = W s ω := hW.mk_ae_forall_eq
  have hXpos := expInt_two_pos_ae B hBbm t ht
  have hXmeas : Measurable (expInt B 2 0 t) := measurable_expInt_bm hBmeas hBcont 2 t
  have hLHS_congr : ∫ ω, φ (Real.exp (-(expInt W 2 0 t ω)⁻¹)) * f (W t ω) ∂P =
      ∫ ω, φExt (Real.exp (-(expInt B 2 0 t ω)⁻¹)) * f (B t ω) ∂P := by
    refine integral_congr_ae ((hBW.and hXpos).mono fun ω ⟨hω, hx⟩ => ?_)
    dsimp only
    have hX : expInt W 2 0 t ω = expInt B 2 0 t ω := by
      simp only [expInt]; exact intervalIntegral.integral_congr fun s _ => by rw [hω s.toNNReal]
    rw [hX, ← hω t, hφExt_eq _ (h_in01 _ hx)]
  have hRHS_congr : ∫ y : ℝ, ∫ x in Ioi (0 : ℝ), φ (Real.exp (-x⁻¹)) * f y * yorDensity t x y =
      ∫ y : ℝ, ∫ x in Ioi (0 : ℝ), φExt (Real.exp (-x⁻¹)) * f y * yorDensity t x y := by
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [hφExt_eq _ (h_in01 x hx)]
  rw [hLHS_congr, hRHS_congr]
  obtain ⟨Cf, hCf0, hCf⟩ : ∃ Cf ≥ 0, ∀ y, |f y| ≤ Cf := by
    obtain ⟨R, hR⟩ := hfC.isCompact.isBounded.subset_closedBall (0 : ℝ)
    obtain ⟨K, hK⟩ := (isCompact_Icc (a := -max R 1 - 1) (b := max R 1 + 1)).exists_bound_of_continuousOn hf.continuousOn
    refine ⟨max K 0, le_max_right _ _, fun y => ?_⟩
    by_cases hy : |y| ≤ max R 1 + 1
    · exact (Real.norm_eq_abs (f y) ▸ hK y ⟨by linarith [neg_le_abs y], by linarith [le_abs_self y]⟩).trans
        (le_max_left _ _)
    · have hf0 : f y = 0 := by
        by_contra hne
        have := hR (subset_tsupport f hne)
        rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
        linarith [le_max_left R 1]
      rw [hf0, abs_zero]; exact le_max_right _ _
  have h_mono : ∀ n : ℕ,
      ∫ ω, (Real.exp (-(expInt B 2 0 t ω)⁻¹)) ^ n * f (B t ω) ∂P =
        ∫ y : ℝ, ∫ x in Ioi (0 : ℝ), (Real.exp (-x⁻¹)) ^ n * f y * yorDensity t x y := by
    intro n
    rcases n with _ | n
    · simp only [pow_zero, one_mul]
      have hlaw : HasLaw (B t) (gaussianReal 0 t) P := hBbm.hasLaw_eval t
      have hL : ∫ ω, f (B t ω) ∂P = ∫ y, f y * gaussianPDFReal 0 t y := by
        rw [← integral_map hlaw.aemeasurable hf.aestronglyMeasurable, hlaw.map_eq,
          integral_gaussianReal_eq_integral_smul ht.ne']
        refine integral_congr_ae (ae_of_all _ fun y => by simp only [smul_eq_mul, mul_comm])
      rw [hL]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      dsimp only
      rw [← yorDensity_integral_x_eq_gaussian t ht y, ← integral_const_mul]
    · have hv : (0 : ℝ) < (n + 1 : ℕ) := by positivity
      have h_powL : ∀ ω, (Real.exp (-(expInt B 2 0 t ω)⁻¹)) ^ (n + 1) * f (B t ω) =
          f (B t ω) * Real.exp (-((n + 1 : ℕ) : ℝ) / expInt B 2 0 t ω) := fun ω => by
        rw [← Real.exp_nat_mul, mul_comm (Real.exp _)]
        congr 1; congr 1; ring
      simp_rw [h_powL]
      rw [jointLaw_two_laplace_inv B hBbm t ht hv hf ⟨Cf, hCf⟩]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      dsimp only
      rw [← (yorDensity_laplace_x t ht hv y).2, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
      rw [← Real.exp_nat_mul]
      have hexp : -((n + 1 : ℕ) : ℝ) / x = (n + 1 : ℕ) * (-x⁻¹) := by ring
      rw [hexp]; ring
  have h_intL_mon : ∀ n : ℕ, Integrable (fun ω => (Real.exp (-(expInt B 2 0 t ω)⁻¹)) ^ n * f (B t ω)) P := by
    intro n
    refine (integrable_const Cf).mono' ?_ ?_
    · exact (((Real.continuous_exp.measurable.comp (hXmeas.inv.neg)).pow_const n).mul
        (hf.measurable.comp (hBmeas t))).aestronglyMeasurable
    · filter_upwards [hXpos] with ω hω
      have hexp : (Real.exp (-(expInt B 2 0 t ω)⁻¹)) ^ n ≤ 1 :=
        pow_le_one₀ (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (inv_nonneg.mpr hω.le)))
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (Real.exp_pos _).le _)]
      exact (mul_le_mul hexp (hCf _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have h_intR_mon : ∀ n : ℕ,
      Integrable (fun y => ∫ x in Ioi (0 : ℝ), (Real.exp (-x⁻¹)) ^ n * f y * yorDensity t x y) := by
    intro n
    have h1 := yorDensity_integrable_y_slice t ht (φ := fun u => (max (0 : ℝ) (min 1 u)) ^ n)
      ((continuous_const.max (continuous_const.min continuous_id)).pow n) ⟨1, fun u => by
        have hm : max (0 : ℝ) (min 1 u) ∈ Icc (0 : ℝ) 1 := h_clamp u
        rw [abs_of_nonneg (pow_nonneg hm.1 _)]
        exact pow_le_one₀ hm.1 hm.2⟩ hf hfC
    refine h1.congr (ae_of_all _ fun y => ?_)
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hm := h_in01 x hx
    rw [min_eq_right hm.2, max_eq_right hm.1]
  have h_poly : ∀ p : ℝ[X],
      ∫ ω, p.eval (Real.exp (-(expInt B 2 0 t ω)⁻¹)) * f (B t ω) ∂P =
        ∫ y : ℝ, ∫ x in Ioi (0 : ℝ), p.eval (Real.exp (-x⁻¹)) * f y * yorDensity t x y := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        have hLp : Integrable (fun ω => p.eval (Real.exp (-(expInt B 2 0 t ω)⁻¹)) * f (B t ω)) P := by
          obtain ⟨Cp, hCp⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
            p.continuous.continuousOn
          refine (integrable_const (max Cp 0 * Cf)).mono' ?_ ?_
          · exact (((p.continuous.measurable.comp (Real.continuous_exp.measurable.comp hXmeas.inv.neg))).mul
              (hf.measurable.comp (hBmeas t))).aestronglyMeasurable
          · refine hXpos.mono fun ω hω => ?_
            have hm := h_in01 _ hω
            rw [Real.norm_eq_abs, abs_mul]
            exact mul_le_mul ((Real.norm_eq_abs _ ▸ hCp _ hm).trans (le_max_left _ _)) (hCf _)
              (abs_nonneg _) (le_max_right _ _)
        have hLq : Integrable (fun ω => q.eval (Real.exp (-(expInt B 2 0 t ω)⁻¹)) * f (B t ω)) P := by
          obtain ⟨Cq, hCq⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
            q.continuous.continuousOn
          refine (integrable_const (max Cq 0 * Cf)).mono' ?_ ?_
          · exact (((q.continuous.measurable.comp (Real.continuous_exp.measurable.comp hXmeas.inv.neg))).mul
              (hf.measurable.comp (hBmeas t))).aestronglyMeasurable
          · refine hXpos.mono fun ω hω => ?_
            have hm := h_in01 _ hω
            rw [Real.norm_eq_abs, abs_mul]
            exact mul_le_mul ((Real.norm_eq_abs _ ▸ hCq _ hm).trans (le_max_left _ _)) (hCf _)
              (abs_nonneg _) (le_max_right _ _)
        have hRp : Integrable (fun y => ∫ x in Ioi (0 : ℝ), p.eval (Real.exp (-x⁻¹)) * f y * yorDensity t x y) := by
          obtain ⟨Cp, hCp⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
            p.continuous.continuousOn
          have h1 := yorDensity_integrable_y_slice t ht
            (φ := fun u => p.eval (max (0 : ℝ) (min 1 u)))
            (p.continuous.comp (continuous_const.max (continuous_const.min continuous_id)))
            ⟨max Cp 0, fun u => (Real.norm_eq_abs _ ▸ hCp _ (h_clamp u)).trans (le_max_left _ _)⟩ hf hfC
          refine h1.congr (ae_of_all _ fun y => setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_)
          have hm := h_in01 x hx
          rw [min_eq_right hm.2, max_eq_right hm.1]
        have hRq : Integrable (fun y => ∫ x in Ioi (0 : ℝ), q.eval (Real.exp (-x⁻¹)) * f y * yorDensity t x y) := by
          obtain ⟨Cq, hCq⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
            q.continuous.continuousOn
          have h1 := yorDensity_integrable_y_slice t ht
            (φ := fun u => q.eval (max (0 : ℝ) (min 1 u)))
            (q.continuous.comp (continuous_const.max (continuous_const.min continuous_id)))
            ⟨max Cq 0, fun u => (Real.norm_eq_abs _ ▸ hCq _ (h_clamp u)).trans (le_max_left _ _)⟩ hf hfC
          refine h1.congr (ae_of_all _ fun y => setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_)
          have hm := h_in01 x hx
          rw [min_eq_right hm.2, max_eq_right hm.1]
        have hL_add : (fun ω => (p + q).eval (Real.exp (-(expInt B 2 0 t ω)⁻¹)) * f (B t ω)) =
            fun ω => p.eval (Real.exp (-(expInt B 2 0 t ω)⁻¹)) * f (B t ω) +
              q.eval (Real.exp (-(expInt B 2 0 t ω)⁻¹)) * f (B t ω) := by
          funext ω; simp [Polynomial.eval_add, add_mul]
        have hR_add : (fun y => ∫ x in Ioi (0 : ℝ), (p + q).eval (Real.exp (-x⁻¹)) * f y * yorDensity t x y) =
            fun y => (∫ x in Ioi (0 : ℝ), p.eval (Real.exp (-x⁻¹)) * f y * yorDensity t x y) +
              (∫ x in Ioi (0 : ℝ), q.eval (Real.exp (-x⁻¹)) * f y * yorDensity t x y) := by
          funext y
          obtain ⟨M, _, hM⟩ := yorDensity_abs_bound t ht
          obtain ⟨_, hy_int, _⟩ := hM y
          have hpx : IntegrableOn (fun x => p.eval (Real.exp (-x⁻¹)) * f y * yorDensity t x y) (Ioi 0) := by
            obtain ⟨Cp, hCp⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
              p.continuous.continuousOn
            refine (hy_int.abs.const_mul (max Cp 0 * |f y|)).mono' ?_ ?_
            · have hc : ContinuousOn (fun x => p.eval (Real.exp (-x⁻¹)) * f y) (Ioi 0) := fun x hx =>
                ((p.continuous.continuousAt.comp (Real.continuous_exp.continuousAt.comp
                  ((continuousAt_id.inv₀ hx.ne').neg))).mul continuousAt_const).continuousWithinAt
              exact (hc.aestronglyMeasurable measurableSet_Ioi).mul hy_int.aestronglyMeasurable
            · refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
              rw [Real.norm_eq_abs, abs_mul, abs_mul]
              have hle : |p.eval (Real.exp (-x⁻¹))| ≤ max Cp 0 :=
                (Real.norm_eq_abs _ ▸ hCp _ (h_in01 x hx)).trans (le_max_left _ _)
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle (abs_nonneg _)) (abs_nonneg _)
          have hqx : IntegrableOn (fun x => q.eval (Real.exp (-x⁻¹)) * f y * yorDensity t x y) (Ioi 0) := by
            obtain ⟨Cq, hCq⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
              q.continuous.continuousOn
            refine (hy_int.abs.const_mul (max Cq 0 * |f y|)).mono' ?_ ?_
            · have hc : ContinuousOn (fun x => q.eval (Real.exp (-x⁻¹)) * f y) (Ioi 0) := fun x hx =>
                ((q.continuous.continuousAt.comp (Real.continuous_exp.continuousAt.comp
                  ((continuousAt_id.inv₀ hx.ne').neg))).mul continuousAt_const).continuousWithinAt
              exact (hc.aestronglyMeasurable measurableSet_Ioi).mul hy_int.aestronglyMeasurable
            · refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
              rw [Real.norm_eq_abs, abs_mul, abs_mul]
              have hle : |q.eval (Real.exp (-x⁻¹))| ≤ max Cq 0 :=
                (Real.norm_eq_abs _ ▸ hCq _ (h_in01 x hx)).trans (le_max_left _ _)
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle (abs_nonneg _)) (abs_nonneg _)
          simp_rw [Polynomial.eval_add, add_mul]
          exact integral_add hpx hqx
        rw [hL_add, hR_add, integral_add hLp hLq, integral_add hRp hRq, hp, hq]
    | monomial n a =>
        have hL_eq : (fun ω => (Polynomial.monomial n a).eval (Real.exp (-(expInt B 2 0 t ω)⁻¹)) * f (B t ω)) =
            fun ω => a * ((Real.exp (-(expInt B 2 0 t ω)⁻¹)) ^ n * f (B t ω)) := by
          funext ω; simp [Polynomial.eval_monomial]; ring
        have hR_eq : (fun y => ∫ x in Ioi (0 : ℝ), (Polynomial.monomial n a).eval (Real.exp (-x⁻¹)) * f y * yorDensity t x y) =
            fun y => a * ∫ x in Ioi (0 : ℝ), (Real.exp (-x⁻¹)) ^ n * f y * yorDensity t x y := by
          funext y
          rw [← integral_const_mul]
          refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
          simp [Polynomial.eval_monomial]; ring
        rw [hL_eq, hR_eq, integral_const_mul, integral_const_mul, h_mono n]
  have h_approx : ∀ k : ℕ, ∃ p : ℝ[X], ∀ u ∈ Icc (0 : ℝ) 1, |p.eval u - φ u| < 1 / ((k : ℝ) + 1) :=
    fun k => exists_polynomial_near_of_continuousOn 0 1 φ hφ (1 / ((k : ℝ) + 1)) (by positivity)
  choose p hp using h_approx
  obtain ⟨Cφ, hCφ0, hCφ⟩ : ∃ Cφ ≥ 0, ∀ u ∈ Icc (0 : ℝ) 1, |φ u| ≤ Cφ := by
    obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hφ
    exact ⟨max K 0, le_max_right _ _, fun u hu => (Real.norm_eq_abs (φ u) ▸ hK u hu).trans (le_max_left _ _)⟩
  have hp_bdd : ∀ k u, u ∈ Icc (0 : ℝ) 1 → |(p k).eval u| ≤ Cφ + 1 := fun k u hu => by
    have h1 := hp k u hu
    have h2 : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
    have htri := abs_sub_abs_le_abs_sub ((p k).eval u) (φ u)
    linarith [hCφ u hu]
  have hL_tendsto : Tendsto (fun k : ℕ => ∫ ω, (p k).eval (Real.exp (-(expInt B 2 0 t ω)⁻¹)) * f (B t ω) ∂P)
      atTop (nhds (∫ ω, φExt (Real.exp (-(expInt B 2 0 t ω)⁻¹)) * f (B t ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (Cφ + 1) * Cf) ?_ (integrable_const _) ?_ ?_
    · intro k
      exact (((p k).continuous.measurable.comp (Real.continuous_exp.measurable.comp hXmeas.inv.neg)).mul
        (hf.measurable.comp (hBmeas t))).aestronglyMeasurable
    · intro k
      filter_upwards [hXpos] with ω hω
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hp_bdd k _ (h_in01 _ hω)) (hCf _) (abs_nonneg _) (by positivity)
    · filter_upwards [hXpos] with ω hω
      have hm := h_in01 _ hω
      rw [hφExt_eq _ hm]
      have hlim : Tendsto (fun k => (p k).eval (Real.exp (-(expInt B 2 0 t ω)⁻¹))) atTop
          (nhds (φ (Real.exp (-(expInt B 2 0 t ω)⁻¹)))) := by
        rw [Metric.tendsto_atTop]
        intro ε hε
        obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
        refine ⟨N, fun k hk => ?_⟩
        rw [Real.dist_eq]
        have hk' : (1 : ℝ) / ((k : ℝ) + 1) < ε :=
          lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)) hN
        exact lt_trans (hp k _ hm) hk'
      exact hlim.mul_const _
  obtain ⟨M, hM0, hM⟩ := yorDensity_abs_bound t ht
  have hR_tendsto : Tendsto (fun k : ℕ => ∫ y : ℝ, ∫ x in Ioi (0 : ℝ),
        (p k).eval (Real.exp (-x⁻¹)) * f y * yorDensity t x y)
      atTop (nhds (∫ y : ℝ, ∫ x in Ioi (0 : ℝ), φExt (Real.exp (-x⁻¹)) * f y * yorDensity t x y)) := by
    have hdom_int : Integrable (fun y : ℝ => (Cφ + 1) * M * |f y|) :=
      (hf.integrable_of_hasCompactSupport hfC).abs.const_mul _
    refine tendsto_integral_of_dominated_convergence (fun y => (Cφ + 1) * M * |f y|) ?_ hdom_int ?_ ?_
    · intro k
      have h1 := yorDensity_integrable_y_slice t ht
        (φ := fun u => (p k).eval (max (0 : ℝ) (min 1 u)))
        ((p k).continuous.comp (continuous_const.max (continuous_const.min continuous_id)))
        ⟨Cφ + 1, fun u => hp_bdd k _ (h_clamp u)⟩ hf hfC
      exact (h1.congr (ae_of_all _ fun y => setIntegral_congr_fun measurableSet_Ioi fun x hx => by
        have hm := h_in01 x hx
        rw [min_eq_right hm.2, max_eq_right hm.1])).aestronglyMeasurable
    · intro k
      filter_upwards with y
      obtain ⟨_, hy_int, hy_M⟩ := hM y
      rw [Real.norm_eq_abs]
      have h1 : ∀ x ∈ Ioi (0 : ℝ), ‖(p k).eval (Real.exp (-x⁻¹)) * f y * yorDensity t x y‖ ≤
          ((Cφ + 1) * |f y|) * |yorDensity t x y| := fun x hx => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hp_bdd k _ (h_in01 x hx))
          (abs_nonneg _)) (abs_nonneg _)
      have h_norm_int : IntegrableOn (fun x => ‖(p k).eval (Real.exp (-x⁻¹)) * f y * yorDensity t x y‖)
          (Ioi 0) := by
        refine (hy_int.abs.const_mul ((Cφ + 1) * |f y|)).mono' ?_ ?_
        · have hc : ContinuousOn (fun x => (p k).eval (Real.exp (-x⁻¹)) * f y) (Ioi 0) := fun x hx =>
            (((p k).continuous.continuousAt.comp (Real.continuous_exp.continuousAt.comp
              ((continuousAt_id.inv₀ hx.ne').neg))).mul continuousAt_const).continuousWithinAt
          exact ((hc.aestronglyMeasurable measurableSet_Ioi).mul hy_int.aestronglyMeasurable).norm
        · refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
          rw [Real.norm_eq_abs, abs_norm]; exact h1 x hx
      calc |∫ x in Ioi (0 : ℝ), (p k).eval (Real.exp (-x⁻¹)) * f y * yorDensity t x y|
          ≤ ∫ x in Ioi (0 : ℝ), ‖(p k).eval (Real.exp (-x⁻¹)) * f y * yorDensity t x y‖ := by
            rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
        _ ≤ ∫ x in Ioi (0 : ℝ), ((Cφ + 1) * |f y|) * |yorDensity t x y| :=
            setIntegral_mono_on h_norm_int (hy_int.abs.const_mul _) measurableSet_Ioi h1
        _ = ((Cφ + 1) * |f y|) * ∫ x in Ioi (0 : ℝ), |yorDensity t x y| := integral_const_mul _ _
        _ ≤ ((Cφ + 1) * |f y|) * M := mul_le_mul_of_nonneg_left hy_M (by positivity)
        _ = (Cφ + 1) * M * |f y| := by ring
    · filter_upwards with y
      obtain ⟨_, hy_int, _⟩ := hM y
      refine tendsto_integral_of_dominated_convergence (fun x => (Cφ + 1) * |f y| * |yorDensity t x y|)
        ?_ (hy_int.abs.const_mul _) ?_ ?_
      · intro k
        have hc : ContinuousOn (fun x => (p k).eval (Real.exp (-x⁻¹)) * f y) (Ioi 0) := fun x hx =>
          (((p k).continuous.continuousAt.comp (Real.continuous_exp.continuousAt.comp
            ((continuousAt_id.inv₀ hx.ne').neg))).mul continuousAt_const).continuousWithinAt
        exact (hc.aestronglyMeasurable measurableSet_Ioi).mul hy_int.aestronglyMeasurable
      · intro k
        refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hp_bdd k _ (h_in01 x hx))
          (abs_nonneg _)) (abs_nonneg _)
      · refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
        have hm := h_in01 x hx
        rw [hφExt_eq _ hm]
        have hlim : Tendsto (fun k => (p k).eval (Real.exp (-x⁻¹))) atTop (nhds (φ (Real.exp (-x⁻¹)))) := by
          rw [Metric.tendsto_atTop]
          intro ε hε
          obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
          refine ⟨N, fun k hk => ?_⟩
          rw [Real.dist_eq]
          have hk' : (1 : ℝ) / ((k : ℝ) + 1) < ε :=
            lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)) hN
          exact lt_trans (hp k _ hm) hk'
        exact (hlim.mul_const (f y)).mul_const (yorDensity t x y)
  have h_eq : (fun k : ℕ => ∫ ω, (p k).eval (Real.exp (-(expInt B 2 0 t ω)⁻¹)) * f (B t ω) ∂P) =
      fun k : ℕ => ∫ y : ℝ, ∫ x in Ioi (0 : ℝ), (p k).eval (Real.exp (-x⁻¹)) * f y * yorDensity t x y :=
    funext fun k => h_poly (p k)
  rw [h_eq] at hL_tendsto
  exact tendsto_nhds_unique hL_tendsto hR_tendsto

/-- `yorDensity t x y ≥ 0` for all `x > 0` and `y ∈ ℝ`, deduced from a Brownian motion `(W, P)`. -/
lemma yorDensity_nonneg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (t : ℝ≥0) (ht : 0 < t) {x : ℝ} (hx : 0 < x) (y : ℝ) :
    0 ≤ yorDensity t x y := by
  by_contra hlt
  push Not at hlt
  have hcont := yorDensity_continuousOn t ht (x, y) (by exact ⟨hx, trivial⟩)
  let ε : ℝ := -yorDensity t x y / 2
  have hε0 : 0 < ε := by dsimp [ε]; linarith
  have hlt' : yorDensity t x y < -ε := by dsimp [ε]; linarith
  have hneg_mem : {p : ℝ × ℝ | yorDensity t p.1 p.2 < -ε} ∈ 𝓝[(Ioi (0 : ℝ) ×ˢ univ)] (x, y) :=
    hcont.preimage_mem_nhdsWithin (isOpen_Iio.mem_nhds hlt')
  have hU_open : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  rw [hU_open.nhdsWithin_eq (by exact ⟨hx, trivial⟩ : (x, y) ∈ Ioi (0 : ℝ) ×ˢ univ),
    Metric.mem_nhds_iff] at hneg_mem
  obtain ⟨r, hr0, hr⟩ := hneg_mem
  let δ : ℝ := min (r / 4) (x / 2)
  have hδ0 : 0 < δ := by positivity
  have h_box : ∀ p : ℝ × ℝ, p.1 ∈ Icc (x - δ) (x + δ) → p.2 ∈ Icc (y - δ) (y + δ) →
      yorDensity t p.1 p.2 ≤ -ε := by
    intro p hp1 hp2
    have hdist : dist p (x, y) < r := by
      rw [Prod.dist_eq, max_lt_iff]
      constructor <;> rw [Real.dist_eq, abs_lt]
      · constructor <;> linarith [hp1.1, hp1.2, min_le_left (r / 4) (x / 2)]
      · constructor <;> linarith [hp2.1, hp2.2, min_le_left (r / 4) (x / 2)]
    exact (hr hdist).le
  have hx_sub_pos : 0 < x - δ := by linarith [min_le_right (r / 4) (x / 2)]
  let T : ℝ → ℝ := fun z => Real.exp (-z⁻¹)
  have hT_mono : StrictMonoOn T (Ioi 0) := by
    intro a ha b _ hab
    exact Real.exp_lt_exp.mpr (neg_lt_neg (inv_strictAnti₀ ha hab))
  let φ : ℝ → ℝ := smoothBump (T (x - δ)) (T (x - δ / 2)) (T (x + δ / 2)) (T (x + δ))
  let f : ℝ → ℝ := smoothBump (y - δ) (y - δ / 2) (y + δ / 2) (y + δ)
  have hφ_cont : ContinuousOn φ (Icc 0 1) := (smoothBump.contDiff _ _ _ _ (n := 0)).continuous.continuousOn
  have hf_cont : Continuous f := (smoothBump.contDiff _ _ _ _ (n := 0)).continuous
  have hf_cs : HasCompactSupport f := smoothBump.hasCompactSupport (by linarith) (by linarith)
  have h_test := jointLaw_two_eq_yorDensity_test W hW t ht hφ_cont hf_cont hf_cs
  have hL_nn : 0 ≤ ∫ ω, φ (Real.exp (-(expInt W 2 0 t ω)⁻¹)) * f (W t ω) ∂P :=
    integral_nonneg fun ω => mul_nonneg (smoothBump.mem_Icc _ _ _ _ _).1
      (smoothBump.mem_Icc _ _ _ _ _).1
  have h_box_nonpos : ∀ y' : ℝ, ∀ x' ∈ Ioi (0 : ℝ),
      φ (T x') * f y' * yorDensity t x' y' ≤ 0 := by
    intro y' x' hx'
    by_cases hx1 : x' ∈ Icc (x - δ) (x + δ)
    · by_cases hy1 : y' ∈ Icc (y - δ) (y + δ)
      · have hneg := h_box (x', y') hx1 hy1
        have hφ_nn := (smoothBump.mem_Icc (T (x - δ)) (T (x - δ / 2)) (T (x + δ / 2)) (T (x + δ)) (T x')).1
        have hf_nn := (smoothBump.mem_Icc (y - δ) (y - δ / 2) (y + δ / 2) (y + δ) y').1
        exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hφ_nn hf_nn) (by linarith)
      · have hy_out : y' ≤ y - δ ∨ y + δ ≤ y' := by
          simp only [mem_Icc, not_and_or, not_le] at hy1
          exact hy1.imp le_of_lt le_of_lt
        dsimp only [f]
        rw [smoothBump.zero_of_not_mem (by linarith) (by linarith) hy_out, mul_zero, zero_mul]
    · have hx_out : T x' ≤ T (x - δ) ∨ T (x + δ) ≤ T x' := by
        simp only [mem_Icc, not_and_or, not_le] at hx1
        rcases hx1 with h | h
        · left; exact (hT_mono (mem_Ioi.mpr hx') (mem_Ioi.mpr hx_sub_pos) h).le
        · right; exact (hT_mono (mem_Ioi.mpr (by positivity)) (mem_Ioi.mpr hx') h).le
      have hφ0 : φ (T x') = 0 := smoothBump.zero_of_not_mem
        (hT_mono (mem_Ioi.mpr hx_sub_pos) (mem_Ioi.mpr (by linarith)) (by linarith))
        (hT_mono (mem_Ioi.mpr (by linarith)) (mem_Ioi.mpr (by linarith)) (by linarith))
        hx_out
      rw [hφ0, zero_mul, zero_mul]
  let g_y : ℝ → ℝ := fun y' => ∫ x' in Ioi (0 : ℝ), φ (T x') * f y' * yorDensity t x' y'
  have hg_nonpos : ∀ y' : ℝ, g_y y' ≤ 0 := fun y' =>
    setIntegral_nonpos measurableSet_Ioi fun x' hx' => h_box_nonpos y' x' hx'
  have hg_slice : ∀ y' ∈ Icc (y - δ / 2) (y + δ / 2), g_y y' ≤ -ε * δ := by
    intro y' hy'
    have hfy1 : f y' = 1 := smoothBump.one_of_mem (by linarith) (by linarith) hy'.1 hy'.2
    let indX : ℝ → ℝ := (Icc (x - δ / 2) (x + δ / 2)).indicator (fun _ => -ε)
    have h_ind_int : IntegrableOn indX (Ioi 0) :=
      ((integrableOn_const (C := -ε) (hs := isCompact_Icc.measure_lt_top.ne)).integrable_indicator
        measurableSet_Icc).integrableOn
    have h_le_ind : ∀ x' ∈ Ioi (0 : ℝ), φ (T x') * f y' * yorDensity t x' y' ≤ indX x' := by
      intro x' hx'
      by_cases hx2 : x' ∈ Icc (x - δ / 2) (x + δ / 2)
      · have hφ1 : φ (T x') = 1 := smoothBump.one_of_mem
          (hT_mono (mem_Ioi.mpr hx_sub_pos) (mem_Ioi.mpr (by linarith)) (by linarith))
          (hT_mono (mem_Ioi.mpr (by linarith)) (mem_Ioi.mpr (by linarith)) (by linarith))
          (hT_mono.monotoneOn (mem_Ioi.mpr (by linarith)) (mem_Ioi.mpr hx') hx2.1)
          (hT_mono.monotoneOn (mem_Ioi.mpr hx') (mem_Ioi.mpr (by linarith)) hx2.2)
        have hbox := h_box (x', y') ⟨by linarith [hx2.1], by linarith [hx2.2]⟩
          ⟨by linarith [hy'.1], by linarith [hy'.2]⟩
        simp only [indX, indicator_of_mem hx2, hφ1, hfy1, one_mul]
        exact hbox
      · simp only [indX, indicator_of_notMem hx2]
        exact h_box_nonpos y' x' hx'
    obtain ⟨M, _, hM⟩ := yorDensity_abs_bound t ht
    obtain ⟨_, hy'_int, _⟩ := hM y'
    have h_lhs_int : IntegrableOn (fun x' => φ (T x') * f y' * yorDensity t x' y') (Ioi 0) := by
      refine (hy'_int.abs.const_mul 1).mono' ?_ ?_
      · have hc : ContinuousOn (fun x' => φ (T x') * f y') (Ioi 0) := fun x' hx' =>
          (((smoothBump.contDiff _ _ _ _ (n := 0)).continuous.continuousAt.comp
            (Real.continuous_exp.continuousAt.comp ((continuousAt_id.inv₀ hx'.ne').neg))).mul
            continuousAt_const).continuousWithinAt
        exact (hc.aestronglyMeasurable measurableSet_Ioi).mul hy'_int.aestronglyMeasurable
      · refine ae_restrict_of_forall_mem measurableSet_Ioi fun x' _ => ?_
        have hφm := smoothBump.mem_Icc (T (x - δ)) (T (x - δ / 2)) (T (x + δ / 2)) (T (x + δ)) (T x')
        have hfm := smoothBump.mem_Icc (y - δ) (y - δ / 2) (y + δ / 2) (y + δ) y'
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hφm.1, abs_of_nonneg hfm.1, one_mul]
        exact mul_le_of_le_one_left (abs_nonneg _)
          ((mul_le_of_le_one_right hφm.1 hfm.2).trans hφm.2)
    have h_ind_val : ∫ x' in Ioi (0 : ℝ), indX x' = -ε * δ := by
      have hsub : Icc (x - δ / 2) (x + δ / 2) ⊆ Ioi 0 := fun z hz => by
        change 0 < z
        have hz1 : x - δ / 2 ≤ z := hz.1
        linarith [hz1, hx_sub_pos, hδ0]
      rw [setIntegral_indicator measurableSet_Icc, inter_eq_right.mpr hsub,
        setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith)]
      ring
    calc g_y y' ≤ ∫ x' in Ioi (0 : ℝ), indX x' :=
          setIntegral_mono_on h_lhs_int h_ind_int measurableSet_Ioi h_le_ind
      _ = -ε * δ := h_ind_val
  let indY : ℝ → ℝ := (Icc (y - δ / 2) (y + δ / 2)).indicator (fun _ => -ε * δ)
  have hg_int : Integrable g_y := yorDensity_integrable_y_slice t ht
    ((smoothBump.contDiff _ _ _ _ (n := 0)).continuous)
    ⟨1, fun u => by
      have hm := smoothBump.mem_Icc (T (x - δ)) (T (x - δ / 2)) (T (x + δ / 2)) (T (x + δ)) u
      rw [abs_of_nonneg hm.1]; exact hm.2⟩ hf_cont hf_cs
  have h_indY_int : Integrable indY :=
    (integrableOn_const (C := -ε * δ) (hs := isCompact_Icc.measure_lt_top.ne)).integrable_indicator
      measurableSet_Icc
  have h_le_indY : ∀ y' : ℝ, g_y y' ≤ indY y' := fun y' => by
    by_cases hy' : y' ∈ Icc (y - δ / 2) (y + δ / 2)
    · simp only [indY, indicator_of_mem hy']; exact hg_slice y' hy'
    · simp only [indY, indicator_of_notMem hy']; exact hg_nonpos y'
  have h_indY_val : ∫ y' : ℝ, indY y' = -ε * δ ^ 2 := by
    rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, Measure.real,
      Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hR_neg : ∫ y' : ℝ, g_y y' < 0 := by
    calc ∫ y' : ℝ, g_y y' ≤ ∫ y' : ℝ, indY y' := integral_mono hg_int h_indY_int h_le_indY
      _ = -ε * δ ^ 2 := h_indY_val
      _ < 0 := by nlinarith [sq_pos_of_pos hδ0]
  dsimp only [g_y] at hR_neg
  linarith [h_test, hL_nn, hR_neg]

/-- `yorDensity t x y = 0` for all `x ≤ 0`. -/
lemma yorDensity_zero_of_nonpos {t : ℝ} (ht : 0 < t) {x : ℝ} (hx : x ≤ 0) (y : ℝ) :
    yorDensity t x y = 0 := by
  rcases eq_or_lt_of_le hx with rfl | hx_neg
  · simp [yorDensity]
  · have hr_neg : Real.exp y / x < 0 := div_neg_of_pos_of_neg (Real.exp_pos y) hx_neg
    set r := Real.exp y / x
    let a : ℝ := -r
    have ha : 0 < a := neg_pos.mpr hr_neg
    let F : ℝ → ℝ := fun u =>
      Real.exp (-u ^ 2 / (2 * t)) * Real.exp (-r * Real.cosh u) * Real.sinh u * Real.sin (Real.pi * u / t)
    have h_not_int : ¬ IntegrableOn F (Ioi 0) := by
      intro hF
      have h_norm : IntegrableOn (fun u => ‖F u‖) (Ioi 0) := hF.norm
      let U : ℝ := max (12 / (a * t) + 1) (2 * t + 4)
      have hU : ∀ u ≥ U,
          2 ≤ Real.exp (-u ^ 2 / (2 * t) + a * (Real.exp u / 2)) * ((Real.exp u - 1) / 2) := by
        intro u hu
        have hu4 : 4 ≤ u := le_trans (by linarith [le_max_right (12 / (a * t) + 1) (2 * t + 4)]) hu
        have hu0 : 0 ≤ u := by linarith
        have hu_at : 12 / (a * t) + 1 ≤ u :=
          le_trans (le_max_left (12 / (a * t) + 1) (2 * t + 4)) hu
        have hexp_ge : 1 + u + u ^ 2 / 2 + u ^ 3 / 6 ≤ Real.exp u := by
          have h3 := Real.sum_le_exp_of_nonneg hu0 4
          simpa [Finset.sum_range_succ, Nat.factorial, pow_succ] using h3
        have h_u3 : u ^ 3 / 6 ≤ Real.exp u := by nlinarith
        have h_exp_lin : 1 ≤ (Real.exp u - 1) / 2 := by nlinarith [sq_nonneg u]
        have h_au : 1 / t ≤ a * u / 12 := by
          have : 12 ≤ a * t * u := by
            have := (div_le_iff₀ (mul_pos ha ht)).mp (by linarith : 12 / (a * t) ≤ u)
            linarith
          rw [div_le_div_iff₀ ht (by norm_num)]
          linarith
        have h_arg_ge : u ^ 2 / (2 * t) ≤ -u ^ 2 / (2 * t) + a * (Real.exp u / 2) := by
          have h1 : a * u ^ 3 / 12 ≤ a * (Real.exp u / 2) := by nlinarith [ha, h_u3]
          have h2 : u ^ 2 / t ≤ a * u ^ 3 / 12 := by
            have h := mul_le_mul_of_nonneg_left h_au (sq_nonneg u)
            linarith [show u ^ 2 * (1 / t) = u ^ 2 / t by ring, show u ^ 2 * (a * u / 12) = a * u ^ 3 / 12 by ring]
          have h_half : u ^ 2 / (2 * t) + u ^ 2 / (2 * t) = u ^ 2 / t := by field_simp [ht.ne']; ring
          calc u ^ 2 / (2 * t)
              = u ^ 2 / t - u ^ 2 / (2 * t) := by rw [← h_half]; ring
            _ ≤ a * u ^ 3 / 12 - u ^ 2 / (2 * t) := sub_le_sub_right h2 _
            _ ≤ a * (Real.exp u / 2) - u ^ 2 / (2 * t) := sub_le_sub_right h1 _
            _ = -u ^ 2 / (2 * t) + a * (Real.exp u / 2) := by ring
        have h_arg_1 : 1 ≤ -u ^ 2 / (2 * t) + a * (Real.exp u / 2) := by
          have h2t : 2 * t ≤ u := le_trans (by linarith [le_max_right (12 / (a * t) + 1) (2 * t + 4)]) hu
          have h_sq : 1 ≤ u ^ 2 / (2 * t) := by
            rw [one_le_div (by positivity)]
            nlinarith
          exact le_trans h_sq h_arg_ge
        have h_exp_2 : 2 ≤ Real.exp (-u ^ 2 / (2 * t) + a * (Real.exp u / 2)) :=
          le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_le_exp.mpr h_arg_1)
        exact le_trans (by norm_num) (mul_le_mul h_exp_2 h_exp_lin zero_le_one (by positivity))
      have h_sin_ge : ∀ u : ℝ, ∀ k : ℕ,
          k * t + t / 4 ≤ u → u ≤ k * t + 3 * t / 4 → (1 / 2 : ℝ) ≤ |Real.sin (Real.pi * u / t)| := by
        intro u k hu1 hu2
        have harg : Real.pi * u / t = Real.pi * (u - k * t) / t + (k : ℝ) * Real.pi := by
          field_simp [ht.ne']; ring
        rw [harg, Real.sin_add_nat_mul_pi, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        have hlo : Real.pi / 4 ≤ Real.pi * (u - k * t) / t := by
          rw [le_div_iff₀ ht]; nlinarith [Real.pi_pos]
        have hhi : Real.pi * (u - k * t) / t ≤ 3 * Real.pi / 4 := by
          rw [div_le_iff₀ ht]; nlinarith [Real.pi_pos]
        have hpos : 0 ≤ Real.sin (Real.pi * (u - k * t) / t) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
        rw [abs_of_nonneg hpos]
        have h_val : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
        have h_lower : (1 / 2 : ℝ) ≤ Real.sqrt 2 / 2 := by
          have : (1 : ℝ) ≤ Real.sqrt 2 := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num)
          linarith
        rcases le_total (Real.pi * (u - k * t) / t) (Real.pi / 2) with h | h
        · have hm := Real.sin_le_sin_of_le_of_le_pi_div_two
            (by linarith [Real.pi_pos]) h hlo
          linarith [h_val, h_lower, hm]
        · have h' : Real.sin (Real.pi - Real.pi * (u - k * t) / t) = Real.sin (Real.pi * (u - k * t) / t) :=
            Real.sin_pi_sub _
          rw [← h']
          have hm := Real.sin_le_sin_of_le_of_le_pi_div_two
            (x := Real.pi / 4) (y := Real.pi - Real.pi * (u - k * t) / t)
            (by linarith [Real.pi_pos]) (by linarith) (by linarith)
          linarith [h_val, h_lower, hm]
      obtain ⟨K, hK⟩ := exists_nat_gt (max U 0 / t + 1)
      have h_piece : ∀ k : ℕ, K ≤ k →
          t / 2 ≤ ∫ u in Icc ((k : ℝ) * t + t / 4) ((k : ℝ) * t + 3 * t / 4), ‖F u‖ := by
        intro k hk
        have hkU : max U 0 ≤ (k : ℝ) * t := by
          have : max U 0 / t + 1 < k := lt_of_lt_of_le hK (by exact_mod_cast hk)
          have h1 : max U 0 / t < k := by linarith
          exact (div_lt_iff₀ ht).mp h1 |>.le
        have h_pt : ∀ u ∈ Icc ((k : ℝ) * t + t / 4) ((k : ℝ) * t + 3 * t / 4), 1 ≤ ‖F u‖ := by
          intro u hu
          have huU : U ≤ u := le_trans (le_max_left _ _) (le_trans hkU (by linarith [hu.1]))
          have hu0 : 0 ≤ u := le_trans (le_max_right _ _) (le_trans hkU (by linarith [hu.1]))
          have h1 : Real.exp u / 2 ≤ Real.cosh u := by rw [Real.cosh_eq]; linarith [Real.exp_pos (-u)]
          have h2 : (Real.exp u - 1) / 2 ≤ Real.sinh u := by
            rw [Real.sinh_eq]
            have : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu0)
            linarith
          have h3 : 2 ≤ Real.exp (-u ^ 2 / (2 * t) + a * (Real.exp u / 2)) * ((Real.exp u - 1) / 2) :=
            hU u huU
          have h4 : Real.exp (-u ^ 2 / (2 * t) + a * (Real.exp u / 2)) ≤
              Real.exp (-u ^ 2 / (2 * t)) * Real.exp (-r * Real.cosh u) := by
            rw [Real.exp_add]
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
            dsimp only [a]; nlinarith [ha, h1]
          have h5 : (1 / 2 : ℝ) ≤ |Real.sin (Real.pi * u / t)| := h_sin_ge u k hu.1 hu.2
          have hsinh_nn : 0 ≤ Real.sinh u := Real.sinh_nonneg_iff.mpr hu0
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
            abs_of_pos (Real.exp_pos _), abs_of_nonneg hsinh_nn]
          calc 1 = 2 * (1 / 2) := by norm_num
            _ ≤ (Real.exp (-u ^ 2 / (2 * t) + a * (Real.exp u / 2)) * ((Real.exp u - 1) / 2)) *
                  |Real.sin (Real.pi * u / t)| := by
                refine mul_le_mul h3 h5 (by norm_num) (by positivity)
            _ ≤ (Real.exp (-u ^ 2 / (2 * t)) * Real.exp (-r * Real.cosh u) * Real.sinh u) *
                  |Real.sin (Real.pi * u / t)| := by
                refine mul_le_mul_of_nonneg_right (mul_le_mul h4 h2 ?_ ?_) (abs_nonneg _)
                · have : 1 ≤ Real.exp u := Real.one_le_exp hu0; linarith
                · positivity
        have h_sub : Icc ((k : ℝ) * t + t / 4) ((k : ℝ) * t + 3 * t / 4) ⊆ Ioi 0 := fun u hu => by
          have hpos : (0 : ℝ) < (k : ℝ) * t + t / 4 := by positivity
          exact lt_of_lt_of_le hpos hu.1
        have h_int_sub := h_norm.mono_set h_sub
        calc t / 2 = ∫ _ in Icc ((k : ℝ) * t + t / 4) ((k : ℝ) * t + 3 * t / 4), (1 : ℝ) := by
              rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, Real.volume_Icc,
                ENNReal.toReal_ofReal (by linarith)]
              ring
          _ ≤ ∫ u in Icc ((k : ℝ) * t + t / 4) ((k : ℝ) * t + 3 * t / 4), ‖F u‖ :=
              setIntegral_mono_on (integrableOn_const (C := (1 : ℝ)) (hs := isCompact_Icc.measure_lt_top.ne))
                h_int_sub measurableSet_Icc h_pt
      let S : ℕ → Set ℝ := fun k => Icc (((K + k : ℕ) : ℝ) * t + t / 4) (((K + k : ℕ) : ℝ) * t + 3 * t / 4)
      have h_disj : Pairwise (fun i j => Disjoint (S i) (S j)) := by
        intro i j hij
        rw [Set.disjoint_left]
        intro u hui huj
        rcases lt_or_gt_of_ne hij with h | h
        · have hij1 : (i : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt h
          have : ((K + i : ℕ) : ℝ) * t + 3 * t / 4 < ((K + j : ℕ) : ℝ) * t + t / 4 := by
            push_cast; nlinarith
          linarith [hui.2, huj.1]
        · have hji1 : (j : ℝ) + 1 ≤ i := by exact_mod_cast Nat.succ_le_of_lt h
          have : ((K + j : ℕ) : ℝ) * t + 3 * t / 4 < ((K + i : ℕ) : ℝ) * t + t / 4 := by
            push_cast; nlinarith
          linarith [hui.1, huj.2]
      have h_big : ∀ N : ℕ, (N : ℝ) * (t / 2) ≤ ∫ u in Ioi 0, ‖F u‖ := by
        intro N
        have h_sum_le : ∑ k ∈ Finset.range N, ∫ u in S k, ‖F u‖ ≤ ∫ u in Ioi 0, ‖F u‖ := by
          have h_sub_U : (⋃ k ∈ Finset.range N, S k) ⊆ Ioi 0 := by
            intro u hu
            simp only [mem_iUnion, Finset.mem_range] at hu
            obtain ⟨k, _, hk⟩ := hu
            have hpos : (0 : ℝ) < ((K + k : ℕ) : ℝ) * t + t / 4 := by positivity
            exact lt_of_lt_of_le hpos hk.1
          rw [← integral_biUnion_finset (Finset.range N) (fun k _ => measurableSet_Icc)
            (fun i _ j _ hij => h_disj hij) (fun k _ => h_norm.mono_set (fun u hu => by
              have hpos : (0 : ℝ) < ((K + k : ℕ) : ℝ) * t + t / 4 := by positivity
              exact lt_of_lt_of_le hpos hu.1))]
          exact setIntegral_mono_set h_norm (ae_of_all _ fun _ => norm_nonneg _) h_sub_U.eventuallyLE
        calc (N : ℝ) * (t / 2) = ∑ _ ∈ Finset.range N, (t / 2) := by simp
          _ ≤ ∑ k ∈ Finset.range N, ∫ u in S k, ‖F u‖ :=
              Finset.sum_le_sum fun k _ => h_piece (K + k) (Nat.le_add_right K k)
          _ ≤ ∫ u in Ioi 0, ‖F u‖ := h_sum_le
      obtain ⟨N, hN⟩ := exists_nat_gt ((∫ u in Ioi 0, ‖F u‖) / (t / 2) + 1)
      have h1 : (∫ u in Ioi 0, ‖F u‖) < (N : ℝ) * (t / 2) := by
        rw [← div_lt_iff₀ (by positivity : 0 < t / 2)]
        linarith
      linarith [h_big N]
    simp only [yorDensity, theta]
    rw [integral_undef h_not_int]
    simp

/-- Constructive, axiom-free proof of Yor's joint density formula (`σ = 2, ν = 0`). -/
theorem yor_joint_density {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W) (t : ℝ≥0) (ht : 0 < t) :
    IsJointDensity P W 2 0 t (fun x y => yorDensity t x y) := by
  unfold IsJointDensity
  let μ : Measure (ℝ × ℝ) := jointLaw P W 2 0 t
  let ν : Measure (ℝ × ℝ) := (volume : Measure (ℝ × ℝ)).withDensity (fun p => ENNReal.ofReal (yorDensity t p.1 p.2))
  have htR : (0 : ℝ) < t := ht
  have h_yor_meas : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (yorDensity t p.1 p.2)) := by
    have h_eq : (fun p : ℝ × ℝ => ENNReal.ofReal (yorDensity t p.1 p.2)) =
        fun p => ENNReal.ofReal (if 0 < p.1 then yorDensity t p.1 p.2 else 0) := by
      funext p
      split_ifs with h
      · rfl
      · simp [yorDensity_zero_of_nonpos htR (not_lt.mp h) p.2]
    rw [h_eq]
    exact (yorDensity_ite_measurable t ht).ennreal_ofReal
  have hν_univ : ν univ = 1 := by
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    have h_zero : ∀ p : ℝ × ℝ, p ∉ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) →
        ENNReal.ofReal (yorDensity t p.1 p.2) = 0 := by
      intro p hp
      simp only [mem_prod, mem_Ioi, mem_univ, and_true, not_lt] at hp
      simp [yorDensity_zero_of_nonpos htR hp p.2]
    have h_ind : (fun p : ℝ × ℝ => ENNReal.ofReal (yorDensity t p.1 p.2)) =
        (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)).indicator (fun p => ENNReal.ofReal (yorDensity t p.1 p.2)) := by
      funext p
      by_cases hp : p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)
      · rw [indicator_of_mem hp]
      · rw [indicator_of_notMem hp, h_zero p hp]
    rw [h_ind, lintegral_indicator (measurableSet_Ioi.prod MeasurableSet.univ),
      Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ,
      lintegral_prod_symm _ (h_yor_meas.aemeasurable)]
    have h_inner : ∀ y : ℝ, (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (yorDensity t x y)) =
        ENNReal.ofReal (gaussianPDFReal 0 t y) := by
      intro y
      obtain ⟨_, hy_int, _⟩ := (yorDensity_abs_bound t ht).choose_spec.2 y
      rw [← ofReal_integral_eq_lintegral_ofReal hy_int
        (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => yorDensity_nonneg P W hW t ht hx y),
        yorDensity_integral_x_eq_gaussian t ht y]
    simp_rw [h_inner]
    simpa [gaussianPDF] using lintegral_gaussianPDF_eq_one (μ := 0) ht.ne'
  have : IsProbabilityMeasure ν := ⟨hν_univ⟩
  have hμ_prob : IsProbabilityMeasure μ := by
    let B : ℝ≥0 → Ω → ℝ := hW.toIsPreBrownianReal.mk W
    have hBmeas : ∀ s, Measurable (B s) := hW.toIsPreBrownianReal.measurable_mk
    have hBcont : ∀ ω, Continuous (B · ω) := hW.toIsPreBrownianReal.continuous_mk
    have hBW : ∀ᵐ ω ∂P, ∀ s, B s ω = W s ω := hW.mk_ae_forall_eq
    have hXmeas : Measurable (expInt B 2 0 t) := measurable_expInt_bm hBmeas hBcont 2 t
    have haemeas : AEMeasurable (fun ω => (expInt W 2 0 t ω, W t ω)) P := by
      refine AEMeasurable.congr ((hXmeas.prodMk (hBmeas t)).aemeasurable) (hBW.mono fun ω hω => ?_)
      refine Prod.ext ?_ (hω t)
      simp only [expInt]; exact intervalIntegral.integral_congr fun s _ => by rw [hω s.toNNReal]
    have hμ_univ : μ univ = 1 := by
      change (P.map (fun ω => (expInt W 2 0 t ω, W t ω))) univ = 1
      rw [Measure.map_apply_of_aemeasurable haemeas .univ, preimage_univ, measure_univ]
    exact ⟨hμ_univ⟩
  -- Both `μ` and `ν` vanish on `Iic 0 ×ˢ univ`.
  have hμ_nonpos : μ (Iic (0 : ℝ) ×ˢ univ) = 0 := by
    let B : ℝ≥0 → Ω → ℝ := hW.toIsPreBrownianReal.mk W
    have hBmeas : ∀ s, Measurable (B s) := hW.toIsPreBrownianReal.measurable_mk
    have hBcont : ∀ ω, Continuous (B · ω) := hW.toIsPreBrownianReal.continuous_mk
    have hBW : ∀ᵐ ω ∂P, ∀ s, B s ω = W s ω := hW.mk_ae_forall_eq
    have hXmeas : Measurable (expInt B 2 0 t) := measurable_expInt_bm hBmeas hBcont 2 t
    have haemeas : AEMeasurable (fun ω => (expInt W 2 0 t ω, W t ω)) P := by
      refine AEMeasurable.congr ((hXmeas.prodMk (hBmeas t)).aemeasurable) (hBW.mono fun ω hω => ?_)
      refine Prod.ext ?_ (hω t)
      simp only [expInt]; exact intervalIntegral.integral_congr fun s _ => by rw [hω s.toNNReal]
    change (P.map (fun ω => (expInt W 2 0 t ω, W t ω))) (Iic (0 : ℝ) ×ˢ univ) = 0
    rw [Measure.map_apply_of_aemeasurable haemeas (measurableSet_Iic.prod MeasurableSet.univ)]
    have hnull : ∀ᵐ ω ∂P, 0 < expInt W 2 0 t ω := expInt_two_pos_ae W hW t ht
    have hnull_eq : (fun ω => (expInt W 2 0 t ω, W t ω)) ⁻¹' (Iic (0 : ℝ) ×ˢ univ) =
        {ω | ¬ 0 < expInt W 2 0 t ω} := by
      ext ω; simp [not_lt]
    rw [hnull_eq]
    exact ae_iff.mp hnull
  have hν_nonpos : ν (Iic (0 : ℝ) ×ˢ univ) = 0 := by
    rw [withDensity_apply _ (measurableSet_Iic.prod MeasurableSet.univ), setLIntegral_eq_zero_iff'
      (measurableSet_Iic.prod MeasurableSet.univ) h_yor_meas.aemeasurable]
    refine ae_of_all _ fun p hp => ?_
    simp [yorDensity_zero_of_nonpos htR hp.1 p.2]
  -- Now prove `μ (Ioo a b ×ˢ Ioo c d) = ν (Ioo a b ×ˢ Ioo c d)` for `0 < a < b, c < d`.
  have h_pos_rect : ∀ a b c d : ℝ, 0 < a → a < b → c < d →
      μ (Ioo a b ×ˢ Ioo c d) = ν (Ioo a b ×ˢ Ioo c d) := by
    intro a b c d ha hab hcd
    let T : ℝ → ℝ := fun z => Real.exp (-z⁻¹)
    have hT_mono : StrictMonoOn T (Ioi 0) := by
      intro x hx y _ hxy
      exact Real.exp_lt_exp.mpr (neg_lt_neg (inv_strictAnti₀ hx hxy))
    have hTab : T a < T b := hT_mono ha (ha.trans hab) hab
    let φ : ℕ → ℝ → ℝ := fun k u =>
      smoothBump (T a) (T a + (T b - T a) / ((k : ℝ) + 3))
        (T b - (T b - T a) / ((k : ℝ) + 3)) (T b) u
    let f : ℕ → ℝ → ℝ := fun k y =>
      smoothBump c (c + (d - c) / ((k : ℝ) + 3)) (d - (d - c) / ((k : ℝ) + 3)) d y
    have h_test_k : ∀ k : ℕ,
        ∫ ω, φ k (Real.exp (-(expInt W 2 0 t ω)⁻¹)) * f k (W t ω) ∂P =
          ∫ y : ℝ, ∫ x in Ioi (0 : ℝ), φ k (Real.exp (-x⁻¹)) * f k y * yorDensity t x y := by
      intro k
      have hk1 : T a < T a + (T b - T a) / ((k : ℝ) + 3) := by
        linarith [div_pos (sub_pos.mpr hTab) (by positivity : (0 : ℝ) < (k : ℝ) + 3)]
      have hk2 : c < c + (d - c) / ((k : ℝ) + 3) := by
        linarith [div_pos (sub_pos.mpr hcd) (by positivity : (0 : ℝ) < (k : ℝ) + 3)]
      exact jointLaw_two_eq_yorDensity_test W hW t ht
        (smoothBump.contDiff _ _ _ _ (n := 0)).continuous.continuousOn
        (smoothBump.contDiff _ _ _ _ (n := 0)).continuous
        (smoothBump.hasCompactSupport hk2 (by linarith [show (0 : ℝ) < (d - c) / ((k : ℝ) + 3) by positivity]))
    have hφ_lim : ∀ x ∈ Ioi (0 : ℝ),
        Tendsto (fun k : ℕ => φ k (T x)) atTop (nhds ((Ioo a b).indicator (fun _ => (1 : ℝ)) x)) := by
      intro x hx
      by_cases hx_in : x ∈ Ioo a b
      · have hTx1 : T a < T x := hT_mono ha hx hx_in.1
        have hTx2 : T x < T b := hT_mono hx (ha.trans hab) hx_in.2
        have h_ev : ∀ᶠ k : ℕ in atTop, φ k (T x) = 1 := by
          let gap := min (T x - T a) (T b - T x)
          have hgap : 0 < gap := lt_min (sub_pos.mpr hTx1) (sub_pos.mpr hTx2)
          obtain ⟨N, hN⟩ := exists_nat_one_div_lt (div_pos hgap (sub_pos.mpr hTab))
          refine eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
          have hsmall : (T b - T a) / ((k : ℝ) + 3) < gap := by
            have hk' : (1 : ℝ) / ((k : ℝ) + 3) < gap / (T b - T a) :=
              lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (by omega : N + 1 ≤ k + 3))) hN
            have hk'' := mul_lt_mul_of_pos_right hk' (sub_pos.mpr hTab)
            field_simp [(sub_pos.mpr hTab).ne'] at hk'' ⊢
            linarith
          have ha_lt : T a < T a + (T b - T a) / ((k : ℝ) + 3) := by
            linarith [div_pos (sub_pos.mpr hTab) (by positivity : (0 : ℝ) < (k : ℝ) + 3)]
          have hb_lt : T b - (T b - T a) / ((k : ℝ) + 3) < T b := by
            linarith [show 0 < (T b - T a) / ((k : ℝ) + 3) by positivity]
          exact smoothBump.one_of_mem ha_lt hb_lt
            (by linarith [min_le_left (T x - T a) (T b - T x)])
            (by linarith [min_le_right (T x - T a) (T b - T x)])
        simp only [indicator_of_mem hx_in]
        exact tendsto_const_nhds.congr' (h_ev.mono fun k hk => hk.symm)
      · have hx_out : T x ≤ T a ∨ T b ≤ T x := by
          simp only [mem_Ioo, not_and_or, not_lt] at hx_in
          rcases hx_in with h | h
          · left; exact (hT_mono.monotoneOn hx ha h)
          · right; exact (hT_mono.monotoneOn (ha.trans hab) hx h)
        have h_const : ∀ k : ℕ, φ k (T x) = 0 := fun k =>
          smoothBump.zero_of_not_mem
            (by linarith [div_pos (sub_pos.mpr hTab) (by positivity : (0 : ℝ) < (k : ℝ) + 3)])
            (by linarith [show 0 < (T b - T a) / ((k : ℝ) + 3) by positivity])
            hx_out
        simp only [indicator_of_notMem hx_in, h_const]
        exact tendsto_const_nhds
    have hf_lim : ∀ y : ℝ,
        Tendsto (fun k : ℕ => f k y) atTop (nhds ((Ioo c d).indicator (fun _ => (1 : ℝ)) y)) := by
      intro y
      by_cases hy_in : y ∈ Ioo c d
      · have h_ev : ∀ᶠ k : ℕ in atTop, f k y = 1 := by
          let gap := min (y - c) (d - y)
          have hgap : 0 < gap := lt_min (sub_pos.mpr hy_in.1) (sub_pos.mpr hy_in.2)
          obtain ⟨N, hN⟩ := exists_nat_one_div_lt (div_pos hgap (sub_pos.mpr hcd))
          refine eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
          have hsmall : (d - c) / ((k : ℝ) + 3) < gap := by
            have hk' : (1 : ℝ) / ((k : ℝ) + 3) < gap / (d - c) :=
              lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (by omega : N + 1 ≤ k + 3))) hN
            have hk'' := mul_lt_mul_of_pos_right hk' (sub_pos.mpr hcd)
            field_simp [(sub_pos.mpr hcd).ne'] at hk'' ⊢
            linarith
          exact smoothBump.one_of_mem
            (by linarith [div_pos (sub_pos.mpr hcd) (by positivity : (0 : ℝ) < (k : ℝ) + 3)])
            (by linarith [show 0 < (d - c) / ((k : ℝ) + 3) by positivity])
            (by linarith [min_le_left (y - c) (d - y)])
            (by linarith [min_le_right (y - c) (d - y)])
        simp only [indicator_of_mem hy_in]
        exact tendsto_const_nhds.congr' (h_ev.mono fun k hk => hk.symm)
      · have hy_out : y ≤ c ∨ d ≤ y := by
          simp only [mem_Ioo, not_and_or, not_lt] at hy_in
          exact hy_in.imp id id
        have h_const : ∀ k : ℕ, f k y = 0 := fun k =>
          smoothBump.zero_of_not_mem
            (by linarith [div_pos (sub_pos.mpr hcd) (by positivity : (0 : ℝ) < (k : ℝ) + 3)])
            (by linarith [show 0 < (d - c) / ((k : ℝ) + 3) by positivity])
            hy_out
        simp only [indicator_of_notMem hy_in, h_const]
        exact tendsto_const_nhds
    let B : ℝ≥0 → Ω → ℝ := hW.toIsPreBrownianReal.mk W
    have hBmeas : ∀ s, Measurable (B s) := hW.toIsPreBrownianReal.measurable_mk
    have hBcont : ∀ ω, Continuous (B · ω) := hW.toIsPreBrownianReal.continuous_mk
    have hBbm : IsBM P B := ⟨hW.toIsPreBrownianReal.isBrownianReal_mk.toIsPreBrownianReal,
      Eventually.of_forall hBcont⟩
    have hBW : ∀ᵐ ω ∂P, ∀ s, B s ω = W s ω := hW.mk_ae_forall_eq
    have hXpos := expInt_two_pos_ae W hW t ht
    have hL_lim : Tendsto (fun k : ℕ => ∫ ω, φ k (Real.exp (-(expInt W 2 0 t ω)⁻¹)) * f k (W t ω) ∂P)
        atTop (nhds ((μ (Ioo a b ×ˢ Ioo c d)).toReal)) := by
      have h_tgt : (μ (Ioo a b ×ˢ Ioo c d)).toReal =
          ∫ ω, (Ioo a b).indicator (fun _ => (1 : ℝ)) (expInt W 2 0 t ω) *
            (Ioo c d).indicator (fun _ => (1 : ℝ)) (W t ω) ∂P := by
        have hXmeas : Measurable (expInt B 2 0 t) := measurable_expInt_bm hBmeas hBcont 2 t
        have haemeas : AEMeasurable (fun ω => (expInt W 2 0 t ω, W t ω)) P := by
          refine AEMeasurable.congr ((hXmeas.prodMk (hBmeas t)).aemeasurable) (hBW.mono fun ω hω => ?_)
          refine Prod.ext ?_ (hω t)
          simp only [expInt]; exact intervalIntegral.integral_congr fun s _ => by rw [hω s.toNNReal]
        have h_map : ∫ p : ℝ × ℝ, (Ioo a b ×ˢ Ioo c d).indicator (fun _ => (1 : ℝ)) p ∂μ =
            ∫ ω, (Ioo a b).indicator (fun _ => (1 : ℝ)) (expInt W 2 0 t ω) *
              (Ioo c d).indicator (fun _ => (1 : ℝ)) (W t ω) ∂P := by
          rw [show μ = P.map (fun ω => (expInt W 2 0 t ω, W t ω)) from rfl,
            integral_map haemeas ((measurable_const.indicator (measurableSet_Ioo.prod measurableSet_Ioo)).aestronglyMeasurable)]
          refine integral_congr_ae (ae_of_all _ fun ω => ?_)
          by_cases h1 : expInt W 2 0 t ω ∈ Ioo a b <;> by_cases h2 : W t ω ∈ Ioo c d <;>
            simp [h1, h2]
        rw [← h_map, integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo), setIntegral_const,
          smul_eq_mul, mul_one]
        rfl
      rw [h_tgt]
      refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ (integrable_const _) ?_ ?_
      · intro k
        have hXmeas : Measurable (expInt B 2 0 t) := measurable_expInt_bm hBmeas hBcont 2 t
        have hcφ : Continuous (φ k) := (smoothBump.contDiff _ _ _ _ (n := 0)).continuous
        have hcf : Continuous (f k) := (smoothBump.contDiff _ _ _ _ (n := 0)).continuous
        have h_ae1 : (fun ω => φ k (Real.exp (-(expInt B 2 0 t ω)⁻¹))) =ᵐ[P]
            fun ω => φ k (Real.exp (-(expInt W 2 0 t ω)⁻¹)) :=
          hBW.mono fun ω hω => by
            dsimp only
            have hX : expInt B 2 0 t ω = expInt W 2 0 t ω := by
              simp only [expInt]; exact intervalIntegral.integral_congr fun s _ => by rw [hω s.toNNReal]
            rw [hX]
        have h_ae2 : (fun ω => f k (B t ω)) =ᵐ[P] fun ω => f k (W t ω) :=
          hBW.mono fun ω hω => by dsimp only; rw [hω t]
        have hm1 : AEMeasurable (fun ω => φ k (Real.exp (-(expInt W 2 0 t ω)⁻¹))) P :=
          ((hcφ.measurable.comp (Real.continuous_exp.measurable.comp hXmeas.inv.neg)).aemeasurable).congr h_ae1
        have hm2 : AEMeasurable (fun ω => f k (W t ω)) P :=
          ((hcf.measurable.comp (hBmeas t)).aemeasurable).congr h_ae2
        exact (hm1.mul hm2).aestronglyMeasurable
      · intro k
        filter_upwards with ω
        have hm1 := smoothBump.mem_Icc (T a) (T a + (T b - T a) / ((k : ℝ) + 3))
          (T b - (T b - T a) / ((k : ℝ) + 3)) (T b) (Real.exp (-(expInt W 2 0 t ω)⁻¹))
        have hm2 := smoothBump.mem_Icc c (c + (d - c) / ((k : ℝ) + 3))
          (d - (d - c) / ((k : ℝ) + 3)) d (W t ω)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hm1.1, abs_of_nonneg hm2.1]
        exact (mul_le_of_le_one_right hm1.1 hm2.2).trans hm1.2
      · filter_upwards [hXpos] with ω hω
        exact (hφ_lim (expInt W 2 0 t ω) hω).mul (hf_lim (W t ω))
    have hR_lim : Tendsto (fun k : ℕ => ∫ y : ℝ, ∫ x in Ioi (0 : ℝ), φ k (Real.exp (-x⁻¹)) * f k y * yorDensity t x y)
        atTop (nhds ((ν (Ioo a b ×ˢ Ioo c d)).toReal)) := by
      have h_tgt : (ν (Ioo a b ×ˢ Ioo c d)).toReal =
          ∫ y : ℝ, ∫ x in Ioi (0 : ℝ),
            (Ioo a b).indicator (fun _ => (1 : ℝ)) x * (Ioo c d).indicator (fun _ => (1 : ℝ)) y *
              yorDensity t x y := by
        rw [withDensity_apply _ (measurableSet_Ioo.prod measurableSet_Ioo)]
        have h_prod_ind : ∫⁻ p in Ioo a b ×ˢ Ioo c d, ENNReal.ofReal (yorDensity t p.1 p.2) =
            ∫⁻ y in Ioo c d, ∫⁻ x in Ioo a b, ENNReal.ofReal (yorDensity t x y) := by
          rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
          exact lintegral_prod_symm _ h_yor_meas.aemeasurable
        have h_inner : ∀ y : ℝ, (∫⁻ x in Ioo a b, ENNReal.ofReal (yorDensity t x y)) =
            ENNReal.ofReal (∫ x in Ioo a b, yorDensity t x y) := by
          intro y
          obtain ⟨_, hy_int, _⟩ := (yorDensity_abs_bound t ht).choose_spec.2 y
          have hsub : Ioo a b ⊆ Ioi 0 := fun x hx => lt_trans ha hx.1
          exact (ofReal_integral_eq_lintegral_ofReal (hy_int.mono_set hsub)
            (ae_restrict_of_forall_mem measurableSet_Ioo fun x hx =>
              yorDensity_nonneg P W hW t ht (hsub hx) y)).symm
        obtain ⟨M, hM0, hM⟩ := yorDensity_abs_bound t ht
        have h_outer_int : IntegrableOn (fun y => ∫ x in Ioo a b, yorDensity t x y) (Ioo c d) := by
          refine (integrableOn_const (C := M) (hs := measure_Ioo_lt_top.ne)).mono' ?_ ?_
          · have hg_ab : StronglyMeasurable (fun p : ℝ × ℝ => if 0 < p.1 then yorDensity t p.1 p.2 else 0) :=
              (yorDensity_ite_measurable t ht).stronglyMeasurable
            have h1 : StronglyMeasurable (fun y => ∫ x in Ioo a b,
                if 0 < x then yorDensity t x y else 0) := hg_ab.integral_prod_left'
            refine h1.aestronglyMeasurable.congr (ae_of_all _ fun y => ?_)
            refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
            simp [lt_trans ha hx.1]
          · refine ae_restrict_of_forall_mem measurableSet_Ioo fun y _ => ?_
            obtain ⟨_, hy_int, hy_M⟩ := hM y
            have hsub : Ioo a b ⊆ Ioi 0 := fun x hx => lt_trans ha hx.1
            rw [Real.norm_eq_abs, abs_of_nonneg (setIntegral_nonneg measurableSet_Ioo fun x hx =>
              yorDensity_nonneg P W hW t ht (hsub hx) y)]
            calc ∫ x in Ioo a b, yorDensity t x y
                ≤ ∫ x in Ioo a b, |yorDensity t x y| :=
                  setIntegral_mono_on (hy_int.mono_set hsub) (hy_int.mono_set hsub).abs measurableSet_Ioo
                    fun x _ => le_abs_self _
              _ ≤ ∫ x in Ioi (0 : ℝ), |yorDensity t x y| :=
                  setIntegral_mono_set hy_int.abs (ae_of_all _ fun _ => abs_nonneg _) hsub.eventuallyLE
              _ ≤ M := hy_M
        rw [h_prod_ind]
        simp_rw [h_inner]
        rw [← ofReal_integral_eq_lintegral_ofReal h_outer_int
          (ae_restrict_of_forall_mem measurableSet_Ioo fun y _ =>
            setIntegral_nonneg measurableSet_Ioo fun x hx =>
              yorDensity_nonneg P W hW t ht (lt_trans ha hx.1) y)]
        rw [ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioo fun y _ =>
          setIntegral_nonneg measurableSet_Ioo fun x hx =>
            yorDensity_nonneg P W hW t ht (lt_trans ha hx.1) y)]
        rw [← integral_indicator measurableSet_Ioo]
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        by_cases hy : y ∈ Ioo c d
        · simp only [indicator_of_mem hy]
          have hsub : Ioo a b ⊆ Ioi 0 := fun x hx => lt_trans ha hx.1
          rw [show (fun x => (Ioo a b).indicator (fun _ => (1 : ℝ)) x * 1 * yorDensity t x y) =
              (Ioo a b).indicator (fun x => yorDensity t x y) by
            funext x; by_cases hx' : x ∈ Ioo a b <;> simp [hx']]
          rw [setIntegral_indicator measurableSet_Ioo, inter_eq_right.mpr hsub]
        · simp [indicator_of_notMem hy]
      rw [h_tgt]
      obtain ⟨M, hM0, hM⟩ := yorDensity_abs_bound t ht
      let boundY : ℝ → ℝ := (Icc c d).indicator (fun _ => M)
      have h_boundY_int : Integrable boundY :=
        (integrableOn_const (C := M) (hs := isCompact_Icc.measure_lt_top.ne)).integrable_indicator
          measurableSet_Icc
      refine tendsto_integral_of_dominated_convergence boundY ?_ h_boundY_int ?_ ?_
      · intro k
        have hk2 : c < c + (d - c) / ((k : ℝ) + 3) := by
          linarith [div_pos (sub_pos.mpr hcd) (by positivity : (0 : ℝ) < (k : ℝ) + 3)]
        have hk3 : d - (d - c) / ((k : ℝ) + 3) < d := by
          linarith [div_pos (sub_pos.mpr hcd) (by positivity : (0 : ℝ) < (k : ℝ) + 3)]
        have h1 := yorDensity_integrable_y_slice t ht
          (φ := fun u => φ k (max 0 (min 1 u)))
          ((smoothBump.contDiff _ _ _ _ (n := 0)).continuous.comp
            (continuous_const.max (continuous_const.min continuous_id)))
          ⟨1, fun u => by
            have hm := smoothBump.mem_Icc (T a) (T a + (T b - T a) / ((k : ℝ) + 3))
              (T b - (T b - T a) / ((k : ℝ) + 3)) (T b) (max 0 (min 1 u))
            rw [abs_of_nonneg hm.1]; exact hm.2⟩
          (smoothBump.contDiff _ _ _ _ (n := 0)).continuous
          (smoothBump.hasCompactSupport hk2 hk3)
        refine (h1.congr (ae_of_all _ fun y => setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_)).aestronglyMeasurable
        have hm : Real.exp (-x⁻¹) ∈ Icc (0 : ℝ) 1 :=
          ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr (inv_nonneg.mpr hx.le))⟩
        rw [min_eq_right hm.2, max_eq_right hm.1]
      · intro k
        filter_upwards with y
        obtain ⟨_, hy_int, hy_M⟩ := hM y
        by_cases hy : y ∈ Icc c d
        · simp only [boundY, indicator_of_mem hy, Real.norm_eq_abs]
          have h_le : ∀ x ∈ Ioi (0 : ℝ), ‖φ k (T x) * f k y * yorDensity t x y‖ ≤ |yorDensity t x y| := by
            intro x _
            have hm1 := smoothBump.mem_Icc (T a) (T a + (T b - T a) / ((k : ℝ) + 3))
              (T b - (T b - T a) / ((k : ℝ) + 3)) (T b) (T x)
            have hm2 := smoothBump.mem_Icc c (c + (d - c) / ((k : ℝ) + 3))
              (d - (d - c) / ((k : ℝ) + 3)) d y
            rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hm1.1, abs_of_nonneg hm2.1]
            exact mul_le_of_le_one_left (abs_nonneg _) ((mul_le_of_le_one_right hm1.1 hm2.2).trans hm1.2)
          have h_int_norm : IntegrableOn (fun x => ‖φ k (T x) * f k y * yorDensity t x y‖) (Ioi 0) :=
            hy_int.abs.mono' (by
              have hc : ContinuousOn (fun x => φ k (T x) * f k y) (Ioi 0) := fun x hx =>
                (((smoothBump.contDiff _ _ _ _ (n := 0)).continuous.continuousAt.comp
                  (Real.continuous_exp.continuousAt.comp ((continuousAt_id.inv₀ hx.ne').neg))).mul
                  continuousAt_const).continuousWithinAt
              exact ((hc.aestronglyMeasurable measurableSet_Ioi).mul hy_int.aestronglyMeasurable).norm)
              (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => by
                rw [Real.norm_eq_abs, abs_norm]; exact h_le x hx)
          calc |∫ x in Ioi (0 : ℝ), φ k (T x) * f k y * yorDensity t x y|
              ≤ ∫ x in Ioi (0 : ℝ), ‖φ k (T x) * f k y * yorDensity t x y‖ := by
                rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
            _ ≤ ∫ x in Ioi (0 : ℝ), |yorDensity t x y| :=
                setIntegral_mono_on h_int_norm hy_int.abs measurableSet_Ioi h_le
            _ ≤ M := hy_M
        · have hy_out : y ≤ c ∨ d ≤ y := by
            simp only [mem_Icc, not_and_or, not_le] at hy
            exact hy.imp le_of_lt le_of_lt
          have hf0 : f k y = 0 := smoothBump.zero_of_not_mem
            (by linarith [div_pos (sub_pos.mpr hcd) (by positivity : (0 : ℝ) < (k : ℝ) + 3)])
            (by linarith [show 0 < (d - c) / ((k : ℝ) + 3) by positivity])
            hy_out
          simp [boundY, indicator_of_notMem hy, hf0]
      · filter_upwards with y
        obtain ⟨_, hy_int, _⟩ := hM y
        refine tendsto_integral_of_dominated_convergence (fun x => |yorDensity t x y|)
          ?_ hy_int.abs ?_ ?_
        · intro k
          have hc : ContinuousOn (fun x => φ k (T x) * f k y) (Ioi 0) := fun x hx =>
            (((smoothBump.contDiff _ _ _ _ (n := 0)).continuous.continuousAt.comp
              (Real.continuous_exp.continuousAt.comp ((continuousAt_id.inv₀ hx.ne').neg))).mul
              continuousAt_const).continuousWithinAt
          exact (hc.aestronglyMeasurable measurableSet_Ioi).mul hy_int.aestronglyMeasurable
        · intro k
          refine ae_restrict_of_forall_mem measurableSet_Ioi fun x _ => ?_
          have hm1 := smoothBump.mem_Icc (T a) (T a + (T b - T a) / ((k : ℝ) + 3))
            (T b - (T b - T a) / ((k : ℝ) + 3)) (T b) (T x)
          have hm2 := smoothBump.mem_Icc c (c + (d - c) / ((k : ℝ) + 3))
            (d - (d - c) / ((k : ℝ) + 3)) d y
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hm1.1, abs_of_nonneg hm2.1]
          exact mul_le_of_le_one_left (abs_nonneg _) ((mul_le_of_le_one_right hm1.1 hm2.2).trans hm1.2)
        · refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
          exact ((hφ_lim x hx).mul (hf_lim y)).mul_const _
    have h_eq_k : (fun k : ℕ => ∫ ω, φ k (Real.exp (-(expInt W 2 0 t ω)⁻¹)) * f k (W t ω) ∂P) =
        fun k : ℕ => ∫ y : ℝ, ∫ x in Ioi (0 : ℝ), φ k (Real.exp (-x⁻¹)) * f k y * yorDensity t x y :=
      funext h_test_k
    rw [h_eq_k] at hL_lim
    have h_toReal : (μ (Ioo a b ×ˢ Ioo c d)).toReal = (ν (Ioo a b ×ˢ Ioo c d)).toReal :=
      tendsto_nhds_unique hL_lim hR_lim
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top ν _)).mp h_toReal
  -- Extend to all `a < b, c < d`, and apply `ext_of_generate_finite`!
  have h_all_rect : ∀ a b c d : ℝ, a < b → c < d →
      μ (Ioo a b ×ˢ Ioo c d) = ν (Ioo a b ×ˢ Ioo c d) := by
    intro a b c d hab hcd
    rcases le_or_gt b 0 with hb | hb
    · have hsub : Ioo a b ×ˢ Ioo c d ⊆ Iic (0 : ℝ) ×ˢ univ := fun p hp =>
        ⟨hp.1.2.le.trans hb, trivial⟩
      rw [measure_mono_null hsub hμ_nonpos, measure_mono_null hsub hν_nonpos]
    · have h_split : ∀ m : Measure (ℝ × ℝ), m (Iic (0 : ℝ) ×ˢ univ) = 0 →
          m (Ioo a b ×ˢ Ioo c d) = m ((Ioo a b ∩ Ioi 0) ×ˢ Ioo c d) := by
        intro m hm
        have h1 : Ioo a b ×ˢ Ioo c d = ((Ioo a b ∩ Ioi 0) ×ˢ Ioo c d) ∪ ((Ioo a b ∩ Iic 0) ×ˢ Ioo c d) := by
          ext ⟨x, y⟩
          simp only [mem_prod, mem_Ioo, mem_inter_iff, mem_Ioi, mem_Iic, mem_union]
          constructor
          · rintro ⟨⟨hx1, hx2⟩, hy⟩
            rcases lt_or_ge 0 x with hx | hx
            · left; exact ⟨⟨⟨hx1, hx2⟩, hx⟩, hy⟩
            · right; exact ⟨⟨⟨hx1, hx2⟩, hx⟩, hy⟩
          · rintro (⟨⟨⟨hx1, hx2⟩, _⟩, hy⟩ | ⟨⟨⟨hx1, hx2⟩, _⟩, hy⟩) <;> exact ⟨⟨hx1, hx2⟩, hy⟩
        have h_null : m ((Ioo a b ∩ Iic 0) ×ˢ Ioo c d) = 0 :=
          measure_mono_null (fun p hp => by
            simp only [mem_prod, mem_inter_iff, mem_Iic, mem_univ, and_true] at hp ⊢
            exact hp.1.2) hm
        have h_disj : Disjoint ((Ioo a b ∩ Ioi 0) ×ˢ Ioo c d) ((Ioo a b ∩ Iic 0) ×ˢ Ioo c d) := by
          rw [Set.disjoint_left]
          intro ⟨x, y⟩ h1 h2
          linarith [mem_Ioi.mp h1.1.2, mem_Iic.mp h2.1.2]
        rw [h1, measure_union h_disj ((measurableSet_Ioo.inter measurableSet_Iic).prod measurableSet_Ioo),
          h_null, add_zero]
      rw [h_split μ hμ_nonpos, h_split ν hν_nonpos]
      rcases lt_or_ge 0 a with ha | ha
      · have hinter : Ioo a b ∩ Ioi 0 = Ioo a b := inter_eq_left.mpr fun x hx => lt_trans ha hx.1
        rw [hinter]
        exact h_pos_rect a b c d ha hab hcd
      · have hinter : Ioo a b ∩ Ioi 0 = Ioo 0 b := by
          ext x; simp only [mem_inter_iff, mem_Ioo, mem_Ioi]
          exact ⟨fun ⟨⟨_, hx2⟩, hx3⟩ => ⟨hx3, hx2⟩, fun ⟨hx1, hx2⟩ => ⟨⟨lt_of_le_of_lt ha hx1, hx2⟩, hx1⟩⟩
        rw [hinter]
        have h_iUnion : Ioo (0 : ℝ) b ×ˢ Ioo c d = ⋃ k : ℕ, Ioo (b / ((k : ℝ) + 2)) b ×ˢ Ioo c d := by
          ext ⟨x, y⟩
          simp only [mem_prod, mem_Ioo, mem_iUnion]
          constructor
          · rintro ⟨⟨hx0, hxb⟩, hy⟩
            obtain ⟨k, hk⟩ := exists_nat_one_div_lt (div_pos hx0 hb)
            refine ⟨k, ⟨?_, hxb⟩, hy⟩
            have hk' : (1 : ℝ) / ((k : ℝ) + 2) < x / b :=
              lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (by omega : k + 1 ≤ k + 2))) hk
            have hk'' := mul_lt_mul_of_pos_right hk' hb
            field_simp [hb.ne'] at hk'' ⊢
            linarith
          · rintro ⟨k, ⟨hx1, hxb⟩, hy⟩
            exact ⟨⟨lt_trans (by positivity) hx1, hxb⟩, hy⟩
        have h_mono_set : Monotone (fun k : ℕ => Ioo (b / ((k : ℝ) + 2)) b ×ˢ Ioo c d) := by
          intro i j hij ⟨x, y⟩ ⟨⟨hx1, hx2⟩, hy⟩
          refine ⟨⟨lt_of_le_of_lt ?_ hx1, hx2⟩, hy⟩
          exact div_le_div_of_nonneg_left hb.le (by positivity) (by exact_mod_cast (by omega : i + 2 ≤ j + 2))
        rw [h_iUnion, h_mono_set.measure_iUnion, h_mono_set.measure_iUnion]
        congr 1; funext k
        exact h_pos_rect (b / ((k : ℝ) + 2)) b c d (by positivity)
          (div_lt_self hb (by norm_cast; omega)) hcd
  let C1 : Set (Set ℝ) := ⋃ (a : ℚ) (b : ℚ) (_ : a < b), {Ioo (a : ℝ) (b : ℝ)}
  let C : Set (Set (ℝ × ℝ)) := Set.image2 (· ×ˢ ·) C1 C1
  have h_gen : (inferInstance : MeasurableSpace (ℝ × ℝ)) = MeasurableSpace.generateFrom C := by
    rw [BorelSpace.measurable_eq (α := ℝ × ℝ)]
    exact (Real.isTopologicalBasis_Ioo_rat.prod Real.isTopologicalBasis_Ioo_rat).borel_eq_generateFrom
  have h_pi : IsPiSystem C := Real.isPiSystem_Ioo_rat.prod Real.isPiSystem_Ioo_rat
  exact MeasureTheory.ext_of_generate_finite C h_gen h_pi (fun s hs => by
    simp only [C, C1, Set.mem_image2, Set.mem_iUnion, Set.mem_singleton_iff] at hs
    rcases hs with ⟨s1, ⟨a, b, hab, rfl⟩, s2, ⟨c, d, hcd, rfl⟩, rfl⟩
    exact h_all_rect (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) (by exact_mod_cast hab) (by exact_mod_cast hcd))
    (by simp [measure_univ])

end YorNonnegAndDensity

end Lyasoff2016

