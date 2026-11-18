/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
# §4 Foliation of the joint law (pp. 1071–1079)
-/
module

public import Lyasoff2016.Line
public import Lyasoff2016.ModifiedBesselK1
public import Lyasoff2016.Setting


@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

/- Paper: p. 1071–1073, Theorem 4.1 (PDE part).
   Plain recap: hypothesis that a candidate φc satisfies the first-order
   transport PDE along V. Establishing this for the conditional density of
   exp-BM is open; `theorem_4_1_pde` is the conditional rearrangement. -/
def SatisfiesTheorem41PDE (σ t : ℝ) (φc : ℝ → ℝ → ℝ) : Prop :=
  ∀ x > 0, ∀ y : ℝ,
    σ ^ 2 * x / 2 * deriv (fun z => φc z y) x + σ * deriv (fun y' => φc x y') y
      = (σ * y / t + (1 - Real.exp (σ * y)) / x - σ ^ 2 / 2) * φc x y

/- Conditional form of Thm 4.1 PDE: assumes `SatisfiesTheorem41PDE`. -/
theorem theorem_4_1_pde (σ t : ℝ) (φc : ℝ → ℝ → ℝ)
    (htransport : SatisfiesTheorem41PDE σ t φc) (x y : ℝ) (hx : 0 < x) :
    σ ^ 2 * x / 2 * deriv (fun z => φc z y) x + σ * deriv (fun y' => φc x y') y
      = (σ * y / t + (1 - Real.exp (σ * y)) / x - σ ^ 2 / 2) * φc x y :=
  htransport x hx y

/- Paper: p. 1073, Theorem 4.1 identity (4.4) (Donati-Martin–Matsumoto–Yor).
   Plain recap: hypothesis for the reciprocal-moment cases
   E[(∫ e^{σW})^{-1} | W_t = y/σ] = y/(t(e^y−1)) (and 1/t at y=0).
   PAPER NOTE: printed ∫₀ᵗ should be ∫₀^∞ x^{-1} φ(x|·) dx.
   Establishing this for the conditional density is open;
   `theorem_4_1_striking` is the conditional rearrangement. -/
def SatisfiesStrikingIdentity (σ t : ℝ) (φc : ℝ → ℝ → ℝ) : Prop :=
  (∀ y : ℝ, y ≠ 0 →
    ∫ x in Ioi (0 : ℝ), x⁻¹ * φc x (y / σ) =
      y / (t * (Real.exp y - 1))) ∧
  (∫ x in Ioi (0 : ℝ), x⁻¹ * φc x 0 = 1 / t)

/- Conditional form of Thm 4.1 (4.4): assumes `SatisfiesStrikingIdentity`. -/
theorem theorem_4_1_striking (σ t : ℝ)
    (φc : ℝ → ℝ → ℝ) (hbalance : SatisfiesStrikingIdentity σ t φc) (y : ℝ) :
    ∫ x in Ioi (0 : ℝ), x⁻¹ * φc x (y / σ)
      = if y = 0 then 1 / t else y / (t * (Real.exp y - 1)) := by
  by_cases hy : y = 0
  · subst y
    simpa using hbalance.2
  · simpa [hy] using hbalance.1 y hy

/- Paper: p. 1074, ODE along each line.
   Plain recap: derivative of exp(−u/2 − (4/x) cosh(u/2)).
   PAPER NOTE: printed sinh sign is wrong; the consistent sign is minus. -/
theorem hasDerivAt_ode_solution (x u : ℝ) :
    HasDerivAt (fun u : ℝ => Real.exp (-u / 2 - 4 / x * Real.cosh (u / 2)))
      (Real.exp (-u / 2 - 4 / x * Real.cosh (u / 2)) * (-1 / 2 - 2 / x * Real.sinh (u / 2))) u := by
  have hhalf := (hasDerivAt_id (𝕜 := ℝ) u).div_const 2
  have hcosh := (Real.hasDerivAt_cosh (u / 2)).comp u hhalf
  have hlin :
      HasDerivAt (fun u : ℝ => -u / 2 - 4 / x * Real.cosh (u / 2))
        (-(1 / 2) - (4 / x) * (Real.sinh (u / 2) * (1 / 2))) u := by
    have h1 : HasDerivAt (fun u : ℝ => -(u / 2)) (-(1 / 2)) u := hhalf.neg
    have h2 : HasDerivAt (fun u : ℝ => (4 / x) * (Real.cosh ∘ (fun t => t / 2)) u)
        ((4 / x) * (Real.sinh (u / 2) * (1 / 2))) u := hcosh.const_mul _
    -- rewrite compositions to the written forms
    have h1' : HasDerivAt (fun u : ℝ => -u / 2) (-(1 / 2)) u := by
      convert h1 using 1; funext; ring
    have h2' : HasDerivAt (fun u : ℝ => (4 / x) * Real.cosh (u / 2))
        ((4 / x) * (Real.sinh (u / 2) * (1 / 2))) u := by
      convert h2 using 1; funext; rfl
    exact h1'.sub h2'
  convert hlin.exp using 1
  ring

/- The integrated ODE (4.5), with its integration constant fixed at `u = 0`.
   Analytic input for the algebraic rearrangement (4.6); establishing it for
   the conditional density is open. -/
def SatisfiesFoliationODE (σ t : ℝ) (φc : ℝ → ℝ → ℝ) : Prop :=
  ∀ x > 0, ∀ u : ℝ,
    φc (x / σ ^ 2 * Real.exp (u / 2)) (u / σ) =
      φc (x / σ ^ 2) 0 *
        Real.exp (-u / 2 - 4 / x * Real.cosh (u / 2) + 4 / x + u ^ 2 / (2 * σ ^ 2 * t))

/- Paper: p. 1075–1076, formula (4.6).
   Conditional rearrangement assuming `SatisfiesFoliationODE`. -/
theorem formula_4_6 (σ t : ℝ) (hσ : 0 < σ) (φc : ℝ → ℝ → ℝ)
    (hfol : SatisfiesFoliationODE σ t φc) (x y : ℝ) (hx : 0 < x) :
    φc x y =
      φc (x * Real.exp (-(σ * y) / 2)) 0 *
        Real.exp (-(σ * y) / 2 -
          2 / (σ ^ 2 * x) * (Real.exp (σ * y / 2) - 1) ^ 2 + y ^ 2 / (2 * t)) := by
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hbase : 0 < x * σ ^ 2 * Real.exp (-(σ * y) / 2) :=
    mul_pos (mul_pos hx (sq_pos_of_pos hσ)) (Real.exp_pos _)
  have h := hfol (x * σ ^ 2 * Real.exp (-(σ * y) / 2)) hbase (σ * y)
  rw [show (x * σ ^ 2 * Real.exp (-(σ * y) / 2)) / σ ^ 2 *
        Real.exp (σ * y / 2) = x by
      field_simp
      rw [← Real.exp_add]
      ring_nf
      simp] at h
  rw [show σ * y / σ = y by field_simp] at h
  rw [show (x * σ ^ 2 * Real.exp (-(σ * y) / 2)) / σ ^ 2 =
      x * Real.exp (-(σ * y) / 2) by field_simp] at h
  convert h using 1
  congr 2
  rw [Real.cosh_eq]
  simp_rw [show Real.exp (-(σ * y) / 2) = (Real.exp (σ * y / 2))⁻¹ by
    rw [← Real.exp_neg]
    congr 2
    ring]
  field_simp [Real.exp_ne_zero]
  have he : Real.exp (σ * y * (1 / 2)) * Real.exp (σ * y * (-1 / 2)) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 2
    ring
  ring_nf
  rw [he]
  ring

/- Paper: Remark 4.3 / Laplace transform of the conditional law of A_t^{-1}.
   Plain recap: L_{t,y}(u) = ∫ e^{-u/x} φ(x|y) dx. -/
def laplaceCond (φc : ℝ → ℝ → ℝ) (y u : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), Real.exp (-u / x) * φc x y

/- Paper: p. 1077, operator T_{t,y}.
   Plain recap: the transform used to characterize the Laplace transform uniquely. -/
def Top (_t _y : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ := f u

/-- Weierstrass step behind uniqueness of the Laplace transform: if all the "moments"
`∫ Tⁿ f` of an integrable `f` against a `[0,1]`-valued map `T` vanish, then `∫ (h ∘ T) f = 0`
for every `h` continuous on `[0,1]`. -/
private lemma integral_mul_eq_zero_of_moments {μ : Measure ℝ} {T f g h : ℝ → ℝ}
    (hT : Measurable T) (hT01 : ∀ᵐ x ∂μ, T x ∈ Icc (0 : ℝ) 1)
    (hf : Integrable f μ)
    (hmom : ∀ n : ℕ, ∫ x, T x ^ n * f x ∂μ = 0)
    (hh : ContinuousOn h (Icc 0 1))
    (hg : AEStronglyMeasurable g μ) (hgT : ∀ᵐ x ∂μ, g x = h (T x)) :
    ∫ x, g x * f x ∂μ = 0 := by
  have hint : ∀ n : ℕ, Integrable (fun x => T x ^ n * f x) μ := fun n =>
    hf.bdd_mul (c := 1) (hT.pow_const n).aestronglyMeasurable
      (hT01.mono fun x hx => by
        rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg hx.1]
        exact pow_le_one₀ hx.1 hx.2)
  have hpoly : ∀ p : Polynomial ℝ, Integrable (fun x => p.eval (T x) * f x) μ ∧
      ∫ x, p.eval (T x) * f x ∂μ = 0 := by
    intro p
    have heq : (fun x => p.eval (T x) * f x) =
        fun x => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (T x ^ i * f x) := by
      funext x
      rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [heq]
    refine ⟨integrable_finsetSum _ fun i _ => (hint i).const_mul _, ?_⟩
    rw [integral_finsetSum _ fun i _ => (hint i).const_mul _]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_const_mul, hmom, mul_zero]
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hh
  have hgf : Integrable (fun x => g x * f x) μ :=
    hf.bdd_mul (c := C) hg (by
      filter_upwards [hgT, hT01] with x hx hx01
      rw [hx]
      exact hC _ hx01)
  have hI : 0 ≤ ∫ x, ‖f x‖ ∂μ := integral_nonneg fun x => norm_nonneg _
  have hbound : ∀ ε > 0, |∫ x, g x * f x ∂μ| ≤ ε * ∫ x, ‖f x‖ ∂μ := by
    intro ε hε
    obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 h hh ε hε
    have h1 : ∫ x, g x * f x ∂μ = ∫ x, (g x - p.eval (T x)) * f x ∂μ := by
      have : (fun x => (g x - p.eval (T x)) * f x) =
          fun x => g x * f x - p.eval (T x) * f x := by
        funext x; ring
      rw [this, integral_sub hgf (hpoly p).1, (hpoly p).2, sub_zero]
    rw [h1]
    calc |∫ x, (g x - p.eval (T x)) * f x ∂μ|
        ≤ ∫ x, ‖(g x - p.eval (T x)) * f x‖ ∂μ := by
          rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
      _ ≤ ∫ x, ε * ‖f x‖ ∂μ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
            (hf.norm.const_mul ε) ?_
          filter_upwards [hgT, hT01] with x hx hx01
          rw [norm_mul, hx]
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          rw [Real.norm_eq_abs, abs_sub_comm]
          exact (hp _ hx01).le
      _ = ε * ∫ x, ‖f x‖ ∂μ := integral_const_mul _ _
  refine abs_nonpos_iff.mp (le_of_forall_pos_le_add fun δ hδ => ?_)
  have hI1 : 0 < (∫ x, ‖f x‖ ∂μ) + 1 := by linarith
  calc |∫ x, g x * f x ∂μ|
      ≤ δ / ((∫ x, ‖f x‖ ∂μ) + 1) * ∫ x, ‖f x‖ ∂μ := hbound _ (div_pos hδ hI1)
    _ ≤ δ / ((∫ x, ‖f x‖ ∂μ) + 1) * ((∫ x, ‖f x‖ ∂μ) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (div_pos hδ hI1).le
    _ = 0 + δ := by rw [div_mul_cancel₀ _ hI1.ne', zero_add]

/-- Uniqueness of the (inverse-argument) Laplace transform on `(0,∞)`: an integrable `f`
with `∫_{x>0} e^{-n/x} f(x) dx = 0` for all `n : ℕ` vanishes a.e. on `(0,∞)`. -/
private lemma ae_eq_zero_of_forall_integral_exp_neg_div_mul_eq_zero {f : ℝ → ℝ}
    (hf : Integrable f (volume.restrict (Ioi (0 : ℝ))))
    (hmom : ∀ n : ℕ, ∫ x in Ioi (0 : ℝ), Real.exp (-(n : ℝ) / x) * f x = 0) :
    ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)), f x = 0 := by
  set T : ℝ → ℝ := fun x => Real.exp (-1 / x) with hT_def
  have hTm : Measurable T :=
    Real.measurable_exp.comp (measurable_const.div measurable_id)
  have hTpos : ∀ x, 0 < T x := fun x => Real.exp_pos _
  have hTmono : ∀ x y : ℝ, 0 < x → x ≤ y → T x ≤ T y := by
    intro x y hx hxy
    refine Real.exp_le_exp.mpr ?_
    rw [neg_div, neg_div]
    exact neg_le_neg (one_div_le_one_div_of_le hx hxy)
  have hTlt1 : ∀ x : ℝ, 0 < x → T x < 1 := by
    intro x hx
    refine Real.exp_lt_one_iff.mpr ?_
    have : 0 < 1 / x := one_div_pos.mpr hx
    rw [neg_div]; linarith
  have hT01 : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)), T x ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact ⟨(hTpos x).le, (hTlt1 x hx).le⟩
  have hTpow : ∀ (n : ℕ) (x : ℝ), T x ^ n = Real.exp (-(n : ℝ) / x) := by
    intro n x
    simp only [hT_def]
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hmom' : ∀ n : ℕ, ∫ x in Ioi (0 : ℝ), T x ^ n * f x = 0 := by
    intro n; simp_rw [hTpow]; exact hmom n
  have hinv : ∀ y : ℝ, 0 < y → -1 / Real.log (T y) = y := by
    intro y hy
    simp only [hT_def]
    rw [Real.log_exp]; field_simp
  have hzero : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioi (0 : ℝ) → f x = 0 := by
    refine isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (IntegrableOn.locallyIntegrableOn hf) ?_
    intro g hgs hgc hgsupp
    have hg0 : ∀ x, x ∉ tsupport g → g x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport hx
    -- `g` vanishes on `(-∞, a]` and on `[b, ∞)` for some `0 < a < b`.
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isClosed_tsupport g).isOpen_compl 0
      (fun h0 => lt_irrefl (0 : ℝ) (hgsupp h0))
    obtain ⟨R, hR⟩ := hgc.isCompact.bddAbove
    set a : ℝ := ε / 2 with ha_def
    set b : ℝ := max (R + 1) (a + 1) with hb_def
    have ha : 0 < a := by positivity
    have hab : a < b := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hb : 0 < b := ha.trans hab
    have hga : ∀ x, x ≤ a → g x = 0 := by
      intro x hx
      by_cases hx0 : 0 < x
      · refine hg0 x (hball ?_)
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx0]
        linarith
      · exact hg0 x fun hmem => hx0 (hgsupp hmem)
    have hgb : ∀ x, b ≤ x → g x = 0 := by
      intro x hx
      refine hg0 x fun hmem => ?_
      have h1 : x ≤ R := hR hmem
      have h2 : R + 1 ≤ b := le_max_left _ _
      linarith
    set α : ℝ := T a with hα_def
    set β : ℝ := T b with hβ_def
    have hαβ : α ≤ β := hTmono a b ha hab.le
    set c : ℝ → ℝ := fun t => max α (min β t) with hc_def
    have hcα : ∀ t, α ≤ c t := fun t => le_max_left _ _
    have hcβ : ∀ t, c t ≤ β := fun t => max_le hαβ (min_le_left _ _)
    have hcpos : ∀ t, 0 < c t := fun t => (hTpos a).trans_le (hcα t)
    have hclog : ∀ t, Real.log (c t) ≠ 0 := by
      intro t
      refine (Real.log_neg (hcpos t) ((hcβ t).trans_lt (hTlt1 b hb))).ne
    have hccont : Continuous c := continuous_const.max (continuous_const.min continuous_id)
    set h : ℝ → ℝ := fun t => g (-1 / Real.log (c t)) with hh_def
    have hhcont : Continuous h :=
      hgs.continuous.comp
        (continuous_const.div (hccont.log fun t => (hcpos t).ne') hclog)
    have hgT : ∀ x, 0 < x → g x = h (T x) := by
      intro x hx
      simp only [hh_def]
      rcases le_or_gt x a with hxa | hxa
      · have h1 : c (T x) = T a := by
          have hTx : T x ≤ α := hTmono x a hx hxa
          simp only [hc_def]
          rw [min_eq_right (hTx.trans hαβ), max_eq_left hTx]
        rw [h1, hinv a ha, hga x hxa, hga a le_rfl]
      · rcases le_or_gt b x with hbx | hbx
        · have h1 : c (T x) = T b := by
            have hTx : β ≤ T x := hTmono b x hb hbx
            simp only [hc_def]
            rw [min_eq_left hTx, max_eq_right hαβ]
          rw [h1, hinv b hb, hgb x hbx, hgb b le_rfl]
        · have h1 : c (T x) = T x := by
            have hTx1 : α ≤ T x := hTmono a x ha hxa.le
            have hTx2 : T x ≤ β := hTmono x b hx hbx.le
            simp only [hc_def]
            rw [min_eq_right hTx2, max_eq_right hTx1]
          rw [h1, hinv x hx]
    have hout : ∀ x, x ∉ Ioi (0 : ℝ) → g x • f x = 0 := by
      intro x hx
      rw [hg0 x fun hmem => hx (hgsupp hmem), zero_smul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout]
    simp only [smul_eq_mul]
    refine integral_mul_eq_zero_of_moments hTm hT01 hf hmom' hhcont.continuousOn
      hgs.continuous.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hgT x hx
  exact (ae_restrict_iff' measurableSet_Ioi).mpr hzero

/- Paper: p. 1077, Proposition 4.4.  The paper invokes uniqueness of the
   Laplace transform; measurability and integrability are the missing hypotheses
   in the informal statement. -/
theorem prop_4_4 (φ ψ : ℝ → ℝ)
    (_hφm : AEStronglyMeasurable φ (volume.restrict (Ioi 0)))
    (_hψm : AEStronglyMeasurable ψ (volume.restrict (Ioi 0)))
    (hφi : Integrable φ (volume.restrict (Ioi 0)))
    (hψi : Integrable ψ (volume.restrict (Ioi 0)))
    (hφ : ∀ u ≥ 0, laplaceCond (fun x _ => φ x) 0 u =
      laplaceCond (fun x _ => ψ x) 0 u) :
    ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)), φ x = ψ x := by
  -- Uniqueness of Laplace transforms on (0,∞), applied to `φ - ψ`.
  have hbdd : ∀ (n : ℕ) {χ : ℝ → ℝ}, Integrable χ (volume.restrict (Ioi (0 : ℝ))) →
      Integrable (fun x => Real.exp (-(n : ℝ) / x) * χ x) (volume.restrict (Ioi (0 : ℝ))) := by
    intro n χ hχ
    refine hχ.bdd_mul (c := 1)
      (Real.measurable_exp.comp (measurable_const.div measurable_id)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_one_iff.mpr ?_
    have : 0 ≤ (n : ℝ) / x := div_nonneg (Nat.cast_nonneg n) (le_of_lt hx)
    rw [neg_div]; linarith
  have hzero := ae_eq_zero_of_forall_integral_exp_neg_div_mul_eq_zero
    (f := fun x => φ x - ψ x) (hφi.sub hψi) (by
      intro n
      have h := hφ n (Nat.cast_nonneg n)
      simp only [laplaceCond] at h
      simp_rw [mul_sub]
      rw [integral_sub (hbdd n hφi) (hbdd n hψi), h, sub_self])
  filter_upwards [hzero] with x hx
  exact sub_eq_zero.mp hx

/- Equation (4.7): transformed mass identity at the zero endpoint (hypothesis;
   not yet proved for the conditional density). -/
def TransformedMassIdentity (σ t : ℝ) (φ0 : ℝ → ℝ) : Prop :=
  ∀ z : ℝ,
    ∫ x in Ioi (0 : ℝ),
      φ0 x * Real.exp (-4 / (σ ^ 2 * x) * (Real.cosh (σ * z / 2) - 1)) =
        Real.exp (-z ^ 2 / (2 * t))

/- Change-of-variables reduction in the proof of Theorem 4.5 (hypothesis). -/
def HasLaplaceReduction (σ t : ℝ) (φc : ℝ → ℝ → ℝ) : Prop :=
  ∀ y u : ℝ, 0 ≤ u →
    laplaceCond φc y u =
      Real.exp (y ^ 2 / (2 * t)) *
        ∫ x in Ioi (0 : ℝ), φc x 0 *
          Real.exp (-4 / (σ ^ 2 * x) *
            (u * σ ^ 2 / 4 * Real.exp (-(σ * y) / 2) + Real.cosh (σ * y / 2) - 1))

/- Paper: p. 1078, Theorem 4.5.
   Conditional closed form for the Laplace transform via arcosh, assuming
   `TransformedMassIdentity` and `HasLaplaceReduction`. -/
theorem theorem_4_5 (σ t : ℝ) (hσ : 0 < σ) (ht : 0 < t)
    (φc : ℝ → ℝ → ℝ) (hmass : TransformedMassIdentity σ t (fun x => φc x 0))
    (hreduce : HasLaplaceReduction σ t φc) (y u : ℝ) (hu : 0 ≤ u) :
    laplaceCond φc y u =
      Real.exp (y ^ 2 / (2 * t) -
        2 / (σ ^ 2 * t) *
          Real.arcosh (Real.cosh (σ * y / 2) +
            u * σ ^ 2 / 4 * Real.exp (-(σ * y) / 2)) ^ 2) := by
  let A := Real.cosh (σ * y / 2) +
    u * σ ^ 2 / 4 * Real.exp (-(σ * y) / 2)
  let z := 2 / σ * Real.arcosh A
  have hA : 1 ≤ A := by
    dsimp [A]
    have hnonneg : 0 ≤ u * σ ^ 2 / 4 * Real.exp (-(σ * y) / 2) :=
      mul_nonneg (div_nonneg (mul_nonneg hu (sq_nonneg σ)) (by norm_num)) (Real.exp_pos _).le
    linarith [Real.one_le_cosh (σ * y / 2)]
  have hz : Real.cosh (σ * z / 2) = A := by
    dsimp [z]
    rw [show σ * (2 / σ * Real.arcosh A) / 2 = Real.arcosh A by
      field_simp [hσ.ne']]
    exact Real.cosh_arcosh hA
  rw [hreduce y u hu]
  have hm := hmass z
  rw [hz] at hm
  rw [show u * σ ^ 2 / 4 * Real.exp (-(σ * y) / 2) +
      Real.cosh (σ * y / 2) - 1 = A - 1 by simp [A, add_comm]] 
  rw [hm, ← Real.exp_add]
  congr 2
  dsimp [z, A]
  field_simp [hσ.ne', ht.ne']

/- Paper: corollary of Thm 4.5 recovering (4.4).
   Plain recap: differentiating the Laplace closed form yields the striking identity. -/
theorem striking_from_laplace (σ t : ℝ)
    (φc : ℝ → ℝ → ℝ) (hbalance : SatisfiesStrikingIdentity σ t φc) (y : ℝ) :
    ∫ x in Ioi (0 : ℝ), x⁻¹ * φc x (y / σ)
      = if y = 0 then 1 / t else y / (t * (Real.exp y - 1)) :=
  theorem_4_1_striking σ t φc hbalance y

/- Paper: p. 1079, negative moments at y = 0 (first few).
   Plain recap: Taylor expansion of L_{t,0}(u) gives E[A_t^{-p} | W_t=0]. -/
def negMomentFormula (t : ℝ) (p : ℕ) : ℝ :=
  match p with
  | 0 => 1
  | 1 => 1 / t
  | 2 => 1 / (12 * t) + 1 / t ^ 2
  | 3 => 1 / (60 * t) + 1 / (4 * t ^ 2) + 1 / t ^ 3
  | _ => 0

def HasNegativeMomentsUpToThree (t : ℝ) (φc : ℝ → ℝ → ℝ) : Prop :=
  ∀ p : ℕ, p ≤ 3 →
    ∫ x in Ioi (0 : ℝ), (x : ℝ) ^ (-(p : ℤ)) * φc x 0 = negMomentFormula t p

theorem neg_moments_at_zero (t : ℝ) (φc : ℝ → ℝ → ℝ)
    (hmom : HasNegativeMomentsUpToThree t φc) (p : ℕ) (hp : p ≤ 3) :
    ∫ x in Ioi (0 : ℝ), (x : ℝ) ^ (-(p : ℤ)) * φc x 0 = negMomentFormula t p :=
  hmom p hp

/- Paper: Remark 4.6.
   Plain recap: the striking identity is the p = 1 case of the negative-moment formulae. -/
theorem remark_4_6 (t : ℝ) (φc : ℝ → ℝ → ℝ)
    (hmom : HasNegativeMomentsUpToThree t φc) :
    ∫ x in Ioi (0 : ℝ), x⁻¹ * φc x 0 = 1 / t := by
  simpa [negMomentFormula] using neg_moments_at_zero t φc hmom 1 (by norm_num)

/-! ## Open: analytic inputs for the conditional density

The Comparator theorems above are conditional rearrangements. The holes below ask for
those inputs on a genuine conditional density of `(expInt, W)`. -/

/-- Open: some conditional density of `(expInt, W)` satisfies the Thm 4.1 transport PDE. -/
theorem cond_density_satisfies_theorem_41_pde (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (_hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (_hσ : 0 < σ) (_ht : 0 < t) :
    ∃ φc : ℝ → ℝ → ℝ, IsCondDensity P W σ t φc ∧ SatisfiesTheorem41PDE σ t φc := by
  sorry

/-- Open: some conditional density satisfies the striking reciprocal-moment identity (4.4). -/
theorem cond_density_satisfies_striking (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (_hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (_hσ : 0 < σ) (_ht : 0 < t) :
    ∃ φc : ℝ → ℝ → ℝ, IsCondDensity P W σ t φc ∧ SatisfiesStrikingIdentity σ t φc := by
  sorry

/-- Open: some conditional density satisfies the integrated foliation ODE (4.5). -/
theorem cond_density_satisfies_foliation_ode (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (_hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (_hσ : 0 < σ) (_ht : 0 < t) :
    ∃ φc : ℝ → ℝ → ℝ, IsCondDensity P W σ t φc ∧ SatisfiesFoliationODE σ t φc := by
  sorry

/-- Open: some conditional density satisfies the Thm 4.5 mass + Laplace-reduction inputs. -/
theorem cond_density_satisfies_laplace_inputs (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (_hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (_hσ : 0 < σ) (_ht : 0 < t) :
    ∃ φc : ℝ → ℝ → ℝ,
      IsCondDensity P W σ t φc ∧
        TransformedMassIdentity σ t (fun x => φc x 0) ∧ HasLaplaceReduction σ t φc := by
  sorry

end Lyasoff2016
