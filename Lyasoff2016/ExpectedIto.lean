/-
Expected Itô formula for functionals of `(∫₀ᵗ a(B_s) ds, B_t)` and the
distributional Fokker–Planck / Laplace-transform characterization of `(∫₀ᵗ e^{2 W_s} ds, W_t)`.

Used to prove `yor_formula` (and hence `prop_2_2`) without circularity.
-/
module

public import Lyasoff2016.Setting
public import Lyasoff2016.IntegralMoments
public import MathFin.Probability.Brownian.Ito.ItoFormulaTDRemainder
public import MathFin.Probability.Brownian.WeightedQuadraticVariation

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

open MathFin ItoIntegralL2 ItoIsometryAdapted QuadraticVariationL2

section ExpectedItoPath

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- For a continuous function `g : ℝ≥0 → ℝ` and `s : ℝ≥0`, the `Ioc 0 s` integral against
`ItoIntegralL2.timeMeasure` equals the interval integral `∫ r in 0..(s : ℝ), g r.toNNReal`. -/
lemma timeMeasure_Ioc_eq_intervalIntegral (g : ℝ≥0 → ℝ) (s : ℝ≥0) :
    ∫ r in Ioc (0 : ℝ≥0) s, g r ∂timeMeasure =
      ∫ r in (0 : ℝ)..(s : ℝ), g r.toNNReal := by
  simpa using ItoIntegralProcessGeneral.timeMeasure_Ioc_eq_interval (g := g) s

private lemma measurable_of_tendsto_real' {Ω : Type*} (m : MeasurableSpace Ω)
    {S : ℕ → Ω → ℝ} {g : Ω → ℝ} (hS : ∀ n, Measurable[m] (S n))
    (hlim : ∀ ω, Tendsto (fun n => S n ω) atTop (nhds (g ω))) :
    Measurable[m] g :=
  measurable_of_tendsto_metrizable hS (tendsto_pi_nhds.mpr hlim)

/-- Pathwise integral `A s ω = ∫ r in 0..(s : ℝ), a (B r.toNNReal ω)` is adapted to the
natural filtration of `B` when `B` has continuous paths and measurable marginals. -/
lemma measurable_pathIntegral_natFiltration
    {B : ℝ≥0 → Ω → ℝ} (hBmeas : ∀ s, Measurable (B s)) (hBcont : ∀ ω, Continuous (B · ω))
    {a : ℝ → ℝ} (ha : Continuous a) (s : ℝ≥0) :
    Measurable[natFiltration hBmeas s]
      (fun ω => ∫ r in (0 : ℝ)..(s : ℝ), a (B r.toNNReal ω)) := by
  let S : ℕ → Ω → ℝ := fun n ω =>
    ∑ k ∈ Finset.range n,
      a (B (unifPart s n k) ω) * ((unifPart s n (k + 1) : ℝ) - unifPart s n k)
  have hSmeas : ∀ n, Measurable[natFiltration hBmeas s] (S n) := by
    intro n
    have hterm : ∀ k ∈ Finset.range n, Measurable[natFiltration hBmeas s] (fun ω =>
        a (B (unifPart s n k) ω) * ((unifPart s n (k + 1) : ℝ) - unifPart s n k)) := by
      intro k hk
      have hk_le : unifPart s n k ≤ s := unifPart_le_T (Finset.mem_range.mp hk).le
      have hBk : Measurable[natFiltration hBmeas s] (fun ω => B (unifPart s n k) ω) :=
        ((stronglyAdapted_natFiltration hBmeas (unifPart s n k)).measurable).mono
          ((natFiltration hBmeas).mono hk_le) le_rfl
      exact (ha.measurable.comp (mα := natFiltration hBmeas s) hBk).mul_const _
    exact Finset.measurable_fun_sum (m := natFiltration hBmeas s) _ hterm
  have hlim : ∀ ω, Tendsto (fun n => S n ω) atTop
      (nhds (∫ r in (0 : ℝ)..(s : ℝ), a (B r.toNNReal ω))) := by
    intro ω
    have hcont : Continuous fun r : ℝ≥0 => a (B r ω) := ha.comp (hBcont ω)
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := s)).bddAbove_image
      (hcont.abs.continuousOn)
    have hbdd : ∀ r ≤ s, |a (B r ω)| ≤ M := fun r hr =>
      hM (mem_image_of_mem _ ⟨zero_le, hr⟩)
    have htend := tendsto_riemann_continuous hcont s hbdd
    rwa [timeMeasure_Ioc_eq_intervalIntegral] at htend
  exact measurable_of_tendsto_real' (natFiltration hBmeas s) hSmeas hlim

/-- Elementary AM-GM bound: for `δ > 0` and any `u, v : ℝ`,
`2 * |u| * |v| ≤ δ * u ^ 2 + δ⁻¹ * v ^ 2`. -/
lemma two_mul_abs_mul_le {δ : ℝ} (hδ : 0 < δ) (u v : ℝ) :
    2 * |u| * |v| ≤ δ * u ^ 2 + δ⁻¹ * v ^ 2 := by
  have h : 0 ≤ (√δ * |u| - (√δ)⁻¹ * |v|) ^ 2 := sq_nonneg _
  have hs : √δ * (√δ)⁻¹ = 1 := mul_inv_cancel₀ (Real.sqrt_pos.mpr hδ).ne'
  have hsq1 : (√δ) ^ 2 = δ := Real.sq_sqrt hδ.le
  have hsq2 : ((√δ)⁻¹) ^ 2 = δ⁻¹ := by rw [inv_pow, hsq1]
  have expand : (√δ * |u| - (√δ)⁻¹ * |v|) ^ 2 =
      δ * u ^ 2 - 2 * |u| * |v| + δ⁻¹ * v ^ 2 := by
    calc (√δ * |u| - (√δ)⁻¹ * |v|) ^ 2
        = (√δ) ^ 2 * |u| ^ 2 - 2 * (√δ * (√δ)⁻¹) * |u| * |v| + ((√δ)⁻¹) ^ 2 * |v| ^ 2 := by ring
      _ = δ * u ^ 2 - 2 * |u| * |v| + δ⁻¹ * v ^ 2 := by
          rw [hsq1, hsq2, hs, sq_abs, sq_abs]; ring
  linarith

/-- Cubic bound via quadratic and quartic powers: for `δ > 0` and any `u : ℝ`,
`2 * |u| ^ 3 ≤ δ * u ^ 2 + δ⁻¹ * u ^ 4`. -/
lemma two_mul_abs_cube_le {δ : ℝ} (hδ : 0 < δ) (u : ℝ) :
    2 * |u| ^ 3 ≤ δ * u ^ 2 + δ⁻¹ * u ^ 4 := by
  have h := two_mul_abs_mul_le hδ u (u ^ 2)
  rw [abs_pow, sq_abs, show (u ^ 2) ^ 2 = u ^ 4 by ring] at h
  calc 2 * |u| ^ 3 = 2 * |u| * u ^ 2 := by rw [← sq_abs u]; ring
    _ ≤ δ * u ^ 2 + δ⁻¹ * u ^ 4 := h

/-- Continuity of `s ↦ ∫ r in 0..(s : ℝ), g r.toNNReal` for continuous `g : ℝ≥0 → ℝ`. -/
lemma continuous_pathIntegral_nnreal {g : ℝ≥0 → ℝ} (hg : Continuous g) :
    Continuous fun s : ℝ≥0 => ∫ r in (0 : ℝ)..(s : ℝ), g r.toNNReal := by
  have hcontR : Continuous fun r : ℝ => g r.toNNReal := hg.comp continuous_real_toNNReal
  exact (intervalIntegral.continuous_primitive (fun a b => hcontR.intervalIntegrable a b) 0).comp
    NNReal.continuous_coe

/-- Convergence of the weighted path-integral sum `∑ F_x(A_{t_k}, B_{t_k}) (A_{t_{k+1}} - A_{t_k})`
for a single path. -/
private lemma tendsto_sum_mul_increment_path
    {t : ℝ≥0} (ht : 0 < t) {h g : ℝ≥0 → ℝ} (hh : Continuous h) (hg : Continuous g)
    {C : ℝ} (hbd : ∀ s ≤ t, |h s| ≤ C) :
    Tendsto (fun n : ℕ =>
        ∑ k ∈ Finset.range n,
          h (unifPart t n k) *
            ((∫ r in (0 : ℝ)..(unifPart t n (k + 1) : ℝ), g r.toNNReal) -
             (∫ r in (0 : ℝ)..(unifPart t n k : ℝ), g r.toNNReal)))
      atTop (𝓝 (∫ r in (0 : ℝ)..(t : ℝ), h r.toNNReal * g r.toNNReal)) := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hbd 0 zero_le)
  have hg_contR : Continuous fun r : ℝ => g r.toNNReal := hg.comp continuous_real_toNNReal
  have hh_contR : Continuous fun r : ℝ => h r.toNNReal := hh.comp continuous_real_toNNReal
  have hR_lim : Tendsto (fun n : ℕ =>
      ∑ k ∈ Finset.range n,
        (h (unifPart t n k) * g (unifPart t n k)) *
          ((unifPart t n (k + 1) : ℝ) - unifPart t n k))
      atTop (𝓝 (∫ r in (0 : ℝ)..(t : ℝ), h r.toNNReal * g r.toNNReal)) := by
    obtain ⟨Mg, hMg⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).bddAbove_image
      hg.abs.continuousOn
    have hbd2 : ∀ s ≤ t, |h s * g s| ≤ C * Mg := fun s hs => by
      rw [abs_mul]
      exact mul_le_mul (hbd s hs) (hMg (mem_image_of_mem _ ⟨zero_le, hs⟩)) (abs_nonneg _) hC0
    have htend := tendsto_riemann_continuous (hh.mul hg) t hbd2
    simpa [timeMeasure_Ioc_eq_intervalIntegral] using htend
  have hdiff : Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.range n,
        h (unifPart t n k) *
          ((∫ r in (0 : ℝ)..(unifPart t n (k + 1) : ℝ), g r.toNNReal) -
           (∫ r in (0 : ℝ)..(unifPart t n k : ℝ), g r.toNNReal))) -
      (∑ k ∈ Finset.range n,
        (h (unifPart t n k) * g (unifPart t n k)) *
          ((unifPart t n (k + 1) : ℝ) - unifPart t n k)))
      atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have htpos : (0 : ℝ) < t := ht
    have huc : UniformContinuousOn (fun r : ℝ => g r.toNNReal) (Icc 0 (t : ℝ)) :=
      isCompact_Icc.uniformContinuousOn_of_continuous hg_contR.continuousOn
    obtain ⟨δ, hδ, hδ_unif⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / ((C + 1) * t))
      (div_pos hε (mul_pos (by linarith) htpos))
    obtain ⟨N, hN⟩ := exists_nat_gt ((t : ℝ) / δ)
    refine ⟨max N 1, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn1
    have hN' : (t : ℝ) / δ < n := lt_of_lt_of_le hN (Nat.cast_le.mpr (le_trans (le_max_left _ _) hn))
    have hgap : (t : ℝ) / n < δ := (div_lt_iff₀ (Nat.cast_pos.mpr hn1)).mpr
      ((div_lt_iff₀ hδ).mp hN' |> fun h => by linarith)
    rw [Real.dist_eq, sub_zero, ← Finset.sum_sub_distrib]
    have hterm : ∀ k ∈ Finset.range n,
        |h (unifPart t n k) *
            ((∫ r in (0 : ℝ)..(unifPart t n (k + 1) : ℝ), g r.toNNReal) -
             (∫ r in (0 : ℝ)..(unifPart t n k : ℝ), g r.toNNReal)) -
          (h (unifPart t n k) * g (unifPart t n k)) *
            ((unifPart t n (k + 1) : ℝ) - unifPart t n k)| ≤
          C * (ε / ((C + 1) * t)) * ((t : ℝ) / n) := by
      intro k hk
      have hk_lt : k < n := Finset.mem_range.mp hk
      have hk_le : unifPart t n k ≤ t := unifPart_le_T hk_lt.le
      have hk1_le : unifPart t n (k + 1) ≤ t := unifPart_le_T hk_lt
      have hsub_le : (unifPart t n k : ℝ) ≤ unifPart t n (k + 1) :=
        NNReal.coe_le_coe.mpr (unifPart_mono t n (Nat.le_succ k))
      have hint : (∫ r in (0 : ℝ)..(unifPart t n (k + 1) : ℝ), g r.toNNReal) -
          (∫ r in (0 : ℝ)..(unifPart t n k : ℝ), g r.toNNReal) =
          ∫ r in (unifPart t n k : ℝ)..(unifPart t n (k + 1) : ℝ), g r.toNNReal := by
        rw [sub_eq_iff_eq_add']
        exact (intervalIntegral.integral_add_adjacent_intervals
          (hg_contR.intervalIntegrable _ _) (hg_contR.intervalIntegrable _ _)).symm
      have hconst : g (unifPart t n k) * ((unifPart t n (k + 1) : ℝ) - unifPart t n k) =
          ∫ _ in (unifPart t n k : ℝ)..(unifPart t n (k + 1) : ℝ), g (unifPart t n k) := by
        simp [mul_comm]
      have hdiff_int :
          ((∫ r in (0 : ℝ)..(unifPart t n (k + 1) : ℝ), g r.toNNReal) -
           (∫ r in (0 : ℝ)..(unifPart t n k : ℝ), g r.toNNReal)) -
          g (unifPart t n k) * ((unifPart t n (k + 1) : ℝ) - unifPart t n k) =
          ∫ r in (unifPart t n k : ℝ)..(unifPart t n (k + 1) : ℝ),
            (g r.toNNReal - g (unifPart t n k)) := by
        rw [hint, hconst, intervalIntegral.integral_sub (hg_contR.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _)]
      have hfactor :
          h (unifPart t n k) *
              ((∫ r in (0 : ℝ)..(unifPart t n (k + 1) : ℝ), g r.toNNReal) -
               (∫ r in (0 : ℝ)..(unifPart t n k : ℝ), g r.toNNReal)) -
            (h (unifPart t n k) * g (unifPart t n k)) *
              ((unifPart t n (k + 1) : ℝ) - unifPart t n k) =
          h (unifPart t n k) *
            ∫ r in (unifPart t n k : ℝ)..(unifPart t n (k + 1) : ℝ),
              (g r.toNNReal - g (unifPart t n k)) := by
        rw [← hdiff_int]; ring
      rw [hfactor, abs_mul]
      have hbd_k : |h (unifPart t n k)| ≤ C := hbd _ hk_le
      have hint_bd : |∫ r in (unifPart t n k : ℝ)..(unifPart t n (k + 1) : ℝ),
            (g r.toNNReal - g (unifPart t n k))| ≤ ε / ((C + 1) * t) * ((t : ℝ) / n) := by
        have hle_int : |∫ r in (unifPart t n k : ℝ)..(unifPart t n (k + 1) : ℝ),
            (g r.toNNReal - g (unifPart t n k))| ≤
            ∫ r in (unifPart t n k : ℝ)..(unifPart t n (k + 1) : ℝ),
              |g r.toNNReal - g (unifPart t n k)| :=
          intervalIntegral.abs_integral_le_integral_abs hsub_le
        refine hle_int.trans ?_
        have hpt : ∀ r ∈ Icc (unifPart t n k : ℝ) (unifPart t n (k + 1) : ℝ),
            |g r.toNNReal - g (unifPart t n k)| ≤ ε / ((C + 1) * t) := by
          intro r hr
          have hrI : r ∈ Icc 0 (t : ℝ) := ⟨le_trans (unifPart t n k).coe_nonneg hr.1,
            le_trans hr.2 (NNReal.coe_le_coe.mpr hk1_le)⟩
          have hkI : (unifPart t n k : ℝ) ∈ Icc 0 (t : ℝ) :=
            ⟨(unifPart t n k).coe_nonneg, NNReal.coe_le_coe.mpr hk_le⟩
          have hdist : dist r (unifPart t n k : ℝ) < δ := by
            rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hr.1)]
            have : (unifPart t n (k + 1) : ℝ) - unifPart t n k = (t : ℝ) / n :=
              unifPart_succ_sub t n k
            linarith [hr.2]
          have h := hδ_unif r hrI (unifPart t n k : ℝ) hkI hdist
          rw [Real.dist_eq, Real.toNNReal_coe] at h
          exact h.le
        have hmono := intervalIntegral.integral_mono_on (μ := volume) hsub_le
          ((hg_contR.sub continuous_const).abs.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _) hpt
        rw [intervalIntegral.integral_const, smul_eq_mul, unifPart_succ_sub, mul_comm] at hmono
        exact hmono
      calc |h (unifPart t n k)| * |∫ r in (unifPart t n k : ℝ)..(unifPart t n (k + 1) : ℝ),
              (g r.toNNReal - g (unifPart t n k))|
          ≤ C * (ε / ((C + 1) * t) * ((t : ℝ) / n)) :=
            mul_le_mul hbd_k hint_bd (abs_nonneg _) hC0
        _ = C * (ε / ((C + 1) * t)) * ((t : ℝ) / n) := by ring
    calc |∑ k ∈ Finset.range n, _|
        ≤ ∑ k ∈ Finset.range n, |_| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.range n, C * (ε / ((C + 1) * t)) * ((t : ℝ) / n) :=
          Finset.sum_le_sum hterm
      _ = n * (C * (ε / ((C + 1) * t)) * ((t : ℝ) / n)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = C / (C + 1) * ε := by
          have hn_real : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
          field_simp
      _ < ε := by
          have hC1 : C / (C + 1) < 1 := by
            rw [div_lt_one (by linarith)]; linarith
          nlinarith
  simpa using hdiff.add hR_lim

/-- **Expected Itô formula for `(A_t, B_t)`** where `A_t = ∫₀ᵗ a(B_s) ds` and `B` is a
continuous pre-Brownian motion with `B 0 = 0` a.s.
For `F(x, y)` of class `C^{2,3}` (with `F_yy` jointly continuous and all partials bounded on
`ℝ × ℝ`) and `E[(sup_{s ≤ T} |a(B_s)|)^2] < ∞`,
`E[F(A_t, B_t)] - F 0 0 = ∫₀ᵗ E[F_x(A_s, B_s) * a(B_s) + (1/2) * F_yy(A_s, B_s)] ds`. -/
theorem expected_ito_integral_path
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P) (hBmeas : ∀ s, Measurable (B s))
    (hBcont : ∀ ω, Continuous (B · ω)) (hB0 : ∀ᵐ ω ∂P, B 0 ω = 0)
    (a : ℝ → ℝ) (ha : Continuous a)
    (T : ℝ≥0) (ha_sup : Integrable (fun ω => (⨆ i : Iic T, |a (B i ω)|) ^ 2) P)
    (F F_x F_y F_xx F_xy F_yy F_yyy : ℝ → ℝ → ℝ)
    (hF_x : ∀ x y, HasDerivAt (fun x' => F x' y) (F_x x y) x)
    (hF_xx : ∀ x y, HasDerivAt (fun x' => F_x x' y) (F_xx x y) x)
    (hF_xy : ∀ x y, HasDerivAt (fun y' => F_x x y') (F_xy x y) y)
    (hF_y : ∀ x y, HasDerivAt (fun y' => F x y') (F_y x y) y)
    (hF_yy : ∀ x y, HasDerivAt (fun y' => F_y x y') (F_yy x y) y)
    (hF_yyy : ∀ x y, HasDerivAt (fun y' => F_yy x y') (F_yyy x y) y)
    (hF_yy_cont : Continuous (Function.uncurry F_yy))
    {M : ℝ} (hM : 0 ≤ M)
    (hbd_F : ∀ x y, |F x y| ≤ M)
    (hbd_x : ∀ x y, |F_x x y| ≤ M)
    (hbd_y : ∀ x y, |F_y x y| ≤ M)
    (hbd_xx : ∀ x y, |F_xx x y| ≤ M)
    (hbd_xy : ∀ x y, |F_xy x y| ≤ M)
    (hbd_yy : ∀ x y, |F_yy x y| ≤ M)
    (hbd_yyy : ∀ x y, |F_yyy x y| ≤ M)
    (t : ℝ≥0) (ht : t ≤ T) :
    ∫ ω, F (∫ r in (0 : ℝ)..(t : ℝ), a (B r.toNNReal ω)) (B t ω) ∂P - F 0 0 =
      ∫ s in (0 : ℝ)..(t : ℝ),
        ∫ ω, (F_x (∫ r in (0 : ℝ)..s, a (B r.toNNReal ω)) (B s.toNNReal ω) *
            a (B s.toNNReal ω) +
          (1 / 2 : ℝ) * F_yy (∫ r in (0 : ℝ)..s, a (B r.toNNReal ω)) (B s.toNNReal ω)) ∂P := by
  let A : ℝ≥0 → Ω → ℝ := fun s ω => ∫ r in (0 : ℝ)..(s : ℝ), a (B r.toNNReal ω)
  let 𝓕 : Filtration ℝ≥0 mΩ := natFiltration (mΩ := mΩ) hBmeas
  have hFB : IsFilteredPreBrownian B 𝓕 P := hB.isFilteredPreBrownian hBmeas
  have hF_cont : Continuous (Function.uncurry F) :=
    continuous_uncurry_of_bdd_partials hF_x hF_y hbd_x hbd_y
  have hFx_cont : Continuous (Function.uncurry F_x) :=
    continuous_uncurry_of_bdd_partials hF_xx hF_xy hbd_xx hbd_xy
  have hFy_meas : Measurable (Function.uncurry F_y) := by
    have hlim : ∀ p : ℝ × ℝ, Tendsto
        (fun n : ℕ => ((n : ℝ) + 1) * (F p.1 (p.2 + ((n : ℝ) + 1)⁻¹) - F p.1 p.2))
        atTop (nhds (F_y p.1 p.2)) := by
      intro p
      have hd := (hF_y p.1 p.2).tendsto_slope_zero_right
      have htend : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝[>] 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          (tendsto_inv_atTop_zero.comp
            (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
          (Eventually.of_forall fun n => inv_pos.mpr (by positivity))
      refine (hd.comp htend).congr (fun n => ?_)
      simp only [Function.comp_apply, smul_eq_mul, inv_inv]
    refine measurable_of_tendsto_metrizable (fun n => ?_) (tendsto_pi_nhds.mpr hlim)
    exact measurable_const.mul ((hF_cont.measurable.comp
      (measurable_fst.prodMk (measurable_snd.add_const _))).sub hF_cont.measurable)
  have hA_cont : ∀ ω, Continuous (A · ω) := fun ω =>
    continuous_pathIntegral_nnreal (ha.comp (hBcont ω))
  have hA_adapted : ∀ s, Measurable[𝓕 s] (A s) := fun s =>
    measurable_pathIntegral_natFiltration hBmeas hBcont ha s
  have hA_meas : ∀ s, Measurable (A s) := fun s => (hA_adapted s).mono (𝓕.le s) le_rfl
  by_cases ht0 : t = 0
  · subst ht0
    simp only [NNReal.coe_zero, intervalIntegral.integral_same, sub_eq_zero]
    have h1 : Integrable (fun ω => F 0 (B 0 ω)) P :=
      Integrable.of_bound
        ((hF_cont.comp (continuous_const.prodMk continuous_id)).measurable.comp
          (hBmeas 0)).aestronglyMeasurable
        M (ae_of_all _ fun ω => hbd_F _ _)
    have heq : (fun ω => F 0 (B 0 ω) - F 0 0) =ᵐ[P] 0 := hB0.mono fun ω h0 => by
      simp [h0]
    have hsub := integral_eq_zero_of_ae heq
    rw [integral_sub h1 (integrable_const _)] at hsub
    simp only [integral_const, smul_eq_mul, probReal_univ, one_mul] at hsub
    exact sub_eq_zero.mp hsub
  have ht_pos : 0 < t := pos_iff_ne_zero.mpr ht0
  let S : Ω → ℝ := fun ω => ⨆ i : Iic T, |a (B i ω)|
  have hS_nn : ∀ ω, 0 ≤ S ω := fun ω =>
    le_trans (abs_nonneg _) (le_ciSup (bddAbove_range_Iic_of_continuous _
      (ha.comp (hBcont ω)).abs T) ⟨0, mem_Iic.2 zero_le⟩)
  have hS_meas : Measurable S := by
    have hSeq : S = fun ω => ⨆ n : ℕ, |a (B (min (TopologicalSpace.denseSeq ℝ≥0 n) T) ω)| := by
      funext ω
      exact ciSup_Iic_eq_iSup_denseSeq (fun r => |a (B r ω)|) ((ha.comp (hBcont ω)).abs) T
    rw [hSeq]
    exact Measurable.iSup fun n => (ha.measurable.comp (hBmeas _)).abs
  have hS_int : Integrable S P := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add ha_sup) hS_meas.aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hS_nn ω)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (S ω - 1)]
  have hA_diff_le : ∀ {s₁ s₂ : ℝ≥0} (_ : s₁ ≤ s₂) (_ : s₂ ≤ t) (ω : Ω),
      |A s₂ ω - A s₁ ω| ≤ ((s₂ : ℝ) - s₁) * S ω := by
    intro s₁ s₂ h12 h2t ω
    have hg_cont : Continuous fun r : ℝ => a (B r.toNNReal ω) :=
      ha.comp ((hBcont ω).comp continuous_real_toNNReal)
    have hsub : A s₂ ω - A s₁ ω = ∫ r in (s₁ : ℝ)..(s₂ : ℝ), a (B r.toNNReal ω) := by
      simp only [A]
      rw [sub_eq_iff_eq_add']
      exact (intervalIntegral.integral_add_adjacent_intervals
        (hg_cont.intervalIntegrable _ _) (hg_cont.intervalIntegrable _ _)).symm
    rw [hsub]
    have h12R : (s₁ : ℝ) ≤ s₂ := NNReal.coe_le_coe.mpr h12
    refine (intervalIntegral.abs_integral_le_integral_abs h12R).trans ?_
    have hbdd := bddAbove_range_Iic_of_continuous (fun r => |a (B r ω)|)
      (ha.comp (hBcont ω)).abs T
    have hpt : ∀ r ∈ Icc (s₁ : ℝ) (s₂ : ℝ), |a (B r.toNNReal ω)| ≤ S ω := by
      intro r hr
      have hrT : r.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr
        (hr.2.trans (NNReal.coe_le_coe.mpr (h2t.trans ht)))
      exact le_ciSup hbdd ⟨r.toNNReal, mem_Iic.2 hrT⟩
    have hmono := intervalIntegral.integral_mono_on (μ := volume) h12R
      (hg_cont.abs.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _) hpt
    simpa [intervalIntegral.integral_const, smul_eq_mul] using hmono
  let T1 : ℕ → Ω → ℝ := fun n ω =>
    ∑ k ∈ Finset.range n,
      F_x (A (unifPart t n k) ω) (B (unifPart t n k) ω) *
        (A (unifPart t n (k + 1)) ω - A (unifPart t n k) ω)
  let T2 : ℕ → Ω → ℝ := fun n ω =>
    ∑ k ∈ Finset.range n,
      F_y (A (unifPart t n k) ω) (B (unifPart t n k) ω) *
        (B (unifPart t n (k + 1)) ω - B (unifPart t n k) ω)
  let T3 : ℕ → Ω → ℝ := fun n ω =>
    ∑ k ∈ Finset.range n,
      F_yy (A (unifPart t n k) ω) (B (unifPart t n k) ω) *
        (B (unifPart t n (k + 1)) ω - B (unifPart t n k) ω) ^ 2
  let T4 : ℕ → Ω → ℝ := fun n ω =>
    ∑ k ∈ Finset.range n,
      discreteTaylorRemainder2D F F_x F_y F_yy
        (A (unifPart t n k) ω) (A (unifPart t n (k + 1)) ω)
        (B (unifPart t n k) ω) (B (unifPart t n (k + 1)) ω)
  have hdecomp : ∀ n, 0 < n → ∀ ω,
      F (A t ω) (B t ω) - F (A 0 ω) (B 0 ω) =
        T1 n ω + T2 n ω + (1 / 2 : ℝ) * T3 n ω + T4 n ω := by
    intro n hn ω
    have h := discrete_ito_formula_2d n (fun k => A (unifPart t n k) ω)
      (fun k => B (unifPart t n k) ω) F F_x F_y F_yy
    rwa [unifPart_zero, unifPart_self t hn.ne'] at h
  have hT1_int : ∀ n, 0 < n → Integrable (T1 n) P := by
    intro n _
    refine integrable_finsetSum _ fun k hk => ?_
    have hk1_le : unifPart t n (k + 1) ≤ t := unifPart_le_T (Finset.mem_range.mp hk)
    have hmeas : Measurable (fun ω =>
        F_x (A (unifPart t n k) ω) (B (unifPart t n k) ω) *
          (A (unifPart t n (k + 1)) ω - A (unifPart t n k) ω)) :=
      (hFx_cont.measurable.comp ((hA_meas _).prodMk (hBmeas _))).mul
        ((hA_meas _).sub (hA_meas _))
    refine Integrable.mono' (hS_int.const_mul (M * (t : ℝ) / n)) hmeas.aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := hbd_x (A (unifPart t n k) ω) (B (unifPart t n k) ω)
    have h2 := hA_diff_le (unifPart_mono t n (Nat.le_succ k)) hk1_le ω
    rw [unifPart_succ_sub] at h2
    calc |F_x (A (unifPart t n k) ω) (B (unifPart t n k) ω)| *
          |A (unifPart t n (k + 1)) ω - A (unifPart t n k) ω|
        ≤ M * (((t : ℝ) / n) * S ω) := mul_le_mul h1 h2 (abs_nonneg _) hM
      _ = (M * (t : ℝ) / n) * S ω := by ring
  have hT2_exp : ∀ n, Integrable (T2 n) P ∧ ∫ ω, T2 n ω ∂P = 0 := by
    intro n
    have hterm : ∀ k ∈ Finset.range n,
        Integrable (fun ω => F_y (A (unifPart t n k) ω) (B (unifPart t n k) ω) *
          (B (unifPart t n (k + 1)) ω - B (unifPart t n k) ω)) P ∧
        ∫ ω, F_y (A (unifPart t n k) ω) (B (unifPart t n k) ω) *
          (B (unifPart t n (k + 1)) ω - B (unifPart t n k) ω) ∂P = 0 := by
      intro k _
      have hk_m : Measurable[𝓕 (unifPart t n k)]
          (fun ω => F_y (A (unifPart t n k) ω) (B (unifPart t n k) ω)) :=
        hFy_meas.comp ((hA_adapted _).prodMk (stronglyAdapted_natFiltration hBmeas _).measurable)
      have hΔ : Integrable (fun ω => B (unifPart t n (k + 1)) ω - B (unifPart t n k) ω) P :=
        (hB.hasLaw_sub (unifPart t n (k + 1)) (unifPart t n k)).integrable_comp
          ((memLp_id_gaussianReal 1).integrable le_rfl)
      refine ⟨?_, integral_adapted_mul_increment hFB (unifPart_mono t n (Nat.le_succ k)) hk_m⟩
      exact hΔ.bdd_mul (hk_m.mono (𝓕.le _) le_rfl).aestronglyMeasurable
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hbd_y _ _)
    refine ⟨integrable_finsetSum _ fun k hk => (hterm k hk).1, ?_⟩
    rw [integral_finsetSum _ fun k hk => (hterm k hk).1]
    exact Finset.sum_eq_zero fun k hk => (hterm k hk).2
  have hT3_exp : ∀ n, Integrable (T3 n) P ∧
      ∫ ω, T3 n ω ∂P =
        ∑ k ∈ Finset.range n,
          (∫ ω, F_yy (A (unifPart t n k) ω) (B (unifPart t n k) ω) ∂P) * ((t : ℝ) / n) := by
    intro n
    have hterm : ∀ k ∈ Finset.range n,
        Integrable (fun ω => F_yy (A (unifPart t n k) ω) (B (unifPart t n k) ω) *
          (B (unifPart t n (k + 1)) ω - B (unifPart t n k) ω) ^ 2) P ∧
        ∫ ω, F_yy (A (unifPart t n k) ω) (B (unifPart t n k) ω) *
          (B (unifPart t n (k + 1)) ω - B (unifPart t n k) ω) ^ 2 ∂P =
          (∫ ω, F_yy (A (unifPart t n k) ω) (B (unifPart t n k) ω) ∂P) * ((t : ℝ) / n) := by
      intro k _
      have hk_m : Measurable[𝓕 (unifPart t n k)]
          (fun ω => F_yy (A (unifPart t n k) ω) (B (unifPart t n k) ω)) :=
        hF_yy_cont.measurable.comp
          ((hA_adapted _).prodMk (stronglyAdapted_natFiltration hBmeas _).measurable)
      have hΔ : Integrable (fun ω => (B (unifPart t n (k + 1)) ω - B (unifPart t n k) ω) ^ 2) P :=
        integrable_increment_sq hB _ _
      refine ⟨?_, ?_⟩
      · exact hΔ.bdd_mul (hk_m.mono (𝓕.le _) le_rfl).aestronglyMeasurable
          (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hbd_yy _ _)
      · rw [integral_adapted_mul_increment_sq hFB (unifPart_mono t n (Nat.le_succ k)) hk_m,
          unifPart_succ_sub]
    refine ⟨integrable_finsetSum _ fun k hk => (hterm k hk).1, ?_⟩
    rw [integral_finsetSum _ fun k hk => (hterm k hk).1]
    exact Finset.sum_congr rfl fun k hk => (hterm k hk).2
  let CS : ℝ := ∫ ω, S ω ^ 2 ∂P
  have hT4_int : ∀ n, 0 < n → Integrable (T4 n) P ∧
      |∫ ω, T4 n ω ∂P| ≤
        (t : ℝ) * (M * ((t : ℝ) / n * CS + (1 / 2) * (1 + CS) * √((t : ℝ) / n) +
          2 * √((t : ℝ) / n))) := by
    intro n hn
    set δ : ℝ := (t : ℝ) / n with hδ_def
    have hδ : 0 < δ := div_pos (by exact_mod_cast ht_pos) (Nat.cast_pos.mpr hn)
    have hterm : ∀ k ∈ Finset.range n,
        Integrable (fun ω => discreteTaylorRemainder2D F F_x F_y F_yy
          (A (unifPart t n k) ω) (A (unifPart t n (k + 1)) ω)
          (B (unifPart t n k) ω) (B (unifPart t n (k + 1)) ω)) P ∧
        ∫ ω, |discreteTaylorRemainder2D F F_x F_y F_yy
          (A (unifPart t n k) ω) (A (unifPart t n (k + 1)) ω)
          (B (unifPart t n k) ω) (B (unifPart t n (k + 1)) ω)| ∂P ≤
          δ * (M * (δ * CS + (1 / 2) * (1 + CS) * √δ + 2 * √δ)) := by
      intro k hk
      have hk1_le : unifPart t n (k + 1) ≤ t := unifPart_le_T (Finset.mem_range.mp hk)
      have hk_le_succ : unifPart t n k ≤ unifPart t n (k + 1) := unifPart_mono t n (Nat.le_succ k)
      let ΔB : Ω → ℝ := fun ω => B (unifPart t n (k + 1)) ω - B (unifPart t n k) ω
      have hΔB2_int : Integrable (fun ω => ΔB ω ^ 2) P := integrable_increment_sq hB _ _
      have hΔB4_int : Integrable (fun ω => ΔB ω ^ 4) P := by
        have hmem : MemLp (id : ℝ → ℝ) 4
            (gaussianReal 0 (nndist (unifPart t n (k + 1) : ℝ) (unifPart t n k))) :=
          memLp_id_gaussianReal 4
        have hi : Integrable (fun x : ℝ => x ^ 4)
            (gaussianReal 0 (nndist (unifPart t n (k + 1) : ℝ) (unifPart t n k))) := by
          refine (hmem.integrable_norm_pow (by norm_num)).congr (ae_of_all _ fun x => ?_)
          simp only [Real.norm_eq_abs, id_eq]
          rw [show |x| ^ 4 = (|x| ^ 2) ^ 2 by ring, sq_abs]; ring
        exact (hB.hasLaw_sub (unifPart t n (k + 1)) (unifPart t n k)).integrable_comp hi
      have hΔB2_exp : ∫ ω, ΔB ω ^ 2 ∂P = δ := by
        simpa [ΔB, unifPart_succ_sub] using integral_increment_sq hB hk_le_succ
      have hΔB4_exp : ∫ ω, ΔB ω ^ 4 ∂P = 3 * δ ^ 2 := by
        simpa [ΔB, unifPart_succ_sub] using integral_increment_pow4 hB hk_le_succ
      let cS : ℝ := M * (δ ^ 2 + (1 / 2) * (√δ)⁻¹ * δ ^ 2)
      let cB2 : ℝ := M * √δ
      let cB4 : ℝ := M * (1 / 2) * (√δ)⁻¹
      let Bdom : Ω → ℝ := fun ω => cS * S ω ^ 2 + cB2 * ΔB ω ^ 2 + cB4 * ΔB ω ^ 4
      have hBdom_int : Integrable Bdom P :=
        ((ha_sup.const_mul cS).add (hΔB2_int.const_mul cB2)).add (hΔB4_int.const_mul cB4)
      have hmeasR : Measurable (fun ω => discreteTaylorRemainder2D F F_x F_y F_yy
          (A (unifPart t n k) ω) (A (unifPart t n (k + 1)) ω)
          (B (unifPart t n k) ω) (B (unifPart t n (k + 1)) ω)) := by
        unfold discreteTaylorRemainder2D
        have hF0 : Measurable (fun ω => F (A (unifPart t n k) ω) (B (unifPart t n k) ω)) :=
          hF_cont.measurable.comp ((hA_meas _).prodMk (hBmeas _))
        have hF1 : Measurable (fun ω => F (A (unifPart t n (k + 1)) ω) (B (unifPart t n (k + 1)) ω)) :=
          hF_cont.measurable.comp ((hA_meas _).prodMk (hBmeas _))
        have hFx0 : Measurable (fun ω => F_x (A (unifPart t n k) ω) (B (unifPart t n k) ω)) :=
          hFx_cont.measurable.comp ((hA_meas _).prodMk (hBmeas _))
        have hFy0 : Measurable (fun ω => F_y (A (unifPart t n k) ω) (B (unifPart t n k) ω)) :=
          hFy_meas.comp ((hA_meas _).prodMk (hBmeas _))
        have hFyy0 : Measurable (fun ω => F_yy (A (unifPart t n k) ω) (B (unifPart t n k) ω)) :=
          hF_yy_cont.measurable.comp ((hA_meas _).prodMk (hBmeas _))
        exact (((hF1.sub hF0).sub (hFx0.mul ((hA_meas _).sub (hA_meas _)))).sub
          (hFy0.mul ((hBmeas _).sub (hBmeas _)))).sub
          (measurable_const.mul (hFyy0.mul (((hBmeas _).sub (hBmeas _)).pow_const 2)))
      have hpt : ∀ ω, |discreteTaylorRemainder2D F F_x F_y F_yy
          (A (unifPart t n k) ω) (A (unifPart t n (k + 1)) ω)
          (B (unifPart t n k) ω) (B (unifPart t n (k + 1)) ω)| ≤ Bdom ω := by
        intro ω
        have hrem := abs_discreteTaylorRemainder2D_le hF_x hF_xx hF_xy hF_y hF_yy hF_yyy
          hbd_xx hbd_xy hbd_yyy
          (A (unifPart t n k) ω) (A (unifPart t n (k + 1)) ω)
          (B (unifPart t n k) ω) (B (unifPart t n (k + 1)) ω)
        have hAd := hA_diff_le hk_le_succ hk1_le ω
        rw [unifPart_succ_sub] at hAd
        have hA2 : |A (unifPart t n (k + 1)) ω - A (unifPart t n k) ω| ^ 2 ≤ δ ^ 2 * S ω ^ 2 := by
          calc _ ≤ (δ * S ω) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hAd 2
            _ = δ ^ 2 * S ω ^ 2 := by ring
        have hsδ : 0 < √δ := Real.sqrt_pos.mpr hδ
        have hBA : |ΔB ω| * |A (unifPart t n (k + 1)) ω - A (unifPart t n k) ω| ≤
            (1 / 2) * (√δ * ΔB ω ^ 2 + (√δ)⁻¹ * (δ ^ 2 * S ω ^ 2)) := by
          have h := two_mul_abs_mul_le hsδ (ΔB ω) (A (unifPart t n (k + 1)) ω - A (unifPart t n k) ω)
          have h1 : (A (unifPart t n (k + 1)) ω - A (unifPart t n k) ω) ^ 2 ≤ δ ^ 2 * S ω ^ 2 := by
            rw [← sq_abs]
            exact hA2
          have hpos : 0 ≤ (√δ)⁻¹ := inv_nonneg.mpr hsδ.le
          nlinarith [mul_le_mul_of_nonneg_left h1 hpos]
        have hB3 : |ΔB ω| ^ 3 ≤ (1 / 2) * (√δ * ΔB ω ^ 2 + (√δ)⁻¹ * ΔB ω ^ 4) := by
          have h := two_mul_abs_cube_le hsδ (ΔB ω)
          linarith
        calc |discreteTaylorRemainder2D F F_x F_y F_yy _ _ _ _|
            ≤ M * |A (unifPart t n (k + 1)) ω - A (unifPart t n k) ω| ^ 2 +
                M * |ΔB ω| * |A (unifPart t n (k + 1)) ω - A (unifPart t n k) ω| +
                M * |ΔB ω| ^ 3 := hrem
          _ ≤ M * (δ ^ 2 * S ω ^ 2) +
                M * ((1 / 2) * (√δ * ΔB ω ^ 2 + (√δ)⁻¹ * (δ ^ 2 * S ω ^ 2))) +
                M * ((1 / 2) * (√δ * ΔB ω ^ 2 + (√δ)⁻¹ * ΔB ω ^ 4)) := by
              have hmul : M * |ΔB ω| * |A (unifPart t n (k + 1)) ω - A (unifPart t n k) ω| =
                  M * (|ΔB ω| * |A (unifPart t n (k + 1)) ω - A (unifPart t n k) ω|) := by ring
              rw [hmul]
              gcongr
          _ = Bdom ω := by simp only [Bdom, cS, cB2, cB4, ΔB]; ring
      have hR_int : Integrable (fun ω => discreteTaylorRemainder2D F F_x F_y F_yy
          (A (unifPart t n k) ω) (A (unifPart t n (k + 1)) ω)
          (B (unifPart t n k) ω) (B (unifPart t n (k + 1)) ω)) P :=
        hBdom_int.mono' hmeasR.aestronglyMeasurable (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs]; exact hpt ω)
      refine ⟨hR_int, ?_⟩
      calc ∫ ω, |discreteTaylorRemainder2D F F_x F_y F_yy _ _ _ _| ∂P
          ≤ ∫ ω, Bdom ω ∂P := integral_mono hR_int.abs hBdom_int hpt
        _ = cS * CS + cB2 * δ + cB4 * (3 * δ ^ 2) := by
            have h12 : Integrable (fun ω => cS * S ω ^ 2 + cB2 * ΔB ω ^ 2) P :=
              (ha_sup.const_mul cS).add (hΔB2_int.const_mul cB2)
            calc ∫ ω, Bdom ω ∂P
                = ∫ ω, (cS * S ω ^ 2 + cB2 * ΔB ω ^ 2) ∂P + ∫ ω, cB4 * ΔB ω ^ 4 ∂P :=
                    integral_add h12 (hΔB4_int.const_mul cB4)
              _ = (∫ ω, cS * S ω ^ 2 ∂P + ∫ ω, cB2 * ΔB ω ^ 2 ∂P) + ∫ ω, cB4 * ΔB ω ^ 4 ∂P := by
                    rw [integral_add (ha_sup.const_mul cS) (hΔB2_int.const_mul cB2)]
              _ = cS * CS + cB2 * δ + cB4 * (3 * δ ^ 2) := by
                    rw [integral_const_mul, integral_const_mul, integral_const_mul,
                      hΔB2_exp, hΔB4_exp]
        _ = δ * (M * (δ * CS + (1 / 2) * (1 + CS) * √δ + 2 * √δ)) := by
            have hsδ : 0 < √δ := Real.sqrt_pos.mpr hδ
            have hsq : √δ ^ 2 = δ := Real.sq_sqrt hδ.le
            have h1 : (√δ)⁻¹ * δ ^ 2 = δ * √δ := by
              calc (√δ)⁻¹ * δ ^ 2 = (√δ)⁻¹ * (δ * δ) := by ring
                _ = (√δ)⁻¹ * (√δ ^ 2 * δ) := by rw [hsq]
                _ = ((√δ)⁻¹ * √δ) * (√δ * δ) := by ring
                _ = δ * √δ := by rw [inv_mul_cancel₀ hsδ.ne', one_mul, mul_comm]
            have h2 : √δ * δ = δ * √δ := by ring
            have h3 : (√δ)⁻¹ * (3 * δ ^ 2) = 3 * (δ * √δ) := by
              calc (√δ)⁻¹ * (3 * δ ^ 2) = 3 * ((√δ)⁻¹ * δ ^ 2) := by ring
                _ = 3 * (δ * √δ) := by rw [h1]
            simp only [cS, cB2, cB4]
            calc M * (δ ^ 2 + 1 / 2 * (√δ)⁻¹ * δ ^ 2) * CS + M * √δ * δ +
                  M * (1 / 2) * (√δ)⁻¹ * (3 * δ ^ 2)
                = M * (δ ^ 2 * CS + 1 / 2 * ((√δ)⁻¹ * δ ^ 2) * CS + (√δ * δ) +
                    1 / 2 * ((√δ)⁻¹ * (3 * δ ^ 2))) := by ring
              _ = _ := by rw [h1, h2, h3]; ring
    refine ⟨integrable_finsetSum _ fun k hk => (hterm k hk).1, ?_⟩
    calc |∫ ω, T4 n ω ∂P|
        ≤ ∫ ω, |T4 n ω| ∂P := by rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
      _ ≤ ∫ ω, ∑ k ∈ Finset.range n, |discreteTaylorRemainder2D F F_x F_y F_yy
            (A (unifPart t n k) ω) (A (unifPart t n (k + 1)) ω)
            (B (unifPart t n k) ω) (B (unifPart t n (k + 1)) ω)| ∂P := by
          refine integral_mono (integrable_finsetSum _ fun k hk => (hterm k hk).1).abs
            (integrable_finsetSum _ fun k hk => (hterm k hk).1.abs) fun ω => ?_
          exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k ∈ Finset.range n, ∫ ω, |discreteTaylorRemainder2D F F_x F_y F_yy
            (A (unifPart t n k) ω) (A (unifPart t n (k + 1)) ω)
            (B (unifPart t n k) ω) (B (unifPart t n (k + 1)) ω)| ∂P :=
          integral_finsetSum _ fun k hk => (hterm k hk).1.abs
      _ ≤ ∑ _k ∈ Finset.range n, δ * (M * (δ * CS + (1 / 2) * (1 + CS) * √δ + 2 * √δ)) :=
          Finset.sum_le_sum fun k hk => (hterm k hk).2
      _ = (t : ℝ) * (M * (δ * CS + (1 / 2) * (1 + CS) * √δ + 2 * √δ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
          simp only [δ]; field_simp
  let G : Ω → ℝ := fun ω =>
    ∫ s in (0 : ℝ)..(t : ℝ),
      (F_x (A s.toNNReal ω) (B s.toNNReal ω) * a (B s.toNNReal ω) +
        (1 / 2 : ℝ) * F_yy (A s.toNNReal ω) (B s.toNNReal ω))
  let Wsum : ℕ → Ω → ℝ := fun n ω =>
    T1 n ω + (1 / 2 : ℝ) * ∑ k ∈ Finset.range n,
      F_yy (A (unifPart t n k) ω) (B (unifPart t n k) ω) * ((t : ℝ) / n)
  have hWsum_int : ∀ n, 0 < n → Integrable (Wsum n) P := by
    intro n hn
    refine (hT1_int n hn).add ((integrable_finsetSum _ fun k _ => ?_).const_mul _)
    exact (Integrable.of_bound
      (hF_yy_cont.measurable.comp ((hA_meas _).prodMk (hBmeas _))).aestronglyMeasurable
      M (ae_of_all _ fun ω => hbd_yy _ _)).mul_const _
  have hWsum_lim : ∀ ω, Tendsto (fun n => Wsum n ω) atTop (𝓝 (G ω)) := by
    intro ω
    have hcont1 : Continuous fun s : ℝ≥0 => F_x (A s ω) (B s ω) :=
      hFx_cont.comp ((hA_cont ω).prodMk (hBcont ω))
    have hcont2 : Continuous fun s : ℝ≥0 => a (B s ω) := ha.comp (hBcont ω)
    have hcont3 : Continuous fun s : ℝ≥0 => F_yy (A s ω) (B s ω) :=
      hF_yy_cont.comp ((hA_cont ω).prodMk (hBcont ω))
    have h1 := tendsto_sum_mul_increment_path ht_pos hcont1 hcont2 (fun s _ => hbd_x _ _)
    have h3 : Tendsto (fun n : ℕ => (1 / 2 : ℝ) * ∑ k ∈ Finset.range n,
        F_yy (A (unifPart t n k) ω) (B (unifPart t n k) ω) * ((t : ℝ) / n))
        atTop (𝓝 ((1 / 2 : ℝ) * ∫ s in (0 : ℝ)..(t : ℝ), F_yy (A s.toNNReal ω) (B s.toNNReal ω))) := by
      refine Tendsto.const_mul _ ?_
      have htend := tendsto_riemann_continuous hcont3 t (fun s _ => hbd_yy _ _)
      simp_rw [unifPart_succ_sub] at htend
      rwa [timeMeasure_Ioc_eq_intervalIntegral] at htend
    have hsum := h1.add h3
    have hG_eq : (∫ s in (0 : ℝ)..(t : ℝ), F_x (A s.toNNReal ω) (B s.toNNReal ω) * a (B s.toNNReal ω)) +
        (1 / 2 : ℝ) * (∫ s in (0 : ℝ)..(t : ℝ), F_yy (A s.toNNReal ω) (B s.toNNReal ω)) = G ω := by
      have hi1 : IntervalIntegrable (fun s : ℝ => F_x (A s.toNNReal ω) (B s.toNNReal ω) * a (B s.toNNReal ω))
          volume 0 (t : ℝ) :=
        ((hcont1.mul hcont2).comp continuous_real_toNNReal).intervalIntegrable _ _
      have hi2 : IntervalIntegrable (fun s : ℝ => (1 / 2 : ℝ) * F_yy (A s.toNNReal ω) (B s.toNNReal ω))
          volume 0 (t : ℝ) :=
        ((continuous_const.mul hcont3).comp continuous_real_toNNReal).intervalIntegrable _ _
      rw [← intervalIntegral.integral_const_mul]
      exact (intervalIntegral.integral_add hi1 hi2).symm
    simpa only [Wsum, hG_eq] using hsum
  let Bbound : Ω → ℝ := fun ω => M * (t : ℝ) * S ω + (1 / 2 : ℝ) * M * (t : ℝ)
  have hBbound_int : Integrable Bbound P :=
    (hS_int.const_mul (M * (t : ℝ))).add (integrable_const _)
  have hWsum_bd : ∀ n : ℕ, ∀ᵐ ω ∂P, ‖Wsum n ω‖ ≤ Bbound ω := by
    intro n
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    have hT1_bd : |T1 n ω| ≤ M * (t : ℝ) * S ω := by
      rcases eq_or_ne n 0 with rfl | hn0
      · simp only [T1, Finset.range_zero, Finset.sum_empty, abs_zero]
        exact mul_nonneg (mul_nonneg hM t.coe_nonneg) (hS_nn ω)
      · calc |T1 n ω|
            ≤ ∑ k ∈ Finset.range n,
                |F_x (A (unifPart t n k) ω) (B (unifPart t n k) ω) *
                  (A (unifPart t n (k + 1)) ω - A (unifPart t n k) ω)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ k ∈ Finset.range n,
                |F_x (A (unifPart t n k) ω) (B (unifPart t n k) ω)| *
                  |A (unifPart t n (k + 1)) ω - A (unifPart t n k) ω| := by
              refine Finset.sum_congr rfl fun k _ => abs_mul _ _
          _ ≤ ∑ k ∈ Finset.range n, M * (((t : ℝ) / n) * S ω) := by
              refine Finset.sum_le_sum fun k hk => ?_
              have hk1_le : unifPart t n (k + 1) ≤ t := unifPart_le_T (Finset.mem_range.mp hk)
              have h2 := hA_diff_le (unifPart_mono t n (Nat.le_succ k)) hk1_le ω
              rw [unifPart_succ_sub] at h2
              exact mul_le_mul (hbd_x _ _) h2 (abs_nonneg _) hM
          _ = M * (t : ℝ) * S ω := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              have hn_real : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
              field_simp
    have h3_bd : |(1 / 2 : ℝ) * ∑ k ∈ Finset.range n,
        F_yy (A (unifPart t n k) ω) (B (unifPart t n k) ω) * ((t : ℝ) / n)| ≤
        (1 / 2 : ℝ) * M * (t : ℝ) := by
      have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
      rw [abs_mul, abs_of_nonneg hhalf, mul_assoc (1 / 2 : ℝ) M (t : ℝ)]
      refine mul_le_mul_of_nonneg_left ?_ hhalf
      rcases eq_or_ne n 0 with rfl | hn0
      · simp only [Finset.range_zero, Finset.sum_empty, abs_zero]
        exact mul_nonneg hM t.coe_nonneg
      · calc |∑ k ∈ Finset.range n, F_yy (A (unifPart t n k) ω) (B (unifPart t n k) ω) * ((t : ℝ) / n)|
            ≤ ∑ k ∈ Finset.range n, |F_yy (A (unifPart t n k) ω) (B (unifPart t n k) ω)| * ((t : ℝ) / n) := by
              refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
              rw [abs_mul, abs_of_nonneg (div_nonneg t.coe_nonneg (Nat.cast_nonneg n))]
          _ ≤ ∑ _k ∈ Finset.range n, M * ((t : ℝ) / n) :=
              Finset.sum_le_sum fun k _ =>
                mul_le_mul_of_nonneg_right (hbd_yy _ _) (div_nonneg t.coe_nonneg (Nat.cast_nonneg n))
          _ = M * (t : ℝ) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              have hn_real : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
              field_simp
    calc |Wsum n ω| = |T1 n ω + (1 / 2 : ℝ) * ∑ k ∈ Finset.range n,
            F_yy (A (unifPart t n k) ω) (B (unifPart t n k) ω) * ((t : ℝ) / n)| := rfl
      _ ≤ |T1 n ω| + |(1 / 2 : ℝ) * ∑ k ∈ Finset.range n,
            F_yy (A (unifPart t n k) ω) (B (unifPart t n k) ω) * ((t : ℝ) / n)| := abs_add_le _ _
      _ ≤ Bbound ω := by
          change |T1 n ω| + |(1 / 2 : ℝ) * ∑ k ∈ Finset.range n,
            F_yy (A (unifPart t n k) ω) (B (unifPart t n k) ω) * ((t : ℝ) / n)| ≤
            M * (t : ℝ) * S ω + (1 / 2 : ℝ) * M * (t : ℝ)
          linarith [hT1_bd, h3_bd]
  have hDCT : Tendsto (fun n => ∫ ω, Wsum n ω ∂P) atTop (𝓝 (∫ ω, G ω ∂P)) :=
    tendsto_integral_of_dominated_convergence Bbound
      (fun n => by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp only [Wsum, T1, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
          exact aestronglyMeasurable_const
        · exact (hWsum_int n hn).aestronglyMeasurable)
      hBbound_int hWsum_bd (Eventually.of_forall hWsum_lim)
  have hLHS_int : Integrable (fun ω => F (A t ω) (B t ω)) P :=
    Integrable.of_bound (hF_cont.measurable.comp ((hA_meas t).prodMk (hBmeas t))).aestronglyMeasurable
      M (ae_of_all _ fun ω => hbd_F _ _)
  have h0_int : Integrable (fun ω => F (A 0 ω) (B 0 ω)) P :=
    Integrable.of_bound (hF_cont.measurable.comp ((hA_meas 0).prodMk (hBmeas 0))).aestronglyMeasurable
      M (ae_of_all _ fun ω => hbd_F _ _)
  have h0_eq : ∫ ω, F (A 0 ω) (B 0 ω) ∂P = F 0 0 := by
    have heq : (fun ω => F (A 0 ω) (B 0 ω)) =ᵐ[P] fun _ => F 0 0 :=
      hB0.mono fun ω h0 => by simp [A, h0]
    rw [integral_congr_ae heq]
    simp [integral_const]
  have hT4_lim : Tendsto (fun n => ∫ ω, T4 n ω ∂P) atTop (𝓝 0) := by
    have hδ_lim : Tendsto (fun n : ℕ => (t : ℝ) / n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hbd_lim : Tendsto (fun n : ℕ =>
        (t : ℝ) * (M * ((t : ℝ) / n * CS + (1 / 2) * (1 + CS) * √((t : ℝ) / n) +
          2 * √((t : ℝ) / n)))) atTop (𝓝 0) := by
      have hsq : Tendsto (fun n : ℕ => √((t : ℝ) / n)) atTop (𝓝 0) := by
        have := (Real.continuous_sqrt.continuousAt.tendsto.comp hδ_lim)
        simpa [Function.comp_def] using this
      have h1 : Tendsto (fun n : ℕ => (t : ℝ) / n * CS + (1 / 2) * (1 + CS) * √((t : ℝ) / n) +
          2 * √((t : ℝ) / n)) atTop (𝓝 0) := by
        simpa using ((hδ_lim.mul_const CS).add (hsq.const_mul ((1 / 2) * (1 + CS)))).add
          (hsq.const_mul 2)
      simpa using (h1.const_mul M).const_mul (t : ℝ)
    refine tendsto_zero_iff_norm_tendsto_zero.mpr (tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hbd_lim (Eventually.of_forall fun _ => norm_nonneg _) ?_)
    filter_upwards [eventually_ge_atTop 1] with n hn
    simpa [Real.norm_eq_abs] using (hT4_int n hn).2
  have hWsum_eq : ∀ᶠ n in atTop,
      ∫ ω, Wsum n ω ∂P = (∫ ω, F (A t ω) (B t ω) ∂P - F 0 0) - ∫ ω, T4 n ω ∂P := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hde : (fun ω => F (A t ω) (B t ω) - F (A 0 ω) (B 0 ω)) =
        fun ω => T1 n ω + T2 n ω + (1 / 2 : ℝ) * T3 n ω + T4 n ω :=
      funext (hdecomp n hn)
    have h12 : Integrable (fun ω => T1 n ω + T2 n ω) P := (hT1_int n hn).add (hT2_exp n).1
    have h3 : Integrable (fun ω => (1 / 2 : ℝ) * T3 n ω) P := (hT3_exp n).1.const_mul _
    have hE : ∫ ω, F (A t ω) (B t ω) ∂P - F 0 0 =
        ∫ ω, T1 n ω ∂P + (1 / 2 : ℝ) * ∫ ω, T3 n ω ∂P + ∫ ω, T4 n ω ∂P := by
      calc ∫ ω, F (A t ω) (B t ω) ∂P - F 0 0
          = ∫ ω, (F (A t ω) (B t ω) - F (A 0 ω) (B 0 ω)) ∂P := by
              rw [integral_sub hLHS_int h0_int, h0_eq]
        _ = ∫ ω, (T1 n ω + T2 n ω + (1 / 2 : ℝ) * T3 n ω + T4 n ω) ∂P :=
              integral_congr_ae (Eventually.of_forall (congrFun hde))
        _ = ∫ ω, (T1 n ω + T2 n ω + (1 / 2 : ℝ) * T3 n ω) ∂P + ∫ ω, T4 n ω ∂P :=
              integral_add (h12.add h3) (hT4_int n hn).1
        _ = (∫ ω, (T1 n ω + T2 n ω) ∂P + ∫ ω, (1 / 2 : ℝ) * T3 n ω ∂P) + ∫ ω, T4 n ω ∂P := by
              rw [integral_add h12 h3]
        _ = (∫ ω, T1 n ω ∂P + ∫ ω, T2 n ω ∂P + (1 / 2 : ℝ) * ∫ ω, T3 n ω ∂P) + ∫ ω, T4 n ω ∂P := by
              rw [integral_add (hT1_int n hn) (hT2_exp n).1, integral_const_mul]
        _ = _ := by rw [(hT2_exp n).2, add_zero]
    have hS_int_yy : Integrable (fun ω => ∑ k ∈ Finset.range n,
        F_yy (A (unifPart t n k) ω) (B (unifPart t n k) ω) * ((t : ℝ) / n)) P :=
      integrable_finsetSum _ fun k _ => (Integrable.of_bound
        (hF_yy_cont.measurable.comp ((hA_meas _).prodMk (hBmeas _))).aestronglyMeasurable
        M (ae_of_all _ fun ω => hbd_yy _ _)).mul_const _
    have hW_int_eq : ∫ ω, Wsum n ω ∂P =
        ∫ ω, T1 n ω ∂P + (1 / 2 : ℝ) * ∫ ω, T3 n ω ∂P := by
      simp only [Wsum]
      rw [integral_add (hT1_int n hn) (hS_int_yy.const_mul _), integral_const_mul, (hT3_exp n).2]
      congr 2
      have h_yy_k : ∀ k ∈ Finset.range n, Integrable (fun ω =>
          F_yy (A (unifPart t n k) ω) (B (unifPart t n k) ω) * ((t : ℝ) / n)) P := fun k _ =>
        (Integrable.of_bound (hF_yy_cont.measurable.comp ((hA_meas _).prodMk (hBmeas _))).aestronglyMeasurable
          M (ae_of_all _ fun ω => hbd_yy _ _)).mul_const _
      rw [integral_finsetSum _ h_yy_k]
      exact Finset.sum_congr rfl fun k _ => integral_mul_const _ _
    linarith
  have hLHS_lim : Tendsto (fun n => ∫ ω, Wsum n ω ∂P) atTop
      (𝓝 (∫ ω, F (A t ω) (B t ω) ∂P - F 0 0)) := by
    have hsub : Tendsto (fun n => (∫ ω, F (A t ω) (B t ω) ∂P - F 0 0) - ∫ ω, T4 n ω ∂P)
        atTop (𝓝 ((∫ ω, F (A t ω) (B t ω) ∂P - F 0 0) - 0)) :=
      tendsto_const_nhds.sub hT4_lim
    rw [sub_zero] at hsub
    exact hsub.congr' (hWsum_eq.mono fun _ h => h.symm)
  have hEqG : ∫ ω, F (A t ω) (B t ω) ∂P - F 0 0 = ∫ ω, G ω ∂P :=
    tendsto_nhds_unique hLHS_lim hDCT
  let g : ℝ → Ω → ℝ := fun s ω =>
    F_x (A s.toNNReal ω) (B s.toNNReal ω) * a (B s.toNNReal ω) +
      (1 / 2 : ℝ) * F_yy (A s.toNNReal ω) (B s.toNNReal ω)
  have h_joint_meas : Measurable (Function.uncurry g) := by
    have hA_joint : Measurable (Function.uncurry fun s : ℝ => fun ω => A s.toNNReal ω) :=
      measurable_uncurry_of_continuous_of_measurable
        (fun ω => (hA_cont ω).comp continuous_real_toNNReal) (fun s => hA_meas s.toNNReal)
    have hB_joint : Measurable (Function.uncurry fun s : ℝ => fun ω => B s.toNNReal ω) :=
      measurable_uncurry_of_continuous_of_measurable
        (fun ω => (hBcont ω).comp continuous_real_toNNReal) (fun s => hBmeas s.toNNReal)
    have hFx_joint : Measurable (fun p : ℝ × Ω => F_x (A p.1.toNNReal p.2) (B p.1.toNNReal p.2)) :=
      hFx_cont.measurable.comp (hA_joint.prodMk hB_joint)
    have ha_joint : Measurable (fun p : ℝ × Ω => a (B p.1.toNNReal p.2)) :=
      ha.measurable.comp hB_joint
    have hFyy_joint : Measurable (fun p : ℝ × Ω => F_yy (A p.1.toNNReal p.2) (B p.1.toNNReal p.2)) :=
      hF_yy_cont.measurable.comp (hA_joint.prodMk hB_joint)
    exact (hFx_joint.mul ha_joint).add (measurable_const.mul hFyy_joint)
  have h_joint_int : Integrable (Function.uncurry g)
      ((volume.restrict (uIoc (0 : ℝ) (t : ℝ))).prod P) := by
    let Bdom_prod : ℝ × Ω → ℝ := fun p => M * S p.2 + (1 / 2 : ℝ) * M
    have hBdom_prod_int : Integrable Bdom_prod
        ((volume.restrict (uIoc (0 : ℝ) (t : ℝ))).prod P) := by
      have h1 : Integrable (fun ω => M * S ω + (1 / 2 : ℝ) * M) P :=
        (hS_int.const_mul M).add (integrable_const _)
      have : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) (t : ℝ))) :=
        ⟨by simp [Real.volume_Ioc]⟩
      exact h1.comp_snd (μ := volume.restrict (uIoc (0 : ℝ) (t : ℝ)))
    refine hBdom_prod_int.mono' h_joint_meas.aestronglyMeasurable ?_
    have hmem : ∀ᵐ p ∂((volume.restrict (uIoc (0 : ℝ) (t : ℝ))).prod P),
        p.1 ∈ uIoc (0 : ℝ) (t : ℝ) := by
      have hfst : ∀ᵐ s ∂(volume.restrict (uIoc (0 : ℝ) (t : ℝ))), s ∈ uIoc (0 : ℝ) (t : ℝ) :=
        ae_restrict_mem measurableSet_uIoc
      exact (Measure.quasiMeasurePreserving_fst
        (μ := volume.restrict (uIoc (0 : ℝ) (t : ℝ))) (ν := P)).ae hfst
    filter_upwards [hmem] with p hp
    rw [uIoc_of_le (NNReal.coe_nonneg t)] at hp
    have hpT : p.1.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr (hp.2.trans ht)
    have hbdd := bddAbove_range_Iic_of_continuous (fun r => |a (B r p.2)|)
      (ha.comp (hBcont p.2)).abs T
    have ha_le : |a (B p.1.toNNReal p.2)| ≤ S p.2 :=
      le_ciSup hbdd ⟨p.1.toNNReal, mem_Iic.2 hpT⟩
    rw [Real.norm_eq_abs]
    calc |g p.1 p.2|
        = |F_x (A p.1.toNNReal p.2) (B p.1.toNNReal p.2) * a (B p.1.toNNReal p.2) +
            (1 / 2 : ℝ) * F_yy (A p.1.toNNReal p.2) (B p.1.toNNReal p.2)| := rfl
      _ ≤ |F_x (A p.1.toNNReal p.2) (B p.1.toNNReal p.2) * a (B p.1.toNNReal p.2)| +
            |(1 / 2 : ℝ) * F_yy (A p.1.toNNReal p.2) (B p.1.toNNReal p.2)| := abs_add_le _ _
      _ = |F_x (A p.1.toNNReal p.2) (B p.1.toNNReal p.2)| * |a (B p.1.toNNReal p.2)| +
            (1 / 2 : ℝ) * |F_yy (A p.1.toNNReal p.2) (B p.1.toNNReal p.2)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      _ ≤ M * S p.2 + (1 / 2 : ℝ) * M := by
          gcongr
          · exact hbd_x _ _
          · exact hbd_yy _ _
  have hswap := (intervalIntegral_integral_swap (f := g) (μ := P) (a := (0 : ℝ)) (b := (t : ℝ))
    h_joint_int).symm
  have hcongr : ∫ s in (0 : ℝ)..(t : ℝ), ∫ ω, g s ω ∂P =
      ∫ s in (0 : ℝ)..(t : ℝ), ∫ ω, (F_x (∫ r in (0 : ℝ)..s, a (B r.toNNReal ω)) (B s.toNNReal ω) *
        a (B s.toNNReal ω) + (1 / 2 : ℝ) *
        F_yy (∫ r in (0 : ℝ)..s, a (B r.toNNReal ω)) (B s.toNNReal ω)) ∂P := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le t.coe_nonneg] at hs
    simp only [g, A, Real.coe_toNNReal s hs.1]
  exact (hEqG.trans hswap).trans hcongr

/-- Helper: for any `c : ℝ`, `⨆ i : Iic T, |Real.exp (c * B i ω)|` is square-integrable
for a continuous pre-Brownian motion `B`. -/
lemma integrable_sq_iSup_exp_preBrownian
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P) (hBmeas : ∀ s, Measurable (B s))
    (hBcont : ∀ ω, Continuous (B · ω)) (c : ℝ) (T : ℝ≥0) :
    Integrable (fun ω => (⨆ i : Iic T, |Real.exp (c * B i ω)|) ^ 2) P := by
  have h := integrable_sqrt_iSup_exp_preBrownian P B hB hBmeas hBcont (4 * c) T
  refine h.congr (Eventually.of_forall fun ω => ?_)
  have hpos : ∀ i : Iic T, |Real.exp (c * B i ω)| = Real.exp (c * B i ω) := fun i =>
    abs_of_pos (Real.exp_pos _)
  have hbdd1 : BddAbove (range fun i : Iic T => Real.exp (c * B i ω)) :=
    bddAbove_range_Iic_of_continuous _ (Real.continuous_exp.comp (continuous_const.mul (hBcont ω))) T
  have hbdd4 : BddAbove (range fun i : Iic T => Real.exp (4 * c * B i ω)) :=
    bddAbove_range_Iic_of_continuous _ (Real.continuous_exp.comp (continuous_const.mul (hBcont ω))) T
  have hnn1 : 0 ≤ ⨆ i : Iic T, Real.exp (c * B i ω) :=
    le_trans (Real.exp_pos _).le (le_ciSup hbdd1 ⟨0, mem_Iic.2 zero_le⟩)
  have hpow : (⨆ i : Iic T, Real.exp (c * B i ω)) ^ 2 =
      √(⨆ i : Iic T, Real.exp (4 * c * B i ω)) := by
    have h4 : (⨆ i : Iic T, Real.exp (4 * c * B i ω)) =
        (⨆ i : Iic T, Real.exp (c * B i ω)) ^ 4 := by
      refine le_antisymm ?_ ?_
      · refine ciSup_le fun i => ?_
        have hi : Real.exp (4 * c * B i ω) = (Real.exp (c * B i ω)) ^ 4 := by
          rw [← Real.exp_nat_mul]; congr 1; ring
        rw [hi]
        exact pow_le_pow_left₀ (Real.exp_pos _).le (le_ciSup hbdd1 i) 4
      · have hle : ⨆ i : Iic T, Real.exp (c * B i ω) ≤
            (⨆ i : Iic T, Real.exp (4 * c * B i ω)) ^ ((1 : ℝ) / 4) := by
          refine ciSup_le fun i => ?_
          have h1 : Real.exp (c * B i ω) = (Real.exp (4 * c * B i ω)) ^ ((1 : ℝ) / 4) := by
            rw [← Real.exp_mul]; congr 1; ring
          rw [h1]
          exact Real.rpow_le_rpow (Real.exp_pos _).le (le_ciSup hbdd4 i) (by norm_num)
        have hnn4 : 0 ≤ ⨆ i : Iic T, Real.exp (4 * c * B i ω) :=
          le_trans (Real.exp_pos _).le (le_ciSup hbdd4 ⟨0, mem_Iic.2 zero_le⟩)
        calc (⨆ i : Iic T, Real.exp (c * B i ω)) ^ 4
            ≤ ((⨆ i : Iic T, Real.exp (4 * c * B i ω)) ^ ((1 : ℝ) / 4)) ^ 4 :=
              pow_le_pow_left₀ hnn1 hle 4
          _ = ((⨆ i : Iic T, Real.exp (4 * c * B i ω)) ^ ((1 : ℝ) / 4)) ^ ((4 : ℕ) : ℝ) := by
              rw [← Real.rpow_natCast]
          _ = (⨆ i : Iic T, Real.exp (4 * c * B i ω)) ^ ((1 / 4 : ℝ) * 4) :=
              (Real.rpow_mul hnn4 _ _).symm
          _ = ⨆ i : Iic T, Real.exp (4 * c * B i ω) := by norm_num
    rw [h4, Real.sqrt_eq_rpow]
    rw [← Real.rpow_natCast (⨆ i : Iic T, Real.exp (c * B i ω)) 4, ← Real.rpow_mul hnn1,
      ← Real.rpow_natCast (⨆ i : Iic T, Real.exp (c * B i ω)) 2]
    norm_num
  simpa [hpos] using hpow.symm

end ExpectedItoPath

end Lyasoff2016
