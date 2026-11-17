/-
Analytic helpers for `fokker_planck_joint`: open joint domain and pointwise upgrade
from a weak (distributional) identity via the fundamental lemma.
-/
module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.Algebra.Support


@[expose] public section

open MeasureTheory Set Filter Topology Metric Function
open MeasureTheory.Measure
open scoped ContDiff

noncomputable section
namespace Lyasoff2016

/-- Open half-plane domain for joint densities of `(∫ e^{σW}, W_t)`. -/
def jointDomain : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)

theorem isOpen_jointDomain : IsOpen jointDomain :=
  isOpen_Ioi.prod isOpen_univ

theorem mem_jointDomain {x y : ℝ} (hx : 0 < x) : (x, y) ∈ jointDomain :=
  ⟨hx, trivial⟩

/-- Fundamental lemma on the joint domain. -/
theorem ae_eq_zero_of_weak_joint {f : ℝ × ℝ → ℝ}
    (hloc : LocallyIntegrableOn f jointDomain volume)
    (hweak : ∀ (g : ℝ × ℝ → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ jointDomain → ∫ p, g p * f p = 0) :
    ∀ᵐ p ∂volume, p ∈ jointDomain → f p = 0 :=
  isOpen_jointDomain.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hg hc hts => by
    simpa [smul_eq_mul] using hweak g hg hc hts

/-- Continuous-on-open + a.e. zero ⇒ pointwise zero. -/
theorem eq_zero_of_continuousOn_ae_eq_zero {f : ℝ × ℝ → ℝ}
    (hcont : ContinuousOn f jointDomain)
    (hae : ∀ᵐ p ∂volume, p ∈ jointDomain → f p = 0)
    {x y : ℝ} (hx : 0 < x) :
    f (x, y) = 0 := by
  have hxmem : (x, y) ∈ jointDomain := mem_jointDomain hx
  have hae' : f =ᵐ[(volume : Measure (ℝ × ℝ)).restrict jointDomain] (fun _ => (0 : ℝ)) := by
    rw [EventuallyEq, ae_restrict_iff' isOpen_jointDomain.measurableSet]
    exact hae
  have : (volume : Measure (ℝ × ℝ)).IsOpenPosMeasure := inferInstance
  exact eqOn_open_of_ae_eq hae' isOpen_jointDomain hcont continuousOn_const hxmem

/-- Compact support of a tensor product of compactly supported scalars. -/
theorem hasCompactSupport_tensor {u v : ℝ → ℝ}
    (huC : HasCompactSupport u) (hvC : HasCompactSupport v) :
    HasCompactSupport fun p : ℝ × ℝ => u p.1 * v p.2 := by
  have hsubset : tsupport (fun p : ℝ × ℝ => u p.1 * v p.2) ⊆ tsupport u ×ˢ tsupport v := by
    change closure _ ⊆ closure _ ×ˢ closure _
    rw [← closure_prod_eq]
    exact closure_mono fun p hp => mul_ne_zero_iff.mp (mem_support.mp hp)
  exact IsCompact.of_isClosed_subset (huC.prod hvC) isClosed_closure hsubset

/-- Product-test weak vanishing + continuity ⇒ pointwise zero on `jointDomain`.

ContDiff index is `∞` (C^∞), matching Mathlib bump constructors. -/
theorem eq_zero_of_integral_product_eq_zero {f : ℝ × ℝ → ℝ}
    (hcont : ContinuousOn f jointDomain)
    (hweak : ∀ (u v : ℝ → ℝ),
      ContDiff ℝ ∞ u → ContDiff ℝ ∞ v →
      HasCompactSupport u → HasCompactSupport v →
      tsupport (fun p : ℝ × ℝ => u p.1 * v p.2) ⊆ jointDomain →
      ∫ p : ℝ × ℝ, u p.1 * v p.2 * f p = 0)
    {x y : ℝ} (hx : 0 < x) :
    f (x, y) = 0 := by
  by_contra hf0
  -- Core argument under the sign assumption `0 < f(x,y)`.
  have hposCase (f : ℝ × ℝ → ℝ)
      (hcont : ContinuousOn f jointDomain)
      (hweak : ∀ (u v : ℝ → ℝ), ContDiff ℝ ∞ u → ContDiff ℝ ∞ v →
        HasCompactSupport u → HasCompactSupport v →
        tsupport (fun p : ℝ × ℝ => u p.1 * v p.2) ⊆ jointDomain →
        ∫ p : ℝ × ℝ, u p.1 * v p.2 * f p = 0)
      (hpos : 0 < f (x, y)) : False := by
    have hxmem : (x, y) ∈ jointDomain := mem_jointDomain hx
    have hcontAt : ContinuousAt f (x, y) :=
      hcont.continuousAt (isOpen_jointDomain.mem_nhds hxmem)
    obtain ⟨δ, hδ, hδball⟩ :
        ∃ δ > 0, ∀ p : ℝ × ℝ, dist p (x, y) < δ →
          p ∈ jointDomain ∧ f (x, y) / 2 < f p := by
      have hhalf : (0 : ℝ) < f (x, y) / 2 := half_pos hpos
      rcases Metric.continuousAt_iff.1 hcontAt _ hhalf with ⟨δ₁, hδ₁, hδ₁ball⟩
      rcases Metric.mem_nhds_iff.1 (isOpen_jointDomain.mem_nhds hxmem) with ⟨δ₂, hδ₂, hδ₂ball⟩
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun p hp => ?_⟩
      have hp1 : dist p (x, y) < δ₁ := hp.trans_le (min_le_left _ _)
      have hp2 : dist p (x, y) < δ₂ := hp.trans_le (min_le_right _ _)
      refine ⟨hδ₂ball hp2, ?_⟩
      have habs : |f p - f (x, y)| < f (x, y) / 2 := by
        simpa [Real.dist_eq] using hδ₁ball hp1
      linarith [neg_lt_of_abs_lt habs]
    -- Max-metric: `dist = max |Δx| |Δy|`, so an open square of side `2r` sits in the ball.
    set r : ℝ := min δ (x / 2)
    have hr_pos : 0 < r := lt_min hδ (half_pos hx)
    have hx_sub : 0 < x - r := by
      have : r ≤ x / 2 := min_le_right _ _
      linarith
    set a : ℝ := x - r
    set b : ℝ := x + r
    set c : ℝ := y - r
    set d : ℝ := y + r
    have ha_lt_x : a < x := by simp [a]; linarith [hr_pos]
    have hx_lt_b : x < b := by simp [b]; linarith [hr_pos]
    have hc_lt_y : c < y := by simp [c]; linarith [hr_pos]
    have hy_lt_d : y < d := by simp [d]; linarith [hr_pos]
    have hIoo_ball {p : ℝ × ℝ} (hp1 : p.1 ∈ Ioo a b) (hp2 : p.2 ∈ Ioo c d) :
        dist p (x, y) < δ := by
      have hx' : dist p.1 x < r := by
        simp only [a, b, mem_Ioo, Real.dist_eq] at hp1 ⊢
        rw [abs_sub_lt_iff]; constructor <;> linarith
      have hy' : dist p.2 y < r := by
        simp only [c, d, mem_Ioo, Real.dist_eq] at hp2 ⊢
        rw [abs_sub_lt_iff]; constructor <;> linarith
      have : dist p (x, y) < r := by
        rw [Prod.dist_eq]
        exact max_lt hx' hy'
      exact this.trans_le (min_le_left _ _)
    -- Avoid ContDiff-scope `∞` clashing with `ℕ∞`: pass `n` as `ENat`.
    obtain ⟨u, hu_ts, huC, huTop, hu_range, hux⟩ :=
      exists_contDiff_tsupport_subset (E := ℝ) (n := (⊤ : WithTop ℕ)) (x := x) (s := Ioo a b)
        (Ioo_mem_nhds ha_lt_x hx_lt_b)
    obtain ⟨v, hv_ts, hvC, hvTop, hv_range, hvy⟩ :=
      exists_contDiff_tsupport_subset (E := ℝ) (n := (⊤ : WithTop ℕ)) (x := y) (s := Ioo c d)
        (Ioo_mem_nhds hc_lt_y hy_lt_d)
    have hu_nn : ∀ t, 0 ≤ u t := fun t => (hu_range ⟨t, rfl⟩).1
    have hv_nn : ∀ t, 0 ≤ v t := fun t => (hv_range ⟨t, rfl⟩).1
    have hu_cont : Continuous u := huTop.continuous
    have hv_cont : Continuous v := hvTop.continuous
    set φ : ℝ × ℝ → ℝ := fun p => u p.1 * v p.2
    have hφ_cont : Continuous φ :=
      (hu_cont.comp continuous_fst).mul (hv_cont.comp continuous_snd)
    have hφ_nn : ∀ p, 0 ≤ φ p := fun p => mul_nonneg (hu_nn _) (hv_nn _)
    have hts_prod : tsupport φ ⊆ Ioo a b ×ˢ Ioo c d := by
      intro p hp
      have hsub : tsupport φ ⊆ tsupport u ×ˢ tsupport v := by
        change closure _ ⊆ closure _ ×ˢ closure _
        rw [← closure_prod_eq]
        exact closure_mono fun q hq => mul_ne_zero_iff.mp (mem_support.mp hq)
      exact ⟨hu_ts (hsub hp).1, hv_ts (hsub hp).2⟩
    have hts_joint : tsupport φ ⊆ jointDomain := by
      intro p hp
      exact ⟨lt_trans hx_sub (hts_prod hp).1.1, trivial⟩
    have hφC : HasCompactSupport φ := hasCompactSupport_tensor huC hvC
    -- `ContDiff ℝ ⊤` on `WithTop ℕ` coerces to `ContDiff ℝ ∞`.
    have huCinf : ContDiff ℝ ∞ u := huTop
    have hvCinf : ContDiff ℝ ∞ v := hvTop
    have hint0 : ∫ p : ℝ × ℝ, φ p * f p = 0 :=
      hweak u v huCinf hvCinf huC hvC hts_joint
    have hf_ge : ∀ p ∈ tsupport φ, f (x, y) / 2 ≤ f p := fun p hp =>
      le_of_lt (hδball p (hIoo_ball (hts_prod hp).1 (hts_prod hp).2)).2
    set g : ℝ × ℝ → ℝ := fun p => φ p * f p
    have hg_ts : tsupport g ⊆ tsupport φ := tsupport_mul_subset_left
    have hg_joint : tsupport g ⊆ jointDomain := hg_ts.trans hts_joint
    have hg_contOn : ContinuousOn g jointDomain :=
      (hφ_cont.continuousOn).mul hcont
    have hg_cont : Continuous g :=
      hg_contOn.continuous_of_tsupport_subset isOpen_jointDomain hg_joint
    have hgC : HasCompactSupport g := hφC.mul_right
    have hg_int : Integrable g volume := hg_cont.integrable_of_hasCompactSupport hgC
    have hφ_int : Integrable φ volume := hφ_cont.integrable_of_hasCompactSupport hφC
    have hu_pos : (0 : ℝ) < ∫ t, u t :=
      hu_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x) huC hu_nn
        (by simp [hux])
    have hv_pos : (0 : ℝ) < ∫ t, v t :=
      hv_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := y) hvC hv_nn
        (by simp [hvy])
    have hφ_val : ∫ p : ℝ × ℝ, φ p = (∫ t, u t) * (∫ t, v t) := by
      have hvol : (volume : Measure (ℝ × ℝ)) = volume.prod volume := by
        simp [Measure.volume_eq_prod]
      simp only [φ, hvol]
      exact integral_prod_mul (μ := (volume : Measure ℝ)) (ν := volume) u v
    have hφ_pos : (0 : ℝ) < ∫ p : ℝ × ℝ, φ p := by
      rw [hφ_val]; exact mul_pos hu_pos hv_pos
    have hpt : ∀ p, (f (x, y) / 2) * φ p ≤ g p := by
      intro p
      by_cases hp : p ∈ tsupport φ
      · have := hf_ge p hp
        calc
          (f (x, y) / 2) * φ p ≤ f p * φ p :=
            mul_le_mul_of_nonneg_right this (hφ_nn p)
          _ = g p := mul_comm _ _
      · have : φ p = 0 := notMem_support.1 fun h => hp (subset_tsupport _ h)
        simp [g, this]
    have hlower : (f (x, y) / 2) * (∫ p, φ p) ≤ ∫ p, g p := by
      have hconst : Integrable (fun p : ℝ × ℝ => (f (x, y) / 2) * φ p) := hφ_int.const_mul _
      simpa [integral_const_mul] using integral_mono hconst hg_int hpt
    have hpos' : (0 : ℝ) < ∫ p, g p :=
      lt_of_lt_of_le (mul_pos (half_pos hpos) hφ_pos) hlower
    exact absurd hint0 hpos'.ne'
  by_cases hpos : 0 < f (x, y)
  · exact hposCase f hcont hweak hpos
  · have hneg : f (x, y) < 0 := lt_of_le_of_ne (not_lt.mp hpos) hf0
    have hcont' : ContinuousOn (fun p : ℝ × ℝ => -f p) jointDomain := hcont.neg
    have hweak' : ∀ (u v : ℝ → ℝ),
        ContDiff ℝ ∞ u → ContDiff ℝ ∞ v →
        HasCompactSupport u → HasCompactSupport v →
        tsupport (fun p : ℝ × ℝ => u p.1 * v p.2) ⊆ jointDomain →
        ∫ p : ℝ × ℝ, u p.1 * v p.2 * (-f p) = 0 := by
      intro u v hu hv huC hvC hts
      simpa [mul_neg, integral_neg] using congrArg Neg.neg (hweak u v hu hv huC hvC hts)
    exact hposCase (fun p => -f p) hcont' hweak' (neg_pos.mpr hneg)

end Lyasoff2016
