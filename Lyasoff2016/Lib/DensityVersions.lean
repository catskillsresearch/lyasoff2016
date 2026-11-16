/-
Continuous versions of the joint density `φ_{t,σ}` are not unique.

`IsJointDensity P W σ ν t φ` says that the law of `(∫₀ᵗ e^{σW_s+νs} ds, W_t)` is
`volume.withDensity (ENNReal.ofReal ∘ φ)`, so it only constrains the positive part of `φ`.
The law does not charge the half-plane `x < 0` (the integral is nonnegative), hence a
continuous `φ` is `≤ 0` there, but is otherwise arbitrary: `φ + min x 0` is another continuous
version.  Consequently an *unsigned* pointwise identity `φ x y = (expression not involving φ)`
for all `x y` cannot be derived from `IsJointDensity` and continuity alone; only identities
between positive parts (or under an explicit nonnegativity hypothesis) can.
-/
import Lyasoff2016.Setting

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
private theorem expInt_nonneg_aux (W : ℝ≥0 → Ω → ℝ) (σ ν : ℝ) (t : ℝ≥0) (ω : Ω) :
    0 ≤ expInt W σ ν t ω :=
  intervalIntegral.integral_nonneg t.coe_nonneg fun _ _ => (Real.exp_pos _).le

/-- A continuous joint density is `≤ 0` on the half-plane `x < 0`, which the joint law of
`(∫₀ᵗ e^{σW_s+νs} ds, W_t)` does not charge. -/
theorem IsJointDensity.nonpos_of_neg {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} {σ ν : ℝ} {t : ℝ≥0}
    {φ : ℝ → ℝ → ℝ} (h : IsJointDensity P W σ ν t φ) (hc : Continuous (Function.uncurry φ))
    {x : ℝ} (hx : x < 0) (y : ℝ) : φ x y ≤ 0 := by
  set U : Set (ℝ × ℝ) := {p | p.1 < 0} with hU
  have hUo : IsOpen U := isOpen_lt continuous_fst continuous_const
  unfold IsJointDensity at h
  -- a law with a Lebesgue density is not a Dirac mass (the junk value of `Measure.map`)
  have hdirac : ∀ c : ℝ × ℝ, jointLaw P W σ ν t ≠ Measure.dirac c := by
    intro c hd
    have h2 : (Measure.dirac c) {c} = 0 := by
      rw [← hd, h]
      exact withDensity_absolutelyContinuous _ _ (measure_singleton c)
    simp at h2
  have hnull : jointLaw P W σ ν t U = 0 := by
    by_cases hm : AEMeasurable (fun ω => (expInt W σ ν t ω, W t ω)) P
    · unfold jointLaw
      rw [Measure.map_apply_of_aemeasurable hm hUo.measurableSet]
      have : (fun ω => (expInt W σ ν t ω, W t ω)) ⁻¹' U = ∅ := by
        ext ω
        simp [U, expInt_nonneg_aux W σ ν t ω]
      rw [this, measure_empty]
    · by_cases hP : P = 0
      · simp [jointLaw, hP]
      · exact absurd (Measure.map_of_not_aemeasurable_of_ne_zero hm hP) (hdirac _)
  rw [h, withDensity_apply _ hUo.measurableSet] at hnull
  have hmeas : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (φ p.1 p.2) :=
    hc.measurable.ennreal_ofReal
  have hae : (fun p : ℝ × ℝ => ENNReal.ofReal (φ p.1 p.2)) =ᵐ[volume.restrict U] 0 :=
    (lintegral_eq_zero_iff hmeas).1 hnull
  have hae' : (fun p : ℝ × ℝ => max (φ p.1 p.2) 0) =ᵐ[volume.restrict U] fun _ => 0 := by
    filter_upwards [hae] with p hp
    exact max_eq_right (ENNReal.ofReal_eq_zero.1 hp)
  have hEq := Measure.eqOn_open_of_ae_eq hae' hUo
    (hc.max continuous_const).continuousOn continuousOn_const
  have h0 : max (φ x y) 0 = 0 := hEq (show (x, y) ∈ U from hx)
  exact max_eq_right_iff.1 h0

/-- If `φ` is a continuous version of the joint density then so is `φ + min x 0`, which differs
from `φ` at every point with `x < 0`. -/
theorem IsJointDensity.add_min {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} {σ ν : ℝ} {t : ℝ≥0}
    {φ : ℝ → ℝ → ℝ} (h : IsJointDensity P W σ ν t φ) (hc : Continuous (Function.uncurry φ)) :
    IsJointDensity P W σ ν t (fun x y => φ x y + min x 0) ∧
      Continuous (Function.uncurry fun x y => φ x y + min x 0) := by
  refine ⟨?_, hc.add (continuous_fst.min continuous_const)⟩
  have h' := h
  unfold IsJointDensity at h ⊢
  rw [h]
  congr 1
  funext p
  show ENNReal.ofReal (φ p.1 p.2) = ENNReal.ofReal (φ p.1 p.2 + min p.1 0)
  rcases lt_or_ge p.1 0 with hx | hx
  · have h1 := h'.nonpos_of_neg hc hx p.2
    rw [ENNReal.ofReal_of_nonpos h1, ENNReal.ofReal_of_nonpos]
    have := min_le_right p.1 0
    linarith
  · rw [min_eq_right hx, add_zero]

/-- No function `F` can equal *every* continuous version of a joint density pointwise: as soon
as one continuous version exists, two of them differ at `(-1, 0)`. -/
theorem IsJointDensity.not_forall_version_eq {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} {σ ν : ℝ}
    {t : ℝ≥0} {φ : ℝ → ℝ → ℝ} (h : IsJointDensity P W σ ν t φ)
    (hc : Continuous (Function.uncurry φ)) (F : ℝ → ℝ → ℝ) :
    ¬ ∀ φ' : ℝ → ℝ → ℝ, IsJointDensity P W σ ν t φ' → Continuous (Function.uncurry φ') →
        ∀ x y, φ' x y = F x y := by
  intro H
  have ha := H φ h hc (-1) 0
  have hb := H _ (h.add_min hc).1 (h.add_min hc).2 (-1) 0
  rw [← ha] at hb
  norm_num at hb

end Lyasoff2016
