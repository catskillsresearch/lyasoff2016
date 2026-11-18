/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
# Bending a real-line contour into the graph `u + iθ(u)`

An entire function's integral over `ℝ` equals its integral along the graph contour
`u ↦ u + iθ(u)` provided the homotopy `u + i s θ(u)` (`0 ≤ s ≤ 1`) is dominated by an
integrable function.  The proof differentiates in `s`; the `s`-derivative is an exact
`u`-derivative, whose integral over `ℝ` vanishes.
-/
module

public import Mathlib

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

noncomputable section
namespace Lyasoff2016

/-- Point of the homotopy between `ℝ` and the graph of `θ`. -/
def bendPt (θ : ℝ → ℝ) (s u : ℝ) : ℂ := (u : ℂ) + (s : ℂ) * (θ u : ℂ) * I

/-- Integrand along the `s`-th intermediate contour. -/
def bendF (f : ℂ → ℂ) (θ θ' : ℝ → ℝ) (s u : ℝ) : ℂ :=
  f (bendPt θ s u) * (1 + (s : ℂ) * (θ' u : ℂ) * I)

/-- The boundary term `f(γ_s(u)) · iθ(u)`. -/
def bendH (f : ℂ → ℂ) (θ : ℝ → ℝ) (s u : ℝ) : ℂ := f (bendPt θ s u) * ((θ u : ℂ) * I)

/-- Common value of `∂_s bendF` and `∂_u bendH`. -/
def bendD (f : ℂ → ℂ) (θ θ' : ℝ → ℝ) (s u : ℝ) : ℂ :=
  deriv f (bendPt θ s u) * ((θ u : ℂ) * I) * (1 + (s : ℂ) * (θ' u : ℂ) * I) +
    f (bendPt θ s u) * ((θ' u : ℂ) * I)

section
variable {f : ℂ → ℂ} {θ θ' : ℝ → ℝ}

lemma bendPt_hasDerivAt_s (θ : ℝ → ℝ) (s u : ℝ) :
    HasDerivAt (fun s => bendPt θ s u) ((θ u : ℂ) * I) s := by
  have h := ((hasDerivAt_id (s : ℂ)).mul_const ((θ u : ℂ) * I)).comp_ofReal (z := s)
  have h2 := h.const_add (u : ℂ)
  convert h2 using 1
  · funext s; simp [bendPt, mul_assoc]
  · simp

lemma bendPt_hasDerivAt_u (hθ : ∀ u, HasDerivAt θ (θ' u) u) (s u : ℝ) :
    HasDerivAt (fun u => bendPt θ s u) (1 + (s : ℂ) * (θ' u : ℂ) * I) u := by
  have h1 : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 u := (hasDerivAt_id (u : ℂ)).comp_ofReal
  have h2 : HasDerivAt (fun u : ℝ => (θ u : ℂ)) (θ' u : ℂ) u := (hθ u).ofReal_comp
  have h3 := (h2.const_mul (s : ℂ)).mul_const I
  exact h1.add h3

lemma bendF_hasDerivAt_s (hf : Differentiable ℂ f) (s u : ℝ) :
    HasDerivAt (fun s => bendF f θ θ' s u) (bendD f θ θ' s u) s := by
  have hγ := bendPt_hasDerivAt_s θ s u
  have hfγ : HasDerivAt (fun s => f (bendPt θ s u))
      (deriv f (bendPt θ s u) * ((θ u : ℂ) * I)) s :=
    (hf (bendPt θ s u)).hasDerivAt.comp s hγ
  have hlin : HasDerivAt (fun s : ℝ => (1 : ℂ) + (s : ℂ) * (θ' u : ℂ) * I)
      ((θ' u : ℂ) * I) s := by
    have := (((hasDerivAt_id (s : ℂ)).mul_const ((θ' u : ℂ) * I)).comp_ofReal (z := s)).const_add 1
    convert this using 1
    · funext s; simp [mul_assoc]
    · simp
  unfold bendF bendD
  exact hfγ.mul hlin

lemma bendH_hasDerivAt_u (hf : Differentiable ℂ f) (hθ : ∀ u, HasDerivAt θ (θ' u) u)
    (s u : ℝ) : HasDerivAt (fun u => bendH f θ s u) (bendD f θ θ' s u) u := by
  have hγ := bendPt_hasDerivAt_u hθ s u
  have hfγ := (hf (bendPt θ s u)).hasDerivAt.comp u hγ
  have h2 : HasDerivAt (fun u : ℝ => (θ u : ℂ) * I) ((θ' u : ℂ) * I) u :=
    (hθ u).ofReal_comp.mul_const I
  unfold bendH bendD
  exact (hfγ.mul h2).congr_deriv (by simp only [Function.comp_apply]; ring)

lemma continuous_bendPt (hθc : Continuous θ) :
    Continuous (fun p : ℝ × ℝ => bendPt θ p.1 p.2) := by
  unfold bendPt; fun_prop

lemma continuous_bendD (hf : Differentiable ℂ f) (hθc : Continuous θ) (hθ'c : Continuous θ') :
    Continuous (fun p : ℝ × ℝ => bendD f θ θ' p.1 p.2) := by
  have hγ := continuous_bendPt hθc
  have hdf : Continuous (deriv f) := hf.deriv.continuous
  unfold bendD
  have := hf.continuous
  fun_prop

lemma continuous_bendF (hf : Differentiable ℂ f) (hθc : Continuous θ) (hθ'c : Continuous θ') :
    Continuous (fun p : ℝ × ℝ => bendF f θ θ' p.1 p.2) := by
  have hγ := continuous_bendPt hθc
  unfold bendF
  have := hf.continuous
  fun_prop

lemma continuous_bendH (hf : Differentiable ℂ f) (hθc : Continuous θ) :
    Continuous (fun p : ℝ × ℝ => bendH f θ p.1 p.2) := by
  have hγ := continuous_bendPt hθc
  unfold bendH
  have := hf.continuous
  fun_prop

/-- **Contour bending.**  If `f` is entire, `θ` is `C¹` with derivative `θ'`, and the
homotopy integrands `bendF`, `bendH`, `bendD` are dominated on `0 ≤ s ≤ 1` by one integrable
function `g`, then `∫_ℝ f(u) du = ∫_ℝ f(u + iθ(u)) (1 + iθ'(u)) du`. -/
theorem integral_eq_integral_bend (hf : Differentiable ℂ f)
    (hθ : ∀ u, HasDerivAt θ (θ' u) u) (hθ'c : Continuous θ')
    {g : ℝ → ℝ} (hg : Integrable g)
    (hF : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u, ‖bendF f θ θ' s u‖ ≤ g u)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u, ‖bendH f θ s u‖ ≤ g u)
    (hD : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u, ‖bendD f θ θ' s u‖ ≤ g u) :
    ∫ u : ℝ, f u = ∫ u : ℝ, f ((u : ℂ) + (θ u : ℂ) * I) * (1 + (θ' u : ℂ) * I) := by
  have hθc : Continuous θ := continuous_iff_continuousAt.2 fun u => (hθ u).continuousAt
  have cF := continuous_bendF hf hθc hθ'c
  have cH := continuous_bendH hf hθc
  have cD := continuous_bendD hf hθc hθ'c
  have hint : ∀ {φ : ℝ × ℝ → ℂ}, Continuous φ → ∀ s ∈ Icc (0 : ℝ) 1,
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ u, ‖φ (s, u)‖ ≤ g u) → Integrable (fun u => φ (s, u)) := by
    intro φ hφ s hs hb
    exact hg.mono' (hφ.comp (Continuous.prodMk_right s)).aestronglyMeasurable
      (ae_of_all _ fun u => hb s hs u)
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have iF0 : Integrable (fun u => bendF f θ θ' 0 u) := hint cF 0 h0 (fun s hs u => hF s hs u)
  have iF1 : Integrable (fun u => bendF f θ θ' 1 u) := hint cF 1 h1 (fun s hs u => hF s hs u)
  -- ∫ D(s,·) = 0 for each s ∈ [0,1]
  have hzero : ∀ s ∈ Icc (0 : ℝ) 1, ∫ u, bendD f θ θ' s u = 0 := fun s hs =>
    integral_eq_zero_of_hasDerivAt_of_integrable (bendH_hasDerivAt_u hf hθ s)
      (hint cD s hs (fun s hs u => hD s hs u)) (hint cH s hs (fun s hs u => hH s hs u))
  -- pointwise FTC in s
  have hftc : ∀ u, bendF f θ θ' 1 u - bendF f θ θ' 0 u = ∫ s in (0 : ℝ)..1, bendD f θ θ' s u := by
    intro u
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => bendF_hasDerivAt_s hf s u)]
    exact (cD.comp (Continuous.prodMk_left u)).intervalIntegrable _ _
  -- Fubini
  have hprod : Integrable (Function.uncurry (bendD f θ θ'))
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod volume) := by
    have hg2 : Integrable (fun p : ℝ × ℝ => (1 : ℝ) * g p.2)
        ((volume.restrict (uIoc (0 : ℝ) 1)).prod volume) := by
      have : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) 1)) := by
        rw [uIoc_of_le zero_le_one]; infer_instance
      exact (integrable_const (1 : ℝ)).mul_prod hg
    refine hg2.mono' cD.aestronglyMeasurable ?_
    have hset : MeasurableSet (uIoc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) :=
      measurableSet_uIoc.prod MeasurableSet.univ
    have hμ : (volume.restrict (uIoc (0 : ℝ) 1)).prod (volume : Measure ℝ) =
        ((volume : Measure ℝ).prod volume).restrict (uIoc (0 : ℝ) 1 ×ˢ univ) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [hμ]
    refine ae_restrict_of_forall_mem hset fun p hp => ?_
    have hs : p.1 ∈ Icc (0 : ℝ) 1 := by
      have := hp.1; rw [uIoc_of_le zero_le_one] at this; exact ⟨this.1.le, this.2⟩
    simpa [Function.uncurry] using hD p.1 hs p.2
  have hswap := intervalIntegral_integral_swap hprod
  have hdiff : (∫ u, bendF f θ θ' 1 u) - ∫ u, bendF f θ θ' 0 u = 0 := by
    rw [← integral_sub iF1 iF0]
    simp_rw [hftc]
    rw [← hswap]
    rw [intervalIntegral.integral_of_le zero_le_one]
    refine (setIntegral_congr_fun measurableSet_Ioc fun s hs => hzero s ⟨hs.1.le, hs.2⟩).trans ?_
    simp
  have e0 : ∀ u : ℝ, bendF f θ θ' 0 u = f u := by intro u; simp [bendF, bendPt]
  have e1 : ∀ u : ℝ, bendF f θ θ' 1 u =
      f ((u : ℂ) + (θ u : ℂ) * I) * (1 + (θ' u : ℂ) * I) := by intro u; simp [bendF, bendPt]
  simp_rw [e0, e1] at hdiff
  exact (sub_eq_zero.1 hdiff).symm

end
end Lyasoff2016
