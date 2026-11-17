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

public section

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

Proof sketch: if `f(x,y) ≠ 0`, take the sign so `f(x,y) > 0`, shrink to a product
rectangle inside `{f > f(x,y)/2} ∩ jointDomain` with left edge `a > 0`, place 1D bumps
`u,v` via `exists_contDiff_tsupport_subset`, then
`∫∫ u⊗v·f ≥ (f(x,y)/2)(∫u)(∫v) > 0`, contradicting `hweak`. -/
theorem eq_zero_of_integral_product_eq_zero {f : ℝ × ℝ → ℝ}
    (hcont : ContinuousOn f jointDomain)
    (hweak : ∀ (u v : ℝ → ℝ),
      ContDiff ℝ (⊤ : WithTop ℕ∞) u → ContDiff ℝ (⊤ : WithTop ℕ∞) v →
      HasCompactSupport u → HasCompactSupport v →
      tsupport (fun p : ℝ × ℝ => u p.1 * v p.2) ⊆ jointDomain →
      ∫ p : ℝ × ℝ, u p.1 * v p.2 * f p = 0)
    {x y : ℝ} (hx : 0 < x) :
    f (x, y) = 0 := by
  -- 1D bumps on a positivity rectangle + Fubini lower bound (see docstring).
  sorry

end Lyasoff2016
