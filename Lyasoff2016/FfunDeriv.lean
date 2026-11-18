/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Strike-derivative Asian integrand `F'_{t,σ,μ,k}(u,w)` (p. 1091).
-/
module

public import Lyasoff2016.Ffun
public import Lyasoff2016.SfunCDeriv


@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

/- Paper: p. 1091, display before (6.1):
     F'_{t,σ,μ,k(α)}(u,w) := B(w) C(u,w) g_{σ²t,4}(u − iπ/2) S'_{k(α),4}(u,w),
   here with k(α) = α. -/
def FfunDeriv (σ ν t k : ℝ) (u w : ℝ) : ℂ :=
  (Bfun σ ν t w : ℂ) * Cfun 4 σ ν t u w * gFour (σ ^ 2 * t) (u - Complex.I * (π / 2)) *
    SfunDerivC k 4 (Afun σ ν t u w)

/-- Prefactor of `F` / `F'` independent of the strike. -/
def FfunPrefactor (σ ν t u w : ℝ) : ℂ :=
  (Bfun σ ν t w : ℂ) * Cfun 4 σ ν t u w * gFour (σ ^ 2 * t) (u - Complex.I * (π / 2))

theorem Ffun_eq_prefactor (σ ν t k u w : ℝ) :
    Ffun σ ν t k u w = FfunPrefactor σ ν t u w * SfunC k 4 (Afun σ ν t u w) := by
  simp [Ffun, FfunPrefactor, mul_assoc]

theorem FfunDeriv_eq_prefactor (σ ν t k u w : ℝ) :
    FfunDeriv σ ν t k u w =
      FfunPrefactor σ ν t u w * SfunDerivC k 4 (Afun σ ν t u w) := by
  simp [FfunDeriv, FfunPrefactor, mul_assoc]

/-- Pointwise strike derivative of `Ffun` equals `FfunDeriv`. -/
theorem hasDerivAt_Ffun (σ ν t k u w : ℝ) (hσ : σ ≠ 0) (hk : 0 < k) :
    HasDerivAt (fun κ => Ffun σ ν t κ u w) (FfunDeriv σ ν t k u w) k := by
  have hA : 0 < (Afun σ ν t u w).re := Afun.re_pos σ ν t u w hσ
  have hS := SfunC.hasDerivAt k 4 (Afun σ ν t u w) hk (by decide) hA
  have hconst :
      HasDerivAt (fun _ : ℝ => FfunPrefactor σ ν t u w) 0 k := hasDerivAt_const _ _
  have hprod := hconst.mul hS
  simp only [zero_mul, zero_add] at hprod
  convert hprod using 1
  · funext κ; exact Ffun_eq_prefactor σ ν t κ u w
  · exact FfunDeriv_eq_prefactor σ ν t k u w

/-- Pointwise strike derivative of `Re F` equals `Re F'`. -/
theorem hasDerivAt_Ffun_re (σ ν t k u w : ℝ) (hσ : σ ≠ 0) (hk : 0 < k) :
    HasDerivAt (fun κ => (Ffun σ ν t κ u w).re) (FfunDeriv σ ν t k u w).re k := by
  have h := (hasDerivAt_Ffun σ ν t k u w hσ hk).hasFDerivAt
  have hre := (Complex.reCLM.hasFDerivAt.comp k h).hasDerivAt
  have hfun : (⇑Complex.reCLM ∘ fun κ => Ffun σ ν t κ u w) = fun κ => (Ffun σ ν t κ u w).re := by
    funext κ; exact Complex.reCLM_apply _
  rw [← hfun]
  convert hre
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    Complex.reCLM_apply]

end Lyasoff2016
