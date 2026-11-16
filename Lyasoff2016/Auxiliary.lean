/-
# §2 Auxiliary results (pp. 1064–1066)
-/
import Lyasoff2016.Setting
import Lyasoff2016.Lib.IntegralMoments
import Lyasoff2016.Lib.BrownianScaling
import Lyasoff2016.Lib.DensityVersions
import Lyasoff2016.Lib.CameronMartin

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real

noncomputable section
namespace Lyasoff2016

variable {Ω : Type*} [MeasurableSpace Ω]

/- Paper: p. 1065, proof of Lemma 2.1 (deterministic bound).
   Plain recap: if |f| ≤ M on [0,t] and σ ≥ 0 then ∫₀ᵗ e^{σ f} ≤ t e^{σ M}. -/
lemma integral_exp_le (f : ℝ → ℝ) (hf : Continuous f) {σ t M : ℝ} (hσ : 0 ≤ σ)
    (ht : 0 ≤ t) (h : ∀ s ∈ Icc 0 t, |f s| ≤ M) :
    ∫ s in (0 : ℝ)..t, Real.exp (σ * f s) ≤ t * Real.exp (σ * M) := by
  have h1 : ∫ s in (0 : ℝ)..t, Real.exp (σ * f s) ≤ ∫ s in (0 : ℝ)..t, Real.exp (σ * M) :=
    intervalIntegral.integral_mono_on ht
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)
      (fun s hs => Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (h s hs)) hσ))
  simpa using h1

/- Paper: p. 1065, matching lower bound.
   Plain recap: ∫₀ᵗ e^{σ f} ≥ t e^{-σ M}, so the reciprocal is ≤ t⁻¹ e^{σ M}. -/
lemma integral_exp_ge (f : ℝ → ℝ) (hf : Continuous f) {σ t M : ℝ} (hσ : 0 ≤ σ)
    (ht : 0 ≤ t) (h : ∀ s ∈ Icc 0 t, |f s| ≤ M) :
    t * Real.exp (-(σ * M)) ≤ ∫ s in (0 : ℝ)..t, Real.exp (σ * f s) := by
  have h1 : ∫ s in (0 : ℝ)..t, Real.exp (-(σ * M)) ≤ ∫ s in (0 : ℝ)..t, Real.exp (σ * f s) :=
    intervalIntegral.integral_mono_on ht
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)
      (fun s hs => Real.exp_le_exp.2 (by
        have := neg_le_of_abs_le (h s hs)
        nlinarith [this, hσ]))
  simpa using h1

/- Paper: p. 1065, Lemma 2.1.
   Plain recap: all positive and negative integer moments of ∫₀ᵗ e^{σ W_s} ds are finite.
   PAPER NOTE: the proof writes sup|W| =ᵈ |W_t|; only one-sided max equals |W_t| in law.
   Use e^{σ sup|W|} ≤ e^{σ sup W} + e^{σ sup(-W)} instead.
   Positive moments: Hölder + Fubini + Gaussian mgf (no reflection).
   Negative moments: integral_exp_ge + moments of the running max. -/
theorem lemma_2_1 (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (hσ : 0 < σ) (ht : 0 < t) (p : ℕ) :
    Integrable (fun ω => (expInt W σ 0 t ω) ^ p) P ∧
    Integrable (fun ω => (expInt W σ 0 t ω) ^ (-(p : ℤ))) P :=
  ⟨expInt_pow_integrable P W hW σ t ht p,
    expInt_zpow_neg_integrable P W hW σ t hσ ht p⟩

theorem prop_2_2 (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ : ℝ) (t : ℝ≥0) (hσ : 0 < σ) (ht : 0 < t) :
    ∃ φc : ℝ → ℝ → ℝ, IsCondDensity P W σ t φc ∧
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry φc) (Ioi (0 : ℝ) ×ˢ univ)) ∧
      (∀ y, Tendsto (fun x => φc x y) (nhdsWithin 0 (Ioi 0)) (nhds 0)) ∧
      (∀ m n y, Tendsto (fun x => pd m n φc x y) atTop (nhds 0)) ∧
      (∀ m n y, ∃ l, Tendsto (fun x => pd m n φc x y) (nhdsWithin 0 (Ioi 0)) (nhds l)) ∧
      (∀ m n p : ℕ,
        (∫⁻ y, ENNReal.ofReal (Real.exp (-y ^ 2 / (2 * (t : ℝ)))) *
          ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |(x : ℝ) ^ (p : ℤ) * pd m n φc x y|) < ∞ ∧
        (∫⁻ y, ENNReal.ofReal (Real.exp (-y ^ 2 / (2 * (t : ℝ)))) *
          ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |(x : ℝ) ^ (-(p : ℤ)) * pd m n φc x y|) < ∞) := by
  sorry

/- Paper: p. 1065, ψ_{σ,ν} the infinite-horizon density.
   Plain recap: density of ∫₀^∞ e^{σ W_s + ν s} ds. -/
def IsInftyDensity (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (σ ν : ℝ) (ψ : ℝ → ℝ) : Prop :=
  P.map (fun ω => ∫ s in Ioi (0 : ℝ), Real.exp (σ * W s.toNNReal ω + ν * s)) =
    (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (ψ x))

/- Paper: p. 1066, three scaling displays after Prop. 2.2 — positive-part form.
   Plain recap: with B_s = σ W_{s/σ²} (again a Brownian motion, `IsBrownianReal.smul`) one has
   (∫₀ᵗ e^{B}, B_t) = (σ² ∫₀^{t/σ²} e^{σW}, σ W_{t/σ²}); pushing the laws forward under
   (x,y) ↦ (σ²x, σy) gives the Jacobians σ⁻³ / σ⁻², and continuous functions agreeing a.e. agree
   everywhere.  `IsJointDensity`, `IsCondDensity`, `IsInftyDensity` only constrain
   `ENNReal.ofReal ∘ φ`, i.e. the positive part of `φ`, so this is exactly the pointwise
   statement the hypotheses of `scaling_relations` determine.  Proved in full
   (`Lib/BrownianScaling.lean`). -/
theorem scaling_relations_posPart (σ : ℝ) (t : ℝ≥0) (hσ : 0 < σ) (ht : 0 < t)
    (φ₁ φσ : ℝ → ℝ → ℝ) (c₁ cσ : ℝ → ℝ → ℝ) (ψ₁ ψσ : ℝ → ℝ) (ν : ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W)
    (h1 : IsJointDensity P W 1 0 t φ₁)
    (hσ' : IsJointDensity P W σ 0 ((↑t : ℝ) / σ ^ 2).toNNReal φσ)
    (hc1 : IsCondDensity P W 1 t c₁)
    (hcσ : IsCondDensity P W σ ((↑t : ℝ) / σ ^ 2).toNNReal cσ)
    (hψ₁ : IsInftyDensity P W 1 ν ψ₁) (hψσ : IsInftyDensity P W σ (ν * σ ^ 2) ψσ)
    (hφcont : Continuous (Function.uncurry φ₁) ∧ Continuous (Function.uncurry φσ))
    (hccont : Continuous (Function.uncurry c₁) ∧ Continuous (Function.uncurry cσ))
    (hψcont : Continuous ψ₁ ∧ Continuous ψσ) :
    (∀ x y, max (φ₁ x y) 0 = σ⁻¹ ^ 3 * max (φσ (x / σ ^ 2) (y / σ)) 0) ∧
    (∀ x y, max (c₁ x y) 0 = σ⁻¹ ^ 2 * max (cσ (x / σ ^ 2) (y / σ)) 0) ∧
    (∀ x, max (ψ₁ x) 0 = σ⁻¹ ^ 2 * max (ψσ (x / σ ^ 2)) 0) := by
  refine ⟨fun x y => jointDensity_scaling_posPart P W hW hσ t φ₁ φσ h1 hσ' hφcont.1 hφcont.2 x y,
    fun x y => ?_,
    fun x => inftyDensity_scaling_posPart P W hW hσ ν ψ₁ ψσ hψ₁ hψσ hψcont.1 hψcont.2 x⟩
  -- Conditional densities: divide the joint relation by the Gaussian factor, using
  -- `gaussianPDF(0, t/σ²)(y/σ) = σ · gaussianPDF(0, t)(y)`.
  have hg : ∀ v : ℝ≥0, Continuous (gaussianPDFReal 0 v) := fun v => by
    rw [gaussianPDFReal_def]; fun_prop
  have hk1 : Continuous (Function.uncurry fun x y => gaussianPDFReal 0 t y * c₁ x y) :=
    ((hg t).comp continuous_snd).mul hccont.1
  have hkσ : Continuous (Function.uncurry fun x y =>
      gaussianPDFReal 0 ((↑t : ℝ) / σ ^ 2).toNNReal y * cσ x y) :=
    ((hg _).comp continuous_snd).mul hccont.2
  have h := jointDensity_scaling_posPart P W hW hσ t _ _ hc1 hcσ hk1 hkσ x y
  have hgpos : 0 < gaussianPDFReal 0 t y := gaussianPDFReal_pos 0 t y ht.ne'
  have hgT : gaussianPDFReal 0 ((↑t : ℝ) / σ ^ 2).toNNReal (y / σ) =
      σ * gaussianPDFReal 0 t y := by
    have ht' : (0 : ℝ) < t := by exact_mod_cast ht
    have hsqrt : √(2 * π * ((t : ℝ) / σ ^ 2)) = √(2 * π * t) / σ := by
      rw [← mul_div_assoc, Real.sqrt_div' _ (sq_nonneg σ), Real.sqrt_sq hσ.le]
    have hexp : -(y / σ - 0) ^ 2 / (2 * ((t : ℝ) / σ ^ 2)) = -(y - 0) ^ 2 / (2 * t) := by
      simp only [sub_zero]
      field_simp
    simp only [gaussianPDFReal_def]
    rw [Real.coe_toNNReal _ (by positivity), hsqrt, hexp, inv_div]
    have hne : √(2 * π * (t : ℝ)) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
    field_simp
  have key : ∀ a b : ℝ, 0 ≤ a → max (a * b) 0 = a * max b 0 := fun a b ha => by
    rw [mul_max_of_nonneg _ _ ha, mul_zero]
  rw [hgT, key _ _ hgpos.le, key _ _ (mul_nonneg hσ.le hgpos.le)] at h
  refine mul_left_cancel₀ hgpos.ne' (h.trans ?_)
  field_simp

/- Paper: p. 1066, the three scaling displays in the printed (unsigned) form, for
   continuous versions of the densities that are pointwise nonnegative. -/
theorem scaling_relations_of_nonneg (σ : ℝ) (t : ℝ≥0) (hσ : 0 < σ) (ht : 0 < t)
    (φ₁ φσ : ℝ → ℝ → ℝ) (c₁ cσ : ℝ → ℝ → ℝ) (ψ₁ ψσ : ℝ → ℝ) (ν : ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W)
    (h1 : IsJointDensity P W 1 0 t φ₁)
    (hσ' : IsJointDensity P W σ 0 ((↑t : ℝ) / σ ^ 2).toNNReal φσ)
    (hc1 : IsCondDensity P W 1 t c₁)
    (hcσ : IsCondDensity P W σ ((↑t : ℝ) / σ ^ 2).toNNReal cσ)
    (hψ₁ : IsInftyDensity P W 1 ν ψ₁) (hψσ : IsInftyDensity P W σ (ν * σ ^ 2) ψσ)
    (hφcont : Continuous (Function.uncurry φ₁) ∧ Continuous (Function.uncurry φσ))
    (hccont : Continuous (Function.uncurry c₁) ∧ Continuous (Function.uncurry cσ))
    (hψcont : Continuous ψ₁ ∧ Continuous ψσ)
    (hφnn : (∀ x y, 0 ≤ φ₁ x y) ∧ ∀ x y, 0 ≤ φσ x y)
    (hcnn : (∀ x y, 0 ≤ c₁ x y) ∧ ∀ x y, 0 ≤ cσ x y)
    (hψnn : (∀ x, 0 ≤ ψ₁ x) ∧ ∀ x, 0 ≤ ψσ x) :
    (∀ x y, φ₁ x y = σ⁻¹ ^ 3 * φσ (x / σ ^ 2) (y / σ)) ∧
    (∀ x y, c₁ x y = σ⁻¹ ^ 2 * cσ (x / σ ^ 2) (y / σ)) ∧
    (∀ x, ψ₁ x = σ⁻¹ ^ 2 * ψσ (x / σ ^ 2)) := by
  obtain ⟨hA, hB, hC⟩ := scaling_relations_posPart σ t hσ ht φ₁ φσ c₁ cσ ψ₁ ψσ ν P W hW
    h1 hσ' hc1 hcσ hψ₁ hψσ hφcont hccont hψcont
  refine ⟨fun x y => ?_, fun x y => ?_, fun x => ?_⟩
  · simpa [max_eq_left (hφnn.1 x y), max_eq_left (hφnn.2 (x / σ ^ 2) (y / σ))] using hA x y
  · simpa [max_eq_left (hcnn.1 x y), max_eq_left (hcnn.2 (x / σ ^ 2) (y / σ))] using hB x y
  · simpa [max_eq_left (hψnn.1 x), max_eq_left (hψnn.2 (x / σ ^ 2))] using hC x

/- STATEMENT NOTE for `scaling_relations` below (machine-checked, sorry-free).
   As soon as one continuous version `φ₁` of the `σ = 1` joint density exists, the first
   (unsigned) identity of `scaling_relations` fails for another continuous version: `φ₁ + min x 0`
   is also a continuous `IsJointDensity` (`IsJointDensity.add_min`), and the two differ at
   `(-1, 0)`.  So `scaling_relations` as stated is provable only if *no* continuous joint density
   exists, which contradicts Prop. 2.2 / Yor's formula.  The provable content is
   `scaling_relations_posPart` and `scaling_relations_of_nonneg` above. -/
theorem scaling_relations_unsigned_obstruction (σ : ℝ) (t : ℝ≥0)
    (φ₁ φσ : ℝ → ℝ → ℝ) (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (h1 : IsJointDensity P W 1 0 t φ₁) (hφcont : Continuous (Function.uncurry φ₁)) :
    ¬ ∀ φ₁' : ℝ → ℝ → ℝ, IsJointDensity P W 1 0 t φ₁' → Continuous (Function.uncurry φ₁') →
        ∀ x y, φ₁' x y = σ⁻¹ ^ 3 * φσ (x / σ ^ 2) (y / σ) :=
  h1.not_forall_version_eq hφcont _

/- Paper: p. 1066, three scaling displays after Prop. 2.2.
   Plain recap: Brownian scaling relates densities at σ = 1 and general σ.
   Hypothesis: the named densities are continuous nonnegative versions (Prop. 2.2), so
   a.e. identities from the law of `s ↦ σ W_{s/σ²}` upgrade to pointwise ones.
   PAPER NOTE: nonnegativity is required for the unsigned pointwise form
   (`scaling_relations_unsigned_obstruction`); densities are nonnegative by construction. -/
theorem scaling_relations (σ : ℝ) (t : ℝ≥0) (hσ : 0 < σ) (ht : 0 < t)
    (φ₁ φσ : ℝ → ℝ → ℝ) (c₁ cσ : ℝ → ℝ → ℝ) (ψ₁ ψσ : ℝ → ℝ) (ν : ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBM P W)
    (h1 : IsJointDensity P W 1 0 t φ₁)
    (hσ' : IsJointDensity P W σ 0 ((↑t : ℝ) / σ ^ 2).toNNReal φσ)
    (hc1 : IsCondDensity P W 1 t c₁)
    (hcσ : IsCondDensity P W σ ((↑t : ℝ) / σ ^ 2).toNNReal cσ)
    (hψ₁ : IsInftyDensity P W 1 ν ψ₁) (hψσ : IsInftyDensity P W σ (ν * σ ^ 2) ψσ)
    (hφcont : Continuous (Function.uncurry φ₁) ∧ Continuous (Function.uncurry φσ))
    (hccont : Continuous (Function.uncurry c₁) ∧ Continuous (Function.uncurry cσ))
    (hψcont : Continuous ψ₁ ∧ Continuous ψσ)
    (hφnn : (∀ x y, 0 ≤ φ₁ x y) ∧ ∀ x y, 0 ≤ φσ x y)
    (hcnn : (∀ x y, 0 ≤ c₁ x y) ∧ ∀ x y, 0 ≤ cσ x y)
    (hψnn : (∀ x, 0 ≤ ψ₁ x) ∧ ∀ x, 0 ≤ ψσ x) :
    (∀ x y, φ₁ x y = σ⁻¹ ^ 3 * φσ (x / σ ^ 2) (y / σ)) ∧
    (∀ x y, c₁ x y = σ⁻¹ ^ 2 * cσ (x / σ ^ 2) (y / σ)) ∧
    (∀ x, ψ₁ x = σ⁻¹ ^ 2 * ψσ (x / σ ^ 2)) :=
  scaling_relations_of_nonneg σ t hσ ht φ₁ φσ c₁ cσ ψ₁ ψσ ν P W hW
    h1 hσ' hc1 hcσ hψ₁ hψσ hφcont hccont hψcont hφnn hcnn hψnn

/- STATEMENT NOTE for `girsanov_density` below (machine-checked, sorry-free): the same sign
   obstruction.  Given one continuous version `φμ` of the drifted joint density, the unsigned
   identity (2.2) fails for the continuous version `φμ + min x 0`. -/
theorem girsanov_density_unsigned_obstruction (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (σ μ : ℝ) (t : ℝ≥0) (φμ φ0 : ℝ → ℝ → ℝ) (h1 : IsJointDensity P W σ μ t φμ)
    (hcont : Continuous (Function.uncurry φμ)) :
    ¬ ∀ φμ' : ℝ → ℝ → ℝ, IsJointDensity P W σ μ t φμ' → Continuous (Function.uncurry φμ') →
        ∀ x y, φμ' x y =
          Real.exp (μ / σ * y + μ ^ 2 / (2 * σ ^ 2) * (t : ℝ)) * φ0 x (y + μ / σ * (t : ℝ)) :=
  h1.not_forall_version_eq hcont _

/- Paper: p. 1066, (2.2) Cameron–Martin–Girsanov.
   Plain recap: adding drift μ shifts the joint density by an exponential Girsanov factor.
   Continuous nonnegative versions of the densities are assumed so a.e. identities become
   pointwise. PAPER NOTE: nonnegativity as in `scaling_relations`. -/
theorem girsanov_density (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBM P W) (σ μ : ℝ) (t : ℝ≥0) (hσ : 0 < σ) (ht : 0 < t)
    (φμ φ0 : ℝ → ℝ → ℝ) (h1 : IsJointDensity P W σ μ t φμ)
    (h0 : IsJointDensity P W σ 0 t φ0)
    (hcont : Continuous (Function.uncurry φμ) ∧ Continuous (Function.uncurry φ0))
    (hnn : (∀ x y, 0 ≤ φμ x y) ∧ ∀ x y, 0 ≤ φ0 x y) :
    ∀ x y, φμ x y =
      Real.exp (μ / σ * y + μ ^ 2 / (2 * σ ^ 2) * (t : ℝ)) * φ0 x (y + μ / σ * (t : ℝ)) := by
  -- Under the Girsanov tilt `exp(−θ W_t − θ² t / 2)` with market price of risk θ = μ/σ,
  -- `s ↦ W_s + θ (s ∧ t)` is again a Brownian motion (MathFin constant-θ Girsanov, extended
  -- past the horizon), so the μ-drifted joint law, tilted and shifted by `y ↦ y + θ t`, is the
  -- zero-drift joint law (`jointLaw_girsanov`).  Continuity upgrades the resulting a.e.
  -- identity of densities to a pointwise one (`jointDensity_girsanov_posPart`).
  intro x y
  have hμ : σ * (μ / σ) = μ := mul_div_cancel₀ μ hσ.ne'
  have h := jointDensity_girsanov_posPart P W hW σ (μ / σ) t φμ φ0 (hμ.symm ▸ h1) h0
    hcont.1 hcont.2 x y
  rw [max_eq_left (hnn.1 x y), max_eq_left (hnn.2 x _)] at h
  rw [h]
  congr 2
  rw [div_pow]
  ring

end Lyasoff2016
