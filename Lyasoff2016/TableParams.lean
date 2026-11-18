/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
# §6 Tables 1–4 (pp. 1094–1095) — parameter regimes

Paper: all cases use S₀ = 1, r = 2.5% = 5/200; prices at t = 0.

`err0` records the paper's *reported* error figure for its method at K = 0 only; it is
not claimed in Lean at the printed strikes. The Lean table theorems claim agreement with
the printed digits to `tableClaimTol = 1e-9` only (see `tableClaimTol`).
-/
module

public import Mathlib


@[expose] public section

open scoped Real

noncomputable section
namespace Lyasoff2016

/- Paper: p. 1094–1095, Tables 1–4 parameter regimes.
   Plain recap: Asian calls with fixed r = 2.5%, S₀ = 1, varying T, σ, K. -/
structure TableParams where
  T : ℝ
  σ : ℝ
  mp_dps : ℕ
  err0 : ℝ  -- paper's reported K = 0 error figure (documentation only; not claimed)

/-- Table 1: T = 1/2, σ = 22/100, mp.dps = 120, paper-reported K=0 error ≤ 1e-15 (not claimed). -/
def table1Params : TableParams :=
  ⟨(1 : ℝ) / 2, (22 : ℝ) / 100, 120, (1e-15 : ℝ)⟩

/-- Table 2: T = 1/2, σ = 1/3, mp.dps = 60, paper-reported K=0 error ≤ 1e-11 (not claimed). -/
def table2Params : TableParams :=
  ⟨(1 : ℝ) / 2, (1 : ℝ) / 3, 60, (1e-11 : ℝ)⟩

/-- Table 3: T = 1, σ = 22/100, mp.dps = 60, paper-reported K=0 error ≤ 1e-12 (not claimed). -/
def table3Params : TableParams :=
  ⟨(1 : ℝ), (22 : ℝ) / 100, 60, (1e-12 : ℝ)⟩

/-- Table 4: T = 1, σ = 1/3, mp.dps = 45, paper-reported K=0 error ≤ 1e-11 (not claimed). -/
def table4Params : TableParams :=
  ⟨(1 : ℝ), (1 : ℝ) / 3, 45, (1e-11 : ℝ)⟩

/-- Claimed absolute tolerance for all four tables (Lyasoff pp. 1094–1095): the Lean table
theorems assert only that `asianMarketPrice` reproduces each printed digit string to within
`1e-9`. An independent high-precision check (`scripts/asian_tables_independent_check.py`:
Geman–Yor/Talbot Laplace inversion and Linetsky's spectral formula, agreeing to ~1e-41)
finds a worst miss of 2.2e-10 over the 24 printed values; the paper's per-table K = 0
error figures (`err0`, down to 1e-15) do not hold at the printed strikes and are not
claimed. -/
def tableClaimTol : ℝ := (1e-9 : ℝ)

/-- Market strikes K in Tables 1–4 (paper); integral strike is `K * T` with S₀ = 1. -/
def tableStrikes : Fin 6 → ℚ
  | 0 => (7 : ℚ) / 10
  | 1 => (8 : ℚ) / 10
  | 2 => (9 : ℚ) / 10
  | 3 => 1
  | 4 => (11 : ℚ) / 10
  | 5 => (12 : ℚ) / 10

end Lyasoff2016
