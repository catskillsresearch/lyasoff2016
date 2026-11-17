# Proof holes (Lyasoff 2016)

Inventory of paper-facing Lean holes, ordered **prove-first**.

**Updated:** 2026-11-17T14:07:11Z
**Holes:** 3 open+blocked · 1 open · 2 blocked · 36 done.

**Live board:** [`holes.html`](holes.html) + [`holes-graph.json`](holes-graph.json).

```bash
python3 scripts/build_holes.py
python3 -m http.server 8765   # then open http://localhost:8765/holes.html
```

## Open now (Layer 0)

| Id | Label | File |
|---|---|---|
| `weak_joint_fokker_planck_product` | Weak FP product | `Lyasoff2016/FokkerPlanck.lean:3411` |

## By section

### §1 — 0 hole(s)

| Status | Id | Label | File |
|---|---|---|---|
| done | `time_reversal` | §1 time rev | `Lyasoff2016/Setting.lean:90` |

### §2 — 0 hole(s)

| Status | Id | Label | File |
|---|---|---|---|
| done | `lemma_2_1` | Lem 2.1 | `Lyasoff2016/Auxiliary.lean:57` |
| done | `prop_2_2` | Prop 2.2 | `Lyasoff2016/Auxiliary.lean:64` |
| done | `scaling_relations` | Scaling | `Lyasoff2016/Auxiliary.lean:184` |
| done | `girsanov_density` | Girsanov (2.2) | `Lyasoff2016/Auxiliary.lean:219` |

### §3 — 3 hole(s)

| Status | Id | Label | File |
|---|---|---|---|
| done | `infinite_integral_finite` | ∫₀^∞ finite | `Lyasoff2016/FokkerPlanck.lean:97` |
| done | `Z_stationary` | Z stationary | `Lyasoff2016/FokkerPlanck.lean:439` |
| done | `dufresne_zero_flux` | Zero-flux ODE | `Lyasoff2016/FokkerPlanck.lean:455` |
| done | `perpetuity_inv_moment` | E[A⁻¹]=−ν | `Lyasoff2016/FokkerPlanck.lean:1192` |
| done | `perpetuity_neg_moments` | E[A⁻ⁿ] | `Lyasoff2016/FokkerPlanck.lean:2756` |
| done | `dufresne_theorem_sigma_one` | Dufresne σ=1 | `Lyasoff2016/FokkerPlanck.lean:2828` |
| done | `dufresne_theorem` | Dufresne thm | `Lyasoff2016/FokkerPlanck.lean:2918` |
| done | `ito_expInt_test_product` | Ito (3.4a) | `Lyasoff2016/JointFokkerPlanckIto.lean:376` |
| done | `ito_timeReversed_expInt_test_product` | Ito (3.4b) | `Lyasoff2016/JointFokkerPlanckIto.lean:953` |
| done | `joint_dynkin_Aop_product` | Dynkin (3.5) | `Lyasoff2016/FokkerPlanck.lean:3233` |
| open | `weak_joint_fokker_planck_product` | Weak FP product | `Lyasoff2016/FokkerPlanck.lean:3411` |
| done | `eq_zero_of_integral_product_eq_zero` | Product fund. lemma | `Lyasoff2016/JointFokkerPlanckHelpers.lean:70` |
| blocked | `jointFokkerPlanckAdjoint_eq_zero` | Adjoint = 0 | `Lyasoff2016/FokkerPlanck.lean:3425` |
| blocked | `fokker_planck_joint` | FP (3.6b) | `Lyasoff2016/FokkerPlanck.lean:3446` |
| done | `remark_3_2` | Rem 3.2 | `Lyasoff2016/FokkerPlanck.lean:3500` |

### §4 — 0 hole(s)

| Status | Id | Label | File |
|---|---|---|---|
| done | `theorem_4_1_pde` | Thm 4.1 PDE | `Lyasoff2016/Foliation.lean:60` |
| done | `theorem_4_1_striking` | Thm 4.1 (4.4) | `Lyasoff2016/Foliation.lean:75` |
| done | `formula_4_6` | (4.6) | `Lyasoff2016/Foliation.lean:144` |
| done | `prop_4_4` | Prop 4.4 | `Lyasoff2016/Foliation.lean:363` |
| done | `theorem_4_5` | Thm 4.5 | `Lyasoff2016/Foliation.lean:410` |

### §5 — 0 hole(s)

| Status | Id | Label | File |
|---|---|---|---|
| done | `g_solves_contour_equation` | g contour eq | `Lyasoff2016/IntegralReps.lean:109` |
| done | `yor_formula_classical` | Yor classical | `Lyasoff2016/IntegralReps.lean:231` |
| done | `remark_5_1` | Rem 5.1 | `Lyasoff2016/IntegralReps.lean:222` |
| done | `pi_formula` | π / π/2 | `Lyasoff2016/IntegralReps.lean:270` |
| done | `yor_formula` | Yor via Rem 5.1 | `Lyasoff2016/IntegralReps.lean:238` |

### §6 — 0 hole(s)

| Status | Id | Label | File |
|---|---|---|---|
| done | `S_zero` | S_{0,p} | `Lyasoff2016/Asian.lean:92` |
| done | `S_closed_form` | S_{k,p} | `Lyasoff2016/Asian.lean:166` |
| done | `benchmark_k_zero` | k=0 benchmark | `Lyasoff2016/Asian.lean:331` |
| done | `asian_price_formula` | Asian price | `Lyasoff2016/Asian.lean:395` |
| done | `asian_delta` | Asian delta | `Lyasoff2016/Asian.lean:502` |
| done | `table1_asian_enclosure` | Table 1 | `Lyasoff2016/Tables.lean:142` |
| done | `table2_asian_enclosure` | Table 2 | `Lyasoff2016/Tables.lean:156` |
| done | `table3_asian_enclosure` | Table 3 | `Lyasoff2016/Tables.lean:170` |
| done | `table4_asian_enclosure` | Table 4 | `Lyasoff2016/Tables.lean:184` |

## Dependency sketch

```mermaid
flowchart TD
  L2[lemma_2_1] --> P22[prop_2_2]
  P22 --> Scale[scaling_relations]
  Scale --> Gir[girsanov_density]
  Inf[infinite_integral_finite] --> Z[Z_stationary]
  Z --> Inv[perpetuity_inv_moment]
  ZF[dufresne_zero_flux] --> Inv
  Inv --> Neg[perpetuity_neg_moments]
  Neg --> D1[dufresne_theorem_sigma_one]
  D1 --> D[dufresne_theorem]
  ItoA[ito_expInt_test_product] --> Dyn[joint_dynkin_Aop_product]
  ItoB[ito_timeReversed] --> Dyn
  Dyn --> Weak[weak_joint_fokker_planck_product]
  Weak --> Adj[jointFokkerPlanckAdjoint_eq_zero]
  Fund[eq_zero_of_integral_product] --> Adj
  Adj --> FP[fokker_planck_joint]
  TR[time_reversal] --> FP
  P22 --> FP
  FP --> T41[theorem_4_1_pde]
  T41 --> F46[formula_4_6]
  F46 --> P44[prop_4_4]
  P44 --> T45[theorem_4_5]
  T45 --> G[g_solves_contour_equation]
  G --> Pi[pi_formula]
  YorC[yor_formula_classical] --> Pi
  Pi --> Asian[asian_price_formula]
  Gir --> Asian
  Asian --> Delta[asian_delta]
  Asian --> T1[tables 1-4]
```

