# Provenance

This repository is a standalone Lean 4 / Mathlib formalization of Andrew
Lyasoff, *Another look at the integral of exponential Brownian motion and
the pricing of Asian options*, Finance Stoch. **20** (2016) 1061–1096. It is
not a thin wrapper and not a reimplementation of an independent
formalization.

**Andrew Lyasoff did not participate in, review, or endorse this
formalization.** There are no other human collaborators. The Lean
development was produced by Lars Warren Ericson with AI-agent assistance
under his direction and review. The source paper is cited as literature
only and is not licensed under this repository's Apache-2.0 terms (see
`NOTICE`).

**This repository is registered with Palomar on its own**, for the Lyasoff 2016
Asian-options development alone, following the Challenge / Solution /
`comparator.json` / `formalization.yaml` pattern used in
[`catskillsresearch/scott_models`](https://github.com/catskillsresearch/scott_models)
and [`catskillsresearch/nowakowska1982`](https://github.com/catskillsresearch/nowakowska1982).
Registry entry:
[PALOMAR-2026-11-19-000018](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-19-000018&version=1),
version 1.

## Framing

Primary story: **rigorous reconstruction / verification** of Lyasoff 2016
(§1–§6), including Yor’s joint density (1.1) / Rem 5.1, the π / π/2
integral representations, and the Asian call pricing formula. Secondary
story: closed forms for the Asian inner integral `S_{k,p}` and the
undiscounted call as a double integral of `Re F`.

Proof-path note (also in the Asian writeup): Lean often identifies
`yorDensity` with the joint law via Laplace matching and transfers density
*from* Yor *to* the π-family, rather than deriving Yor by specializing a
previously proved π-density as in the paper’s narrative order. The
compared conclusions match the paper.

## Proof chart and Comparator

The paper-facing proof chart (`holes-graph.json` / `HOLES.md`) lists **40**
done holes. Offline axiom audit (`scripts/validate_chart_axioms.sh`):

| Class | Count | Axioms |
| --- | ---: | --- |
| Comparator family | 40 (all chart theorems) | ⊆ `{propext, Quot.sound, Classical.choice}` |
| Reported numerical tables | 4 | definitions only; no price-enclosure claim |

**Project rule: no Lean `axiom`.** No unfinished library proofs remain.

Tables 1–4 are reported numerical data only. The former numerical enclosure
statements were withdrawn, not proved. Independent Python computations support
agreement at absolute level 1e-9, but this is not a Lean certificate. The tables
remain outside `comparator.json`. All proof-chart theorems use only `propext`,
`Quot.sound`, and `Classical.choice`.

Selected §4 Comparator theorems (`theorem_4_1_pde`, `theorem_4_1_striking`,
`formula_4_6`, `theorem_4_5`) are **conditional rearrangements**: they assume
the paper’s foliation PDE / striking / ODE / Laplace inputs and prove the
displayed identities under those hypotheses. The Comparator theorems
`cond_density_satisfies_*` discharge those inputs by exhibiting a conditional
density (Brownian-scaled Yor) satisfying each of them; see the §4 Asian
writeup.

Compared declarations live in namespace `Lyasoff2016`. `Lyasoff2016Comparator/Challenge.lean` is
a single Mathlib-only statement file (deliberate `sorry` holes).
`Lyasoff2016Comparator/Solution.lean` imports the `Lyasoff2016/` library.

## Dependencies

Proofs use Mathlib together with these dependencies: BrownianMotion as a
path copy under `vendor/brownian-motion` (upstream pin with a few unfinished
declarations removed, listed in `vendor/SOURCES`), and formal-mathfin and
kolmogorov_extension4 (transitive) as Lake Git pins in `lake-manifest.json`. Challenge imports Mathlib only
(including Mathlib’s `IsBrownianReal`). Pin ledger: `vendor/SOURCES`.

No project-defined `axiom`s or unfinished proofs remain in `Lyasoff2016/`.
Intentional challenge stubs in `Lyasoff2016Comparator/Challenge.lean` are unchanged.
