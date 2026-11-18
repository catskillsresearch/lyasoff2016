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

Packaging follows the Palomar Challenge / Solution / `comparator.json` /
`formalization.yaml` pattern used in
[`catskillsresearch/scott_models`](https://github.com/catskillsresearch/scott_models)
and [`catskillsresearch/nowakowska1982`](https://github.com/catskillsresearch/nowakowska1982).

## Framing

Primary story: **rigorous reconstruction / verification** of Lyasoff 2016
(§1–§6), including Yor’s joint density (1.1) / Rem 5.1, the π / π/2
integral representations, and the Asian call pricing formula. Secondary
story: closed forms for the Asian inner integral `S_{k,p}` and the
undiscounted call as a double integral of `Re F`.

Proof-path note (also in the Actions writeup): Lean often identifies
`yorDensity` with the joint law via Laplace matching and transfers density
*from* Yor *to* the π-family, rather than deriving Yor by specializing a
previously proved π-density as in the paper’s narrative order. The
compared conclusions match the paper.

## Proof chart and Comparator

The paper-facing proof chart (`holes-graph.json` / `HOLES.md`) lists **38**
done holes. Offline axiom audit (`scripts/validate_chart_axioms.sh`):

| Class | Count | Axioms |
| --- | ---: | --- |
| Comparator family | 34 | ⊆ `{propext, Quot.sound, Classical.choice}` |
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
displayed identities under those hypotheses. They do not establish those
inputs for the conditional density; see `known_gaps` and the §4 Actions
writeup.

Compared declarations live in namespace `Lyasoff2016`. `Challenge.lean` is a
single Mathlib-only statement file (deliberate `sorry` holes).
`Solution.lean` imports the `Lyasoff2016/` library.

## Dependencies

Proofs use Mathlib together with public Git dependencies pinned in
`lake-manifest.json` (BrownianMotion, formal-mathfin /
kolmogorov_extension4 as transitive). Challenge imports Mathlib only
(including Mathlib’s `IsBrownianReal`). Pin ledger: `vendor/SOURCES`.

No project-defined `axiom`s or unfinished proofs remain in `Lyasoff2016/`.
Intentional challenge stubs in `Challenge.lean` are unchanged.
