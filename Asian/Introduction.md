# Introduction

@import "../Asian.svg" {code_block=false, caption="Section dependencies (§1–§6): arrows point from a prerequisite section to the section that uses it"}

This formalization reconstructs Lyasoff's Asian option model [@lyasoff2016]
in Lean 4 [@lean4; @gh-lean4], using Mathlib [@mathlib2020; @gh-mathlib4].

The Lean library `Lyasoff2016` follows the paper’s section order. Density identities are proved without classical citation axioms (Palomar-clean). The §6 differentiation results are proved. Tables 1–4 are reported data only, not certified prices; the former numerical enclosure statements were withdrawn, not proved.

**Faithfulness note (Yor / Rem 5.1).** The paper recovers Yor by specializing a previously proved $\pi$-density. Lean reaches the same joint law by Laplace matching: `yorDensity` is identified with `jointLaw`, and density is often transferred *from* Yor *to* the $\pi$-family rather than the other way around.

## Sources, software and AI assistance

The Brownian-motion and stochastic-calculus proofs build on the pinned
BrownianMotion, Kolmogorov extension and formal-mathfin repositories
[@gh-brownian-motion; @gh-kolmogorov-extension4; @gh-formal-mathfin].
All direct and transitive Lake repositories, with their pinned revisions, are
credited in the bibliography; the exact full hashes are in `lake-manifest.json`
and `vendor/SOURCES`. LeanCert is not a dependency of this formalization.

Challenge/Solution packaging follows the scott_models and nowakowska1982
repositories [@gh-scott-models; @gh-nowakowska1982], using the Palomar policy,
Comparator conventions and formalization metadata schema
[@gh-palomar-policy; @gh-comparator; @gh-formalization-yaml]. These are tooling
credits, not a claim of Palomar registration, submission or independent review:
**Palomar Registration: TBD**. The Unicode-to-LaTeX listing sanitizer was adapted
from scott1964 [@gh-scott1964]. The formalization source is available on GitHub
[@gh-lyasoff2016].

The independent Python table checks use the Geman--Yor transform and Linetsky's
spectral representation [@gemanyor1993; @linetsky2004], with mpmath's Talbot and
optional de Hoog inversions [@mpmath; @talbot1979; @dehoog1982]. These are numerical
experiments, not Lean-certified error bounds. Only agreement at absolute level
1e-9 is reported; no theorem connects the printed table digits to the price.

Lars Warren Ericson directed and reviewed the development and takes
responsibility for the mathematical claims. As recorded in `formalization.yaml`,
AI assistance used Cursor Grok 4.7, Cursor Composer, Claude Fable and Google
Gemini through Cursor [@ai-cursor-agents]. The module English summaries record
Grok Bot as their AI author [@ai-grok-bot]. These names reproduce the repository's
provenance records, not guesses about model identities or independent reviews.
Andrew Lyasoff did not participate in, review or endorse this formalization.
