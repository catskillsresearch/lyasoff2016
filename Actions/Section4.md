# §4 Foliation of the joint law

Paper: Lyasoff pp. 1071–1079 (Thm 4.1, (4.4), Prop. 4.4, Thm 4.5).

The Comparator entries in this section are **conditional implications**: Lean
proves the algebraic / change-of-variables rearrangements under hypotheses
`SatisfiesTheorem41PDE`, `SatisfiesStrikingIdentity`, `SatisfiesFoliationODE`,
and `TransformedMassIdentity` / `HasLaplaceReduction`. Establishing those
inputs for the conditional density itself remains open (`known_gaps`).

@import "Section4.svg" {code_block=false, caption="Subsection dependencies within §4"}

Subsections follow Lean import order; labels are mathematical English.

- [Foliation of the joint law](Section4/Foliation.md)
