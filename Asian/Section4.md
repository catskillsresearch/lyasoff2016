# §4 Foliation of the joint law

Paper: Lyasoff pp. 1071–1079 (Thm 4.1, (4.4), Prop. 4.4, Thm 4.5).

The Comparator theorems `theorem_4_1_pde`, `theorem_4_1_striking`,
`formula_4_6`, `prop_4_4` and `theorem_4_5` prove the displayed identities
from the paper's analytic inputs (`SatisfiesTheorem41PDE`,
`SatisfiesStrikingIdentity`, `SatisfiesFoliationODE`,
`TransformedMassIdentity` / `HasLaplaceReduction`). The theorems
`cond_density_satisfies_*` discharge those inputs for a genuine conditional
density (Brownian-scaled Yor, `CondDensityYor`), so the identities hold for
the conditional density itself.

@import "Section4.svg" {code_block=false, caption="Subsection dependencies within §4"}

Subsections follow Lean import order; labels are mathematical English.

- [Brownian scaling of joint densities from the reference volatility `2`](Section4/JointDensityScaling.md)
- [A genuine conditional density of `(expInt, W)` from Yor's formula](Section4/CondDensityYor.md)
- [Reciprocal moments from the transformed mass identity (4.7)](Section4/StrikingMass.md)
- [Foliation of the joint law](Section4/Foliation.md)
