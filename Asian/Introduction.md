# Introduction

@import "../Asian.svg" {code_block=false, caption="Section dependencies (§1–§6): edge A → B means a `.lean` in A imports a `.lean` in B"}

The Lean library `Lyasoff2016` follows the paper’s section order. Density identities are proved without classical citation axioms (Palomar-clean). The §6 differentiation results are proved. Tables 1–4 are reported data only, not certified prices; the former numerical enclosure statements were withdrawn, not proved.

**Faithfulness note (Yor / Rem 5.1).** The paper recovers Yor by specializing a previously proved $\pi$-density. Lean reaches the same joint law by Laplace matching: `yorDensity` is identified with `jointLaw`, and density is often transferred *from* Yor *to* the $\pi$-family rather than the other way around.
