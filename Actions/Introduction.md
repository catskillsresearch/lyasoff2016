# Introduction

@import "../Lyasoff2016_files.svg" {code_block=false, caption="Lyasoff2016: module import graph"}

The Lean library `Lyasoff2016` follows the paper’s section order. Density identities are proved without classical citation axioms (Palomar-clean). Table enclosures and two Leibniz / differentiation-under-integral steps for §6 use explicitly marked classical certificates.

**Faithfulness note (Yor / Rem 5.1).** The paper recovers Yor by specializing a previously proved $\pi$-density. Lean reaches the same joint law by Laplace matching: `yorDensity` is identified with `jointLaw`, and density is often transferred *from* Yor *to* the $\pi$-family rather than the other way around.
