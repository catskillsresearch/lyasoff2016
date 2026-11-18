---
bibliography: references.bib
---

# Formalization of Lyasoff's Asian Option Model

Paper-facing writeup of the formalization of Andrew Lyasoff, *Another look at the integral of exponential Brownian motion and the pricing of Asian options*, Finance Stoch. **20** (2016) 1061–1096.

Every paper-facing hole on the dependency board is **done** (`sorryCount = 0`). Open [`holes.html`](holes.html) for the theorem graph (data is embedded; no server needed). This tree is the linear paper narrative: each `.lean` has a peer subsection with AI English (`*_ailean.txt`), paper ascriptions in green TeX boxes (`*_math.txt` / `Lyasoff2016/*.gist`), and a single `@import` of the Lean source.

Rebuild leaves / section SVGs: `python3 scripts/scaffold_asian_writeup.py`. Flatten + TeX: `python3 scripts/compile_md_tree.py --tex-only` (or omit flags for PDF).

- [Abstract](Asian/Abstract.md)
- [Introduction](Asian/Introduction.md)
- [§1 Setting and time reversal](Asian/Section1.md)
- [§2 Auxiliary results](Asian/Section2.md)
- [§3 Fokker–Planck and Dufresne](Asian/Section3.md)
- [§4 Foliation of the joint law](Asian/Section4.md)
- [§5 Contour equations and integral representations](Asian/Section5.md)
- [§6 Asian options](Asian/Section6.md)
