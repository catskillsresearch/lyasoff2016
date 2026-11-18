---
bibliography: references.bib
---

# Lyasoff 2016 in Lean 4

Paper-facing writeup of the formalization of Andrew Lyasoff, *Another look at the integral of exponential Brownian motion and the pricing of Asian options*, Finance Stoch. **20** (2016) 1061–1096.

Every paper-facing hole on the dependency board is **done** (`sorryCount = 0`). Open [`holes.html`](holes.html) for the theorem graph (data is embedded; no server needed). This tree is the linear paper narrative: each `.lean` has a peer subsection with AI English (`*_ailean.txt`), paper ascriptions in green TeX boxes (`*_math.txt` / `Lyasoff2016/*.gist`), and a single `@import` of the Lean source.

Rebuild leaves / section SVGs: `python3 scripts/scaffold_actions_writeup.py`. Flatten + TeX: `python3 scripts/compile_md_tree.py --tex-only` (or omit flags for PDF).

- [Abstract](Actions/Abstract.md)
- [Introduction](Actions/Introduction.md)
- [§1 Setting and time reversal](Actions/Section1.md)
- [§2 Auxiliary results](Actions/Section2.md)
- [§3 Fokker–Planck and Dufresne](Actions/Section3.md)
- [§4 Foliation of the joint law](Actions/Section4.md)
- [§5 Contour equations and integral representations](Actions/Section5.md)
- [§6 Asian options](Actions/Section6.md)
