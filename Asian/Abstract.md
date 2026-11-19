# Abstract

Lyasoff gives integral formulae for the joint law of $\bigl(\int_0^t e^{\sigma W_s+\mu s}\,ds,\, W_t\bigr)$ via a contour equation for a kernel $g$, recovering Yor’s density as an extremal case, and applies the $\pi/2$ formula of order $4$ to Asian call pricing and numerical tables.

This formalization checks the paper’s definitions and main theorems in Lean 4 / Mathlib, including the constructive $\pi$/$\pi/2$ density identifications, the Asian pricing identity $\mathbb{E}[(\int-k)_+]=\iint \Re F$ and the strike-delta identity. All 40 proof-chart theorems are proved, with no `sorry` and no project axioms; their axiom footprint is only `propext`, `Quot.sound` and `Classical.choice`. A supplementary bent-contour form of the Asian integral is proved under one stated domination hypothesis (`BendDominated`), recorded as a known gap.

Tables 1–4 are recorded as the paper’s reported numerical data only. They are not certified in Lean, and no Lean statement relates the printed digits to the Asian price. An independent high-precision Python computation, outside Lean, agrees with the printed values to about $10^{-9}$. Palomar registration: [PALOMAR-2026-11-19-000018](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-19-000018&version=1), version 1.
