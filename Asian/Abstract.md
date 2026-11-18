# Abstract

Lyasoff gives integral formulae for the joint law of $\bigl(\int_0^t e^{\sigma W_s+\mu s}\,ds,\, W_t\bigr)$ via a contour equation for a kernel $g$, recovering Yor’s density as an extremal case, and applies the $\pi/2$ formula of order $4$ to Asian call pricing and numerical tables.

This formalization checks the paper’s definitions and main theorems in Lean 4 / Mathlib, including the constructive $\pi$/$\pi/2$ density identifications, the Asian pricing identity $\mathbb{E}[(\int-k)_+]=\iint \Re F$, the strike-delta identity, and classical numerical certificates for Tables 1–4.
