# Lyasoff 2016 in Lean 4

Formalization of Andrew Lyasoff,
*Another look at the integral of exponential Brownian motion and the pricing of Asian options*,
Finance Stoch. **20** (2016) 1061–1096.

## Build

```bash
lake exe cache get   # optional, after lake update
lake build Lyasoff2016
```

Toolchain: Lean `v4.35.0` (see `lean-toolchain`), Mathlib pin in `lakefile.toml`.

## Layout

| Path | Content |
|------|---------|
| `sources/lyasoff2016.pdf` | Source paper |
| `Lyasoff2016/*.lean` | Section modules (§0–§6) with paper-position comments |
| `vendor/` | Verbatim copies of BrownianMotion, kolmogorov_extension4, formal-mathfin (see `vendor/SOURCES`) |

## Status

Lake project builds. Deterministic cores proved include Lemma 2.1 bounds, foliation/ODE calculus,
`dufresne_zero_flux`, Girsanov scaling, and Asian `S_*` / strike-derivative lemmas. Stochastic and
contour theorems are stated against Mathlib `IsBrownianReal` and vendored Itô/Girsanov; remaining
`sorry`s track paper arguments awaiting full discharge.

## Proof-hole board

Same style as the AEC board: dependency graph of paper-facing holes (open / blocked / done).

```bash
python3 scripts/build_holes.py
python3 -m http.server 8765
# open http://localhost:8765/holes.html
```

| File | Role |
|------|------|
| [`holes.html`](holes.html) | Interactive board |
| [`holes-graph.json`](holes-graph.json) | Node/edge data (regenerated) |
| [`HOLES.md`](HOLES.md) | Markdown inventory |
