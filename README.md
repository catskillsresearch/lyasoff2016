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

All paper-facing holes are discharged (`sorryCount = 0`). Browse the completed formalization
in paper order via [`Actions.md`](Actions.md).

## Completed proof (paper writeup)

| File | Role |
|------|------|
| [`Actions.md`](Actions.md) | Paper-facing TOC and section barrels |
| [`Actions/`](Actions/) | §1–§6 pages with `@import` of each `.lean` once |

## Proof-hole board

Dependency graph of paper-facing theorems (all **done**). The graph JSON is **embedded** in
`holes.html`, so you can open that file directly (no local server).

```bash
python3 scripts/build_holes.py   # refreshes HOLES.md / holes-graph.json / embeds into holes.html
# then open holes.html in a browser
```

| File | Role |
|------|------|
| [`holes.html`](holes.html) | Interactive board (embedded graph) |
| [`holes-graph.json`](holes-graph.json) | Node/edge data (also embedded) |
| [`HOLES.md`](HOLES.md) | Markdown inventory |
