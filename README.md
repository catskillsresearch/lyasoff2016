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
| [`Actions.md`](Actions.md) | Paper-facing TOC |
| [`Actions/SectionN.md`](Actions/) | Section barrels + subsection dependency SVGs |
| [`Actions/SectionN/Name.md`](Actions/) | One leaf per `.lean` (`*_aisummary.txt`, `*_math.txt` green ascriptions, `*_ailean.txt`, Lean `@import`) |
| [`Lyasoff2016/*.gist`](Lyasoff2016/) | Paper-quote source synced into `*_math.txt` |

```bash
python3 scripts/scaffold_actions_writeup.py   # refresh leaves / gists / section SVGs
python3 scripts/compile_md_tree.py --tex-only # → arxiv.md + arxiv.tex (green sourcequote boxes)
bash scripts/build_arxiv_pdf.sh               # → Actions.pdf (needs latexmk)
```


## Palomar packaging

Challenge / Solution / Comparator / metadata (scott_models / nowakowska1982 pattern):

| File | Role |
|------|------|
| [`Challenge.lean`](Challenge.lean) | Mathlib-only statement of record (`sorry` holes) |
| [`Solution.lean`](Solution.lean) | Imports `Lyasoff2016/` |
| [`comparator.json`](comparator.json) | 33 proof-chart theorems + 7 formula defs |
| [`formalization.yaml`](formalization.yaml) | v0.4 self-report; `project.description` is the abstract |
| [`PROVENANCE.md`](PROVENANCE.md) | Authorship, Lyasoff non-involvement, reported numerical data |
| [`LICENSE`](LICENSE) / [`NOTICE`](NOTICE) | Apache-2.0 + third-party source notice |

```bash
python3 scripts/regen_challenge.py          # refresh Challenge + comparator from holes-graph
bash scripts/validate_chart_axioms.sh       # all chart theorems: Palomar-clean
bash scripts/palomar_preflight.sh           # comparator + chart audit + lake build
lake build Challenge Solution
```

Andrew Lyasoff did not participate in or endorse this formalization. Author:
Lars Warren Ericson (no other collaborators).

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
