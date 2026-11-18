# Formalization of Lyasoff's Asian Option Model

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
| `vendor/` | `brownian-motion/`: path copy of RemyDegenne/brownian-motion at the pinned commit, with a few unfinished upstream declarations removed (listed in `vendor/SOURCES`). formal-mathfin, kolmogorov_extension4 (transitive) and Mathlib are Lake Git pins, not vendored; revisions in `vendor/SOURCES` and `lake-manifest.json`. `palomar-policy/`: pinned Palomar policy. |

## Status

All paper-facing holes are discharged (`sorryCount = 0`). Browse the completed formalization
in paper order via [`Asian.md`](Asian.md).

## Completed proof (paper writeup)

| File | Role |
|------|------|
| [`Asian.md`](Asian.md) | Paper-facing TOC |
| [`Asian/SectionN.md`](Asian/) | Section barrels + subsection dependency SVGs |
| [`Asian/SectionN/Name.md`](Asian/) | One leaf per `.lean` (`*_aisummary.txt`, `*_math.txt` green ascriptions, `*_ailean.txt`, Lean `@import`) |
| [`Lyasoff2016/*.gist`](Lyasoff2016/) | Paper-ascription / recap metadata synced from the Lean `Paper:` blocks | 
| [`Asian/module_summaries.json`](Asian/module_summaries.json) | AI-written English summaries keyed by module, with Lean source SHA-256 | 
| [`scripts/paper_quotes.py`](scripts/paper_quotes.py) | Resolves verbatim quotes from `sources/lyasoff2016_vision.md`; explicit anchors in `paper_quote_anchors.json` |

`Asian.md` is the root of the writeup and holds only the title and chapter list, so nothing repository-specific reaches the PDF. The tree follows the paper in order: each `.lean` module has its own subsection with paper quotes in green boxes, an AI-written English summary and the Lean source. Every paper-facing hole on the [dependency board](holes.html) is done (`sorryCount = 0`).

```bash
python3 scripts/scaffold_asian_writeup.py --check # refresh 95 leaves / gists / section SVGs; fail on stale AI summary
python3 scripts/compile_md_tree.py --tex-only # → arxiv.md + arxiv.tex (green sourcequote boxes)
bash scripts/build_arxiv_pdf.sh               # → Asian.pdf (needs latexmk)
```

Regeneration needs Python 3 and Graphviz (`dot`) for the dependency SVGs; the TeX
build needs pandoc, latexmk and the preamble's LaTeX packages. No LLM API key is
needed by the writeup generator. `*_aisummary.txt` is rendered from the
AI-written summary database, not invented by a template; after changing a Lean
module, have an AI agent reread it and update its summary, then run
`python3 scripts/scaffold_asian_writeup.py --restamp MODULE` before `--check`.
`*_ailean.txt` is generated from declaration docstrings / recaps. Every module
under `Lyasoff2016/` must be placed in a section; generation fails otherwise.

Paper quotes precede the AI prose in each leaf. They appear as green HTML boxes
in Markdown and green `sourcequote` tcolorboxes in the PDF. Resolution uses Lean
`Paper:` blocks (or gist headers), equation / named-result matches and explicit
verbatim source anchors; no quote wording is synthesized. Missing sources are
listed in [`Asian/paper_quotes_unresolved.txt`](Asian/paper_quotes_unresolved.txt).


## Palomar packaging

Challenge / Solution / Comparator / metadata (scott_models / nowakowska1982 pattern):

| File | Role |
|------|------|
| [`Challenge.lean`](Challenge.lean) | Mathlib-only statement of record (`sorry` holes) |
| [`Solution.lean`](Solution.lean) | Imports `Lyasoff2016/` |
| [`comparator.json`](comparator.json) | 40 proof-chart theorems + 13 definitions |
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

### PDF bibliography and layout

Run `bash scripts/build_arxiv_pdf.sh` from the repository root to rebuild
`Asian.pdf` (and `view.pdf`). Requires Python 3, pandoc, Graphviz, latexmk,
PDFLaTeX and **BibTeX**, plus the packages in `scripts/tex_preamble_arxiv.tex`.
The build runs BibTeX on `references.bib`, checks for unresolved citations,
and includes every entry (`\nocite{*}`), including all pinned Lake repositories.
The title page is followed by a dedicated multi-page table of contents; every
top-level section, including References, starts on a fresh page.
