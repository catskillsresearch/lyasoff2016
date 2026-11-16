# Vendored Lean libraries (Palomar)

These directories are **full verbatim copies** of external repositories (not git
submodules or soft links), as required for Palomar reproducibility.

| Directory | Upstream | Role |
|-----------|----------|------|
| `brownian-motion/` | RemyDegenne/brownian-motion | Brownian motion, Kolmogorov–Chentsov, Gaussian processes |
| `kolmogorov_extension4/` | RemyDegenne/kolmogorov_extension4 | Kolmogorov extension (BM dependency) |
| `formal-mathfin/` | formal-applied-math/formal-mathfin | Itô integral/formula, Girsanov, SDEs, math finance |

Exact commits are recorded in [`SOURCES`](SOURCES).

Lake path dependencies in the repo-root `lakefile.toml` and in the patched
vendor lakefiles point at these trees. Mathlib itself is a normal Lake `git`
require (pinned in `SOURCES`), not vendored.
