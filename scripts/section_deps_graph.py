#!/usr/bin/env python3
# Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
"""Build Asian.svg: dependencies among Asian/Section{1..6}.md.

An edge §i → §j means some .lean listed in Section i imports a .lean listed in
Section j (i ≠ j). Nodes are the six numbered section markdown files.

Usage (from repo root):

    python3 scripts/section_deps_graph.py
"""

from __future__ import annotations

import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ASIAN = ROOT / "Asian"
LEAN_DIR = ROOT / "Lyasoff2016"
OUT_DOT = ROOT / "Asian.dot"
OUT_SVG = ROOT / "Asian.svg"

IMPORT_RE = re.compile(
    r"^\s*(?:public\s+)?import\s+Lyasoff2016\.([A-Za-z0-9_']+)",
    re.MULTILINE,
)
MD_IMPORT_RE = re.compile(r'@import\s+"\.\./Lyasoff2016/([^"]+\.lean)"')
MD_LEAF_LINK_RE = re.compile(r"\]\(Section\d+/([^)]+)\.md\)")

SECTION_FILES = [ASIAN / f"Section{i}.md" for i in range(1, 7)]

# Short labels for the six section nodes (match Asian.md TOC).
SECTION_LABELS = {
    1: "§1 Setting",
    2: "§2 Auxiliary",
    3: "§3 Fokker–Planck",
    4: "§4 Foliation",
    5: "§5 Contours / π",
    6: "§6 Asian",
}


def lean_stem(name: str) -> str:
    return Path(name).stem


def section_leans() -> dict[int, set[str]]:
    mapping: dict[int, set[str]] = {}
    for i, path in enumerate(SECTION_FILES, start=1):
        text = path.read_text(encoding="utf-8")
        stems = {lean_stem(m) for m in MD_IMPORT_RE.findall(text)}
        # Barrel form (scaffold_asian_writeup.py): links to SectionN/Stem.md leaves.
        stems |= {lean_stem(m) for m in MD_LEAF_LINK_RE.findall(text)}
        mapping[i] = stems
    return mapping


def lean_imports(stem: str) -> set[str]:
    path = LEAN_DIR / f"{stem}.lean"
    if not path.exists():
        return set()
    text = path.read_text(encoding="utf-8")
    return set(IMPORT_RE.findall(text))


def build_edges(sec_leans: dict[int, set[str]]) -> set[tuple[int, int]]:
    stem_to_sec: dict[str, int] = {}
    for sec, stems in sec_leans.items():
        for s in stems:
            if s in stem_to_sec and stem_to_sec[s] != sec:
                raise SystemExit(f"lean {s}.lean listed in §{stem_to_sec[s]} and §{sec}")
            stem_to_sec[s] = sec

    edges: set[tuple[int, int]] = set()
    for sec, stems in sec_leans.items():
        for stem in stems:
            for dep in lean_imports(stem):
                if dep not in stem_to_sec:
                    continue
                other = stem_to_sec[dep]
                if other != sec:
                    # importer section → imported section
                    edges.add((sec, other))
    return edges


def write_dot(edges: set[tuple[int, int]]) -> str:
    lines = [
        "digraph AsianSections {",
        "  graph [rankdir=LR, bgcolor=\"white\", pad=\"0.3\", nodesep=\"0.45\", ranksep=\"0.7\"];",
        "  node [shape=box, style=\"rounded,filled\", fillcolor=\"#dbeafe\",",
        "        color=\"#1e40af\", fontname=\"Helvetica\", fontsize=12,",
        "        fontcolor=\"#0f172a\", margin=\"0.18,0.12\"];",
        "  edge [color=\"#64748b\", arrowsize=0.7];",
        "",
    ]
    for i in range(1, 7):
        label = SECTION_LABELS[i]
        href = f"Asian/Section{i}.md"
        lines.append(
            f'  S{i} [label="{label}", URL="{href}", tooltip="Asian/Section{i}.md"];'
        )
    lines.append("")
    for a, b in sorted(edges):
        lines.append(f"  S{a} -> S{b};")
    lines.append("}")
    return "\n".join(lines) + "\n"


def main() -> int:
    sec_leans = section_leans()
    for i, stems in sec_leans.items():
        print(f"§{i}: {len(stems)} lean modules")
    edges = build_edges(sec_leans)
    print(f"cross-section import edges: {len(edges)}")
    for a, b in sorted(edges):
        print(f"  §{a} → §{b}")

    dot = write_dot(edges)
    OUT_DOT.write_text(dot, encoding="utf-8")
    try:
        subprocess.run(
            ["dot", "-Tsvg", "-o", str(OUT_SVG), str(OUT_DOT)],
            check=True,
        )
    except FileNotFoundError:
        print("graphviz `dot` not found; wrote", OUT_DOT, file=sys.stderr)
        return 1
    except subprocess.CalledProcessError as e:
        print("dot failed:", e, file=sys.stderr)
        return 1
    print("wrote", OUT_SVG.relative_to(ROOT))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
