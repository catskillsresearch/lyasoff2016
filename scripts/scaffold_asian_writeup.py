#!/usr/bin/env python3
# Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
"""Scaffold Asian/ leaf subsections: one .md peer per .lean, with sidecars.

Every ``Lyasoff2016/*.lean`` module gets a leaf.  Modules that are not yet linked
from a section barrel are placed by ``MODULE_SECTION`` (the script fails loudly
for an unplaced module).

For each `@import` in Asian/Section{N}.md (legacy flat form) or the section's
lean list, writes:

  Asian/Section{N}/Name.md
  Asian/Section{N}/Name_aisummary.txt (AI module summary, from
                                       Asian/module_summaries.json)
  Asian/Section{N}/Name_math.txt   (verbatim paper quotes, one green box per
                                    `Paper:` ascription; see scripts/paper_quotes.py)
  Asian/Section{N}/Name_ailean.txt (English recap of decls, from docstrings)
  Lyasoff2016/Name.gist              (paper ascription source of truth)

Rewrites Asian/Section{N}.md as a barrel linking to those leaves.
Also builds Asian/Section{N}.svg (subsection import graph).

``Asian/module_summaries.json`` stores each AI-written summary together with the
SHA-256 of the Lean file it was written from; a mismatch is reported as STALE
(``--check`` exits non-zero) so the summary gets rewritten when the code changes.

Usage (repo root)::

    python3 scripts/scaffold_asian_writeup.py [--check]
    python3 scripts/scaffold_asian_writeup.py --restamp STEM ...  # after rewriting
                                                                 # STEM's summary
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ASIAN = ROOT / "Asian"
LEAN_DIR = ROOT / "Lyasoff2016"
SUMMARIES = ASIAN / "module_summaries.json"
UNRESOLVED_REPORT = ASIAN / "paper_quotes_unresolved.txt"

sys.path.insert(0, str(Path(__file__).resolve().parent))
import paper_quotes  # noqa: E402

# Section for modules not yet linked from a barrel (inserted before the first
# barrel entry that imports them, else appended).
MODULE_SECTION: dict[str, int] = {
    "CondDensityYor": 4,
    "StrikingMass": 4,
    "ContourBend": 6,
    "ContourBendFfun": 6,
    # Helpers placed with their importers so Figure 1 has no §2↔§5 / §5↔§6
    # two-way arrows (Lars, 2026-11-18). Only the writeup grouping moves.
    "CharA": 2,
    "PsiBranch": 2,
    "SmoothBump": 2,
    "UpperGamma": 5,
}

# Extra prose under a section barrel's blurb.
SECTION_NOTES: dict[int, str] = {
    4: (
        "The Comparator theorems `theorem_4_1_pde`, `theorem_4_1_striking`,\n"
        "`formula_4_6`, `prop_4_4` and `theorem_4_5` prove the displayed identities\n"
        "from the paper's analytic inputs (`SatisfiesTheorem41PDE`,\n"
        "`SatisfiesStrikingIdentity`, `SatisfiesFoliationODE`,\n"
        "`TransformedMassIdentity` / `HasLaplaceReduction`). The theorems\n"
        "`cond_density_satisfies_*` discharge those inputs for a genuine conditional\n"
        "density (Brownian-scaled Yor, `CondDensityYor`), so the identities hold for\n"
        "the conditional density itself."
    ),
}

MD_IMPORT_RE = re.compile(r'@import\s+"\.\./Lyasoff2016/([^"]+\.lean)"')
MD_LEAF_LINK_RE = re.compile(r"\]\((Section\d+/[^)]+\.md)\)")
LEAN_IMPORT_RE = re.compile(
    r"^\s*(?:public\s+)?import\s+Lyasoff2016\.([A-Za-z0-9_']+)",
    re.MULTILINE,
)
# Paper comment blocks (Lean /- ... -/)
PAPER_BLOCK_RE = re.compile(
    r"/-[\s\S]*?Paper:\s*([^-]*?)(?:\n\s*Plain recap:\s*([^-]*?))?\s*-/",
    re.MULTILINE,
)
PAPER_LINE_RE = re.compile(
    r"Paper:\s*(.+?)(?:\n\s*Plain recap:\s*(.+?))?(?=\n\s*(?:Paper:|-/)|$)",
    re.DOTALL,
)
DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected|nonrec)\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|axiom|class|inductive|instance)\s+"
    r"(?P<name>[A-Za-z0-9_'.«»₀-₉]+)",
    re.MULTILINE,
)
_COMMENT_RE = re.compile(r"/-[\s\S]*?-/")


def _comment_spans(lean_text: str) -> list[tuple[int, int]]:
    return [(m.start(), m.end()) for m in _COMMENT_RE.finditer(lean_text)]


def _in_spans(pos: int, spans: list[tuple[int, int]]) -> bool:
    return any(a <= pos < b for a, b in spans)
HEADER_TITLE_RE = re.compile(r"^#\s+(.+)$", re.MULTILINE)

SECTION_TITLES = {
    1: "§1 Setting and time reversal",
    2: "§2 Auxiliary results",
    3: "§3 Fokker–Planck and Dufresne",
    4: "§4 Foliation of the joint law",
    5: "§5 Contour equations and integral representations",
    6: "§6 Asian options",
}

SECTION_BLURBS = {
    1: "Paper: Lyasoff pp. 1061–1063 (setting) and time-reversibility (1.3).",
    2: "Paper: Lyasoff pp. 1064–1066 (Lemma 2.1, Prop. 2.2, scaling, Girsanov).",
    3: "Paper: Lyasoff pp. 1067–1071 (infinite-horizon flux, joint Fokker–Planck).",
    4: "Paper: Lyasoff pp. 1071–1079 (Thm 4.1, (4.4), Prop. 4.4, Thm 4.5).",
    5: "Paper: Lyasoff pp. 1079–1088 ($g$ contour equation, $\\pi$ / $\\pi/2$ formulae, Rem 5.1).",
    6: "Paper: Lyasoff pp. 1088–1095 (pricing identity (6.1), delta, Tables 1–4).",
}


def strip_indent(s: str) -> str:
    return re.sub(r"[ \t]+\n", "\n", s).strip()


def lean_stems_from_section_md(path: Path) -> list[str]:
    """Ordered unique stems from flat @imports or leaf links."""
    text = path.read_text(encoding="utf-8")
    stems: list[str] = []
    seen: set[str] = set()
    for m in MD_IMPORT_RE.findall(text):
        stem = Path(m).stem
        if stem not in seen:
            seen.add(stem)
            stems.append(stem)
    if stems:
        return stems
    # Already barrel: links like Section1/Setting.md
    for rel in MD_LEAF_LINK_RE.findall(text):
        stem = Path(rel).stem
        if stem not in seen:
            seen.add(stem)
            stems.append(stem)
    # Or directory listing order if md files exist
    sec_dir = path.with_suffix("")
    if not stems and sec_dir.is_dir():
        for md in sorted(sec_dir.glob("*.md")):
            stem = md.stem
            if stem not in seen and (LEAN_DIR / f"{stem}.lean").exists():
                seen.add(stem)
                stems.append(stem)
    return stems


def extract_paper_blocks(lean_text: str) -> list[tuple[str, str]]:
    """Return list of (ascription, body) from Paper: / Plain recap: comments."""
    blocks: list[tuple[str, str]] = []
    for m in re.finditer(r"/-([\s\S]*?)-/", lean_text):
        body = m.group(1)
        if "Paper:" not in body:
            continue
        for pm in re.finditer(
            r"Paper:\s*(.*?)(?:\n\s*Plain recap:\s*(.*?))?(?=\n\s*Paper:|\Z)",
            body,
            re.DOTALL,
        ):
            ascription = strip_indent(pm.group(1))
            recap = strip_indent(pm.group(2) or "")
            if not ascription or ascription.startswith("Copyright"):
                continue
            ascription = re.sub(r"\s+", " ", ascription).strip().rstrip(".")
            blocks.append((ascription, recap))
    return blocks


def extract_header_blurb(lean_text: str) -> str:
    m = HEADER_TITLE_RE.search(lean_text)
    if m:
        return m.group(1).strip()
    # first non-copyright line of opening comment
    if lean_text.startswith("/-"):
        end = lean_text.find("-/")
        if end > 0:
            lines = [
                ln.strip()
                for ln in lean_text[2:end].splitlines()
                if ln.strip()
                and not ln.strip().startswith("Copyright")
                and not ln.strip().startswith("Released")
            ]
            if lines:
                return lines[0].lstrip("# ").strip()
    return "Lyasoff 2016 formalization module."


# Manual overrides when the Lean header is a section banner or a CamelCase stem.
TITLE_OVERRIDES: dict[str, str] = {
    "Setting": "Brownian setting and standing notation",
    "Auxiliary": "Lemma 2.1, Prop. 2.2, scaling, and Girsanov",
    "FokkerPlanck": "Fokker–Planck characterization of the joint law",
    "Foliation": "Foliation of the joint law",
    "IntegralReps": "Integral representations via contour formulae",
    "Asian": "Asian call price and strike delta",
    "AsianDensity": "Density ingredients for the Asian pricing identity",
    "TableParams": "Numerical table parameter regimes",
    "TableClassical": "Reported digit strings for Tables 1–4",
    "TableClaim": "Reported rows for Tables 1–4",
    "IntegralMoments": "Moments of the exponential integral",
    "PiFormulaScale": "Compatibility shim for π-formula scaling",
    "Prop22Classical": "Prop. 2.2 as a classical citation point",
    "YorClassical": "Yor’s joint density as a classical citation point",
}


def camel_to_spaced(stem: str) -> str:
    s = re.sub(r"(?<=[a-z0-9])(?=[A-Z])", " ", stem)
    s = re.sub(r"(?<=[A-Z])(?=[A-Z][a-z])", " ", s)
    return s.replace("_", " ").strip()


def english_title(stem: str, lean_text: str) -> str:
    """Human label for a subsection: mathematical intent, not the Lean token."""
    if stem in TITLE_OVERRIDES:
        return TITLE_OVERRIDES[stem]
    blurb = extract_header_blurb(lean_text)
    # Drop journal / page / paper parentheticals (balanced-ish).
    title = re.sub(
        r"\s*\((?:[^()]|\([^()]*\))*(?:Lyasoff|Finance Stoch|pp?\.\s*\d|paper\s*\()(?:[^()]|\([^()]*\))*\)",
        "",
        blurb,
        flags=re.IGNORECASE,
    )
    # Also drop simpler trailing `(p. NNN…)` / `(paper (3.2))` fragments.
    title = re.sub(r"\s*\((?:p+\.\s*\d|paper)[^)]*$", "", title, flags=re.IGNORECASE)
    title = re.sub(r"\s*\((?:p+\.\s*\d|paper)[^)]*\)", "", title, flags=re.IGNORECASE)
    title = re.sub(r"\s*[—–]\s*$", "", title).strip()
    title = re.sub(r"^§\d+\s+", "", title).strip()
    # First sentence / clause only (avoid truncated multi-line headers).
    title = re.split(r"[.]\s+|,\s*$", title, maxsplit=1)[0].strip()
    title = title.rstrip(".,;:").rstrip()
    # Remove a dangling unmatched closing paren left by a bad strip.
    if title.count("(") < title.count(")"):
        title = title.rstrip(")").rstrip()
    compact = re.sub(r"[\s_\-`]", "", title)
    if compact.lower() == stem.lower() or not title:
        title = camel_to_spaced(stem)
    if len(title) > 88:
        # Break at a word boundary when possible.
        cut = title[:88]
        if " " in cut:
            cut = cut.rsplit(" ", 1)[0]
        title = cut.rstrip(".,;:") + "…"
    # Capitalize first letter unless it starts with math/Greek/backtick.
    if title and title[0].islower() and title[0] not in "`$\\π":
        title = title[0].upper() + title[1:]
    return title


def extract_decls_with_recaps(lean_text: str) -> list[dict]:
    """Associate nearest preceding Plain recap / Paper with each decl."""
    # Build map of position -> last paper recap
    events: list[tuple[int, str, object]] = []
    for m in re.finditer(r"/-([\s\S]*?)-/", lean_text):
        body = m.group(1)
        if "Paper:" in body or "Plain recap:" in body:
            paper = ""
            recap = ""
            pm = re.search(
                r"Paper:\s*(.*?)(?:\n\s*Plain recap:\s*(.*?))?\s*\Z",
                body.strip(),
                re.DOTALL,
            )
            if pm:
                paper = re.sub(r"\s+", " ", strip_indent(pm.group(1))).strip()
                recap = strip_indent(pm.group(2) or "")
            events.append((m.end(), "paper", (paper, recap)))
    spans = _comment_spans(lean_text)
    for m in DECL_RE.finditer(lean_text):
        if _in_spans(m.start(), spans):
            continue
        events.append((m.start(), "decl", m))
    events.sort(key=lambda x: x[0])

    last_paper = ("", "")
    decls: list[dict] = []
    for _, kind, payload in events:
        if kind == "paper":
            last_paper = payload  # type: ignore[assignment]
        else:
            m = payload  # type: ignore[assignment]
            before = lean_text[: m.start()].rstrip()
            doc = ""
            if before.endswith("-/"):
                k = before.rfind("/--")
                if k >= 0 and "-/" not in before[k:-2]:
                    doc = re.sub(r"\s+", " ", before[k + 3 : -2]).strip()
            decls.append(
                {
                    "kind": m.group("kind"),
                    "name": m.group("name"),
                    "paper": last_paper[0],
                    "recap": last_paper[1],
                    "doc": doc,
                }
            )
            # don't reuse the same recap for every following decl forever—
            # clear after one use unless next decl is very close without new paper
            last_paper = (last_paper[0], "")
    return decls


def format_math_txt(blocks: list[tuple[str, str]]) -> str:
    if not blocks:
        return ""
    parts: list[str] = []
    for ascription, recap in blocks:
        # Normalize ascription header for TeX sourcequote splitter
        header = ascription
        if not header.lower().startswith("lyasoff"):
            header = f"Lyasoff (2016), {header}"
        parts.append(f"**{header}**\n")
        if recap:
            parts.append(recap + "\n")
        parts.append("")
    return "\n".join(parts).rstrip() + "\n"


def format_gist(blocks: list[tuple[str, str]]) -> str:
    return format_math_txt(blocks)


def _lean_sha256(stem: str) -> str:
    return hashlib.sha256((LEAN_DIR / f"{stem}.lean").read_bytes()).hexdigest()


def load_summaries() -> dict[str, dict[str, str]]:
    if SUMMARIES.is_file():
        return json.loads(SUMMARIES.read_text(encoding="utf-8"))
    return {}


STALE: list[str] = []
MISSING_SUMMARY: list[str] = []


def format_aisummary(stem: str, blurb: str, summaries: dict[str, dict[str, str]]) -> str:
    """AI-written module summary; falls back to the Lean header (flagged)."""
    entry = summaries.get(stem)
    if not entry:
        MISSING_SUMMARY.append(stem)
        return blurb.rstrip(".") + ".\n"
    if entry.get("lean_sha256") != _lean_sha256(stem):
        STALE.append(stem)
    return entry["summary"].strip() + "\n"


_KIND_LABEL = {
    "def": "Definition",
    "abbrev": "Abbreviation",
    "structure": "Structure",
    "theorem": "Theorem",
    "lemma": "Lemma",
    "instance": "Instance",
    "class": "Class",
    "inductive": "Inductive type",
    "axiom": "Axiom",
}


def format_ailean(stem: str, decls: list[dict]) -> str:
    """Lean-to-English recap: each declaration's own docstring (or its paper recap)."""
    if not decls:
        return (
            f"Module `{stem}.lean` contains no declarations of its own "
            f"(see the Lean source).\n"
        )
    parts: list[str] = [
        f"Mathematical English for `{stem}.lean` (Lean names in typewriter).\n"
    ]
    undocumented: list[str] = []
    for d in decls:
        text = d.get("doc") or d["recap"]
        if not text:
            undocumented.append(d["name"])
            continue
        text = re.sub(r"\s+", " ", text).strip()
        kind = _KIND_LABEL.get(d["kind"], d["kind"].capitalize())
        parts.append(f"**{kind}** (`{d['name']}`). {text}\n")
    if undocumented:
        names = ", ".join(f"`{n}`" for n in undocumented)
        parts.append(f"Supporting declarations without a docstring: {names}.\n")
    return "\n".join(parts).rstrip() + "\n"


# A `Paper:` block counts as a location label only if it names a page, an
# equation tag, a section, a footnote or a numbered result.
LOCATION_RE = re.compile(
    r"\bpp?\.\s*\d|§\s*\d|\(\d\.\d+[ab]?\)|\bfootnote\b|"
    r"\b(?:Theorem|Thm|Lemma|Proposition|Prop|Remark|Corollary|Table|Tables|Section)\.?\s*\d",
    re.I,
)


def location_blocks(lean_text: str) -> list[tuple[str, str]]:
    return [b for b in extract_paper_blocks(lean_text) if LOCATION_RE.search(b[0])]


def paper_ascriptions(stem: str, lean_text: str) -> list[str]:
    blocks = location_blocks(lean_text)
    if blocks:
        return [a for a, _ in blocks]
    gist = LEAN_DIR / f"{stem}.gist"
    if gist.is_file():
        heads = re.findall(r"^\*\*(.+?)\*\*\s*$", gist.read_text(encoding="utf-8"), re.M)
        return [re.sub(r"^Lyasoff \(2016\),\s*", "", h) for h in heads]
    return []


UNRESOLVED: list[str] = []


def write_leaf(sec: int, stem: str, title: str) -> None:
    lean_path = LEAN_DIR / f"{stem}.lean"
    if not lean_path.exists():
        print(f"  skip missing {lean_path}", file=sys.stderr)
        return
    lean_text = lean_path.read_text(encoding="utf-8")
    blocks = location_blocks(lean_text)
    decls = extract_decls_with_recaps(lean_text)
    blurb = extract_header_blurb(lean_text)

    out_dir = ASIAN / f"Section{sec}"
    out_dir.mkdir(parents=True, exist_ok=True)

    gist_path = LEAN_DIR / f"{stem}.gist"
    if blocks:
        gist_path.write_text(format_gist(blocks), encoding="utf-8")

    quotes = []
    for asc in paper_ascriptions(stem, lean_text):
        q, _how = paper_quotes.resolve(stem, asc)
        if q is None:
            UNRESOLVED.append(f"{stem}: {asc}")
        else:
            quotes.append(q)
    math_path = out_dir / f"{stem}_math.txt"
    if quotes:
        math_path.write_text(paper_quotes.format_quotes(quotes), encoding="utf-8")
    elif math_path.exists():
        math_path.unlink()

    (out_dir / f"{stem}_aisummary.txt").write_text(
        format_aisummary(stem, blurb, SUMMARY_DB), encoding="utf-8"
    )
    (out_dir / f"{stem}_ailean.txt").write_text(
        format_ailean(stem, decls), encoding="utf-8"
    )

    # Leaf markdown — heading is mathematical English; file name stays the Lean stem.
    # Paper quotations (green boxes) open the subsection.
    lines = [f"# {title}", ""]
    if math_path.exists():
        lines += [
            f'@import "{stem}_math.txt" {{code_block=false}}',
            "",
        ]
    lines += [
        f'@import "{stem}_aisummary.txt" {{code_block=false}}',
        "",
        f'@import "{stem}_ailean.txt" {{code_block=false}}',
        "",
        f"**[Lyasoff2016/{stem}.lean](../../Lyasoff2016/{stem}.lean)**",
        "",
        f'@import "../../Lyasoff2016/{stem}.lean"',
        "",
    ]
    (out_dir / f"{stem}.md").write_text("\n".join(lines), encoding="utf-8")


def write_section_barrel(sec: int, stems: list[str], titles: dict[str, str]) -> None:
    title = SECTION_TITLES[sec]
    blurb = SECTION_BLURBS[sec]
    svg_name = f"Section{sec}.svg"
    lines = [
        f"# {title}",
        "",
        blurb,
        "",
    ]
    if sec in SECTION_NOTES:
        lines += [SECTION_NOTES[sec], ""]
    lines += [
        f'@import "{svg_name}" {{code_block=false, caption="Subsection dependencies within {title.split()[0]}"}}',
        "",
        "Subsections follow Lean import order; labels are mathematical English.",
        "",
    ]
    for stem in stems:
        lines.append(f"- [{titles[stem]}](Section{sec}/{stem}.md)")
    lines.append("")
    (ASIAN / f"Section{sec}.md").write_text("\n".join(lines), encoding="utf-8")


def _dot_escape(label: str) -> str:
    return label.replace("\\", "\\\\").replace('"', '\\"')


def build_section_svg(
    sec: int, stems: list[str], titles: dict[str, str]
) -> None:
    stem_set = set(stems)
    edges: set[tuple[str, str]] = set()
    for stem in stems:
        text = (LEAN_DIR / f"{stem}.lean").read_text(encoding="utf-8")
        for dep in LEAN_IMPORT_RE.findall(text):
            if dep in stem_set and dep != stem:
                edges.add((stem, dep))

    lines = [
        f"digraph Section{sec} {{",
        '  graph [rankdir=TD, bgcolor="white", pad="0.2", nodesep="0.35", ranksep="0.55"];',
        '  node [shape=box, style="rounded,filled", fillcolor="#ecfdf5",',
        '        color="#047857", fontname="Helvetica", fontsize=10,',
        '        fontcolor="#064e3b", margin="0.12,0.08"];',
        '  edge [color="#64748b", arrowsize=0.6];',
        "",
    ]
    for stem in stems:
        label = _dot_escape(titles[stem])
        lines.append(
            f'  "{stem}" [label="{label}", URL="Section{sec}/{stem}.md", '
            f'tooltip="{stem}.lean"];'
        )
    lines.append("")
    for a, b in sorted(edges):
        lines.append(f'  "{a}" -> "{b}";')
    lines.append("}")
    dot_path = ASIAN / f"Section{sec}.dot"
    svg_path = ASIAN / f"Section{sec}.svg"
    dot_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    try:
        subprocess.run(
            ["dot", "-Tsvg", "-o", str(svg_path), str(dot_path)],
            check=True,
        )
    except (FileNotFoundError, subprocess.CalledProcessError) as e:
        print(f"  warn: could not build {svg_path.name}: {e}", file=sys.stderr)


def verify_unique_imports() -> None:
    imports: list[str] = []
    for md in ASIAN.rglob("*.md"):
        text = md.read_text(encoding="utf-8")
        imports += re.findall(
            r'@import\s+"(\.\./\.\./Lyasoff2016/[^"]+\.lean)"', text
        )
        imports += re.findall(
            r'@import\s+"(\.\./Lyasoff2016/[^"]+\.lean)"', text
        )
    stems = [Path(p).stem for p in imports]
    from collections import Counter

    c = Counter(stems)
    dupes = [k for k, v in c.items() if v > 1]
    leans = {p.stem for p in LEAN_DIR.glob("*.lean")}
    missing = sorted(leans - set(stems))
    print(f"leaf lean imports: {len(stems)} unique={len(c)}")
    if dupes:
        print("DUPLICATES:", dupes)
    if missing:
        print("MISSING FROM WRITEUP:", missing)


SUMMARY_DB: dict[str, dict[str, str]] = {}


def place_unlinked(sections: dict[int, list[str]]) -> None:
    linked = {st for stems in sections.values() for st in stems}
    for lean in sorted(LEAN_DIR.glob("*.lean")):
        stem = lean.stem
        if stem in linked:
            continue
        sec = MODULE_SECTION.get(stem)
        if sec is None:
            raise SystemExit(
                f"{stem}.lean has no writeup section: add it to MODULE_SECTION"
            )
        stems = sections[sec]
        idx = len(stems)
        for i, other in enumerate(stems):
            text = (LEAN_DIR / f"{other}.lean").read_text(encoding="utf-8")
            if stem in LEAN_IMPORT_RE.findall(text):
                idx = i
                break
        stems.insert(idx, stem)
        linked.add(stem)


def main() -> int:
    global SUMMARY_DB
    check = "--check" in sys.argv[1:]
    SUMMARY_DB = load_summaries()
    if sys.argv[1:2] == ["--restamp"]:
        for stem in sys.argv[2:]:
            SUMMARY_DB[stem]["lean_sha256"] = _lean_sha256(stem)
        SUMMARIES.write_text(
            json.dumps(SUMMARY_DB, ensure_ascii=False, indent=1) + "\n", encoding="utf-8"
        )
        print("restamped", ", ".join(sys.argv[2:]))
        return 0
    sections: dict[int, list[str]] = {}
    for sec in range(1, 7):
        barrel = ASIAN / f"Section{sec}.md"
        sections[sec] = lean_stems_from_section_md(barrel) if barrel.exists() else []
    place_unlinked(sections)
    total = 0
    for sec in range(1, 7):
        stems = sections[sec]
        print(f"Section{sec}: {len(stems)} modules")
        titles: dict[str, str] = {}
        for stem in stems:
            lean_text = (LEAN_DIR / f"{stem}.lean").read_text(encoding="utf-8")
            titles[stem] = english_title(stem, lean_text)
            write_leaf(sec, stem, titles[stem])
            total += 1
            print(f"  {stem} → {titles[stem]}")
        write_section_barrel(sec, stems, titles)
        build_section_svg(sec, stems, titles)
    verify_unique_imports()
    UNRESOLVED_REPORT.write_text(
        "Paper ascriptions in Lyasoff2016/*.lean with no verbatim quote located in\n"
        "sources/lyasoff2016_vision.md (no green box is emitted for these):\n\n"
        + "".join(f"- {u}\n" for u in UNRESOLVED),
        encoding="utf-8",
    )
    print(f"scaffolded {total} leaves")
    print(f"paper quotes unresolved: {len(UNRESOLVED)} (see {UNRESOLVED_REPORT.name})")
    if MISSING_SUMMARY:
        print("MISSING AI SUMMARY:", ", ".join(MISSING_SUMMARY))
    if STALE:
        print("STALE AI SUMMARY (Lean changed since written):", ", ".join(STALE))
    if check and (MISSING_SUMMARY or STALE):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
