#!/usr/bin/env python3
# Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
"""Scaffold Actions/ leaf subsections: one .md peer per .lean, with sidecars.

For each `@import` in Actions/Section{N}.md (legacy flat form) or the section's
lean list, writes:

  Actions/Section{N}/Name.md
  Actions/Section{N}/Name_aisummary.txt
  Actions/Section{N}/Name_math.txt   (from Paper: comments / .gist)
  Actions/Section{N}/Name_ailean.txt (English recap of decls)
  Lyasoff2016/Name.gist              (paper ascription source of truth)

Rewrites Actions/Section{N}.md as a barrel linking to those leaves.
Also builds Actions/Section{N}.svg (subsection import graph).

Usage (repo root)::

    python3 scripts/scaffold_actions_writeup.py
"""

from __future__ import annotations

import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ACTIONS = ROOT / "Actions"
LEAN_DIR = ROOT / "Lyasoff2016"

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
    r"^(?P<kind>theorem|lemma|def|abbrev|structure|axiom|class|inductive|instance)\s+"
    r"(?P<name>[A-Za-z0-9_'.«»]+)",
    re.MULTILINE,
)
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
    "TableClassical": "Classical numerical certificates for Tables 1–4",
    "TableClaim": "Interval enclosure claims for Tables 1–4",
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
    for m in DECL_RE.finditer(lean_text):
        events.append((m.start(), "decl", m))
    events.sort(key=lambda x: x[0])

    last_paper = ("", "")
    decls: list[dict] = []
    for _, kind, payload in events:
        if kind == "paper":
            last_paper = payload  # type: ignore[assignment]
        else:
            m = payload  # type: ignore[assignment]
            decls.append(
                {
                    "kind": m.group("kind"),
                    "name": m.group("name"),
                    "paper": last_paper[0],
                    "recap": last_paper[1],
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


def format_aisummary(blurb: str, decls: list[dict]) -> str:
    n = len(decls)
    kinds = defaultdict(int)
    for d in decls:
        kinds[d["kind"]] += 1
    kind_bits = ", ".join(f"{v} {k}{'s' if v != 1 else ''}" for k, v in sorted(kinds.items()))
    extra = f" It declares {n} item{'s' if n != 1 else ''}" + (f" ({kind_bits})." if kind_bits else ".")
    text = blurb.rstrip(".") + "."
    if n:
        text = text + extra
    return text + "\n"


def format_ailean(stem: str, decls: list[dict]) -> str:
    if not decls:
        return (
            f"Module `{stem}` collects supporting definitions and lemmas for the "
            f"Lyasoff 2016 formalization; see the Lean source for details.\n"
        )
    parts: list[str] = [
        f"Mathematical English for `{stem}.lean` "
        f"(Lean names in typewriter).\n"
    ]
    for d in decls:
        kind = d["kind"].capitalize()
        if d["kind"] == "def":
            kind = "Definition"
        elif d["kind"] == "abbrev":
            kind = "Abbreviation"
        name = d["name"]
        recap = d["recap"] or d["paper"]
        if recap:
            # one paragraph
            recap = re.sub(r"\s+", " ", recap).strip()
            parts.append(f"**{kind}** (`{name}`). {recap}\n")
        else:
            parts.append(
                f"**{kind}** (`{name}`). Stated and proved in Lean; "
                f"see the source for the formal statement.\n"
            )
        if d["kind"] in {"theorem", "lemma"} and d["recap"]:
            parts.append(
                f"Proof idea: follow the paper argument encoded in the Lean proof of `{name}`.\n"
            )
    return "\n".join(parts).rstrip() + "\n"


def write_leaf(sec: int, stem: str, title: str) -> None:
    lean_path = LEAN_DIR / f"{stem}.lean"
    if not lean_path.exists():
        print(f"  skip missing {lean_path}", file=sys.stderr)
        return
    lean_text = lean_path.read_text(encoding="utf-8")
    blocks = extract_paper_blocks(lean_text)
    decls = extract_decls_with_recaps(lean_text)
    blurb = extract_header_blurb(lean_text)

    out_dir = ACTIONS / f"Section{sec}"
    out_dir.mkdir(parents=True, exist_ok=True)

    gist_path = LEAN_DIR / f"{stem}.gist"
    math_txt = format_math_txt(blocks)
    if math_txt:
        gist_path.write_text(format_gist(blocks), encoding="utf-8")
        (out_dir / f"{stem}_math.txt").write_text(math_txt, encoding="utf-8")
    elif gist_path.exists():
        # keep existing gist → math
        (out_dir / f"{stem}_math.txt").write_text(
            gist_path.read_text(encoding="utf-8"), encoding="utf-8"
        )

    (out_dir / f"{stem}_aisummary.txt").write_text(
        format_aisummary(blurb, decls), encoding="utf-8"
    )
    (out_dir / f"{stem}_ailean.txt").write_text(
        format_ailean(stem, decls), encoding="utf-8"
    )

    # Leaf markdown — heading is mathematical English; file name stays the Lean stem.
    lines = [
        f"# {title}",
        "",
        f'@import "{stem}_aisummary.txt" {{code_block=false}}',
        "",
    ]
    if (out_dir / f"{stem}_math.txt").exists():
        lines += [
            f'@import "{stem}_math.txt" {{code_block=false}}',
            "",
        ]
    lines += [
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
        f'@import "{svg_name}" {{code_block=false, caption="Subsection dependencies within {title.split()[0]}"}}',
        "",
        "Subsections follow Lean import order; labels are mathematical English.",
        "",
    ]
    for stem in stems:
        lines.append(f"- [{titles[stem]}](Section{sec}/{stem}.md)")
    lines.append("")
    (ACTIONS / f"Section{sec}.md").write_text("\n".join(lines), encoding="utf-8")


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
    dot_path = ACTIONS / f"Section{sec}.dot"
    svg_path = ACTIONS / f"Section{sec}.svg"
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
    for md in ACTIONS.rglob("*.md"):
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


def main() -> int:
    total = 0
    for sec in range(1, 7):
        barrel = ACTIONS / f"Section{sec}.md"
        if not barrel.exists():
            print(f"missing {barrel}", file=sys.stderr)
            continue
        stems = lean_stems_from_section_md(barrel)
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
    print(f"scaffolded {total} leaves")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
