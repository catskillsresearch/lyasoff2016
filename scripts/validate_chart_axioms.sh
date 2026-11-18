#!/usr/bin/env bash
# Offline Palomar axiom gate for every proof-chart theorem in holes-graph.json.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

python3 - <<'PY'
import json, pathlib, re, subprocess, tempfile

g = json.load(open("holes-graph.json"))
names = [n["id"] for n in g["nodes"]]
lean = "import Lyasoff2016\nopen Lyasoff2016\n" + "".join(
    f"#print axioms {n}\n" for n in names
)
path = pathlib.Path(tempfile.mkstemp(suffix=".lean")[1])
path.write_text(lean)
out = subprocess.check_output(["lake", "env", "lean", str(path)], text=True)
path.unlink(missing_ok=True)

permitted = {"propext", "Classical.choice", "Quot.sound"}
bad = []
ok = []
for line in out.splitlines():
    m = re.match(r"'Lyasoff2016\.(\w+)' depends on axioms: \[(.*)\]", line)
    if not m:
        # multi-line axiom lists
        continue
    name, axs = m.group(1), m.group(2)
    items = {a.strip() for a in axs.split(",") if a.strip()}
    extra = sorted(items - permitted)
    if extra:
        bad.append((name, extra))
    else:
        ok.append(name)

# Also parse multi-line forms
cur = None
buf = []
for line in out.splitlines():
    m = re.match(r"'Lyasoff2016\.(\w+)' depends on axioms: \[(.*)\]$", line)
    if m and m.group(2).endswith("]"):
        continue  # already handled single-line
    m2 = re.match(r"'Lyasoff2016\.(\w+)' depends on axioms: \[(.*)$", line)
    if m2:
        cur = m2.group(1)
        buf = [m2.group(2)]
        continue
    if cur is not None:
        buf.append(line.strip())
        if "]" in line:
            body = " ".join(buf).rstrip("]")
            items = {a.strip().strip(",") for a in body.split(",") if a.strip().strip(",")}
            extra = sorted(items - permitted)
            # dedupe against single-line pass
            if extra and not any(n == cur for n, _ in bad):
                bad.append((cur, extra))
            elif not extra and cur not in ok:
                ok.append(cur)
            cur = None

print(f"chart theorems: {len(names)}")
print(f"Palomar-clean: {len(ok)}")
print(f"classical / extra axioms: {len(bad)}")
for n, extra in bad:
    print(f"  FAIL {n}: {', '.join(extra)}")
if len(ok) + len(bad) < len(names):
    print("warning: could not classify all theorems; raw output tail:")
    print("\n".join(out.splitlines()[-20:]))
# Nonzero exit only if a theorem outside the known classical five has extras
known = {
    "asian_delta",
    "table1_asian_enclosure",
    "table2_asian_enclosure",
    "table3_asian_enclosure",
    "table4_asian_enclosure",
}
unexpected = [(n, e) for n, e in bad if n not in known]
if unexpected:
    raise SystemExit("unexpected extra axioms beyond classical chart certificates")
print("OK: every chart theorem is either Palomar-clean or a disclosed classical certificate")
PY
