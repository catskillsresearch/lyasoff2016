#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 - <<'PY'
import json, pathlib, subprocess, tempfile, re
cfg = json.load(open("comparator.json"))
names = cfg["theorem_names"] + cfg.get("definition_names", [])

def run(mod):
    lines = [f"import {mod}", "set_option pp.all true", "set_option pp.explicit true"]
    lines += [f"#check @{n}" for n in names]
    p = pathlib.Path(tempfile.mkstemp(suffix=".lean")[1])
    p.write_text("\n".join(lines) + "\n")
    out = subprocess.run(["lake", "env", "lean", str(p)], capture_output=True, text=True)
    p.unlink(missing_ok=True)
    if out.returncode != 0:
        raise SystemExit(out.stderr or out.stdout)
    return out.stdout

def parse(out):
    blocks, cur, buf = {}, None, []
    pat = re.compile(r"^@?(Lyasoff2016\.\w+)(?:\.\{\w+\})?\s+:\s*(.*)$")
    for line in out.splitlines():
        m = pat.match(line)
        if m:
            if cur:
                blocks[cur] = "\n".join(buf).strip()
            cur, buf = m.group(1), [m.group(2)]
        elif cur is not None:
            buf.append(line)
    if cur:
        blocks[cur] = "\n".join(buf).strip()
    return blocks

cb, sb = parse(run("Challenge")), parse(run("Solution"))
missing = [n for n in names if n not in cb or n not in sb]
diffs = [n for n in names if n in cb and n in sb and cb[n] != sb[n]]
print(f"compared {len(names)}; missing {len(missing)}; diffs {len(diffs)}")
if missing or diffs:
    print("missing:", missing)
    print("diffs:", diffs)
    raise SystemExit(1)
print("OK: Challenge/Solution types match")
PY
