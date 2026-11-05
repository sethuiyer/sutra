#!/usr/bin/env python3
"""Generate a CNF/CNFgen corpus for the certified SUTRA-V3 benchmark.

Writes bench/cnf/*.cnf plus bench/manifest.json.
Expected verdicts are recorded only where the construction guarantees them.
"""
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "cnf")
os.makedirs(OUT, exist_ok=True)

# (family, cnfgen args, expected)  expected: "unsat" | "sat" | None
SPECS = []
for p, h in [(5, 4), (6, 5), (7, 6), (8, 7), (10, 9), (12, 11)]:
    SPECS.append((f"php_{p}_{h}", ["php", str(p), str(h)], "unsat"))
for n in (6, 8, 10, 12):
    SPECS.append((f"op_{n}", ["op", str(n)], "unsat"))
for n in (6, 8, 10):
    SPECS.append((f"parity_{n}", ["parity", str(n)], "sat"))  # even N is satisfiable
for n in (8, 12, 16, 20, 24, 28):
    SPECS.append((f"tseitin_{n}", ["tseitin", str(n)], "unsat"))
for n, d in [(12, 3), (20, 3), (16, 4)]:
    SPECS.append((f"tseitin_{n}_{d}reg", ["tseitin", str(n), str(d)], "unsat"))
for w, h in [(4, 4), (6, 6), (8, 8)]:
    SPECS.append((f"mchess_{w}_{h}", ["mchess", str(w), str(h)], "unsat"))
for w, h in [(4, 5), (5, 6)]:
    SPECS.append((f"mchess_{w}_{h}", ["mchess", str(w), str(h)], "sat"))
for s, n in [(3, 6), (4, 7)]:
    SPECS.append((f"stone_{s}_{n}", ["stone", str(s), "path", str(n)], "unsat"))
for n in (8, 12):
    SPECS.append((f"peb_path_{n}", ["peb", "path", str(n)], "unsat"))
for n in (10, 14):
    SPECS.append((f"kcolor_{n}", ["kcolor", "3", "gnm", str(n), str(int(n * 1.6))], None))
for n, m in [(10, 30), (14, 50), (18, 70)]:
    SPECS.append((f"randkxor_3_{n}_{m}", ["randkxor", "3", str(n), str(m)], None))
for n, m in [(12, 40), (16, 60), (20, 80)]:
    SPECS.append((f"randkcnf_3_{n}_{m}", ["randkcnf", "3", str(n), str(m)], None))

manifest = []
for name, args, expected in SPECS:
    path = os.path.join(OUT, name + ".cnf")
    cmd = ["cnfgen", "-q", "-S", "7"] + args
    try:
        with open(path, "w") as f:
            r = subprocess.run(cmd, stdout=f, stderr=subprocess.PIPE, timeout=120)
        if r.returncode != 0:
            print(f"skip {name}: {r.stderr.decode()[:120].strip()}", file=sys.stderr)
            os.unlink(path)
            continue
    except Exception as e:
        print(f"skip {name}: {e}", file=sys.stderr)
        continue
    nv = nc = 0
    with open(path) as f:
        for line in f:
            if line.startswith("p "):
                nv, nc = int(line.split()[2]), int(line.split()[3])
                break
    manifest.append({"name": name, "family": name.rsplit("_", 2)[0],
                     "cnf": path, "vars": nv, "clauses": nc,
                     "expected": expected, "args": args})

with open(os.path.join(HERE, "manifest.json"), "w") as f:
    json.dump(manifest, f, indent=1)
print(f"{len(manifest)} instances -> {OUT}")
