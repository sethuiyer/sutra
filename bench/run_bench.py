#!/usr/bin/env python3
"""Run certified SUTRA-V3 over the cnfgen corpus, verify every certificate.

For each CNF: solve, and if the solver claims UNSAT, check the proof with
sutracert (independent checker).  Also derives two MaxSAT variants per
instance (all-soft weight 1, and mixed hard/soft) and runs those.
"""
import json
import os
import random
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
SOLVER = os.path.join(ROOT, "sutra")
CHECKER = os.path.join(ROOT, "sutracert")
WCNF = os.path.join(HERE, "wcnf")
os.makedirs(WCNF, exist_ok=True)
TIMEOUT = 20
EXACT_CONFLICTS = 300000


def to_wcnf(src, dst, mode, seed=0):
    rng = random.Random(seed)
    clauses, nv = [], 0
    with open(src) as f:
        for line in f:
            if line.startswith("p "):
                nv = int(line.split()[2])
            elif line and line[0] not in "c\n":
                lits = [int(x) for x in line.split() if x != "0"]
                if lits:
                    clauses.append(lits)
    if mode == "soft":
        top = len(clauses) + 1
        weights = [1] * len(clauses)
    else:
        cut = len(clauses) // 2
        top = len(clauses) * 6 + 1
        weights = [(top if i < cut else rng.randint(1, 5)) for i in range(len(clauses))]
    with open(dst, "w") as f:
        f.write(f"p wcnf {nv} {len(clauses)} {top}\n")
        for w, c in zip(weights, clauses):
            f.write(f"{w} " + " ".join(map(str, c)) + " 0\n")


def run(path, proof):
    t0 = time.time()
    cmd = [SOLVER, path, "--proof", proof,
           "--exact-conflicts", str(EXACT_CONFLICTS),
           "--time-budget-seconds", "5", "--restarts", "1",
           "--repair-flips", "200000"]
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        return {"status": "TIMEOUT", "exit": None, "wall": TIMEOUT, "cert": None}
    wall = time.time() - t0
    d = {}
    for line in r.stdout.splitlines():
        line = line.strip()
        if line.startswith("{"):
            try:
                d = json.loads(line)
            except Exception:
                pass
    status = d.get("status", "ERROR")
    cert = None
    if r.returncode == 20:
        c = subprocess.run([CHECKER, "check", path, proof],
                           capture_output=True, text=True)
        cert = (c.returncode == 0, (c.stdout or c.stderr).strip().splitlines()[-1]
                if (c.stdout or c.stderr).strip() else "")
    return {"status": status, "exit": r.returncode, "wall": round(wall, 4),
            "cert": cert, "parity": d.get("parity_contradiction"),
            "fmt": d.get("proof_format"), "json": d}


def main():
    manifest = json.load(open(os.path.join(HERE, "manifest.json")))
    rows = []
    for i, m in enumerate(manifest):
        proof = os.path.join("/tmp", f"cert_{i}.proof")
        res = run(m["cnf"], proof)
        row = dict(m)
        row.update(res)
        rows.append(row)

    # MaxSAT variants
    wrows = []
    for i, m in enumerate(manifest):
        for mode in ("soft", "mixed"):
            name = f'{m["name"]}__{mode}'
            dst = os.path.join(WCNF, name + ".wcnf")
            if not os.path.exists(dst):
                to_wcnf(m["cnf"], dst, mode, seed=i)
            proof = os.path.join("/tmp", f"wcert_{i}_{mode}.proof")
            res = run(dst, proof)
            wrows.append({"name": name, "vars": m["vars"], "clauses": m["clauses"],
                          "status": res["status"], "wall": res["wall"],
                          "cert": res["cert"]})

    print(f'{"instance":26} {"vars":>5} {"cl":>6} {"status":>9} {"wall":>7}  certificate')
    print("-" * 78)
    for r in rows:
        cert = ""
        if r["cert"] is not None:
            cert = ("VERIFIED " + r["cert"][1]) if r["cert"][0] else ("REJECTED " + r["cert"][1])
        print(f'{r["name"]:26} {r["vars"]:5d} {r["clauses"]:6d} {r["status"]:>9} '
              f'{r["wall"]:7.2f}  {cert}')

    unsat = [r for r in rows if r["status"] == "UNSAT"]
    ver = [r for r in unsat if r["cert"] and r["cert"][0]]
    bad = [r for r in unsat if r["cert"] and not r["cert"][0]]
    sat = [r for r in rows if r["status"] == "SAT"]
    unk = [r for r in rows if r["status"] not in ("SAT", "UNSAT")]
    print()
    print(f"CNF: {len(rows)} instances | UNSAT {len(unsat)} | certified-verified {len(ver)}"
          f" | rejected {len(bad)} | SAT {len(sat)} | unknown/other {len(unk)}")
    if bad:
        print("  !! REJECTED CERTIFICATES:", [r["name"] for r in bad])

    wunsat = [r for r in wrows if r["status"] == "UNSAT"]
    wver = [r for r in wunsat if r["cert"] and r["cert"][0]]
    from collections import Counter
    print(f"WCNF: {len(wrows)} runs | status "
          f"{dict(Counter(r['status'] for r in wrows))} | certified {len(wver)}/{len(wunsat)}")
    print(f"  wall sum CNF {sum(r['wall'] for r in rows):.2f}s, "
          f"WCNF {sum(r['wall'] for r in wrows):.2f}s")

    with open(os.path.join(HERE, "results.json"), "w") as f:
        json.dump({"cnf": rows, "wcnf": wrows}, f, indent=1)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
