#!/bin/sh
# =====================================================================
#  SUTRA — test suite
#  Author: Sethu Iyer (github.com/sethuiyer)
#
#  A solver that emits certificates needs three kinds of tests:
#
#    positive   a certificate the solver produced must be ACCEPTED
#    soundness  a satisfiable instance must never be called UNSAT
#    negative   a deliberately corrupted certificate must be REJECTED
#
#  The third group is the important one.  A checker that accepts
#  everything proves nothing; these tests exist to show that the
#  verifier has teeth.  Each family is generated here, so the suite has
#  no external data dependency beyond python3 and cnfgen is not needed.
# =====================================================================
set -u
cd "$(dirname "$0")" || exit 2
TMP=$(mktemp -d) || exit 2
trap 'rm -rf "$TMP"' EXIT
pass=0; fail=0
ok()   { pass=$((pass+1)); printf '  ok   %s\n' "$1"; }
bad()  { fail=$((fail+1)); printf '  FAIL %s\n' "$1"; }

gen_tseitin() { # v out
  python3 - "$1" "$2" <<'PY'
import random, sys, itertools
v = int(sys.argv[1]); out = sys.argv[2]
rng = random.Random(1)
while True:
    stubs = [x for x in range(v) for _ in range(3)]
    rng.shuffle(stubs)
    edges, ok = [], True
    for i in range(0, len(stubs), 2):
        a, b = stubs[i], stubs[i+1]
        if a == b: ok = False; break
        edges.append((min(a,b), max(a,b)))
    if ok and len(set(edges)) == len(edges): break
    charges = None
charges = [rng.randint(0,1) for _ in range(v)]
if sum(charges) % 2 == 0: charges[0] ^= 1
inc = [[] for _ in range(v)]
for i,(a,b) in enumerate(edges): inc[a].append(i); inc[b].append(i)
cl = []
for x in range(v):
    vs = sorted(inc[x]); r = charges[x]
    for bits in itertools.product((0,1), repeat=3):
        if bits[0]^bits[1]^bits[2] != r:
            cl.append([(vs[k]+1) if bits[k]==0 else -(vs[k]+1) for k in range(3)])
with open(out,'w') as f:
    f.write(f"p cnf {len(edges)} {len(cl)}\n")
    for c in cl: f.write(' '.join(map(str,c))+" 0\n")
PY
}

gen_php() { # pigeons holes out
  python3 - "$1" "$2" "$3" <<'PY'
import sys
P,H,out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
v = lambda i,j: i*H+j+1
cl = [[v(i,j) for j in range(H)] for i in range(P)]
cl += [[-v(a,j), -v(b,j)] for j in range(H) for a in range(P) for b in range(a+1,P)]
with open(out,'w') as f:
    f.write(f"p cnf {P*H} {len(cl)}\n")
    for c in cl: f.write(' '.join(map(str,c))+" 0\n")
PY
}

gen_sat() { # vars out  -- satisfiable parity instance, must never be called UNSAT
  python3 - "$1" "$2" <<'PY'
import random, sys
n = int(sys.argv[1]); out = sys.argv[2]
rng = random.Random(7); sol = [rng.randint(0,1) for _ in range(n)]
cl = []
for _ in range(n//2):
    vs = sorted(rng.sample(range(n),3)); r = sol[vs[0]]^sol[vs[1]]^sol[vs[2]]
    for b in range(8):
        bits = [(b>>i)&1 for i in range(3)]
        if bits[0]^bits[1]^bits[2] != r:
            cl.append([(vs[i]+1) if bits[i]==0 else -(vs[i]+1) for i in range(3)])
with open(out,'w') as f:
    f.write(f"p cnf {n} {len(cl)}\n")
    for c in cl: f.write(' '.join(map(str,c))+" 0\n")
PY
}

echo "gfp: parity refutations (positive)"
for v in 32 80 140; do
  gen_tseitin "$v" "$TMP/t$v.cnf"
  ./sutra "$TMP/t$v.cnf" --proof "$TMP/t$v.gfp" >/dev/null 2>&1
  [ $? -eq 20 ] && ok "tseitin v=$v reports UNSAT" || bad "tseitin v=$v exit"
  if ./sutracert check "$TMP/t$v.cnf" "$TMP/t$v.gfp" >/dev/null 2>&1; then
    ok "tseitin v=$v certificate verifies"
  else bad "tseitin v=$v certificate REJECTED"; fi
done

echo "drat: general refutations (positive)"
for spec in "5 4" "6 5"; do
  set -- $spec
  gen_php "$1" "$2" "$TMP/p$1$2.cnf"
  ./sutra "$TMP/p$1$2.cnf" --proof "$TMP/p$1$2.drat" --exact-conflicts 2000000 >/dev/null 2>&1
  [ $? -eq 20 ] && ok "php($1,$2) reports UNSAT" || bad "php($1,$2) exit"
  if ./sutracert check "$TMP/p$1$2.cnf" "$TMP/p$1$2.drat" >/dev/null 2>&1; then
    ok "php($1,$2) certificate verifies"
  else bad "php($1,$2) certificate REJECTED"; fi
done

echo "soundness: satisfiable input is never called UNSAT"
gen_sat 40 "$TMP/sat.cnf"
./sutra "$TMP/sat.cnf" --proof "$TMP/sat.proof" --exact-conflicts 200000 >/dev/null 2>&1
[ $? -eq 10 ] && ok "satisfiable instance returns SAT" || bad "satisfiable instance misclassified"
[ ! -f "$TMP/sat.proof" ] && ok "no proof file left behind" || bad "stale proof file"

echo "negative controls: corrupted certificates MUST be rejected"
awk 'BEGIN{d=0} /^e /&&!d{gsub(/^e [01] /,"e 9 "); d=1} {print}' "$TMP/t32.gfp" > "$TMP/bad.gfp" 2>/dev/null
./sutracert check "$TMP/t32.cnf" "$TMP/bad.gfp" >/dev/null 2>&1
[ $? -eq 1 ] && ok "tampered gfp rejected" || bad "tampered gfp ACCEPTED"
head -5 "$TMP/p54.drat" > "$TMP/short.drat" 2>/dev/null
./sutracert check "$TMP/p54.cnf" "$TMP/short.drat" >/dev/null 2>&1
[ $? -eq 1 ] && ok "truncated drat rejected" || bad "truncated drat ACCEPTED"
./sutracert check "$TMP/t80.cnf" "$TMP/t32.gfp" >/dev/null 2>&1
[ $? -eq 1 ] && ok "wrong-instance proof rejected" || bad "wrong-instance proof ACCEPTED"

echo "generalization: redundant clause does not defeat detection"
python3 - "$TMP/t32.cnf" "$TMP/t32red.cnf" <<'PY'
import sys
src, dst = sys.argv[1], sys.argv[2]
lines = [l for l in open(src) if l.strip() and not l.startswith('c')]
hdr = lines[0].split()
n, m = int(hdr[2]), int(hdr[3])
cls = [l.strip() for l in lines[1:]]
lits = cls[0].split()
extra = ' '.join(list(reversed(lits[:-1])) + ['0']) + '\n'
open(dst,'w').write(f"p cnf {n} {m+1}\n" + ''.join(c + '\n' for c in cls) + extra)
PY
./sutra "$TMP/t32red.cnf" --proof "$TMP/t32red.gfp" >/dev/null 2>&1
[ $? -eq 20 ] && ok "redundant clause: still refuted" || bad "redundant clause defeated detection"
if ./sutracert check "$TMP/t32red.cnf" "$TMP/t32red.gfp" >/dev/null 2>&1; then
  ok "redundant-clause certificate verifies"
else bad "redundant-clause certificate REJECTED"; fi

echo
echo "passed $pass, failed $fail"
[ "$fail" -eq 0 ]
