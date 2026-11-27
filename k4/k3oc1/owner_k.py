"""On the drafts where no rotation into a terminal reaches the no-owner case (FAIL lines of tprime.py): does some
rotation repair with the owner restricted to none or the rotated agent k (B*'s owner), with the exact test?
    python3 k4/k3oc1/owner_k.py FAILFILE..."""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines
from lbtest import upgrade, parts, exposed, lb2, lb2_owners
from de_moves import de_trades
C = collections.Counter()
for fn in sys.argv[1:]:
    for line in read_lines(fn):
        mt = re.search(r'GAP (\[\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\))', line)
        if not mt: continue
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); Y = ast.literal_eval(mt.group(4))
        bu = upgrade(rk, m, base_of(Y, m)); B, J, U, NA, F, T = parts(rk, m, bu)
        ok_k = False; ok_any = False
        for nb, d in de_trades(rk, m, bu):
            for t in T:
                E = set(exposed(rk, bu, t, B, J, U))
                if t in d[1] and (d[0] == 'DEring' or d[1][0] in E):
                    k = d[1][0] if d[0] == 'DEchain' else d[1][(d[1].index(t) + 1) % len(d[1])]
                    if lb2_owners(rk, m, nb, {'none', k}): ok_k = True
                    if lb2(rk, m, nb): ok_any = True
                    break
        C['|T| %d: owner none-or-k repairs %s; any owner repairs %s' % (len(T), ok_k, ok_any)] += 1
for k in sorted(C): print(k, C[k])
