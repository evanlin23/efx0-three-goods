"""The two-terminal gap (k4/k3_oc1.md §12): hard perfect drafts with |T| >= 2 after LB's upgrades that neither R1C nor
B* covers (GAP lines of gap_scan.py with |T| >= 2).  For each: why B* fails at each terminal, and which DE trades
repair (exact test lb2) -- in particular rotations from an exposed agent of a terminal t into t, as in B*, and the
witness after them (no owner / owner).
    python3 k4/k3oc1/t2gap.py GAPFILE... [MAX]"""
import sys, os, json, re, ast, collections, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines, bundles
from lbtest import upgrade, parts, exposed, lb2
from thm_bstar import mh, chains_to
from de_moves import de_trades
C = collections.Counter()
args = [a for a in sys.argv[1:] if not a.isdigit()]; MAX = int(next((a for a in sys.argv[1:] if a.isdigit()), 10 ** 9))
cnt = 0
for fn in args:
    for line in read_lines(fn):
        mt = re.match(r'GAP (\[\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+)', line)
        if not mt or int(mt.group(5)) < 2: continue
        cnt += 1
        if cnt > MAX: break
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); Y = ast.literal_eval(mt.group(4)); n = len(rk)
        b = base_of(Y, m); bu = upgrade(rk, m, b); B, J, U, NA, F, T = parts(rk, m, bu)
        pi = lambda x: [g for g in (rk[x][1], rk[x][2]) if g in J]
        why = []
        for t in T:
            E = exposed(rk, bu, t, B, J, U); h = mh([pi(x) for x in E]); d = h - (len(T) - 1)
            reasons = set()
            if d != 1: reasons.add('deficit %d' % d)
            else:
                for k in E:
                    r = []
                    if k not in F: r.append('k terminal')
                    elif not chains_to(rk, B, U, k, t): r.append('no chain to t')
                    if any(x != k and {rk[x][1], rk[x][2]} == {rk[k][1], rk[k][2]} for x in E): r.append('shared pair')
                    pk = {rk[k][1], rk[k][2]}
                    hk = mh([[g for g in (rk[x][1], rk[x][2]) if g not in pk] for x in E if x != k])
                    if hk is None or hk > len(T) - 1: r.append('(iv)')
                    reasons.add('+'.join(r) if r else 'ok?')
            why.append('t%d: %s' % (T.index(t), ' | '.join(sorted(reasons))))
        C['B* fails: ' + ' ; '.join(why)] += 1
        mv = de_trades(rk, m, bu)
        rot = []
        for nb, d in mv:
            # rotation into a terminal t from an exposed agent of t
            for t in T:
                E = set(exposed(rk, bu, t, B, J, U))
                if t in d[1] and (d[0] == 'DEring' or d[1][0] in E): rot.append((nb, d, t))
        ok = [(nb, d, t, lb2(rk, m, nb)) for nb, d, t in rot]
        rep = [w for nb, d, t, w in ok if w]
        C['some rotation into a terminal repairs %s' % bool(rep)] += 1
        if rep: C['repairing rotations: witness kinds %s' % sorted(set(w[0] for w in rep))] += 1
        C['some DE trade repairs %s' % any(lb2(rk, m, nb) for nb, d in mv)] += 1
for k in sorted(C): print(k, C[k])
