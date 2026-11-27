"""For every valid Rule E rotation of a frozen exposed agent k into the terminal e where its chain ends (t2k.py), which
owners complete it (exact test with the owner restricted, lbtest.lb2_owners): none; k; e; another terminal; another
pair holder.  Counts rotations by the set of owner kinds that work, on GAP lines.
    python3 k4/k3oc1/t2k_owners.py gapfile:FILE... [T=2]"""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines
from lbtest import upgrade, parts, exposed, lb2_owners
from t2k import wanters_of, chain, rotate

C = collections.Counter(); want_T = None
for a in sys.argv[1:]:
    if a.startswith('T='): want_T = int(a[2:])
for a in sys.argv[1:]:
    if a.startswith('T='): continue
    for line in read_lines(a[8:] if a.startswith('gapfile:') else a):
        mt = re.search(r'GAP (\[\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+)', line)
        if not mt or (want_T is not None and int(mt.group(5)) != want_T): continue
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); n = len(rk)
        order = ast.literal_eval(mt.group(3)); Y = ast.literal_eval(mt.group(4)); tag = '|T| %s: ' % mt.group(5)
        pos = {a_: i for i, a_ in enumerate(order)}
        bu = upgrade(rk, m, base_of(Y, m)); B, J, U, NA, F, T = parts(rk, m, bu)
        W = wanters_of(rk, bu, B, U)
        ks = set()
        for t in T: ks |= set(exposed(rk, bu, t, B, J, U))
        per = []
        for k in sorted(ks):
            if B[k] != [rk[k][0]]: continue
            p = chain(k, W, pos)
            if p is None or len(p) < 2 or p[-1] not in T or not {rk[k][1], rk[k][2]} <= set(J) | set(B[p[-1]]): continue
            nb = rotate(rk, bu, B, p); e = p[-1]
            others = set(range(n)) - {k, e}
            kinds = []
            if lb2_owners(rk, m, nb, {'none'}): kinds.append('none')
            if lb2_owners(rk, m, nb, {k}): kinds.append('k')
            if lb2_owners(rk, m, nb, {e}): kinds.append('e')
            if lb2_owners(rk, m, nb, others): kinds.append('other')
            C[tag + 'rotation owners ' + ('+'.join(kinds) or 'NONE WORKS')] += 1
            per.append(kinds)
        if per:
            C[tag + 'draft: every rotation works with none-or-k-or-e %s' % all(set(x) & {'none', 'k', 'e'} for x in per)] += 1
            C[tag + 'draft: some rotation works with none-or-k %s' % any(set(x) & {'none', 'k'} for x in per)] += 1
            C[tag + 'draft: every rotation works with none-or-k %s' % all(set(x) & {'none', 'k'} for x in per)] += 1
for k in sorted(C): print(k, C[k])
