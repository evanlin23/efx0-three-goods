"""Which k?  On GAP lines: every valid Rule E rotation (t2k.py) of an exposed top-holder k into the terminal e where its
earliest-wanter chain ends, then upgrades and the simple Lemma 1 test (no owner, or owner k).  Candidate rules for k:
sigma-first, sigma-last, least omega' (every least / some least), most terminals T', longest chain.
    python3 k4/k3oc1/t2k_rules.py gapfile:FILE... [T=2]"""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines
from lbtest import upgrade, parts, exposed
from t2k import wanters_of, chain, rotate, simple_ok

def rots(rk, m, order, Y):
    pos = {a: i for i, a in enumerate(order)}
    bu = upgrade(rk, m, base_of(Y, m)); B, J, U, NA, F, T = parts(rk, m, bu)
    W = wanters_of(rk, bu, B, U); out = []
    ks = set()
    for t in T: ks |= set(exposed(rk, bu, t, B, J, U))
    for k in sorted(ks, key=lambda v: pos[v]):
        if B[k] != [rk[k][0]]: continue
        p = chain(k, W, pos)
        if p is None or p[-1] not in T or not {rk[k][1], rk[k][2]} <= set(J) | set(B[p[-1]]): continue
        nb = rotate(rk, bu, B, p); s = simple_ok(rk, m, nb, k)
        P = parts(rk, m, upgrade(rk, m, nb)); om = len(P[1]) - len(P[5])
        out.append(dict(k=k, path=p, ok=bool(s), how=s, om=om, T=len(P[5]), frozen=k not in T))
    return out

if __name__ == '__main__':
    C = collections.Counter(); want_T = None
    for a in sys.argv[1:]:
        if a.startswith('T='): want_T = int(a[2:])
    for a in sys.argv[1:]:
        if a.startswith('T='): continue
        for line in read_lines(a[8:] if a.startswith('gapfile:') else a):
            mt = re.search(r'GAP (\[\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+)', line)
            if not mt or (want_T is not None and int(mt.group(5)) != want_T): continue
            rk = [tuple(r) for r in json.loads(mt.group(1))]
            R = rots(rk, int(mt.group(2)), ast.literal_eval(mt.group(3)), ast.literal_eval(mt.group(4)))
            tag = '|T| %s: ' % mt.group(5)
            if not R: C[tag + 'no valid Rule E rotation'] += 1; continue
            C[tag + 'some k ok %s' % any(r['ok'] for r in R)] += 1
            C[tag + 'every k ok %s' % all(r['ok'] for r in R)] += 1
            C[tag + 'sigma-first k ok %s' % R[0]['ok']] += 1
            C[tag + 'sigma-last k ok %s' % R[-1]['ok']] += 1
            mo = min(r['om'] for r in R)
            C[tag + 'every least-omega k ok %s' % all(r['ok'] for r in R if r['om'] == mo)] += 1
            C[tag + 'least omega <= 0 %s' % (mo <= 0)] += 1
            mT = max(r['T'] for r in R)
            C[tag + 'every most-T\' k ok %s' % all(r['ok'] for r in R if r['T'] == mT)] += 1
            mL = max(len(r['path']) for r in R)
            C[tag + 'every longest-chain k ok %s' % all(r['ok'] for r in R if len(r['path']) == mL)] += 1
            C[tag + 'how: ' + '/'.join(sorted(set(str(r['how']) for r in R if r['ok'])))] += 1
            C[tag + 'some frozen k ok %s' % any(r['ok'] and r['frozen'] for r in R)] += 1
    for k in sorted(C): print(k, C[k])
