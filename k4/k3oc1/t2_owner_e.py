"""Two or more terminals, kgen-n3's owner-t route (G6, G7; kgen/n3.md §15.18): for a terminal e, take sigma with e
last; the Rule E rotations of exposed frozen agents k with {b_k, c_k} in J + {Y_e} whose chains end at e.  Test:
(N) no owner, |J'| <= |T'| (no upgrades after the rotation); or (L3) Lemma 3 for owner e:
h({pair_y & J' : y in E'_e frozen}) <= |T' - E'_e| - 1.  Per draft: does some (e, k) pass?
    python3 k4/k3oc1/t2_owner_e.py gapfile:FILE... | source:SOURCE PROFILES SEED [SHARD NSHARDS]"""
import sys, os, json, re, ast, collections, random
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines
from lbtest import upgrade, parts, exposed, min_hit, lb2
from t2k import wanters_of, chain, rotate
from t2k_e import topo

def topo_last(rk, Y, e):
    o = [x for x in topo(rk, Y) if x != e]; return tuple(o + [e])

def lemma3(rk, m, nb, e):
    B, J, U, NA, F, T = parts(rk, m, nb)
    if len(J) <= len(T): return 'N'
    if e not in T: return None
    E = exposed(rk, nb, e, B, J, U); EF = [y for y in E if y in F]
    h = min_hit([[g for g in (rk[y][1], rk[y][2]) if g in J] for y in EF], len(J))
    return 'L3' if h is not None and len(h) <= len([x for x in T if x not in E]) - 1 else None

def test(rk, m, Y, C, tag):
    bu = upgrade(rk, m, base_of(Y, m)); B, J, U, NA, F, T = parts(rk, m, bu)
    res = set(); ends_ok = False
    for e in T:
        pos = {a: i for i, a in enumerate(topo_last(rk, Y, e))}; W = wanters_of(rk, bu, B, U)
        for k in exposed(rk, bu, e, B, J, U):
            if k not in F: continue
            p = chain(k, W, pos)
            if p is None or p[-1] != e: continue
            r = lemma3(rk, m, rotate(rk, bu, B, p), e)
            if r: res.add(r)
    C[tag + 'some (e, k) with chain ending at sigma-last e passes: %s' % ('+'.join(sorted(res)) if res else 'NONE')] += 1
    return bool(res)

if __name__ == '__main__':
    C = collections.Counter()
    if sys.argv[1].startswith('source:'):
        from oc1_fast import drafts
        from oc1_k3 import profiles
        from oc1_max import sources
        src = sys.argv[1][7:]; P, seed = int(sys.argv[2]), int(sys.argv[3])
        shard, nsh = (int(sys.argv[4]), int(sys.argv[5])) if len(sys.argv) > 5 else (0, 1)
        rng = random.Random(seed * 1000 + shard)
        print('$ python3 k4/k3oc1/t2_owner_e.py', *sys.argv[1:], flush=True)
        for ci, (sets, m) in enumerate(sources(src, rng)):
            if ci % nsh != shard: continue
            for rk in profiles(sets, P, rng):
                for Y in drafts(rk, len(sets)):
                    if any(g is None for g in Y) or lb2(rk, m, base_of(Y, m)): continue
                    T = parts(rk, m, upgrade(rk, m, base_of(Y, m)))[5]
                    if not test(rk, m, Y, C, '|T| %d: ' % len(T)):
                        print('FAIL', json.dumps([list(x) for x in rk]), m, 'picks', Y, flush=True)
    else:
        for a in sys.argv[1:]:
            for line in read_lines(a[8:] if a.startswith('gapfile:') else a):
                mt = re.search(r'GAP (\[\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+)', line)
                if not mt: continue
                rk = [tuple(r) for r in json.loads(mt.group(1))]
                if not test(rk, int(mt.group(2)), ast.literal_eval(mt.group(4)), C, '|T| %s: ' % mt.group(5)):
                    print('FAIL', line.strip()[4:220], flush=True)
    for k in sorted(C): print(C[k], k)
