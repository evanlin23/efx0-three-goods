"""T2-k (k4/k3_oc1.md §12): at a hard perfect draft, the rotation of an exposed agent k along its earliest-wanter
chain (kgen-n3's Rule E: sigma = the order, each next receiver the sigma-earliest wanter of the current good), into
the terminal e where the chain ends, valid when {b_k, c_k} lies in J + {Y_e}.  Variant 'target': for each terminal t
with k in E_t, the sigma-earliest wanter from which t can still be reached.  After the rotation, LB's maximal upgrades,
then the simple Lemma 1 test with no owner (|J'| <= |T'|) or owner k (no exposed pair inside k's pair, and
h(E'_k) <= |T'|); also the exact test with owner restricted to {none, k}.
    python3 k4/k3oc1/t2k.py gapfile:FILE... [T=2]"""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines, bundles
from lbtest import upgrade, parts, exposed, lb2_owners, min_hit


def wanters_of(rk, base, B, U):
    rank = [{g: i for i, g in enumerate(r)} for r in rk]
    W = {}
    for y in range(len(rk)):
        if len(B[y]) != 1: continue
        g = B[y][0]
        W[y] = [v for v in range(len(rk)) if v != y and not U[v] and g in rank[v]
                and (not B[v] or rank[v][g] < rank[v][B[v][0]])]
    return W


def chain(k, W, pos, target=None):
    path = [k]
    def reach(v, t, seen=()):
        if v == t: return True
        return any(reach(w, t) for w in W.get(v, []))
    while W.get(path[-1]):
        cand = sorted(W[path[-1]], key=lambda v: pos[v])
        if target is not None: cand = [v for v in cand if reach(v, target)]
        if not cand: return None
        path.append(cand[0])
    if target is not None and path[-1] != target: return None
    return path


def rotate(rk, base, B, path):
    k = path[0]; nb = list(base); e = path[-1]
    for i in range(1, len(path)): nb[B[path[i - 1]][0]] = path[i]
    if len(path) > 1 and B[e]: nb[B[e][0]] = -1
    if len(path) == 1: nb[rk[k][0]] = -1
    nb[rk[k][1]] = k; nb[rk[k][2]] = k
    return tuple(nb)


def simple_ok(rk, m, nb, k):
    bu = upgrade(rk, m, nb); B, J, U, NA, F, T = parts(rk, m, bu)
    if len(J) <= len(T): return 'none'
    E = exposed(rk, bu, k, B, J, U)
    pk = set(B[k])
    if any({rk[x][1], rk[x][2]} <= pk for x in E): return None
    if min_hit([[g for g in (rk[x][1], rk[x][2]) if g in J] for x in E], len(T)) is not None: return 'k'
    return None


def analyse(rk, m, order, Y, C, tag):
    n = len(rk); pos = {a: i for i, a in enumerate(order)}
    bu = upgrade(rk, m, base_of(Y, m)); B, J, U, NA, F, T = parts(rk, m, bu)
    W = wanters_of(rk, bu, B, U)
    ex = {t: set(exposed(rk, bu, t, B, J, U)) for t in T}
    res = {'E-simple': False, 'E-exact': False, 'target-simple': False, 'target-exact': False}
    detail = []
    for k in sorted(set().union(*ex.values())):
        if not (len(B[k]) == 1 and B[k][0] == rk[k][0]): continue
        pair = {rk[k][1], rk[k][2]}
        p = chain(k, W, pos)
        if p is not None:
            e = p[-1]; ok_valid = pair <= set(J) | set(B[e]) and e in T and len(p) >= 1
            if ok_valid:
                nb = rotate(rk, bu, B, p); s = simple_ok(rk, m, nb, k)
                if s: res['E-simple'] = True
                if s or lb2_owners(rk, m, nb, {'none', k}): res['E-exact'] = True
                detail.append(('E', tuple(p), s))
        for t in T:
            if k not in ex[t]: continue
            p = chain(k, W, pos, target=t)
            if p is None: continue
            nb = rotate(rk, bu, B, p); s = simple_ok(rk, m, nb, k)
            if s: res['target-simple'] = True
            if s or lb2_owners(rk, m, nb, {'none', k}): res['target-exact'] = True
    for key, v in res.items(): C[tag + key + ' ' + str(v)] += 1
    return res, detail


if __name__ == '__main__':
    C = collections.Counter(); want_T = None
    args = [a for a in sys.argv[1:] if not a.startswith('T=')]
    for a in sys.argv[1:]:
        if a.startswith('T='): want_T = int(a[2:])
    for a in args:
        for line in read_lines(a[8:] if a.startswith('gapfile:') else a):
            mt = re.search(r'GAP (\[\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+)', line)
            if not mt: continue
            if want_T is not None and int(mt.group(5)) != want_T: continue
            rk = [tuple(r) for r in json.loads(mt.group(1))]
            res, det = analyse(rk, int(mt.group(2)), ast.literal_eval(mt.group(3)), ast.literal_eval(mt.group(4)), C,
                               '|T| %s: ' % mt.group(5))
            if not res['E-exact'] or not res['target-exact']:
                print('MISS', {k_: v for k_, v in res.items()}, line.strip()[4:220], det, flush=True)
    for k in sorted(C): print(k, C[k])
