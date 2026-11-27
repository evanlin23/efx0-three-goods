"""Theorem B* (k4/k3_oc1.md §3): LB+'s rotation for an arbitrary order.  After LB's maximal upgrades, let t be a
terminal with h(E_t) = |T| (deficit one for owner t) and k in E_t frozen, with a need chain to t, no other agent of
E_t with the same pair, and the sets {b_x, c_x} - {b_k, c_k} (x in E_t - {k}) have a hitting set of size <= |T| - 1.  Then rotating k along any need chain to t (k takes its pair,
from J or J + {Y_t}) gives a state with a one-absorber completion (owner k, or no owner).
Coverage on hard drafts, and a check of the conclusion with the exact test lbtest.lb2 on every chain.
    python3 k4/k3oc1/thm_bstar.py LOG..."""
import sys, os, json, re, ast, collections, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines
from lbtest import upgrade, parts, exposed, lb2

def mh(sets):
    goods = sorted(set(g for s in sets for g in s))
    for r in range(len(goods) + 1):
        for H in itertools.combinations(goods, r):
            if all(set(s) & set(H) for s in sets): return r

def chains_to(rk, B, U, k, t):
    n = len(rk); out = []
    def walk(path):
        j = path[-1]
        if j == t: out.append(list(path)); return
        if not B[j]: return
        g = B[j][0]
        for w in range(n):
            if w in path or U[w]: continue
            if g in rk[w] and (not B[w] or rk[w].index(g) < rk[w].index(B[w][0])): walk(path + [w])
    walk([k]); return out

def bstar(rk, m, Y):
    n = len(rk); b = upgrade(rk, m, base_of(Y, m)); B, J, U, NA, F, T = parts(rk, m, b)
    if len(J) <= len(T): return 'no owner after upgrades', None
    pi = lambda x: [g for g in (rk[x][1], rk[x][2]) if g in J]
    found = []
    for t in T:
        E = exposed(rk, b, t, B, J, U)
        h = mh([pi(x) for x in E])
        if h <= len(T) - 1: return 'owner t at the draft', None
        if h != len(T): continue
        for k in E:
            if k not in F: continue
            if any(x != k and {rk[x][1], rk[x][2]} == {rk[k][1], rk[k][2]} for x in E): continue
            pk = {rk[k][1], rk[k][2]}
            if mh([[g for g in (rk[x][1], rk[x][2]) if g not in pk] for x in E if x != k]) > len(T) - 1: continue
            for P in chains_to(rk, B, U, k, t):
                nb = list(b)
                for g in B[t]: nb[g] = -1
                for s in range(len(P) - 1, 0, -1): nb[B[P[s - 1]][0]] = P[s]
                nb[rk[k][1]] = k; nb[rk[k][2]] = k
                found.append((t, k, P, bool(lb2(rk, m, tuple(nb)))))
    if not found: return 'B* does not apply', None
    return 'B* applies', found

if __name__ == '__main__':
    C = collections.Counter()
    for fn in sys.argv[1:]:
        for line in read_lines(fn):
            mt = re.match(r'HARD (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\))', line)
            if not mt: continue
            rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); Y = ast.literal_eval(mt.group(4))
            if lb2(rk, m, base_of(Y, m)): continue
            r, found = bstar(rk, m, Y); C['exact-hard'] += 1; C[r] += 1
            if found:
                C['B* rotations checked'] += len(found); C['B* rotations FAILING (contradicts the theorem)'] += sum(1 for f in found if not f[3])
                if any(not f[3] for f in found): print('FAIL', line.strip(), found)
    for k in sorted(C): print(k, C[k])
