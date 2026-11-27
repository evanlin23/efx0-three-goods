"""Conjecture T-E (k4/k3_oc1.md §12): every valid Rule E rotation -- a frozen exposed agent k, its earliest-wanter
chain (sigma = the order) ending at a terminal e with {b_k, c_k} inside J + {Y_e} -- followed by LB's maximal upgrades,
has a one-absorber completion with owner e (LB+'s owner r), or with no owner.  Tests: the simple Lemma 1 (no owner:
|J'| <= |T'|; owner e: a terminal with h(E'_e) <= |T'| - 1, or a pair holder after upgrading with h(E'_e) <= |T'|);
LE: Lemma 1 plus one slot for k (le_test); the exact test with owner none or e (lb2_owners).
    python3 k4/k3oc1/t2k_e.py gapfile:FILE... [T=1|2]
    python3 k4/k3oc1/t2k_e.py source:SOURCE [PROFILES SEED] [SHARD NSHARDS]   every hard perfect draft (exact lb2), not
        only the gap; sigma = the least-index topological order of the draft's need DAG.  PROFILES = 0: every profile.
        SOURCE as in oc1_k3.py (small:N, certs:N, rand:N:M:COUNT)."""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines
from lbtest import upgrade, parts, exposed, lb2_owners, min_hit, _owner_test
from t2k import wanters_of, chain, rotate


def le_test(rk, m, nb, k, e):
    """after LB's maximal upgrades: no owner, or owner e (a terminal, or a pair holder if e upgraded); every other
    terminal takes at most one junk good, and so may k, if its bundle {b_k, c_k, g} holds no other top-holder's pair"""
    n = len(rk); bu = upgrade(rk, m, nb); B, J, U, NA, F, T = parts(rk, m, bu)
    r = _owner_test(rk, m, bu, B, J, U, T, [i == k for i in range(n)], {'none', e})
    return r


def simple_e(rk, m, nb, e):
    bu = upgrade(rk, m, nb); B, J, U, NA, F, T = parts(rk, m, bu)
    if len(J) <= len(T): return 'none'
    if e not in T and not U[e]: return None
    E = exposed(rk, bu, e, B, J, U)
    if any({rk[x][1], rk[x][2]} <= set(B[e]) for x in E): return None
    if min_hit([[g for g in (rk[x][1], rk[x][2]) if g in J] for x in E], len(T) - (e in T)) is not None: return 'e'
    return None


def valid_rotations(rk, m, order, Y):
    pos = {a: i for i, a in enumerate(order)}
    bu = upgrade(rk, m, base_of(Y, m)); B, J, U, NA, F, T = parts(rk, m, bu)
    W = wanters_of(rk, bu, B, U); ks = set()
    for t in T: ks |= set(exposed(rk, bu, t, B, J, U))
    out = []
    for k in sorted(ks):
        if B[k] != [rk[k][0]]: continue
        p = chain(k, W, pos)
        if p is None or len(p) < 2 or p[-1] not in T or not {rk[k][1], rk[k][2]} <= set(J) | set(B[p[-1]]): continue
        out.append((k, p, rotate(rk, bu, B, p)))
    return out


def topo(rk, Y):
    """least-index topological order of the need DAG (y before x if x ranks Y_y above Y_x)"""
    n = len(rk); rank = [{g: i for i, g in enumerate(r)} for r in rk]
    pred = [set(y for y in range(n) if y != x and Y[y] is not None and Y[y] in rank[x]
                and (Y[x] is None or rank[x][Y[y]] < rank[x][Y[x]])) for x in range(n)]
    order = []
    while len(order) < n:
        x = min(v for v in range(n) if v not in order and pred[v] <= set(order)); order.append(x)
    return tuple(order)


def run_source(argv):
    import random
    from oc1_fast import drafts
    from oc1_k3 import hypergraphs, profiles
    from lbtest import lb2
    src = argv[0]; P, seed = (int(argv[1]), int(argv[2])) if len(argv) > 2 else (0, 0)
    shard, nsh = (int(argv[3]), int(argv[4])) if len(argv) > 4 else (0, 1)
    rng = random.Random(seed); C = collections.Counter()
    print('$ python3 k4/k3oc1/t2k_e.py source:' + ' '.join(argv), flush=True)
    for ci, (sets, m) in enumerate(hypergraphs(src, rng)):
        if ci % nsh != shard: continue
        for rk in profiles(sets, P, rng):
            for Y in drafts(rk, len(sets)):
                if any(g is None for g in Y): continue
                b = base_of(Y, m)
                if lb2(rk, m, b): continue
                T = parts(rk, m, upgrade(rk, m, b))[5]; tag = '|T| %d: ' % len(T)
                C[tag + 'hard perfect drafts'] += 1
                R = valid_rotations(rk, m, topo(rk, Y), Y)
                if not R:
                    C[tag + 'no valid Rule E rotation'] += 1
                    print('NOROT', json.dumps([list(r) for r in rk]), m, 'picks', Y, flush=True); continue
                oks = []
                for k, p, nb in R:
                    le = le_test(rk, m, nb, k, p[-1])
                    if le: C[tag + 'rotations LE owner none-or-e'] += 1; oks.append(True); continue
                    lek = _owner_test(rk, m, *(lambda bu: (bu,) + parts(rk, m, bu)[:3] + (parts(rk, m, bu)[5],))(upgrade(rk, m, nb)), [i == k for i in range(len(rk))], {k})
                    C[tag + 'rotations needing owner k: LE owner k %s' % bool(lek)] += 1; oks.append(bool(lek))
                    if not lek: print('FAIL', json.dumps([list(r) for r in rk]), m, 'picks', Y, 'k', k, 'chain', p, flush=True)
                C[tag + 'drafts: every rotation completes %s' % all(oks)] += 1
                C[tag + 'drafts: some rotation completes %s' % any(oks)] += 1
                if not any(oks): print('NOSOME', json.dumps([list(r) for r in rk]), m, 'picks', Y, flush=True)
    for k_ in sorted(C): print(k_, C[k_])


if __name__ == '__main__' and sys.argv[1].startswith('source:'):
    run_source([sys.argv[1][7:]] + sys.argv[2:]); sys.exit()

if __name__ == '__main__':
    C = collections.Counter(); want_T = None
    for a in sys.argv[1:]:
        if a.startswith('T='): want_T = int(a[2:])
    for a in sys.argv[1:]:
        if a.startswith('T='): continue
        for line in read_lines(a[8:] if a.startswith('gapfile:') else a):
            mt = re.search(r'GAP (\[\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+)', line)
            if not mt or (want_T is not None and int(mt.group(5)) != want_T): continue
            rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); tag = '|T| %s: ' % mt.group(5)
            R = valid_rotations(rk, m, ast.literal_eval(mt.group(3)), ast.literal_eval(mt.group(4)))
            if not R: C[tag + 'drafts with no valid Rule E rotation'] += 1; continue
            allok = True; allsimple = True; allle = True
            for k, p, nb in R:
                s = simple_e(rk, m, nb, p[-1]); le = le_test(rk, m, nb, k, p[-1])
                ok = bool(s) or bool(le) or bool(lb2_owners(rk, m, nb, {'none', p[-1]}))
                C[tag + 'rotations: simple %s, LE %s, exact none-or-e %s' % (s, le[0] if le else None, ok)] += 1
                allle = allle and bool(le)
                allok &= ok; allsimple &= bool(s)
                if not ok: print('FAIL', line.strip()[4:220], 'k', k, 'chain', p, flush=True)
            C[tag + 'drafts: every rotation exact none-or-e %s' % allok] += 1
            C[tag + 'drafts: every rotation simple none-or-e %s' % allsimple] += 1
            C[tag + 'drafts: every rotation LE (owner none or e, slots T and k) %s' % allle] += 1
    for k in sorted(C): print(k, C[k])
