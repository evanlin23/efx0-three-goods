"""GDT reachability (k4/sdc.md §30).  Lemma GDT (proved in §30): a state whose bases are single goods or pairs, with
an owner o holding a single good, has a one-absorber EFX0 completion if
  (G1) no good of a pair is wanted (worth more to some agent than its own base),
  (G2) no junk good is wanted,
  (G3) every pair holder p has at most one good of R_p outside B_p that is junk or in B_o,
  (G4) every frozen agent x (one-good base wanted by someone) has v_x((J + B_o) cap R_x) <= v_x(B_x),
  (G5) B_o is wanted by nobody.
Question: from the serial-dictatorship picks of every order, is a GDT state (for some owner) reachable by improving
chains (de_free.py chains with junk sets of at most 2 goods per agent, bases of at most 2 goods)?  BFS, capped.
The conditions are checked directly (no SAT); a SAT check of the final state confirms Lemma GDT.

    python3 k4/sdc/gdt_reach.py screen|suite|special|logs|cores:FILES N SEED"""
import sys, os, json, itertools, collections, time
import _paths
import de_free as DF
from sdclib import Enc
from sdc_orders import sd
from min_frozen import load
from f1_owner import absorber_ok

DF.CHAIN_ONLY = True; DF.HMAX = 2; DF.BMAX = 2


def gdt_owner(E, base):
    """an owner o for which (G1)-(G5) hold, or None"""
    n, m = E.n, E.m
    B = [[g for g in range(m) if base[g] == i] for i in range(n)]
    if any(len(b) == 0 or len(b) > 2 for b in B): return None
    J = [g for g in range(m) if base[g] < 0]
    val = lambda i, S: sum(E.v[i].get(g, 0) for g in S)
    wanted = lambda g: any(E.v[i].get(g, 0) > val(i, B[i]) for i in range(n) if base[g] != i)
    for i in range(n):
        if len(B[i]) == 2 and any(wanted(g) for g in B[i]): return None          # G1
    if any(wanted(g) for g in J): return None                                     # G2
    frozen = [j for j in range(n) if len(B[j]) == 1 and wanted(B[j][0])]
    for o in range(n):
        if len(B[o]) != 1 or o in frozen: continue                                # G5
        W = set(J) | set(B[o])
        if any(len(B[p]) == 2 and sum(1 for g in E.R[p] if g not in B[p] and g in W) > 1 for p in range(n)): continue  # G3
        if any(val(x, [g for g in W if g in E.R[x]]) > val(x, B[x]) for x in frozen): continue                      # G4
        return o
    return None


def bfs(E, start, cap=2000):
    frontier = [start]; seen = {start}; d = 0
    while frontier:
        for b in frontier:
            o = gdt_owner(E, b)
            if o is not None: return d, b, o
        nxt = []
        for b in frontier:
            for b2 in DF.moves(E, b):
                if b2 not in seen:
                    seen.add(b2); nxt.append(b2)
                    if len(seen) > cap: return 'cap', None, None
        frontier = nxt; d += 1
    return None, None, None


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/gdt_reach.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > 5: continue
        E = Enc(sets, vals, m); C['instances'] += 1; res = {}
        for od in itertools.permutations(range(n)):
            Y = tuple(sd(E, list(od))[0])
            if Y not in res:
                base = [-1] * m
                for i, g in enumerate(Y):
                    if g is not None: base[g] = i
                d, b, o = bfs(E, tuple(base))
                if b is not None:
                    C['GDT states reached'] += 1; C['  of these, SAT confirms owner o'] += absorber_ok(E, b, o)
                res[Y] = d
            C['starts'] += 1; C['starts: chains to a GDT state %s' % res[Y]] += 1
        bad = [Y for Y, d in res.items() if not isinstance(d, int)]
        C['instances with every start reaching a GDT state'] += not bad
        C['instances with some start reaching a GDT state'] += any(isinstance(d, int) for d in res.values())
        if bad and C['shown'] < 3:
            C['shown'] += 1; print('UNREACHED', name, json.dumps((sets, vals)), 'picks', bad[0], res[bad[0]], flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
