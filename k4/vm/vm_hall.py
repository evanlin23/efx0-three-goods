"""The Hall-type placeability condition at a V-M matching Y (k4/vm.md section 7.4).
Facts used (proved there): no pool good is wanted (Lemma S), so {Y_u, d} is EFX0-safe iff u is unfrozen (nobody
prefers Y_u to its own pick); frozen agents can receive nothing.
Condition HDT(Y): some unfrozen owner o and an injective map of some pool goods D into distinct unfrozen agents
other than o, with the rest L = P - D going to o, give an EFX0 allocation.  (This is OC1's zero-move one-absorber
completion at the picks with the absorber unfrozen.)  Checked: (a) every V-M matching where Lemma S's consequence
"no pool good wanted" holds (asserted), (b) HDT versus the no-move completion of VM1 (F1 + rotation, vm_max), and
(c) the Hall count |D_needed| <= |U| - 1, where D_needed is a smallest set of pool goods whose removal from the owner's
bundle protects every frozen agent.  EVIDENCE only.
    python3 k4/vm/vm_hall.py SOURCE"""
import sys, os, itertools, collections, time, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
from vm_test import items_for
from vm_max import no_move_runs


def analyse(I, Y):
    m = I.m; held = set(g for b in Y for g in b); P = sorted(set(range(m)) - held)
    Pv = [g for g in P if I.valued_by(g)]; J = [g for g in P if not I.valued_by(g)]
    own = [I.val(i, Y[i]) for i in range(I.n)]
    wanted = [g for g in Pv if any(I.v[i].get(g, 0) > own[i] for i in range(I.n))]
    frozen = [j for j in range(I.n) if Y[j] and any(i != j and I.val(i, Y[j]) > own[i] for i in range(I.n))]
    U = [j for j in range(I.n) if j not in frozen]
    hdt = False; need = None
    for o in U:
        others = [u for u in U if u != o]
        # smallest D protecting the frozen agents when L = Pv - D (plus junk) sits with o
        for r in range(0, len(Pv) + 1):
            okr = False
            for D in itertools.combinations(Pv, r):
                Xo = list(Y[o]) + [g for g in Pv if g not in D] + J
                if all(not V.efx0_envies(I, Y, i, Xo) for i in frozen):
                    okr = True
                    if need is None or r < need: need = r
                    if r <= len(others):
                        for perm in itertools.permutations(others, r):
                            X = [list(b) for b in Y]; X[o] = Xo
                            for d, u in zip(D, perm): X[u] = X[u] + [d]
                            if V.is_efx0(I, X): hdt = True; break
                    if hdt: break
            if hdt or okr: break
        if hdt: break
    return dict(wanted=bool(wanted), frozen=len(frozen), U=len(U), hdt=hdt, need=need)


def one(args):
    name, sets, vals, m = args
    I = V.Inst(sets, vals, m); out = []; seen = set()
    for ch, r in V.all_runs(V.vm_run, I, stop='II'):
        if isinstance(r, V.Stuck): continue
        Y = [list(b) for b in r[0]]; k = tuple(map(tuple, Y))
        if k in seen: continue
        seen.add(k)
        a = analyse(I, Y)
        succ, runs = no_move_runs(I, Y, 3000)
        a['nomove'] = bool(succ)
        out.append(a)
    return name, I.n, I.m, out


if __name__ == '__main__':
    src = sys.argv[1]
    print('$ python3 k4/vm/vm_hall.py', ' '.join(sys.argv[1:]))
    C = collections.Counter(); t0 = time.time(); viol = []
    with mp.Pool(os.cpu_count()) as pool:
        for name, n, m, out in pool.imap_unordered(one, items_for(src), chunksize=4):
            C['instances'] += 1
            C['instances: some V-M matching is HDT'] += any(a['hdt'] for a in out)
            C['instances: some V-M matching completes without moves'] += any(a['nomove'] for a in out)
            for a in out:
                C['V-M matchings'] += 1
                C['V-M matchings with a wanted pool good (must be 0)'] += a['wanted']
                C['matchings: HDT'] += a['hdt']; C['matchings: no-move completes'] += a['nomove']
                C['matchings: HDT and no-move completes'] += a['hdt'] and a['nomove']
                C['matchings: no-move completes but not HDT'] += a['nomove'] and not a['hdt']
                C['matchings: HDT but no-move fails (must be 0 up to caps)'] += a['hdt'] and not a['nomove']
                if a['wanted']: viol.append(name)
    for k in sorted(C): print('%-60s %d' % (k, C[k]))
    if viol: print('  wanted pool good at:', viol[:5])
    print('time %.0f s' % (time.time() - t0))
