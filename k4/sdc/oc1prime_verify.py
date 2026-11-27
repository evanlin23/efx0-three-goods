"""Coordinator's independent check of OC1' (kgen/rounds.md §4.6) at every n = 4 start where OC1^max fails.
OC1': one official move (addition, chain, ring; k4/sdc.md §29, chains never hand on an empty base), except that every
non-end agent of a chain may also take goods of the end's released base that it values; every chain agent still
strictly gains.  OC1' holds at a start if the picks or some such move's state has a one-absorber completion.
Own code: Inst.one_absorber / efx0 / sd from oc1_mc2_rand.py (raw EFX0, no SAT); the widened chain generator is new
and written from the definition above, not from kgen/rounds' rnd.c or verify_k4zero.
Input: the certifier's export (k4/oc1cert/export_fails.py, results/k4_oc1max/two_move_starts_n4.json.gz on
compute/k4-oc1max-cert; the copy results/kgen_rounds/certifier_two_move_starts_n4.json.gz on proof/kgen-rounds).
For each start: the picks are an SD outcome of each listed order, they form a maximum matching, OC1 fails (no
completion at the picks or after a plain move: checked on a STRIDE sample, it is the certifier's claim), and OC1'
holds (checked on every start; the witness move is printed for the first few).
    python3 k4/sdc/oc1prime_verify.py FILE.json.gz [OC1_STRIDE]"""
import sys, os, gzip, json, itertools, collections, time, multiprocessing as mp
import _paths  # noqa: F401
from oc1_mc2_rand import Inst
from oc1_max_orders import nu


def sub(xs):
    return itertools.chain.from_iterable(itertools.combinations(xs, r) for r in range(len(xs) + 1))


def prime_states(I, base):
    """Yield the states of OC1' moves: plain additions and rings (as in Inst.moves) and the widened chains."""
    n, R, V = I.n, I.R, I.V
    J = [g for g in range(I.m) if all(g not in b for b in base)]
    for x in range(n):                                     # additions
        for H in sub([g for g in J if g in R[x]]):
            if H:
                nb = [list(b) for b in base]; nb[x] = list(base[x]) + list(H); yield nb
    for t in range(1, n):                                  # chains x0 -> x1 -> ... -> xt, end xt releases base[xt]
        for path in itertools.permutations(range(n), t + 1):
            if any(not base[path[i]] for i in range(t)): continue      # never hand on an empty base
            end = path[-1]; E = list(base[end])
            # each released good of the end: kept by nobody (junk) or taken by a non-end agent that values it
            opts = [[None] + [path[i] for i in range(t) if g in R[path[i]]] for g in E]
            for eas in itertools.product(*opts):
                Eget = collections.defaultdict(list)
                for g, a in zip(E, eas):
                    if a is not None: Eget[a].append(g)
                J2 = J + [g for g, a in zip(E, eas) if a is None]   # unassigned released goods become junk
                # junk H_i for each chain agent (x0 must take a nonempty H0 from junk or released goods)
                def dfs(i, used, assign):
                    if i == t + 1:
                        x0 = path[0]; H0 = list(assign[0]) + Eget[x0]
                        if not H0 or V(x0, H0) <= V(x0, base[x0]): return
                        nb = [list(b) for b in base]; nb[x0] = H0
                        for j in range(1, t + 1):
                            y = path[j]; nb[y] = list(base[path[j - 1]]) + list(assign[j]) + Eget[y]
                        yield nb; return
                    y = path[i]
                    pool = [g for g in J2 if g not in used and g in R[y]] if i > 0 else \
                           [g for g in J2 if g not in used and g in R[y] and g in J]  # x0's released goods come via Eget
                    for H in sub(pool):
                        if i > 0 and V(y, list(base[path[i - 1]]) + list(H) + Eget[y]) <= V(y, base[y]): continue
                        yield from dfs(i + 1, used | set(H), {**assign, i: H})
                # x0's junk is chosen last-independent: choose x1..xt first, then x0 from what is left
                def dfs_order():
                    order_idx = list(range(1, t + 1)) + [0]
                    def rec(k, used, assign):
                        if k == len(order_idx):
                            x0 = path[0]; H0 = list(assign[0]) + Eget[x0]
                            if not H0 or V(x0, H0) <= V(x0, base[x0]): return
                            nb = [list(b) for b in base]; nb[x0] = H0
                            for j in range(1, t + 1):
                                y = path[j]; nb[y] = list(base[path[j - 1]]) + list(assign[j]) + Eget[y]
                            yield nb; return
                        i = order_idx[k]; y = path[i]
                        pool = [g for g in J2 if g not in used and g in R[y]]
                        if i == 0: pool = [g for g in pool if g in J]
                        for H in sub(pool):
                            if i > 0 and V(y, list(base[path[i - 1]]) + list(H) + Eget[y]) <= V(y, base[y]): continue
                            yield from rec(k + 1, used | set(H), {**assign, i: H})
                    yield from rec(0, frozenset(), {})
                yield from dfs_order()
    for r in range(2, n + 1):                              # rings (unchanged)
        for cyc in itertools.permutations(range(n), r):
            if cyc[0] != min(cyc): continue
            def ring(i, used, assign):
                if i == r:
                    nb = [list(b) for b in base]
                    for s in range(r): nb[cyc[s]] = list(base[cyc[s - 1]]) + list(assign[s])
                    yield nb; return
                w, pred = cyc[i], cyc[i - 1]
                if not base[pred]: return
                for H in sub([g for g in J if g not in used and g in R[w]]):
                    if V(w, list(base[pred]) + list(H)) > V(w, base[w]): yield from ring(i + 1, used | set(H), {**assign, i: H})
            yield from ring(0, frozenset(), {})


def job(a):
    sets, st, do_oc1 = a
    I = Inst(sets, st['vals']); p = tuple(st['picks']); out = collections.Counter(); wit = None
    out['SD reproduces picks' if all(I.sd(tuple(o)) == p for o in st['orders']) else 'SD MISMATCH'] += 1
    out['maximum matching' if sum(x is not None for x in p) == nu(I) else 'NOT MAXIMUM'] += 1
    base = [[g] if g is not None else [] for g in p]
    if do_oc1: out['OC1 fails (own check)' if I.check(p) == 'OC1 fails' else 'OC1 HOLDS (disagrees)'] += 1
    if I.one_absorber(base): out['picks complete (unexpected)'] += 1; return out, wit
    for nb in prime_states(I, base):
        if I.one_absorber(nb): out["OC1' holds"] += 1; wit = nb; return out, wit
    out["OC1' FAILS"] += 1
    return out, ('FAIL', sets, st)


if __name__ == '__main__':
    src = sys.argv[1]; STRIDE = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    print('$ python3 k4/sdc/oc1prime_verify.py', *sys.argv[1:], flush=True)
    d = json.load(gzip.open(src)); tasks = []
    for h in d['hypergraphs']:
        for st in h['starts']: tasks.append((h['sets'], st, len(tasks) % STRIDE == 0))
    print('starts', len(tasks), flush=True)
    t0 = time.time(); T = collections.Counter(); shown = 0
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for k, (C, wit) in enumerate(pool.imap(job, tasks, chunksize=64)):
            T.update(C)
            if wit and wit[0] == 'FAIL': print("OC1' FAILURE", json.dumps({'sets': wit[1], 'start': wit[2]}), flush=True)
            elif wit and shown < 5: shown += 1; print('witness', json.dumps({'sets': tasks[k][0], 'vals': tasks[k][1]['vals'], 'picks': tasks[k][1]['picks'], 'state': wit}), flush=True)
            if (k + 1) % 10000 == 0: print('...', k + 1, dict(T), '%.0f s' % (time.time() - t0), flush=True)
    for key in sorted(T): print(key, T[key])
    print('time %.0f s' % (time.time() - t0))
