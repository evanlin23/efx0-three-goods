"""The pick-graph route to ROUND-P^max (kgen/rounds.md §4.11).  For an allocation X, the pick graph sends each agent a
to the holder f(a) of its pick Y_a; in-degree = number of picks held.  Each component of a functional graph is one cycle
with in-trees.  Shapes of a component:
  fixed    a single agent keeping its pick (a self-loop), no in-tree;
  ring     a cycle of length >= 2, no in-tree (the two-cycle mechanism: several rings form one round);
  rho      a cycle (length >= 2) with ONE in-tree that is a path, merging at a vertex v that lost its pick: v holds two
           foreign picks (the starved agent of Lemma R1); realised as ONE OC1' chain, v taking the end's pick;
  rho-fix  a fixed point with one path in-tree of length >= 2 (the tail's last agent's pick lies outside at the keeper);
  ka       a fixed point with a one-edge in-tree from a pickless agent (keep-and-add, §4.9);
  complex  anything else (an in-tree that branches, or several in-trees).
SIMPLE: every component is fixed, ring, rho or rho-fix.  For every start, every MD EFX0 allocation (rnd.c list_efx) is
classified and tested as a witness of a round of OC1' moves (recs_vs_rndp.structures).  Reported per start: whether
some witness is SIMPLE, and which shapes the SIMPLE witnesses use.
    python3 kgen/rounds/rndp_structure.py KIND FILE [STRIDE] [JOBS]      KIND as in splice_search.py"""
import sys, os, json, collections, time, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rndlib, recs_vs_rndp as RV
from splice_search import rows_of, dense


def shapes(f, n):
    indeg = [0] * n
    for a in range(n): indeg[f[a]] += 1
    seen = [False] * n; comps = []
    # components: weakly connected
    adj = [[] for _ in range(n)]
    for a in range(n): adj[a].append(f[a]); adj[f[a]].append(a)
    for s in range(n):
        if seen[s]: continue
        st = [s]; seen[s] = True; C = []
        while st:
            a = st.pop(); C.append(a)
            for b in adj[a]:
                if not seen[b]: seen[b] = True; st.append(b)
        # its cycle
        a = C[0]
        for _ in range(n): a = f[a]
        cyc = [a]; b = f[a]
        while b != a: cyc.append(b); b = f[b]
        tree = [a for a in C if a not in cyc]
        if not tree: comps.append('fixed' if len(cyc) == 1 else 'ring'); continue
        leaves = [a for a in tree if indeg[a] == 0]
        merges = [a for a in C if indeg[a] >= 2]
        if len(leaves) == 1 and len(merges) == 1 and indeg[merges[0]] == 2:
            if len(cyc) >= 2: comps.append('rho')
            else: comps.append('rho-fix' if len(tree) >= 2 else 'ka')
        else: comps.append('complex')
    return comps


def outside_one_absorber(V, y, X, f):
    """Theorem ROUND-SIMPLE's outside goods: worthless junk; an unvalued end pick at a ring start / rho merge point
    (here: any second pick an agent holds that it does not value, or any pick held by a keeper besides its own);
    True iff at most one agent has two or more"""
    n = len(V); picks = set(y); big = 0
    for b in range(n):
        out = sum(1 for g in X[b] if g not in picks and V[b][g] == 0)
        held = [a for a in range(n) if f[a] == b and a != b]
        if f[b] == b: out += len(held)                       # a keeper: every foreign pick is outside
        elif len(held) >= 2: out += sum(1 for a in held if V[b][y[a]] == 0) - (1 if all(V[b][y[a]] == 0 for a in held) else 0)
        if out >= 2: big += 1
    return big <= 1


def job(row):
    V = dense(row['sets'], row['vals']); n, m = len(V), len(V[0]); y = tuple(row['picks'])
    alls, _ = rndlib.list_efx(V)
    out = collections.Counter(); simple_shapes = collections.Counter(); any_w = False; any_simple = False
    for o in alls:
        X = [[g for g in range(m) if o[g] == i] for i in range(n)]
        if any(sum(V[a][g] for g in X[a]) < V[a][y[a]] for a in range(n)): continue
        f = [o[y[a]] for a in range(n)]
        sh = shapes(f, n); simple = all(s in ('fixed', 'ring', 'rho', 'rho-fix') for s in sh)
        w = bool(RV.structures(V, y, X, False))
        out[('MD', 'simple' if simple else 'not simple', 'witness' if w else 'not a witness')] += 1
        if simple:
            oa = outside_one_absorber(V, y, X, f)
            out[('simple MD', 'one absorber' if oa else 'two absorbers', 'witness' if w else 'NOT a witness')] += 1
        if w: any_w = True
        if w and simple:
            any_simple = True; simple_shapes[tuple(sorted(set(s for s in sh if s != 'fixed')) or ['keep'])] += 1
    return row, out, any_w, any_simple, simple_shapes


if __name__ == '__main__':
    kind, fn = sys.argv[1], sys.argv[2]; STRIDE = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    JOBS = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    print('$ python3 kgen/rounds/rndp_structure.py', *sys.argv[1:], flush=True)
    rows = rows_of(kind, fn, STRIDE); C = collections.Counter(); t0 = time.time()
    with mp.Pool(JOBS) as pool:
        for t, (row, out, any_w, any_simple, ss) in enumerate(pool.imap_unordered(job, rows, chunksize=16)):
            C['starts'] += 1
            C['starts with an RNDOZ witness' if any_w else 'STARTS WITHOUT AN RNDOZ WITNESS'] += 1
            C['starts with a SIMPLE RNDOZ witness' if any_simple else 'STARTS WITHOUT A SIMPLE WITNESS'] += 1
            for k, v in out.items(): C[k] += v
            # the simplest shape set used by some simple witness at this start
            if ss:
                best = min(ss, key=lambda t: (len(t), t)); C[('simplest witness shape', best)] += 1
            if not any_simple and C['STARTS WITHOUT A SIMPLE WITNESS'] <= 5:
                print('NO SIMPLE WITNESS', json.dumps({k: row[k] for k in ('list', 'idx', 'sets', 'vals', 'picks')}), flush=True)
            if (t + 1) % 20000 == 0: print('...', t + 1, '%.0fs' % (time.time() - t0), flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
