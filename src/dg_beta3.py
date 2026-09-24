"""Lemma 7 of proofs/beta3.md (every beta = 3 core has a Q-plan for every ranking of its Q-agents), the finite part.
By Lemma 8 (shortening) it suffices to find a Q-plan for every *reduced* beta = 3 core (every thread of H carries at
most one P-agent, a thread from a good back to itself at most two) and every ranking profile of its Q-agents, and by
Lemma 9 reduced beta = 3 cores have at most 10 agents. This script enumerates all connected cores with m = 2n - 2 for
the given n (nauty genbg), marks the reduced ones, and stores a Q-plan (beta3.find_plan) for each reduced core and
each of the 6^q profiles of its Q-agents. The file lists every core (reduced or not) so that tools/check_enum.py can
certify that the list is complete; tools/check_qplans.py re-checks reducedness and every plan independently.
Usage: dg_beta3.py n [n ...] [--out=qplans_beta3.json.gz] [--jobs=N]
       dg_beta3.py n [n ...] --hand    checks the Q-plans written down in the hand proof of Lemma 6 (q = 1, 2) on
                                       every beta = 3 core with q in {1, 2}, with beta3.check_plan and
                                       tools/check_qplans.check_plan"""
import sys, os, json, gzip, time, itertools, collections, multiprocessing
from frontier import PERMS, options
from cores_nauty import gen_cores_nauty
import beta3
import networkx as nx


def threads(sets, priv):
    """Threads of H = G minus private goods: maximal paths whose interior vertices have H-degree 2, between vertices
    of H-degree >= 3. Returns a list of (first, last, number of agents in the interior)."""
    H = nx.MultiGraph()
    for i, S in enumerate(sets):
        for g in S:
            if g != priv[i]: H.add_edge(('a', i), ('g', g))
    branch = {v for v in H if H.degree(v) >= 3}
    done, out = set(), []
    for b in branch:
        for _, nb, k in H.edges(b, keys=True):
            if (b, nb, k) in done: continue
            prev, cur, key, agents = b, nb, k, 0
            done.add((b, nb, k)); done.add((nb, b, k))
            while cur not in branch:
                agents += cur[0] == 'a'
                (nxt, nkey), = [(x, kk) for _, x, kk in H.edges(cur, keys=True) if not (x == prev and kk == key)]
                prev, cur, key = cur, nxt, nkey
                done.add((prev, cur, key)); done.add((cur, prev, key))
            out.append((b, cur, agents))
    return out


def is_reduced(sets, priv):
    return all(k <= (2 if (x == y and x[0] == 'g') else 1) for x, y, k in threads(sets, priv))


def hand_plan(core, qrank):
    """The Q-plan of the proof of Lemma 6 (q = 1 or 2), step by step."""
    Q, comp = core.Q, core.comp
    if len(Q) == 1:
        z, = Q; a, b, c = qrank[z]; Y = {z: (a,)}
        needy = [k for k, e in enumerate(beta3.plan_eps(core, Y, ())) if e == -1]
        return Y, ((b,) if needy else ()), None               # the needy component contains b_z and c_z
    u, v = Q
    if qrank[u][0] != qrank[v][0]: Y = {u: (qrank[u][0],), v: (qrank[v][0],)}          # two a-pins
    else: Y = {u: (qrank[u][0],), v: (qrank[v][1],)}                                    # a-pin and b-pin
    needy = [k for k, e in enumerate(beta3.plan_eps(core, Y, ())) if e == -1]
    if len(needy) <= 1: return Y, tuple(core.comps[k][0] for k in needy), None
    beta3.claim(len(needy) == 2 and qrank[u][0] != qrank[v][0], "Lemma 6: two needy components")
    bu, cu = qrank[u][1], qrank[u][2]
    if comp[bu] != comp[cu]: return {u: (bu, cu), v: (qrank[v][0],)}, (), None         # u holds b_u, c_u
    return Y, (bu, qrank[v][1]), None                         # b_u, c_u in one thread, b_v, c_v in the other


def hand_check(task):
    n, m, pi, sets = task
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
    import check_qplans
    core = beta3.Core(n, m, sets)
    bad = 0
    for qp in itertools.product(range(6), repeat=len(core.Q)):
        qrank = {z: tuple(sets[z][k] for k in PERMS[p]) for z, p in zip(core.Q, qp)}
        Y, Z, T = hand_plan(core, qrank)
        e1 = beta3.check_plan(core, qrank, (Y, Z, T))
        e2 = check_qplans.check_plan(n, m, sets, core.Q, qrank, [[list(Y[z]) for z in core.Q], list(Z), T])
        if e1 or e2: bad += 1; print("HAND PLAN FAILS:", sets, qp, (Y, Z, T), e1, e2, flush=True)
    return 6 ** len(core.Q), bad


def plans_for(task):
    n, m, pi, sets = task
    core = beta3.Core(n, m, sets)
    reduced = is_reduced(core.sets, core.priv)
    rec = {'n': n, 'm': m, 'pi': pi, 'sets': sets, 'reduced': reduced}
    if not reduced: return rec, 0
    plans = []
    for qp in itertools.product(range(6), repeat=len(core.Q)):
        qrank = {z: tuple(sets[z][k] for k in PERMS[p]) for z, p in zip(core.Q, qp)}
        plan = beta3.find_plan(core, qrank)
        if plan is None: return dict(rec, missing=list(qp)), 1
        Y, Z, T = plan
        plans.append([[list(Y[z]) for z in core.Q], list(Z), list(T) if T is not None else None])
    rec['Q'] = core.Q
    rec['plans'] = plans                                     # in the order of itertools.product(range(6), repeat=q)
    return rec, 0


if __name__ == '__main__':
    levels, opts = options(sys.argv[1:])
    jobs = int(opts.get('jobs', os.cpu_count()))
    out = opts.get('out', 'qplans_beta3.json.gz')
    t0 = time.time(); log = lambda s: print(f"[{time.time()-t0:6.0f}s] {s}", flush=True)
    if 'hand' in opts:
        fails = 0
        with multiprocessing.Pool(jobs) as pool:
            for n in levels:
                m = 2 * n - 2
                tasks = [(n, m, pi, s) for pi, s in gen_cores_nauty(n, m) if n - pi in (1, 2)]
                res = pool.map(hand_check, tasks, chunksize=8)
                fails += sum(b for _, b in res)
                byq = collections.Counter(n - t[2] for t in tasks)
                log(f"n={n} m={m}: {dict(sorted(byq.items()))} cores with q = 1, 2; {sum(c for c, _ in res)} Q-profiles; "
                    f"hand plans failing: {sum(b for _, b in res)}")
        log(f"ALL DONE; failing: {fails}"); sys.exit(1 if fails else 0)
    recs, missing = [], 0
    with multiprocessing.Pool(jobs) as pool:
        for n in levels:
            m = 2 * n - 2
            cores = gen_cores_nauty(n, m)
            byq, nplans = collections.Counter(), 0
            for rec, miss in pool.imap(plans_for, [(n, m, pi, s) for pi, s in cores], chunksize=8):
                recs.append(rec); missing += miss
                if rec['reduced']: byq[n - rec['pi']] += 1; nplans += len(rec.get('plans', []))
                if miss: log(f"  NO Q-PLAN: {rec['sets']} Q-profile {rec['missing']}")
            log(f"n={n} m={m}: {len(cores)} connected cores, reduced by q {dict(sorted(byq.items()))}, "
                f"{nplans} Q-plans; missing so far {missing}")
    with gzip.open(out, 'wt') as f: json.dump(recs, f)
    log(f"wrote {out}; missing Q-plans: {missing}"); sys.exit(1 if missing else 0)
