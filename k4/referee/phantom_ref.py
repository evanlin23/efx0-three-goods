#!/usr/bin/env python3
"""Referee probe of the phantom class (k4/oc1max_multi.md §14 at 6b6cf7b): after settling k (E(k), pool pair T, k a
phantom with threshold tau_k = v_k(T)), does a second settlement E(k') in I- (order sigma - k, k' in D-, improving pool
pair T') release into the junk of I-- a pick l that the phantom k values above tau_k? That happens when the head of
E(k') holds l and T' does not contain l (if T' contains l, T' threatens the phantom, which the class forbids). Then the
phantom "wants" a junk good of I--, which (G2) for phantoms excludes and which Theorem S's step 3 and Lemma M^c use.
Own code (rec_s_ref helpers); data read as data."""
import itertools, json, gzip, sys
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, sd, rel, mk
from multi_ref import frozen_set
from rec_s_ref import earliest_wanter_chain, reduce_inst
from oc1hall_ref import threatened

def probe(args):
    v, Y, orders = args
    c = Counter(); ex = None
    n = len(Y); m = len(v[0]); B = [{y} for y in Y]; J = set(range(m)) - set(Y)
    p = [v[i][Y[i]] for i in range(n)]
    F = frozen_set(v, B); D = {d for d in F if any(v[d][g] > 0 for g in J)}
    for sigma in orders:
        for k in sorted(D):
            E = earliest_wanter_chain(v, list(Y), list(sigma), k)
            if E is None or E == "CYCLE":
                continue
            pool = J | {Y[E[-1]]}
            for T in itertools.combinations(sorted(pool & rel(v, k)), 2):
                T = set(T); tau = val(v, k, T)
                if not tau > p[k]:
                    continue
                agents, goods, vm, Ym, B1 = reduce_inst(v, list(Y), E, T)
                wanted = {g for g in range(m) if g not in T and v[k][g] > tau}
                if not wanted:
                    continue
                sig = [agents.index(a) for a in sigma if a != k]
                nm = len(agents); Bm = [{y} for y in Ym]; Jm = set(range(len(goods))) - set(Ym)
                pm = [vm[i][Ym[i]] for i in range(nm)]
                Fm = frozen_set(vm, Bm); Dm = {d for d in Fm if any(vm[d][g] > 0 for g in Jm)}
                for k2 in sorted(Dm):
                    E2 = earliest_wanter_chain(vm, list(Ym), sig, k2)
                    if E2 is None or E2 == "CYCLE":
                        continue
                    z2 = E2[-1]; l = goods[Ym[z2]]
                    pool2 = Jm | {Ym[z2]}
                    for T2 in itertools.combinations(sorted(pool2 & rel(vm, k2)), 2):
                        if not val(vm, k2, T2) > pm[k2]:
                            continue
                        c["second_settlements"] += 1
                        if l in wanted:
                            T2I = {goods[g] for g in T2}
                            if l in T2I:
                                c["head_holds_phantom_wanted_pick__T2_contains_it (pair threatens phantom)"] += 1
                            else:
                                pair_ok = not threatened(v, k, T2I, tau)
                                c["head_holds_phantom_wanted_pick__released_into_junk" + ("" if pair_ok else "_and_pair_threatens")] += 1
                                if pair_ok and ex is None:
                                    ex = dict(v=v, picks=list(Y), order=list(sigma), k=k, E=E, T=sorted(T), tau=tau,
                                              k2=agents[k2], E2=[agents[a] for a in E2], T2=sorted(T2I), released=l, v_k_l=v[k][l])
    return c, ex

def main(kind, path, procs):
    if kind == "export":
        d = json.load(gzip.open(path))
        it = ((mk(H["sets"], s["vals"]), s["picks"], [o for o in itertools.permutations(range(len(s["picks"]))) if sd(mk(H["sets"], s["vals"]), list(o)) == list(s["picks"])])
              for H in d["hypergraphs"] for s in H["starts"])
    else:
        def gen():
            f = gzip.open(path, "rt") if path.endswith(".gz") else open(path)
            for line in f:
                dd = json.loads(line); n = len(dd["sets"]); m = 1 + max(g for s in dd["sets"] for g in s)
                v = [[0] * m for _ in range(n)]
                for i in range(n):
                    for g, x in zip(dd["sets"][i], dd["vals"][i]):
                        v[i][g] = x
                Y = sd(v, dd["order"])
                yield v, Y, [o for o in itertools.permutations(range(n)) if sd(v, list(o)) == list(Y)]
        it = gen()
    c = Counter(); exs = []
    with Pool(procs) as pool:
        for cc, ee in pool.imap_unordered(probe, it, chunksize=50):
            c.update(cc); c["starts"] += 1
            if ee and len(exs) < 2:
                exs.append(ee)
    print(json.dumps(dict(source=f"phantom-class probe on {path.rsplit('/', 1)[-1]}", **dict(sorted(c.items())))))
    for e in exs:
        print("EXAMPLE", json.dumps(e))

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], int(sys.argv[3]))
