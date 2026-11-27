#!/usr/bin/env python3
"""Referee check of kgen-rounds' splice sketch (kgen/rounds.md §4.10 at f91c6bc8, proof/kgen-rounds): REC-S's two
moves (E(k) with T, then Theorem S's chain P2 in I-) are one round of ROUND-P (RNDPZ), except when an end of the
composite structure holds a released pick it needs. Own code; nothing from kgen/ or k4/oc1max_multi/ is run.

Round witness test (written from rounds.md §1 Lemma RC and §4.9's RNDPZ / RNDOZ): given the start Y and a complete
EFX0 allocation X, choose which movers (loc(a) != a) are passers (successor s(a) = loc(a)); the others are ends and
must have a predecessor; s injective and acyclic. Base of b: its predecessor's pick (if any), plus the relevant junk of
Y in X_b, plus released end picks in X_b that b may take: RND1Z: a start (passer, no predecessor) only its own chain's
end pick (a ring); RNDOZ: any non-end agent (passer) its own chain's end pick; RNDPZ: any non-end agent any end pick.
Untouched agents keep {y_b}; a non-mover may add relevant junk (t = 0). Every chain agent strictly gains; at most one
agent holds two or more goods outside its base.
Per REC-S configuration (k, T, Theorem S case): is the final allocation X a witness (RND1Z / RNDOZ / RNDPZ)? Does u0
(P2's start) keep its own pick while holding a foreign pick (the "keep-and-add" shape)? Which case: A (u0 = z, the
head of E(k)) or B (u0 = x_{j-1}, P2's head = x_j)?
"""
import itertools, json, gzip, sys, random
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, efx0, rel, sd, mk, apply_move
from multi_ref import frozen_set
from rec_s_ref import earliest_wanter_chain, reduce_inst, theorem_s_cases

def round_witness(v, Y, X, mode):
    n = len(Y); m = len(v[0]); J = set(range(m)) - set(Y)
    loc = {a: next(b for b in range(n) if Y[a] in X[b]) for a in range(n)}
    movers = [a for a in range(n) if loc[a] != a]
    R = [rel(v, i) for i in range(n)]
    for mask in range(1 << len(movers)):
        P = {movers[i] for i in range(len(movers)) if mask >> i & 1}
        succ = {a: loc[a] for a in P}
        if len(set(succ.values())) != len(succ):
            continue
        pred = {b: a for a, b in succ.items()}
        if any(a not in pred for a in movers if a not in P):
            continue
        # acyclic
        ok = True
        for a in P:
            seen = set(); x = a
            while x in succ:
                if x in seen:
                    ok = False; break
                seen.add(x); x = succ[x]
            if not ok:
                break
        if not ok:
            continue
        ends = [a for a in movers if a not in P]
        endpicks = {Y[e]: e for e in ends}
        def chain_end(a):
            x = a
            while x in succ:
                x = succ[x]
            return x
        def chain_start(a):
            x = a
            while x in pred:
                x = pred[x]
            return x
        base = []; extra = 0; good = True
        for b in range(n):
            Xb = X[b]
            if b in pred or b in P:                      # a chain agent
                bb = {Y[pred[b]]} if b in pred else set()
                bb |= (Xb & J & R[b])
                for g in Xb & set(endpicks):
                    if g in bb or v[b][g] == 0:
                        continue
                    e = endpicks[g]
                    if b not in P:
                        continue                         # an end may not take end picks
                    if mode == "RNDPZ" or (mode in ("RNDOZ",) and chain_end(b) == e) or \
                       (mode == "RND1Z" and b not in pred and chain_end(b) == e):
                        bb.add(g)
                if not val(v, b, bb) > v[b][Y[b]]:
                    good = False; break
            else:                                        # untouched or t = 0 adder
                bb = {Y[b]} | (Xb & J & R[b])
            if not bb <= Xb:
                good = False; break
            base.append(bb); extra += len(Xb - bb) >= 2
        if good and extra <= 1:
            return True
    return False

def recs_configs(v, Y, orders):
    """every REC-S configuration (sigma, k, T, Theorem S case with (K)) and its final allocation."""
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
                T = set(T)
                if not val(v, k, T) > p[k]:
                    continue
                agents, goods, vm, Ym, B1 = reduce_inst(v, list(Y), E, T)
                if [sd(vm, [agents.index(a) for a in sigma if a != k])[i] for i in range(len(agents))] != list(Ym):
                    continue
                for kq, sq, h, H0, r, Am in theorem_s_cases(vm, Ym):
                    X = [set() for _ in range(n)]
                    for i, a in enumerate(agents):
                        X[a] = {goods[g] for g in Am[i]}
                    X[k] = set(T)
                    if not efx0(v, X):
                        continue
                    P2 = [agents[a] for a in sq]
                    yield sigma, k, E, T, P2, {goods[g] for g in H0}, X

def analyse(args):
    v, Y, orders = args
    c = Counter(); ex = []
    for sigma, k, E, T, P2, H0, X in recs_configs(v, Y, orders):
        c["configs"] += 1
        u0 = P2[0]; z = E[-1]
        keep = Y[u0] in X[u0]
        foreign = [a for a in range(len(Y)) if a != u0 and Y[a] in X[u0]]
        shape = keep and bool(foreign)
        case = ("A" if u0 == z else ("B" if u0 in E and E.index(u0) + 1 < len(E) and P2[-1] == E[E.index(u0) + 1] else "other")) if shape else None
        res = {mode: round_witness(v, Y, X, mode) for mode in ("RND1Z", "RNDOZ", "RNDPZ")}
        for mode, r in res.items():
            c[f"X_is_{mode}_witness"] += r
        c["keep_and_add_shape"] += shape
        if shape:
            c["keep_and_add_case_" + case] += 1
            c["keep_and_add_and_RNDPZ_witness"] += res["RNDPZ"]
        if not res["RNDPZ"]:
            c["X_NOT_RNDPZ_witness"] += 1
            # classification: k's own pick released by P2's head (x_1) and not received back by anyone as a pick,
            # while k holds no received pick (Y_z not in T): k is a mover with no predecessor that cannot pass
            n_ = len(Y)
            kpick_holder = next(b for b in range(n_) if Y[k] in X[b])
            released_k = (P2[-1] == E[1]) and (Y[k] not in H0)
            c["notwit_P2_head_is_x1"] += (P2[-1] == E[1])
            c["notwit_Yk_released_by_P2_and_not_in_H0"] += released_k
            c["notwit_Yz_in_T"] += (Y[E[-1]] in T)
            c["notwit_Yk_ends_in_completion_at_agent_keeping_own_pick"] += (released_k and Y[kpick_holder] in X[kpick_holder])
            # does ROUND-P (RNDPZ) hold at this start through some other EFX0 allocation? and OC1-style one chain?
            m_ = len(v[0]); anyw = False
            for f in itertools.product(range(n_), repeat=m_):
                A = [set() for _ in range(n_)]
                for g, a in enumerate(f):
                    A[a].add(g)
                if efx0(v, A) and round_witness(v, Y, A, "RNDPZ"):
                    anyw = True; break
            c["notwit_start_still_has_some_RNDPZ_witness"] += anyw
            if len(ex) < 3:
                ex.append(dict(v=v, picks=list(Y), order=list(sigma), k=k, E=E, T=sorted(T), P2=P2, H0=sorted(H0),
                               X=[sorted(x) for x in X], keep_and_add=shape, case=case))
    return c, ex

def load_export(path):
    d = json.load(gzip.open(path))
    for H in d["hypergraphs"]:
        for s in H["starts"]:
            v = mk(H["sets"], s["vals"]); Y = s["picks"]
            yield v, Y, [o for o in itertools.permutations(range(len(Y))) if sd(v, list(o)) == list(Y)]

def rand_starts(N, seed):
    rng = random.Random(seed)
    for _ in range(N):
        n = rng.randint(3, 5); m = rng.randint(n + 2, n + 4)
        v = [[0] * m for _ in range(n)]
        for i in range(n):
            for g, x in zip(rng.sample(range(m), rng.choice([3, 4, 4])), rng.sample(range(1, 40), 4)):
                v[i][g] = x
        o = list(range(n)); rng.shuffle(o)
        Y = sd(v, o)
        if None in Y:
            continue
        yield v, Y, [o]

def main(kind, a, b, procs):
    it = load_export(a) if kind == "export" else rand_starts(int(a), int(b))
    c = Counter(); exs = []
    with Pool(procs) as pool:
        for cc, ee in pool.imap_unordered(analyse, it, chunksize=50):
            c.update(cc); c["starts"] += 1; c["starts_with_configs"] += cc["configs"] > 0
            if ee and len(exs) < 3:
                exs += ee
    print(json.dumps(dict(source=f"splice check on {kind} {a} {b}", **dict(sorted(c.items())))))
    for e in exs[:3]:
        print("EXAMPLE", json.dumps(e))

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else "0", int(sys.argv[4]) if len(sys.argv) > 4 else 4)
