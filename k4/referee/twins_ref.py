#!/usr/bin/env python3
"""Referee check (concrete instances, brute force) of the K4.MC8 certificates (k4/TWINS.md, branch proof/k4-twins at
29bb2e6; results/k4_twins/dbl_q3.json.gz, dbl_p4q4.json.gz). Own code; the certificate is read as data, and only its
state-key and token encoding (documented in k4/check_reductions4.py's docstring and states()/canonical()) is followed.
Nothing from k4/ is run or imported.

For random concrete instances H containing a double edge of a given configuration (e, f with their goods as in the
record; I = {g0, g1} plus private goods valued by nobody else; random strict balanced values for e, f; 2-3 outside
agents with <= 4 relevant goods on the boundary goods and 2-3 outside goods), and for every record of the configuration
with a fixed gadget (DEL or GAD-h with fixed values):
  * build H' (S, I replaced by the gadget agents and gadget goods), enumerate EVERY EFX0 allocation Y of H' whose envy
    graph is acyclic, and every unenvied bundle z of Y (records with 'source'); compute the local state in the
    certificate's canonical form and look it up;
  * realize every stored extension of that state as a concrete allocation X of H (tokens: goods; 'w:h' = all outside
    goods h held; 'W:i' = the outside goods of block i), and check raw EFX0 on H:
      DOMINATION: whenever e and f are safe in X, every outside agent must be safe too (Lemma M1 / M1(b));
      COVERAGE: the record "works" for H if every (Y, z) has an extension with X EFX0. For an excluded configuration
      (every profile reduced, per K4.MC8), some record must work for every H.
"""
import itertools, random, sys, json, gzip
from collections import Counter

def safe(v, own, others):
    mine = sum(v.get(g, 0) for g in own)
    for B in others:
        tot = sum(v.get(g, 0) for g in B)
        if any(tot - v.get(g, 0) > mine for g in B):
            return False
    return True

def efx0(vals, X):
    """vals: dict agent -> dict good -> value; X: dict agent -> set."""
    for i in X:
        if not safe(vals[i], X[i], [X[j] for j in X if j != i and X[j]]):
            return False
    return True

def strict_balanced(rng, goods, lo=1, hi=40):
    while True:
        xs = rng.sample(range(lo, hi), len(goods))
        if 2 * max(xs) >= sum(xs):
            continue
        sums = {}
        ok = True
        idx = range(len(goods))
        for r in range(1, len(goods) + 1):
            for A in itertools.combinations(idx, r):
                sums[A] = sum(xs[a] for a in A)
        for A, a in sums.items():
            for B, b in sums.items():
                if A < B and a == b and not set(A) & set(B):
                    ok = False
        if ok:
            return dict(zip(goods, xs))

def envy_acyclic_unenvied(vals, Y):
    ag = list(Y)
    env = {i: [j for j in ag if j != i and sum(vals[i].get(g, 0) for g in Y[j]) > sum(vals[i].get(g, 0) for g in Y[i])] for i in ag}
    # cycle check
    color = {}
    def dfs(u):
        color[u] = 1
        for w in env[u]:
            if color.get(w) == 1 or (w not in color and dfs(w)):
                return True
        color[u] = 2
        return False
    if any(u not in color and dfs(u) for u in ag):
        return None
    return [z for z in ag if not any(z in env[i] for i in ag)]

def canonical_key(Yb, Ob, src):
    order = sorted(range(len(Ob)), key=lambda k: sorted(Ob[k]))
    pos = {k: i for i, k in enumerate(order)}
    blocks = [sorted(('W:%d' % i) if x == 'W' else x for x in Ob[k]) for i, k in enumerate(order)]
    sd = None if src is None else (['sp', src[1]] if src[0] == 'sp' else ['O', pos[src[1]]])
    return json.dumps([[sorted(Yb[s]) for s in sorted(Yb)], blocks, sd]), order

def run_record(rec, H, rng, c, ex):
    """H: dict with 'vals' (agent -> {good: value}), 'goods', 'outside_agents', 'outside_goods'. Returns works?"""
    S = rec["S"]; I = set(rec["I"]); D = set(rec["D"]); Ip = set(rec["Ip"])
    sps = sorted(rec["Sp"])
    vals = H["vals"]; OA = H["outside_agents"]; OG = H["outside_goods"]
    # H' agents and goods
    valsp = {j: vals[j] for j in OA}
    for s in sps:
        valsp[s] = {g: x for g, x in rec["Sp"][s]["fix"].items() if x > 0}
    goods_p = sorted(D | Ip | set(OG))
    agents_p = OA + sps
    L = sorted(D | Ip)
    states = {k: exts for k, exts in rec["states"]}
    works = True
    nY = 0
    for f in itertools.product(range(len(agents_p)), repeat=len(goods_p)):
        Y = {a: {g for g, x in zip(goods_p, f) if agents_p[x] == a} for a in agents_p}
        if not efx0(valsp, Y):
            continue
        un = envy_acyclic_unenvied(valsp, Y)
        if un is None:
            continue
        nY += 1
        Yb = {s: sorted(Y[s] & set(L)) + (['w:' + s] if Y[s] - set(L) else []) for s in sps}
        meet = [j for j in OA if Y[j] & set(L)]
        Ob0 = [sorted(Y[j] & set(L)) + (['W'] if Y[j] - set(L) else []) for j in meet]
        srcs = [None] if not rec["source"] else [None]
        if rec["source"]:
            srcs = []
            for z in un:
                if z in sps:
                    srcs.append((('sp', z), None))
                elif z in meet:
                    srcs.append((('O', meet.index(z)), None))
                else:
                    srcs.append((('O', len(meet)), z))   # an outside bundle not meeting L'
        else:
            srcs = [(None, None)]
        for src, extra in srcs:
            Ob = [list(b) for b in Ob0]; blk_agents = list(meet)
            if extra is not None:
                Ob.append(['W'] if Y[extra] else []); blk_agents.append(extra)
            key, order = canonical_key(Yb, Ob, src)
            c["states_seen"] += 1
            if key not in states:
                c["state_missing"] += 1
                works = False
                if len(ex) < 6:
                    ex.append(("missing", rec["config"], rec["name"], key))
                continue
            cblock_agent = [blk_agents[k] for k in order]
            any_ok = False
            for ext in states[key]:
                X = {}
                outside_goods_of = {('w:' + s): Y[s] - set(L) for s in sps}
                for i, j in enumerate(cblock_agent):
                    outside_goods_of['W:%d' % i] = Y[j] - set(L)
                def realize(tokens):
                    out = set()
                    for t in tokens:
                        if t in outside_goods_of:
                            out |= outside_goods_of[t]
                        else:
                            out.add(t)
                    return out
                for s, toks in ext["S"].items():
                    X[s] = realize(toks)
                for i, toks in enumerate(ext["O"]):
                    X[cblock_agent[i]] = realize(toks)
                if MUT == "interior" and cblock_agent:
                    # move an interior good from an agent of S into the first outside block that holds a boundary good
                    tgt = next((cblock_agent[i] for i, toks in enumerate(ext["O"]) if any(t in D for t in toks)), None)
                    src = next((s for s in S if X[s] & I), None)
                    if tgt is not None and src is not None:
                        g = sorted(X[src] & I)[0]; X[src].discard(g); X[tgt].add(g)
                for j in OA:
                    if j not in X:
                        X[j] = set(Y[j])
                allg = set().union(*X.values())
                if allg != set(H["goods"]) or sum(len(b) for b in X.values()) != len(H["goods"]):
                    c["ext_not_partition"] += 1
                    if len(ex) < 6:
                        ex.append(("partition", rec["config"], rec["name"], key, ext))
                    continue
                c["extensions_checked"] += 1
                sS = all(safe(vals[s], X[s], [X[j] for j in X if j != s and X[j]]) for s in S)
                full = efx0(vals, X)
                if sS:
                    c["ext_S_safe"] += 1
                    if not full:
                        c["DOMINATION_FAIL"] += 1
                        if len(ex) < 6:
                            ex.append(("domination", rec["config"], rec["name"], key, ext, {k: sorted(v) for k, v in X.items()}))
                if full:
                    any_ok = True
            if not any_ok:
                works = False
    c["Y_enumerated"] += nY
    return works

def make_instance(rec, rng):
    S = rec["S"]; I = set(rec["I"]); D = sorted(rec["D"])
    vals = {}
    for s in S:
        vals[s] = strict_balanced(rng, S[s])
    OG = ["o%d" % i for i in range(rng.randint(2, 3))]
    OA = ["j%d" % i for i in range(rng.randint(2, 3))]
    pool = D + OG
    for j in OA:
        gs = rng.sample(pool, rng.randint(2, min(4, len(pool))))
        vals[j] = {g: rng.randint(1, 30) for g in gs}
    goods = sorted(set().union(*[set(S[s]) for s in S]) | set(OG))
    return dict(vals=vals, goods=goods, outside_agents=OA, outside_goods=OG)

MUT = None
EXCLUDED = {"dbl-Q3-Q3", "dbl-Q3-Q3-c1", "dbl-Q3-P4", "dbl-Q3-P4-c1", "dbl-P4-P4", "dbl-P4-P4-c1", "dbl-Q3-Q4-c1",
            "dbl-P4-Q4-c1"}

def main(files, N, seed, configs=None):
    rng = random.Random(seed)
    recs = []
    for fn in files:
        recs += json.load(gzip.open(fn))
    bycfg = {}
    for r in recs:
        if all("fix" in r["Sp"][s] for s in r["Sp"]):
            bycfg.setdefault(r["config"], []).append(r)
    c = Counter(); ex = []
    cfgs = sorted(bycfg) if not configs else configs
    for cfg in cfgs:
        if cfg not in bycfg:
            continue
        for _ in range(N):
            rec0 = bycfg[cfg][0]
            H = make_instance(rec0, rng)
            c[cfg + "_instances"] += 1
            w = [run_record(r, H, rng, c, ex) for r in bycfg[cfg]]
            if any(w):
                c[cfg + "_covered"] += 1
            elif cfg not in EXCLUDED:
                c[cfg + "_not_covered"] += 1
            else:
                c[cfg + "_COVERAGE_FAIL"] += 1
                if len(ex) < 6:
                    ex.append(("coverage", cfg, {k: v for k, v in H["vals"].items()}))
    print(json.dumps(dict(source=f"K4.MC8 concrete check N={N} per config seed={seed}", **dict(sorted(c.items())))))
    for e in ex[:6]:
        print("EXAMPLE", json.dumps(e)[:1500])

if __name__ == "__main__":
    files = sys.argv[1].split(",")
    N = int(sys.argv[2]); seed = int(sys.argv[3])
    cfgs = sys.argv[4].split(",") if len(sys.argv) > 4 and sys.argv[4] != "all" else None
    if len(sys.argv) > 5:
        MUT = sys.argv[5]
    main(files, N, seed, cfgs)
