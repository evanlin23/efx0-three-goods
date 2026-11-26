"""Adversarial hill-climbs at any k against SD-C, MD, OC and OC1 (k4/ksens.md), every order (n <= 5 or 6).

Objectives (minimized; first coordinate 0 = counterexample to the target):
  oc1 : over the starts whose picks have no one-absorber completion, the least number of states one improving chain
        reaches that have one (ocsat.OC.count, capped), then minus the number of such hard starts;
  oc  : the same with the free completion;
  round1, round: the same with one round of vertex-disjoint chains (ocsat multi) instead of one chain;
  sdc : the number of distinct serial-dictatorship outcomes that extend (free completion), then minus the number of
        outcomes;
  md  : over every start, the least number of value-dominating complete EFX0 allocations (capped);
  oc1r1, ocr1, ...: any target with the starts restricted to R1-priority orders (r1_pw.sd_r1);
  oc2, oc2a: 3 minus the most chains any start needs (ocseq.py, at most 3 tried; free, one absorber), then minus the
        number of starts needing that many: 0 = a start that two chains cannot repair (the ladder of k4/ksens.md §4
        predicts none for k <= 6).
A start where nothing is hard scores (99, 0).

    python3 k4/ksens/climb.py TARGET SEED n K STEPS ROUNDS [gen:KIND | seeds:FILE[:LIFT]] [mmax:M] [mmin:M]
gen:KIND   random starts from gen.py (default jr)
seeds:FILE JSON lines [sets, vals] (or log lines containing such a pair); LIFT = add that many new low goods per agent
           (the lift of a k = 4 instance to k = 4 + LIFT)
mmax, mmin: bounds on the number of goods kept by mutations (default 3n + 2 and 2n: junk-rich)
strict: never accept a worse objective (default: with probability 0.03)"""
import sys, json, random, time, re, itertools
import _paths
import ocsat
from gen import gen

CAP = 20


def objective(target, sets, vals):
    m = 1 + max(max(s) for s in sets); n = len(sets)
    O = ocsat.OC(sets, vals, m); st = ocsat.starts(sets, vals, m)
    if target.endswith('r1'):          # R1-priority orders only (LB's Phase 1)
        from r1_pw import sd_r1
        st = {}
        for o in itertools.permutations(range(n)): st.setdefault(tuple(sd_r1(sets, vals, o, m)), o)
        target = target[:-2]
    try:
        if target in ('oc1', 'oc', 'round1', 'round'):
            A = 1 if target in ('oc1', 'round1') else None; cnt = {}; multi = target.startswith('round')
            for Y in st:
                b = ocsat.bases_of(Y, n)
                if O.holds(b, chain='none', A=A): continue
                cnt[Y] = O.count(b, chain='need', A=A, cap=CAP, multi=multi)
            if not cnt: return (99, 0), None
            lo = min(cnt.values())
            return (lo, -len(cnt)), min(cnt, key=cnt.get)
        if target in ('oc2', 'oc2a'):
            # the ladder's upper side at k = 5, 6: the most chains any start needs (ocseq, up to 3); maximized
            import ocseq
            A = 1 if target == 'oc2a' else None; Q = ocseq.Seq(sets, vals, m); worst = []
            try:
                for Y in st:
                    b = ocsat.bases_of(Y, n)
                    if O.holds(b, chain='any', A=A): continue
                    worst.append((3 if not Q.holds(b, 2, A) else 2, Y))
            finally:
                Q.close()
            if not worst: return (99, 0), None
            mx = max(c for c, _ in worst)
            return (3 - mx, -sum(1 for c, _ in worst if c == mx), -len(worst)), max(worst)[1]
        if target == 'sdc':
            good = [Y for Y in st if O.holds(ocsat.bases_of(Y, n), chain='none')]
            return (len(good), -len(st)), (good[0] if good else None)
        if target == 'md':
            best = None
            for Y in st:
                act, _ = O.group(ocsat.bases_of(Y, n), chain='none', md=True); c = 0
                xs = [O.E.x[g][i] for g in range(m) for i in range(n)]
                while c < CAP and O.S.solve(assumptions=[act]):
                    mdl = set(l for l in O.S.get_model() if l > 0)
                    O.S.add_clause([-act] + [-l for l in xs if l in mdl]); c += 1
                O.retire(act)
                if best is None or c < best[0]: best = (c, Y)
            return (best[0], 0), best[1]
    finally:
        O.close()
    raise ValueError(target)


def renumber(sets, vals):
    used = sorted(set(g for s in sets for g in s)); ren = {g: k for k, g in enumerate(used)}
    return [[ren[g] for g in s] for s in sets], vals


def mutate(sets, vals, rng, K, mmax):
    sets = [list(s) for s in sets]; vals = [list(v) for v in vals]
    n = len(sets); m = 1 + max(max(s) for s in sets); i = rng.randrange(n); r = rng.random()
    if r < 0.5:
        k = rng.randrange(len(sets[i])); vals[i][k] = max(1, vals[i][k] + rng.choice([-5, -3, -2, -1, 1, 2, 3, 5]))
    elif r < 0.62:
        a, b = rng.sample(range(len(sets[i])), 2); vals[i][a], vals[i][b] = vals[i][b], vals[i][a]
    elif r < 0.77:
        k = rng.randrange(len(sets[i])); g = rng.randrange(min(m + 1, mmax))
        if g in sets[i]: return None
        sets[i][k] = g
    elif r < 0.9:
        if len(sets[i]) >= K or (len(sets[i]) > 2 and rng.random() < 0.4):
            k = rng.randrange(len(sets[i])); sets[i].pop(k); vals[i].pop(k)
        else:
            g = rng.randrange(min(m + 1, mmax))
            if g in sets[i]: return None
            sets[i].append(g); vals[i].append(rng.randint(1, max(vals[i])))
    else:   # copy another agent's good with a nearby value (creates shared tops and shared junk)
        j = rng.randrange(n)
        if j == i: return None
        k = rng.randrange(len(sets[j])); g = sets[j][k]
        if g in sets[i]: return None
        if len(sets[i]) >= K:
            kk = rng.randrange(len(sets[i])); sets[i].pop(kk); vals[i].pop(kk)
        sets[i].append(g); vals[i].append(max(1, vals[j][k] + rng.randint(-3, 3)))
    if len(sets[i]) < 1 or len(set(vals[i])) < len(vals[i]): return None
    return renumber(sets, vals)


def lift(sets, vals, L, rng):
    """add L new goods to each agent, each valued below the agent's lowest good, some shared with another agent"""
    sets = [list(s) for s in sets]; vals = [list(v) for v in vals]; m = 1 + max(max(s) for s in sets)
    scale = 4; vals = [[scale * x for x in v] for v in vals]
    for i in range(len(sets)):
        for _ in range(L):
            if rng.random() < 0.4 and m > 0:
                g = rng.randrange(m)
                if g in sets[i]: g = m; m += 1
            else:
                g = m; m += 1
            lo = min(vals[i]); x = rng.randint(1, max(1, lo - 1))
            while x in vals[i]: x = rng.randint(1, max(2, lo + 3))
            sets[i].append(g); vals[i].append(x)
    return renumber(sets, vals)


def load_seeds(path):
    out = []
    for line in open(path, errors='ignore'):
        for mt in re.finditer(r'(\[\[\[[0-9, \[\]]+\]\], \[\[[0-9, \[\]]+\]\]\])', line):
            try: sets, vals = json.loads(mt.group(1))
            except Exception: continue
            if all(len(a) == len(b) for a, b in zip(sets, vals)): out.append((sets, vals))
    return out


if __name__ == '__main__':
    target = sys.argv[1]; seed, n, K, steps, rounds = map(int, sys.argv[2:7]); rng = random.Random(seed)
    kind = 'jr'; seeds = None; L = 0; mmax = 3 * n + 2; mmin = 2 * n; strict = 'strict' in sys.argv[7:]
    for a in sys.argv[7:]:
        if a.startswith('gen:'): kind = a[4:]
        elif a.startswith('seeds:'):
            p = a[6:].split(':'); seeds = load_seeds(p[0]); L = int(p[1]) if len(p) > 1 else 0
            seeds = [s for s in seeds if len(s[0]) == n]
        elif a.startswith('mmax:'): mmax = int(a[5:])
        elif a.startswith('mmin:'): mmin = int(a[5:])
    t0 = time.time(); print('$ python3 k4/ksens/climb.py', *sys.argv[1:], flush=True)
    for r in range(rounds):
        if seeds:
            sets, vals = rng.choice(seeds)
            if L: sets, vals = lift(sets, vals, L, rng)
        else:
            sets, vals = gen(kind, rng, n, K)
        Kr = max(K, max(len(s) for s in sets))
        c, Y = objective(target, sets, vals); best = c
        for s in range(steps):
            mu = mutate(sets, vals, rng, Kr, mmax)
            if mu is None or len(mu[0]) != n or 1 + max(max(x) for x in mu[0]) < mmin: continue
            c2, Y2 = objective(target, *mu)
            if c2 <= c or (not strict and rng.random() < 0.03):
                (sets, vals), c, Y = mu, c2, Y2; best = min(best, c)
                if c[0] == 0:
                    print('COUNTEREXAMPLE', target, json.dumps((sets, vals)), 'picks', Y, flush=True); break
        print('round', r, 'final', c, 'best', best, 'k', max(len(x) for x in sets), 'm', 1 + max(max(x) for x in sets),
              'inst', json.dumps((sets, vals)), 'time %.0f' % (time.time() - t0), flush=True)
