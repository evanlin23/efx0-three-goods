"""Hunt for CROWD (and HEAD case H-ii) configurations at one-absorber-hard starts with one dangerous agent
(k4/d1.md §2).  Evidence generator only.

Random instances (n agents, m goods, every agent values 2-4 goods, values random positive integers, ties allowed with
small probability) and hill climbs that mutate one value or one relevant good at a time.  For every order of every
instance: picks; |D| = 1; a cheap pre-filter (some canonical chain has a minimal improving H0 that crowds a holder,
or a HEAD chain whose second wanter is unfrozen at the picks); then the raw one-absorber test (hard start); then the
census of d1_census.analyse_start.

Records every hard start that has a CROWD chain or a failing HEAD chain to results/k4_d1/hunt_<tag>.jsonl.

    python3 k4/d1/crowd_hunt.py TAG SEED SECONDS [mode]   mode = random | climb
"""
import sys, os, random, itertools, json, time, collections
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
from d1lib import (Inst, sd_picks, Start, one_absorber, canonical_chains, pool, minimal_improving, apply_chain,
                   obstacles, sstar)
from d1_census import analyse_start


def rand_inst(rng, n=None, m=None):
    n = n or rng.choice([3, 3, 4, 4, 4, 5])
    m = m or rng.randint(n + 2, n + 5)
    sets, vals = [], []
    for i in range(n):
        s = min(m, rng.choice([2, 3, 4, 4, 4]))
        S = sorted(rng.sample(range(m), s))
        if rng.random() < 0.15:
            V = [rng.randint(1, 6) for _ in S]
        else:
            V = rng.sample(range(1, 31), s)
        sets.append(S); vals.append(V)
    used = sorted(set(g for S in sets for g in S))
    relabel = {g: t for t, g in enumerate(used)}
    sets = [[relabel[g] for g in S] for S in sets]
    return sets, vals, len(used)


def mutate(rng, sets, vals, m):
    sets = [list(s) for s in sets]; vals = [list(v) for v in vals]
    i = rng.randrange(len(sets)); r = rng.random()
    if r < 0.6 or len(sets[i]) == 0:
        j = rng.randrange(len(sets[i])); vals[i][j] = max(1, vals[i][j] + rng.choice([-3, -2, -1, 1, 2, 3]))
    elif r < 0.8 and len(sets[i]) < 4:
        g = rng.randrange(m + 1)
        if g not in sets[i]: sets[i].append(g); vals[i].append(rng.randint(1, 30))
    elif r < 0.9 and len(sets[i]) > 2:
        j = rng.randrange(len(sets[i])); sets[i].pop(j); vals[i].pop(j)
    else:
        j = rng.randrange(len(sets[i])); g = rng.randrange(m + 1)
        if g not in sets[i]: sets[i][j] = g
    used = sorted(set(g for S in sets for g in S))
    relabel = {g: t for t, g in enumerate(used)}
    sets = [[relabel[g] for g in S] for S in sets]
    return sets, vals, len(used)


def prefilter(S, k):
    """some chain with a crowding minimal H0, or a HEAD chain (H-ii: a second wanter unfrozen at the picks)"""
    I = S.I
    for path in canonical_chains(S, k):
        Pi = pool(S, path)
        for H0 in minimal_improving(S, k, Pi):
            head, crowded, F2 = obstacles(S, path, H0)
            if crowded or head: return True
    return False


def scan(sets, vals, m, C, fo, tag):
    I = Inst(sets, vals, m); n = I.n; seen = set(); score = 0
    for od in itertools.permutations(range(n)):
        Y = sd_picks(I, od)
        if Y in seen: continue
        seen.add(Y); S = Start(I, Y)
        if len(S.D) != 1: continue
        k = S.D[0]
        if not prefilter(S, k): continue
        if one_absorber(I, S.B): continue
        C['hard starts with a CROWD/HEAD chain'] += 1
        rows = analyse_start(I, S, k)
        crowd = [r for r in rows if r['crowded'] and not r['head']]
        fcrowd = [r for r in crowd if not r['ok']]
        fhead = [r for r in rows if r['head'] and not r['ok']]
        score = max(score, 1 + len(crowd) + 5 * len(fcrowd) + 2 * len(fhead))
        rec = dict(sets=sets, vals=vals, m=m, order=list(od), picks=list(Y), k=k, rows=rows)
        if crowd: C['  with a CROWD-only chain'] += 1
        if fcrowd:
            C['  with a failing CROWD-only chain'] += 1
            for r in fcrowd:
                if not any(q['ok'] for q in rows if q['path'] == r['path']):
                    C['  D1-C FAILS'] += 1; rec['d1c_fail'] = True
        if fhead: C['  with a failing HEAD chain'] += 1
        if not any(r['ok'] for r in rows): C['  NO REPAIR (Finding D1 fails)'] += 1; rec['no_repair'] = True
        if crowd or fhead:
            fo.write(json.dumps(rec) + '\n'); fo.flush()
    return score


if __name__ == '__main__':
    tag, seed, secs = sys.argv[1], int(sys.argv[2]), float(sys.argv[3])
    mode = sys.argv[4] if len(sys.argv) > 4 else 'random'
    rng = random.Random(seed); C = collections.Counter(); t0 = time.time()
    fo = open(os.path.join(ROOT, 'results', 'k4_d1', 'hunt_%s.jsonl' % tag), 'w')
    print('$ python3 k4/d1/crowd_hunt.py', *sys.argv[1:], flush=True)
    R1179 = ([[0, 3, 6, 7], [1, 4, 6, 7], [2, 5, 8], [3, 4, 5, 8]], [[8, 1, 6, 4], [4, 8, 3, 2], [4, 2, 3], [5, 8, 6, 4]], 9)
    cur = None; cur_score = -1; stall = 0
    while time.time() - t0 < secs:
        if mode == 'random':
            sets, vals, m = rand_inst(rng); C['instances'] += 1
            scan(sets, vals, m, C, fo, tag)
        else:
            if cur is None or stall > 300:
                cur = R1179 if (cur is None and rng.random() < 0.5) else rand_inst(rng); cur_score = -1; stall = 0
            cand = mutate(rng, *cur) if cur_score >= 0 else cur
            C['instances'] += 1
            if max(len(s) for s in cand[0]) > 4 or min(len(s) for s in cand[0]) < 1: continue
            sc = scan(*cand, C, fo, tag)
            if sc >= cur_score: cur, cur_score = cand, sc; stall = 0 if sc > cur_score else stall + 1
            else: stall += 1
        if C['instances'] % 2000 == 0:
            print(int(time.time() - t0), dict(C), flush=True)
    print('final', int(time.time() - t0), flush=True)
    for key in sorted(C): print(key, C[key])
