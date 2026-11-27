"""Hill climbs toward the corners of the D1-C case analysis (k4/d1.md §3).  Evidence generator only.

Score of an instance (max over its orders with |D| = 1):
  +1    hard start with a CROWD-only chain
  +4    the crowded holder is the head x_t and k's H0 contains Y_{x_t}
  +8    ... and the head has no compensation good e with {a, e} robust
  +6    k's minimal improving family on that chain has a single member (no other H0' to switch to)
  +50   D1-C fails (no minimal H0 on the chain repairs)
  +100  no canonical chain repairs at all (Finding D1 fails)
A cheap pre-score (no hard test) guides the climb: CROWD-only chain with the head crowded by H0 containing Y_{x_t}.

    python3 k4/d1/corner_climb.py TAG SEED SECONDS
"""
import sys, os, random, itertools, json, time, collections
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
from d1lib import (Inst, sd_picks, Start, one_absorber, canonical_chains, pool, minimal_improving, apply_chain,
                   obstacles, sstar)
from d1_census import analyse_start
from crowd_hunt import rand_inst, mutate


def pre(S, k):
    I = S.I; best = 0
    for path in canonical_chains(S, k):
        Pi = pool(S, path); z = path[-1]; M = minimal_improving(S, k, Pi)
        for H0 in M:
            head, crowded, F2 = obstacles(S, path, H0)
            if head or not crowded: continue
            sc = 1
            if z in crowded and S.Y[z] in H0:
                sc += 4
                a = S.Y[path[-2]]; Qz = [g for g in Pi if g in I.R[z]]
                if not any(I.v[z][a] + I.v[z][e] >= I.val(z, [g for g in Qz if g != e]) for e in Qz if e not in H0): sc += 8
            if len(M) == 1: sc += 6
            best = max(best, sc)
    return best


def score(sets, vals, m, C, fo):
    I = Inst(sets, vals, m); best = 0
    for od in itertools.permutations(range(I.n)):
        Y = sd_picks(I, od); S = Start(I, Y)
        if len(S.D) != 1: continue
        k = S.D[0]; p = pre(S, k)
        if p == 0: continue
        if one_absorber(I, S.B): best = max(best, p * 0.3); continue
        rows = analyse_start(I, S, k); sc = p
        C['hard corner starts'] += 1
        for r in rows:
            if r['crowded'] and not r['head'] and not r['ok'] and not any(q['ok'] for q in rows if q['path'] == r['path']):
                sc += 50; C['D1-C FAILS'] += 1
        if not any(r['ok'] for r in rows): sc += 100; C['NO REPAIR'] += 1
        if p >= 5: C['hard: head crowded by H0 containing Y_z'] += 1
        if p >= 13: C['hard: ... and no robust compensation'] += 1
        if p >= 5:
            fo.write(json.dumps(dict(sets=sets, vals=vals, m=m, order=list(od), picks=list(Y), k=k, rows=rows, pre=p)) + '\n'); fo.flush()
        best = max(best, sc)
    return best


if __name__ == '__main__':
    tag, seed, secs = sys.argv[1], int(sys.argv[2]), float(sys.argv[3])
    rng = random.Random(seed); C = collections.Counter(); t0 = time.time()
    fo = open(os.path.join(ROOT, 'results', 'k4_d1', 'corner_%s.jsonl' % tag), 'w')
    print('$ python3 k4/d1/corner_climb.py', *sys.argv[1:], flush=True)
    cur = None; cs = -1; stall = 0; it = 0
    while time.time() - t0 < secs:
        it += 1
        if cur is None or stall > 400:
            n = rng.choice([2, 3, 3, 4]); cur = rand_inst(rng, n, rng.randint(n + 1, n + 4)); cs = -1; stall = 0
        cand = mutate(rng, *cur) if cs >= 0 else cur
        if max(len(s) for s in cand[0]) > 4 or min(len(s) for s in cand[0]) < 1: stall += 1; continue
        sc = score(*cand, C, fo)
        if sc > cs: cur, cs, stall = cand, sc, 0
        elif sc == cs: cur = cand; stall += 1
        else: stall += 1
        if it % 3000 == 0: print(int(time.time() - t0), it, dict(C), flush=True)
    print('final', int(time.time() - t0), it)
    for key in sorted(C): print(key, C[key])
