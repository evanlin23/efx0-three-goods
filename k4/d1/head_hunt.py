"""Hunt for one-absorber-hard starts with D = {k} at which EVERY canonical chain from k has HEAD (k4/d1.md §5).
Evidence generator only.  After Theorem D1-C these are the only starts Finding D1 still needs.

For each such start: every chain, its HEAD case (H-i: every second wanter of a = Y_{x_{t-1}} frozen at the picks;
H-ii: some second wanter unfrozen), every minimal improving H0, whether B' has an S* completion owned by k, and the
witness (who takes which junk good).  Records to results/k4_d1/allhead_<tag>.jsonl.

    python3 k4/d1/head_hunt.py TAG SEED SECONDS [climb]
"""
import sys, os, random, itertools, json, time, collections
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
from d1lib import (Inst, sd_picks, Start, one_absorber, canonical_chains, pool, minimal_improving, apply_chain,
                   obstacles, sstar)
from crowd_hunt import rand_inst, mutate


def all_head(S, k):
    ch = canonical_chains(S, k)
    if not ch: return False
    for path in ch:
        M = minimal_improving(S, k, pool(S, path))
        if not M: return False
        head, _, _ = obstacles(S, path, M[0])
        if not head: return False
    return True


def scan(sets, vals, m, C, fo):
    I = Inst(sets, vals, m); seen = set(); found = 0
    if len(set(g for s in sets for g in s)) != I.m: return 0
    for od in itertools.permutations(range(I.n)):
        Y = sd_picks(I, od)
        if Y in seen: continue
        seen.add(Y); S = Start(I, Y)
        if len(S.D) != 1: continue
        k = S.D[0]
        if not all_head(S, k): continue
        C['all-HEAD starts'] += 1
        if one_absorber(I, S.B): continue
        C['  hard'] += 1; found += 1
        rows = []
        for path in canonical_chains(S, k):
            x = path[-2]; ws = [w for w in S.W[x] if w not in path]
            case = 'H-ii' if any(w not in S.F for w in ws) else 'H-i'
            for H0 in minimal_improving(S, k, pool(S, path)):
                B2 = apply_chain(S, path, H0)
                X = sstar(I, B2, k, witness=True)
                rows.append(dict(path=list(path), case=case, H0=sorted(H0), ok=X is not None, X=X))
        ok = any(r['ok'] for r in rows)
        C['  hard, repaired by some chain'] += ok
        if not ok:
            C['  HARD AND NO REPAIR (Finding D1 fails)'] += 1
            print('NO REPAIR', json.dumps((sets, vals)), od, Y, flush=True)
        fo.write(json.dumps(dict(sets=sets, vals=vals, m=m, order=list(od), picks=list(Y), k=k, rows=rows)) + '\n'); fo.flush()
    return found


if __name__ == '__main__':
    tag, seed, secs = sys.argv[1], int(sys.argv[2]), float(sys.argv[3])
    climb = len(sys.argv) > 4
    rng = random.Random(seed); C = collections.Counter(); t0 = time.time()
    fo = open(os.path.join(ROOT, 'results', 'k4_d1', 'allhead_%s.jsonl' % tag), 'w')
    print('$ python3 k4/d1/head_hunt.py', *sys.argv[1:], flush=True)
    cur = None; cs = -1; stall = 0; it = 0
    while time.time() - t0 < secs:
        it += 1
        if not climb:
            scan(*rand_inst(rng), C, fo)
        else:
            if cur is None or stall > 400:
                n = rng.choice([3, 3, 4, 4, 5]); cur = rand_inst(rng, n); cs = -1; stall = 0
            cand = mutate(rng, *cur) if cs >= 0 else cur
            if max(len(s) for s in cand[0]) > 4 or min(len(s) for s in cand[0]) < 1: stall += 1; continue
            sc = scan(*cand, C, fo)
            if sc > cs: cur, cs, stall = cand, sc, 0
            elif sc == cs: cur = cand; stall += 1
            else: stall += 1
        if it % 5000 == 0: print(int(time.time() - t0), it, dict(C), flush=True)
    print('final', int(time.time() - t0), it)
    for key in sorted(C): print(key, C[key])
