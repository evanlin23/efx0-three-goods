"""ROUND-P (kgen/rounds.md §4.2, single-chain case §4.6): one round of vertex-disjoint OC1' moves (additions, rings,
chains whose non-end agents may take goods of the end's released base), all computed from the same start; the round's
state takes each move's bundles for the agents it changes.  Moves must change disjoint agent sets and the resulting
bundles must be disjoint (so no junk good is used twice; a good released by one move's end stays junk for the other
moves).  ROUND-P holds at a start if the picks or some round's state (up to R moves) has a one-absorber completion.
Coordinator's own code (oc1prime_verify.prime_states + Inst.one_absorber).
    python3 k4/sdc/roundp_check.py FILE.json.gz [R] [STRIDE]     (FILE: the certifier's export format)
    python3 k4/sdc/roundp_check.py idx164                         (the n = 5 OC1' counterexample)"""
import sys, gzip, json, itertools, collections, time, multiprocessing as mp
import _paths  # noqa: F401
from oc1_mc2_rand import Inst
import oc1prime_verify as P


def round_p(I, picks, R=2):
    base = [[g] if g is not None else [] for g in picks]
    if I.one_absorber(base): return 0, base
    key = lambda s: tuple(tuple(sorted(b)) for b in s)
    mv = {}
    for s in P.prime_states(I, base):
        ch = frozenset(i for i in range(I.n) if sorted(s[i]) != sorted(base[i]))
        mv.setdefault(key(s), (ch, s))
    mv = list(mv.values())
    for ch, s in mv:
        if I.one_absorber(s): return 1, s
    for r in range(2, R + 1):
        for combo in itertools.combinations(mv, r):
            chs = [c for c, _ in combo]
            if sum(len(c) for c in chs) != len(frozenset().union(*chs)): continue
            st = [list(b) for b in base]
            for c, s in combo:
                for i in c: st[i] = list(s[i])
            goods = [g for b in st for g in b]
            if len(goods) != len(set(goods)): continue
            if I.one_absorber(st): return r, st
    return None, None


def job(a):
    sets, vals, picks, R = a
    r, st = round_p(Inst(sets, vals), tuple(picks), R)
    return r, (sets, vals, picks, st)


if __name__ == '__main__':
    print('$ python3 k4/sdc/roundp_check.py', *sys.argv[1:], flush=True)
    if sys.argv[1] == 'idx164':
        S = [[0, 2, 3, 7], [1, 2, 6, 7], [3, 4, 5, 6], [3, 4, 5, 7], [4, 5, 6, 7]]
        V = [[1, 8, 6, 4], [4, 8, 2, 7], [6, 7, 3, 5], [7, 10, 2, 6], [7, 5, 3, 6]]
        r, st = round_p(Inst(S, V), (7, 2, 3, 5, 4), 3)
        print('5_pure idx 164, picks (7,2,3,5,4): moves in the smallest repairing round:', r, '| state', st)
        sys.exit()
    R = int(sys.argv[2]) if len(sys.argv) > 2 else 2; STRIDE = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    d = json.load(gzip.open(sys.argv[1]))
    tasks = [(h['sets'], st['vals'], st['picks'], R) for h in d['hypergraphs'] for st in h['starts']][::STRIDE]
    print('starts', len(tasks), flush=True)
    C = collections.Counter(); t0 = time.time()
    with mp.Pool() as pool:
        for r, w in pool.imap_unordered(job, tasks, chunksize=32):
            C[r] += 1
            if r is None: print('ROUND-P FAILS', json.dumps(w[:3]), flush=True)
    print('moves in the smallest repairing round (None = fails):', dict(C), '%.0f s' % (time.time() - t0))
