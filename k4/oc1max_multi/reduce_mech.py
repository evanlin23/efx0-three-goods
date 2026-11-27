"""Which mechanism repairs the reduced start (k4/oc1max_multi.md §8).  At each OC1 failure, for each canonical first
chain P1 from k in D with an improving pool pair T (inside J + B_z) after which the reduced state B1- (agent k and the goods T deleted)
is the serial-dictatorship outcome of an order of the reduced instance I- and has no one-absorber completion there,
the first mechanism of regimes.mechanism (KEEP, OWN, CLEAN = D-red, RING = RING-red, CAN-k, ED, ANY, NONE) that
repairs B1- in I-, and whether some repairing completion lifts to I (k keeps T, nobody threatens k).
Counts over starts: the best mechanism over the qualifying P1 (in the order listed).

    python3 k4/oc1max_multi/reduce_mech.py FILE.jsonl
"""
import sys, os, json, itertools, collections, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from mmlib import Inst, base_from_picks, junk, dangerous, oa_absorbers, moves
from dred import canonical_chains, apply_chain
from reduce_check import reduced, is_sd
from collect import add_repairs
from regimes import mechanism

ORDER = ['KEEP', 'OWN', 'CLEAN', 'RING', 'CAN-k', 'ED', 'ANY', 'NONE']


def study(rec):
    I = Inst(rec['sets'], rec['vals']); Y = tuple(rec['picks']); b = base_from_picks(Y)
    J = junk(I, b); D = dangerous(I, b); p = [I.V(i, b[i]) for i in range(I.n)]; best = None
    for k in D:
        for path in canonical_chains(I, b, k):
            pool = [g for g in J + list(b[path[-1]]) if g in I.R[k]]
            for T in [H for H in itertools.combinations(pool, 2) if I.V(k, H) > p[k]]:
                nb = apply_chain(I, b, path, T); I2, b2, keep = reduced(I, nb, k)
                if not is_sd(I2, b2) or oa_absorbers(I2, b2): continue
                r2 = {'inst': I2.to_json(), 'picks': tuple(x[0] for x in b2)}
                add_repairs(r2)
                if len(r2['D']) == 0: m = 'NONE'
                else: m, _ = mechanism(I2, r2)
                if best is None or ORDER.index(m) < ORDER.index(best): best = m
    return rec, best


if __name__ == '__main__':
    import gzip
    recs = [json.loads(l) for l in (gzip.open(sys.argv[1], 'rt') if sys.argv[1].endswith('.gz') else open(sys.argv[1]))]
    T = collections.Counter()
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for rec, best in pool.imap_unordered(study, recs, chunksize=4):
            T['failing starts'] += 1; T['best mechanism for the reduced start: %s' % best] += 1
    print('$ python3 k4/oc1max_multi/reduce_mech.py', *sys.argv[1:])
    for k in sorted(T): print(k, T[k])
