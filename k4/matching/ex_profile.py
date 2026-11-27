"""How a repairing chain pays for the missing slots (k4/matching.md §3, the exchange accounting).

For every hard start (rows of hard_starts.py) and every (P, H0) with owner k satisfying Lemma EX's hypothesis
(exchange.ex_value: d_k <= s_k), record
  delta_end = Lemma 2*'s S* deficiency of Y with owner x_t (the end) and every demand present (mlib.deficiency),
  d         = the exchange deficiency (owner set W_{x_t}, k's demand deleted, chain agents at their new values),
  s         = the free slots the chain creates (the end, and agents it unfreezes).
delta_end - d is what deleting k's demand (and raising the chain agents' values) is worth; s is what the new slots
are worth.  Per start the EX triple with the least s, then the least d, is kept.

    python3 k4/matching/ex_profile.py FILE.jsonl [...]"""
import sys, os, json, collections, time, multiprocessing as mp
import _mpaths  # noqa: F401
from mlib import M, INF, subsets
from exchange import general_chains, apply_chain, ex_value


def job(row):
    I = M(row['sets'], row['vals'], row['m'], row['name']); Y = row['picks']
    base = [[g] if g is not None else [] for g in Y]; J = I.junk(base); fz = set(I.frozen(base))
    best = None; endcache = {}
    for P, Hs in general_chains(I, base):
        k, xt = P[0], P[-1]; used = set(g for h in Hs.values() for g in h)
        Pi = [g for g in J if g not in used] + [Y[xt]]
        for H0 in subsets([g for g in Pi if g in I.R[k]], 1):
            if I.V(k, H0) <= I.V(k, base[k]) or (xt in fz and Y[xt] not in H0): continue
            Bp = apply_chain(I, base, P, list(H0), Hs)
            d, s, why, _ = ex_value(I, base, P, Bp, k)
            if d > s: continue
            if xt not in endcache: endcache[xt] = I.deficiency(base, 'ss', [xt])
            nD = sum(1 for x in P if x in set(I.dangerous(base)))
            key = (s, d, len(P))
            if best is None or key < best[0]:
                best = (key, dict(delta_end=endcache[xt], d=d, s=s, length=len(P) - 1, D_on_chain=nD,
                                  junk_mid=any(Hs.get(i) for i in range(1, len(P)))))
    return row, best


if __name__ == '__main__':
    print('$ python3 k4/matching/ex_profile.py', *[os.path.relpath(f, _mpaths.ROOT) for f in sys.argv[1:]], flush=True)
    rows = [json.loads(l) for f in sys.argv[1:] for l in open(f)]
    T = collections.Counter(); t0 = time.time()
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for row, b in pool.imap_unordered(job, rows, chunksize=4):
            T['hard starts'] += 1
            if b is None: T['no EX triple with owner k'] += 1; continue
            x = b[1]
            de = 'INF' if x['delta_end'] >= INF else x['delta_end']
            T['delta_oa(Y) = %d | delta(Y, end) = %s, d = %d, s = %d' % (row['d_oa'], de, x['d'], x['s'])] += 1
            T['s = %d' % x['s']] += 1
            T['dangerous agents on the chain: %d' % x['D_on_chain']] += 1
            T['chain length %d' % x['length']] += 1
            if x['junk_mid']: T['middle or end junk used'] += 1
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
