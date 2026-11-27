"""Census of canonical chains at one-absorber-hard starts with exactly one dangerous agent (k4/d1.md §1).

Independent re-implementation (k4/d1/d1lib.py, raw EFX0 by enumeration, no SAT) of k4/oc1_hall/d1_obstacles.py and
the D1-C / D1-H columns of d1_subcases.py.  Only the instance loader of k4/sdc/min_frozen.py is shared.

For every instance (n <= 5), every distinct pick vector over all orders with |D| = 1 and no one-absorber completion:
every canonical chain from k (head unfrozen at the picks), every inclusion-minimal improving H0 inside the pool
(J + B_{x_t}) & R_k; obstacles HEAD and CROWD; S* completion owned by k after the chain.

    python3 k4/d1/d1_census.py SRC [args of the loader]
Writes one JSON line per hard start to results/k4_d1/census_<tag>.jsonl when OUT=<tag> is set.
"""
import sys, os, itertools, collections, json, time
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
from d1lib import (Inst, sd_picks, Start, one_absorber, canonical_chains, pool, minimal_improving, apply_chain,
                   obstacles, sstar)


def analyse_start(I, S, k):
    rows = []
    for path in canonical_chains(S, k):
        Pi = pool(S, path)
        for H0 in minimal_improving(S, k, Pi):
            B2 = apply_chain(S, path, H0)
            head, crowded, F2 = obstacles(S, path, H0, B2)
            ok = sstar(I, B2, k)
            rows.append(dict(path=list(path), H0=sorted(H0), head=head, crowded=crowded, ok=ok))
    return rows


def load_items(src, argv):
    sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
    from min_frozen import load
    return load(src, argv)


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    out = os.environ.get('OUT')
    fo = open(os.path.join(ROOT, 'results', 'k4_d1', 'census_%s.jsonl' % out), 'w') if out else None
    print('$ python3 k4/d1/d1_census.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load_items(src, sys.argv):
        n = len(sets)
        if n > 5: continue
        I = Inst(sets, vals, m, name); seen = set()
        for od in itertools.permutations(range(n)):
            Y = sd_picks(I, od)
            if Y in seen: continue
            seen.add(Y); S = Start(I, Y)
            if len(S.D) != 1: continue
            if one_absorber(I, S.B): continue
            k = S.D[0]; C['starts'] += 1
            rows = analyse_start(I, S, k)
            C['chains'] += len(rows); C['chains repairing'] += sum(r['ok'] for r in rows)
            free = [r for r in rows if not r['head'] and not r['crowded']]
            C['chains free of HEAD and CROWD'] += len(free)
            C['  ... that fail (would refute Lemma D1-red)'] += sum(not r['ok'] for r in free)
            for r in rows:
                if r['head']: C['chains with HEAD'] += 1; C['  chains with HEAD that repair'] += r['ok']
                if r['crowded']: C['chains with CROWD'] += 1; C['  chains with CROWD that repair'] += r['ok']
                if r['crowded'] and not r['head'] and not r['ok']:
                    C['failing CROWD-only chains'] += 1
                    same = [q for q in rows if q['path'] == r['path'] and q['ok']]
                    C['  ... repaired by another minimal H0 on the same chain (D1-C)'] += bool(same)
                    if not same: print('D1-C FAILS', name, json.dumps((sets, vals)), 'order', od, 'picks', Y, 'chain', r['path'], 'H0', r['H0'], flush=True)
            C['starts with a repairing chain'] += any(r['ok'] for r in rows)
            if not any(r['ok'] for r in rows):
                print('NO REPAIR', name, json.dumps((sets, vals)), 'order', od, 'picks', Y, flush=True)
            if fo:
                fo.write(json.dumps(dict(name=name, sets=sets, vals=vals, m=m, order=list(od), picks=list(Y), k=k, rows=rows)) + '\n')
    for key in sorted(C): print(key, C[key])
    print('time %.0f s' % (time.time() - t0))
