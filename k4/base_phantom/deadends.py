"""Dead ends of ROUND-RSD and what the base case can do there.

For every start of a data set, every state reachable by admissible rounds (bplib.rounds: at most two settlements,
(L*) at the round's end, (P2) toward earlier phantoms, reduced state a perfect SD outcome) is generated.  A *dead end*
is a reachable state with no lifted completion and no admissible round.  At each dead end:
  feasible  some EFX0 allocation of I keeps every phantom's T (the present goods go to the present agents in any way;
            bplib.extensions, exact backtracking);
  base      the least class C0..C3 of base.py with a one-move repair (an official move of the present instance, then a
            lifted one-absorber completion), or None.
Per start: whether a dead end, or an infeasible state at all, is reachable.

    python3 k4/base_phantom/deadends.py NAME FILE[,FILE..] [LIMIT]   (log to stdout; dead ends to results/k4_base_phantom/deadends_NAME.jsonl.gz)
"""
import sys, os, json, gzip, collections, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bplib import Inst, start_state, bits, load_rows, row_key, extensions, lifted_completion
from base import explore, dead_ends, good_states, base_repairs, p3_violations

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'results', 'k4_base_phantom')


def path_to(seen, k0, target):
    """A sequence of rounds from k0 to target (BFS over the explored graph)."""
    prev = {k0: None}
    q = [k0]
    while q:
        k = q.pop(0)
        if k == target:
            break
        for combo, s2 in zip(seen[k]['rounds'], seen[k]['succ']):
            if s2 not in prev:
                prev[s2] = (k, combo)
                q.append(s2)
    out = []
    k = target
    while prev[k] is not None:
        k, combo = prev[k]
        out.append([[c[0], list(c[1]), bits(c[2])] for c in combo])
    return out[::-1]


def phantom_kinds(I, D):
    """Lemma PHANTOM's constraint of each phantom f at state D: 'l-alone on a base' (some good of R_f - T_f worth more
    than T_f to f is a present agent's base), 'l-alone on junk', 'pair' (only the y, l separation) or 'none'."""
    out = []
    for f in D.dead:
        tau = I.V(f, D.B[f])
        rest = bits(I.R[f] & ~D.B[f])
        big = [h for h in rest if I.val[f][h] > tau]
        if any(D.B[a] >> h & 1 for a in D.alive for h in big):
            out.append('l-alone on a base')
        elif big:
            out.append('l-alone on junk')
        elif sum(I.val[f][h] for h in rest) > tau and len(rest) == 2:
            out.append('pair')
        else:
            out.append('none')
    return tuple(sorted(set(out)))


def job(r):
    I = Inst(r['sets'], r['vals'])
    S = start_state(I, r['picks'])
    seen = explore(I, S)
    good = good_states(seen)
    C = collections.Counter()
    recs = []
    C['start repaired by rounds and a completion: %s' % good[S.key()]] += 1
    infeas = [k for k, info in seen.items() if info['state'].dead and extensions(I, info['state']) is None]
    C['an infeasible state is reachable: %s' % bool(infeas)] += 1
    de = dead_ends(seen)
    C['a dead end is reachable: %s' % bool(de)] += 1
    for k in de:
        D = seen[k]['state']
        feas = extensions(I, D) is not None
        c, w = base_repairs(I, D)
        C['dead end: %d phantoms, %d rounds, feasible %s, base class %s' % (len(D.dead), len(path_to(seen, S.key(), k)),
                                                                           feas, c)] += 1
        C['dead end with phantoms: constraint kinds %s, feasible %s' % (phantom_kinds(I, D), feas)] += 1 if D.dead else 0
        recs.append(dict(name=r['name'], sets=r['sets'], vals=r['vals'], picks=r['picks'],
                         path=path_to(seen, S.key(), k), alive=list(D.alive), B=[bits(b) for b in D.B],
                         junk=bits(D.junk()), feasible=feas, base=c, p3=p3_violations(I, D),
                         witness=None if w is None else dict(P=list(w[0]), H0=bits(w[1]), Hs=[bits(h) for h in w[2]],
                                                             X=[bits(x) for x in w[3]])))
    return C, recs


if __name__ == '__main__':
    name, fns = sys.argv[1], sys.argv[2].split(',')
    lim = int(sys.argv[3]) if len(sys.argv) > 3 else None
    rows = {}
    for fn in fns:
        for r in load_rows(fn):
            rows.setdefault(row_key(r), r)
    rows = list(rows.values())[:lim]
    print('$ python3 k4/base_phantom/deadends.py', name, ','.join(os.path.relpath(f) for f in fns), lim or '')
    print('distinct starts:', len(rows))
    C = collections.Counter()
    out = gzip.open(os.path.join(OUT, 'deadends_%s.jsonl.gz' % name), 'wt')
    with mp.Pool(4) as pool:
        for c, recs in pool.imap_unordered(job, rows, chunksize=16):
            C.update(c)
            for x in recs:
                out.write(json.dumps(x) + '\n')
    out.close()
    for k in sorted(C):
        print('  %7d  %s' % (C[k], k))
