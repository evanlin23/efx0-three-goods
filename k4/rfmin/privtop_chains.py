"""Canonical chains and Lemma ABS' at RF-PRIV starts (k4/RFMIN.md §6, Lemma CH).

Random strict connected k = 4 cores with a private-top agent f (the generator and seeds of privtop_gap.py). At every
maximum-matching start where ABS' fails at the picks (some frozen agent values the junk above its pick), every canonical
chain is tried: d in D_full takes an improving H0 of its junk, x1 takes Y_d, ..., x_t takes Y_x(t-1), where each x_i
holds a pick and wants its predecessor's pick (no junk to middle agents or the head). ABS' (privtop_absp.absp) is
tested at the resulting state, and every construction is checked by the raw EFX0 definition. Starts are split into gap
starts (no one-absorber completion at the picks) and the others. Violations of (A3) are classified:
  V1: an agent outside the chain, not in D_full;  V1*: another D_full agent;  V2: a chain member.
At gap starts where no canonical chain works, the official moves (Inst.moves) are searched for one in which some agent
takes a pick together with junk and after which ABS' holds.
Usage: privtop_chains.py N SEED NMIN NMAX"""
import sys, os, random, itertools, collections, json
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'sdc'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from oc1_mc2_rand import Inst, gen
from privtop_random import nu
from privtop_absp import absp
from multiprocessing import Pool


def canonical_chains(I, pk, d, J):
    """(H0, path): H0 an improving subset of d's junk, path = [d, x1, ..., xt], each x_i holding a pick and wanting
    the pick of x_(i-1)."""
    n = I.n; p = [I.v[i].get(pk[i], 0) if pk[i] is not None else 0 for i in range(n)]
    Rd = sorted(g for g in J if g in I.R[d])
    def ext(path):
        if len(path) >= 2: yield path
        for y in range(n):
            if y not in path and pk[y] is not None and I.v[y].get(pk[path[-1]], 0) > p[y]:
                yield from ext(path + [y])
    for r in range(2, len(Rd) + 1):
        for H0 in itertools.combinations(Rd, r):
            if I.V(d, H0) > p[d]:
                for path in ext([d]): yield H0, path


def job(args):
    n, seed = args
    rng = random.Random(seed)
    while True:
        try: sets, vals = gen(n, rng)
        except ValueError: continue
        deg = collections.Counter(g for S in sets for g in S)
        pt = [a for a in range(n) if deg[sets[a][vals[a].index(max(vals[a]))]] == 1]
        if pt: break
    I = Inst(sets, vals); N = nu(I); f = pt[0]
    C = collections.Counter(); ex = []
    for pk in set(I.sd(o) for o in itertools.permutations(range(n))):
        if sum(x is not None for x in pk) != N: continue
        base = [[g] if g is not None else [] for g in pk]
        if absp(I, base, f)[0] == 'ok': continue
        J = set(range(I.m)) - {g for g in pk if g is not None}
        p = [I.v[i].get(pk[i], 0) if pk[i] is not None else 0 for i in range(n)]
        wanted = lambda a: any(i != a and I.v[i].get(pk[a], 0) > p[i] for i in range(n))
        D = [a for a in range(n) if pk[a] is not None and wanted(a) and I.V(a, J) > p[a]]
        tag = 'gap' if not I.one_absorber(base) else 'non-gap'
        key = '%s |D_full|=%d' % (tag, len(D))
        C[key + ': starts'] += 1
        some = some_pair = False; every_pair = True; n_pair = 0
        for d in D:
            assert any(pk[x] is not None and I.v[x].get(pk[d], 0) > p[x] for x in range(n) if x != d)
            heads = False
            for H0, path in canonical_chains(I, pk, d, J):
                st = [list(b) for b in base]; st[d] = list(H0)
                for i in range(1, len(path)): st[path[i]] = [pk[path[i - 1]]]
                unf = not wanted(path[-1]); heads |= unf
                why, X = absp(I, st, f)
                if why == 'ok':
                    assert I.efx0(X), ('ABS\' construction not EFX0', sets, vals, pk, st)
                    C['  ABS\' states after canonical chains, construction EFX0 (raw)'] += 1
                    some = True
                if unf and len(H0) == 2:
                    n_pair += 1
                    assert why in ('ok', 'A3'), ('Lemma CH: (A0)-(A2) must hold', why, sets, vals, pk, st)
                    if why == 'ok': some_pair = True
                    else:
                        every_pair = False
                        for q in X:
                            assert q != d, 'Lemma CH: d meets (A3)'
                            k = 'V2' if q in path[1:] else ('V1*' if q in D else 'V1')
                            if k == 'V1': assert I.v[q].get(pk[path[-1]], 0) > 0, 'V1 needs the released pick'
                            C['%s: pair chains (unfrozen head) violating via %s' % (key, k)] += 1
                elif unf:
                    assert why in ('ok', 'A2', 'A3'), why
            assert heads, 'Lemma CH 1: a chain with an unfrozen head exists'
        C['%s: some canonical chain gives ABS\': %s' % (key, some)] += 1
        C['%s: some pair chain, unfrozen head, gives ABS\': %s' % (key, some_pair)] += 1
        if n_pair: C['%s: every pair chain, unfrozen head, gives ABS\': %s' % (key, every_pair)] += 1
        else: C['%s: no pair chain with an unfrozen head' % key] += 1
        if tag == 'gap' and len(D) == 1 and n_pair and not every_pair and len(ex) < 4: ex.append((sets, vals, pk, f))
        if tag == 'gap' and not some:
            # the repairing moves when no canonical chain works: does some official move in which an agent takes a
            # pick together with junk leave ABS'?
            mixed = False
            for st in I.moves(base):
                st = [list(b) for b in st]
                if absp(I, st, f)[0] != 'ok': continue
                if any(any(g in J for g in st[a]) and any(g not in J for g in st[a]) for a in range(n)): mixed = True
            C['%s, no canonical chain: some move with an agent taking a pick plus junk leaves ABS\': %s' % (key, mixed)] += 1
    return C, ex


if __name__ == '__main__':
    N, seed, nmin, nmax = map(int, sys.argv[1:5])
    T = collections.Counter(); exs = []
    with Pool(4) as pool:
        for C, ex in pool.imap_unordered(job, [(nmin + i % (nmax - nmin + 1), seed * 1000003 + i) for i in range(N)]):
            T.update(C); exs += ex
    print('canonical chains at RF-PRIV starts where ABS\' fails at the picks: %d cores, n = %d..%d, seed %d' % (
        N, nmin, nmax, seed))
    for k, x in sorted(T.items()): print('  %-76s %d' % (k, x))
    for e in exs: print('  example (gap, |D_full| = 1, a pair chain fails)', json.dumps(e))
