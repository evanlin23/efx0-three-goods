"""The recursion behind the second move (k4/oc1max_multi.md §8): at an OC1 failure, after a canonical first chain P1 from
k in D in which k takes a pool pair T (inside J + B_z), delete agent k and the goods T (Lemma SET).  Questions, per (start, P1):
  SD   : is the reduced state B1- the serial-dictatorship outcome of some order of the reduced instance I- ?
  hard : does B1- have no one-absorber completion in I- ?
  repair-: is B1- repaired in I- by one official move (one-absorber completion)?
  lifts: does some second move from B1 (in I) that leaves k's pair alone have an S* completion owned by an agent
         other than k (so k keeps exactly T)?
  U-   : does Theorem U's hypothesis hold at B1- in I- (one truly dangerous agent, etc.)?
Counts over starts (some P1 of each kind).

    python3 k4/oc1max_multi/reduce_check.py FILE.jsonl
"""
import sys, os, json, itertools, collections, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from mmlib import Inst, base_from_picks, junk, frozen, dangerous, oa_absorbers, moves, is_canonical, nu, sstar_owners
from lemma_b import truly_dangerous
from dred import canonical_chains, improving_sets, apply_chain


def reduced(I, nb, k):
    """instance without agent k and the goods of nb[k] (goods renumbered), and the state; returns (I2, base2, keep)"""
    T = set(nb[k]); goods = [g for g in range(I.m) if g not in T]; new = {g: i for i, g in enumerate(goods)}
    keep = [i for i in range(I.n) if i != k]
    sets = [[new[g] for g in I.sets[i] if g not in T] for i in keep]
    vals = [[I.v[i][g] for g in I.sets[i] if g not in T] for i in keep]
    I2 = Inst(sets, vals, len(goods))
    base2 = tuple(tuple(new[g] for g in nb[i]) for i in keep)
    return I2, base2, keep


def is_sd(I, base):
    target = tuple(b[0] if b else None for b in base)
    if any(len(b) > 1 for b in base): return False
    return any(I.sd(od) == target for od in itertools.permutations(range(I.n)))


def study(rec):
    I = Inst(rec['sets'], rec['vals']); Y = tuple(rec['picks']); b = base_from_picks(Y)
    J = junk(I, b); D = dangerous(I, b); p = [I.V(i, b[i]) for i in range(I.n)]; st = set()
    for k in D:
        for path in canonical_chains(I, b, k):
            pool = [g for g in J + list(b[path[-1]]) if g in I.R[k]]
            for T in [H for H in itertools.combinations(pool, 2) if I.V(k, H) > p[k]]:
                nb = apply_chain(I, b, path, T)
                I2, b2, keep = reduced(I, nb, k)
                sd = is_sd(I2, b2)
                hard = not oa_absorbers(I2, b2)
                st.add('P1 with a pool pair')
                if sd: st.add('SD')
                if sd and not hard: st.add('SD, B1- completes at once in I-')
                if sd and hard:
                    rep = any(oa_absorbers(I2, x) for x in moves(I2, b2))
                    st.add('SD, hard, one move repairs in I-' if rep else 'SD, hard, NO one move in I-')
                    D2 = dangerous(I2, b2); J2 = junk(I2, b2)
                    st.add('SD, hard: |D_T(I-)| = %d' % len(truly_dangerous(I2, b2, D2, J2)))
                # does a second move in I with k keeping T repair?
                ok = False
                for B2 in moves(I, nb):
                    if set(B2[k]) != set(T): continue
                    if sstar_owners(I, B2) - {k}: ok = True; break     # S*: k (two goods) takes nothing
                if ok: st.add('lifts with k keeping T')
                if ok and sd: st.add('SD and lifts with k keeping T')
    return rec, st


if __name__ == '__main__':
    import gzip
    recs = [json.loads(l) for l in (gzip.open(sys.argv[1], 'rt') if sys.argv[1].endswith('.gz') else open(sys.argv[1]))]
    T = collections.Counter()
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for rec, st in pool.imap_unordered(study, recs, chunksize=4):
            T['failing starts'] += 1
            for s in st: T[s] += 1
    print('$ python3 k4/oc1max_multi/reduce_check.py', *sys.argv[1:])
    for k in sorted(T, key=lambda k: -T[k]): print(T[k], k)
