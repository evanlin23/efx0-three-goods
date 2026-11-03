"""Brute-force check of the repair lemma and of Lemma V of k4/de4.md §9 (EVIDENCE for the written proofs):
- Lemma R: switching every holder of its lower pair whose b is leftover to {b} (repeatedly) gives a (V3)-valid state
  with the same level for every agent;
- Lemma V: if Y is (V3)-valid, Z is valid, nobody's value is lower in Z and every good held in Y is held in Z, then Z
  is (V3)-valid.
On every valid state (Lemma R) and every such pair (Lemma V) of random profiles of the certified cores with n = 3 and
n = 4 (two or three 4-good agents) and of the screen instances with n <= 4.  python3 k4/de4/verify_repair.py"""
import sys, random, collections, json, multiprocessing as mp
import os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ss_screen as S
from de4lib import Inst, load_cores, random_profile, chain_move

DE4 = S.Variant('DE4', {'LP': 3})
def v3ok(I, Y):
    held = set(g for A in Y for g in A)
    return all(not (S.types(I, i, Y[i]) == 'LP' and I.ranked(i)[1] not in held) for i in range(I.n))
def repair(I, Y):
    Z = [tuple(A) for A in Y]
    while True:
        held = set(g for A in Z for g in A)
        bad = [i for i in range(I.n) if S.types(I, i, Z[i]) == 'LP' and I.ranked(i)[1] not in held]
        if not bad: return Z
        i = bad[0]; Z[i] = (I.ranked(i)[1],)
def phi(I, Y): return sum(DE4.level(I, i, Y[i]) for i in range(I.n))
def pareto_ge(I, Z, Y):
    a = [I.val(i, Z[i]) for i in range(I.n)]; b = [I.val(i, Y[i]) for i in range(I.n)]
    return all(x >= y for x, y in zip(a, b)) and a != b

from de4lib import Inst, load_cores, random_profile
def job(args):
    src, per, seed = args
    rng = random.Random(seed); C = collections.Counter()
    cores = []
    for f in src.split(','): cores += load_cores(os.path.join(os.path.dirname(os.path.dirname(HERE)), 'results', f))
    insts = [Inst(s, random_profile(s, rng)) for s in (rng.choice(cores) for _ in range(per))]
    if seed == 0: insts += [I for _, I in S.screen_set() if I.n <= 4]
    for I in insts:
        St = S.all_states(DE4, I)
        for Z in St:
            R = repair(I, Z)
            ok = S.valid(DE4, I, [tuple(a) for a in R]) and v3ok(I, R) and all(DE4.level(I, i, R[i]) == DE4.level(I, i, Z[i]) for i in range(I.n))
            C['Lemma R holds: %s' % ok] += 1
        V3 = [Y for Y in St if v3ok(I, Y)]
        vals = {id(Z): [I.val(i, Z[i]) for i in range(I.n)] for Z in St}
        held = {id(Z): set(g for A in Z for g in A) for Z in St}
        for Y in V3:
            for Z in St:
                if held[id(Y)] <= held[id(Z)] and all(a >= b for a, b in zip(vals[id(Z)], vals[id(Y)])):
                    C['Lemma V holds: %s' % v3ok(I, Z)] += 1
    return C
if __name__ == '__main__':
    tot = collections.Counter()
    with mp.Pool(2) as p:
        for C in p.imap_unordered(job, [('k4_certs_3.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz', 40, k) for k in range(8)]):
            tot.update(C)
    for k in sorted(tot): print('%10d  %s' % (tot[k], k))
