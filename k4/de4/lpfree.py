"""F2-clash cycles on cores without lower pairs (k4/de4.md §10.3, toward P2; ledger K4.DE4V3R.C3). EVIDENCE.

Random strict profiles of the given cores in which no 4-good agent has a lower pair (no v(b) < v(c) + v(d) < v(a)).
There (V3) is empty, so Claim T' in case (L) holds vacuously (EFX.DE4.selfUp_breaks_v3), and with Lemma 18
(EFX.DE4.no_clean_clashCycle) only unclean F2-clash cycles stand between such cores and an unconditional proof. For
every (V3)-valid (H) state: its F2-clash cycles, clean or not; for the unclean ones, the level sum and whether one
replacement on the clashing arcs resolves them (nrcyc.replaced).

    CORES=k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz [XHG=1] python3 k4/de4/lpfree.py PER"""
import sys, os, json, random, collections, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import claimd as CD, nrcyc as NC
CT = CD.CT; T = CD.T; S = CD.S
from de4lib import Inst, wanted_goods, leftover, load_cores
def lpfree(I):
    for i in range(I.n):
        r = I.ranked(i)
        if len(r) == 4:
            a, b, c, d = (I.v[i][g] for g in r)
            if b < c + d < a: return False
    return True
def job(args):
    seed, per = args
    rng = random.Random(seed); C = collections.Counter()
    cores = sum((load_cores(os.path.join(ROOT, 'results', f)) for f in os.environ.get('CORES', 'k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz').split(',')), []) + (CD.XHG if os.environ.get('XHG') else [])
    for _ in range(per):
        s = rng.choice(cores)
        for _ in range(50):
            I = Inst(s, CD.random_profile(s, rng))
            if lpfree(I): break
        else: continue
        C['LP-free profiles'] += 1
        All, ph, P = CT.states(I)
        for Y, p in zip(All, ph):
            if not T.v3ok(I, Y): continue
            J = set(leftover(I, Y))
            if not J: continue
            W = set(wanted_goods(I, Y))
            if not CD.H(I, Y, J, W): continue
            for c in CD.cycles(I, CD.graph(I, Y, J, W), I.n):
                if not CD.f2_clash_only(I, Y, J, W, c): continue
                lab = [g for a in c for g in set(a[2]) & J]
                if len(lab) == len(set(lab)): C['clean F2-clash cycle (Lemma 18)'] += 1; continue
                C['unclean F2-clash cycle at the largest level sum %s' % (p == P)] += 1
                r = NC.replaced(I, Y, J, W, p, c)
                C['  resolved by one replacement: %s' % r] += 1
    return C
if __name__ == '__main__':
    print('$ CORES=%s XHG=%s python3 k4/de4/lpfree.py %s' % (os.environ.get('CORES', 'k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz'), os.environ.get('XHG', ''), ' '.join(sys.argv[1:])))
    tot = collections.Counter()
    with mp.Pool(3) as pool:
        for C in pool.imap_unordered(job, [(1000 + k, int(sys.argv[1])) for k in range(6)]): tot.update(C)
    for k in sorted(tot): print('%7d  %s' % (tot[k], k))
