"""Conjecture OC1-ED (TTC session, claude/k4-ttc, k4/ttc.md §8-§10) against this workstream's Findings B and C
(k4/oc1_hall.md §14).  An ED chain: x_0 dangerous (frozen, values junk); every middle agent x_i (0 < i < t) wants
B_{x_{i-1}} alone and takes no junk; the head x_t (t >= 1) takes B_{x_{t-1}} plus any junk H_t (improving); x_0
takes H_0 from J + B_{x_t} (for t = 0: x_0 adds junk to its own base).  The absorber is x_0 or x_t.
At every hard start (no S* completion at the picks) and on the 20 configurations of results/k4_oc1_hall/no_canonical.json:
  ED-S*  : some ED chain leaves an S* completion owned by x_0 or x_t;
  ED-OA  : some ED chain leaves a one-absorber completion whose absorber is x_0 or x_t (k4/sdc/f1_owner.absorber_ok);
  CANON  : (Finding C's canonical form) some chain from D whose head also takes no junk and wants its good alone.

    python3 k4/oc1_hall/ed_check.py SRC | list        (R1=1: R1-priority serial dictatorship, k4/sdc/sdc_orders.sd; MAX=1: only picks forming a maximum matching)
"""
import sys, os, itertools, collections, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, bundles_of, shaped_completion, frozen_set
from chain_shapes import s_star_owners
from sdclib import Enc
from f1_owner import absorber_ok
from oc_absorb import extends_A
from min_frozen import load
from sdc_orders import sd
R1 = os.environ.get('R1', '0') == '1'; MAX = os.environ.get('MAX', '0') == '1'
from max_matching import nu
import de_free as DF
DF.CHAIN_ONLY = True


def classify(I, E, P, base):
    B = bundles_of(I, base); res = set()
    for b2, ds in DF.moves(E, base, describe=True, all_desc=True).items():
        for kind, path, H in ds:
            x0, xt = path[0], path[-1]; t = len(path) - 1
            if x0 not in P.D: continue
            ed = all(not H.get(i) and B[path[i - 1]] and I.v[path[i]].get(B[path[i - 1]][0], 0) > P.pv[path[i]]
                     for i in range(1, t))
            if not ed: continue
            canon = ed and t >= 1 and not H.get(t) and B[path[t - 1]] and I.v[xt].get(B[path[t - 1]][0], 0) > P.pv[xt]
            ow = set(s_star_owners(I, b2)) & {x0, xt}
            if ow:
                res.add('ED-S*')
                if canon: res.add('CANON-S*')
                if t >= 1 and H.get(t): res.add('ED-S* with head junk')
                if t == 0: res.add('ED-S* with t = 0')
            if 'ED-OA' not in res and any(absorber_ok(E, b2, o) for o in {x0, xt}): res.add('ED-OA')
    return res


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/oc1_hall/ed_check.py', *sys.argv[1:], '(R1=%d MAX=%d)' % (R1, MAX), flush=True)
    if src == 'list':
        root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
        for d in json.load(open(os.path.join(root, 'results', 'k4_oc1_hall', 'no_canonical.json'))):
            I = Inst(d['sets'], d['vals'], d['m'], d['name']); E = Enc(d['sets'], d['vals'], d['m'])
            Y = tuple(d['picks']); P = Picks(I, Y); base = base_of_picks(I, Y)
            r = classify(I, E, P, base)
            C['configurations'] += 1
            for z in r: C['  ' + z] += 1
            print(d['name'], d['n'], d['m'], 'picks', list(Y), sorted(r), flush=True)
    else:
        for name, sets, vals, m in load(src, sys.argv):
            n = len(sets)
            if n > 5: continue
            I = Inst(sets, vals, m, name); E = Enc(sets, vals, m); seen = set(); NU = nu(I)
            for od in itertools.permutations(range(n)):
                Y = tuple(sd(E, list(od), True)[0]) if R1 else picks(I, od)
                if Y in seen: continue
                if MAX and sum(1 for y in Y if y is not None) != NU: seen.add(Y); continue
                seen.add(Y); base = base_of_picks(I, Y)
                if s_star_owners(I, base): continue
                P = Picks(I, Y); r = classify(I, E, P, base)
                oa = extends_A(E, base, 1)
                tag = 'S*-hard, one-absorber complete at the picks' if oa else 'one-absorber-hard'
                C[tag] += 1
                for z in r: C['  %s: %s' % (tag, z)] += 1
                if 'ED-S*' not in r:
                    print('NO ED-S* REPAIR', tag, name, json.dumps((sets, vals)), 'picks', Y, 'ED-OA' in r, flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
