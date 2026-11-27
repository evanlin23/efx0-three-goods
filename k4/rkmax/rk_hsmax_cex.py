"""Replay of the counterexamples to Conjecture HS-MAX (k4/rkmax.md §7; results/k4_rkmax/hsmax_cex_n4.jsonl, found by
rk_climb.py).  For each (sets, vals, picks Y):
  1. values strict (distinct subset sums of disjoint subsets of each agent's goods) and balanced (2 v(g) < v(R_i));
  2. Y is a maximum matching, Pareto optimal, an SD outcome of some order, and sigma(Y) is the maximum over all maximum
     matchings (all matchings enumerated);
  3. hard: no one-absorber completion at the picks, by rklib AND by k4/oc1max_multi/mmlib.oa_absorbers (a second
     implementation);
  4. no Prop. T0 receiver, no Lemma S' case (every canonical chain, every h, every holder r), no Lemma RF-B case;
  5. OC1 holds (one official move repairs, rklib), and Lemma SINK1 applies (an explicit case, raw EFX0).
So HS-MAX (T0 / S' / RF-B) is false, RKMAX is not refuted, and HS-MAX' (SINK1) holds there.
    python3 rk_hsmax_cex.py"""
import os, sys, json, itertools, collections
from rklib import Prof, lexmax
from rk_classes import theta, sprime_cases, rfb_cases, sink1_cases
from rk_climb import strict_balanced
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.join(HERE, '..', '..')
sys.path.insert(0, os.path.join(ROOT, 'k4', 'oc1max_multi'))
import mmlib  # noqa: E402

C = collections.Counter()
for line in open(os.path.join(ROOT, 'results', 'k4_rkmax', 'hsmax_cex_n4.jsonl')):
    e = json.loads(line); sets, vals, Y = e['sets'], e['vals'], tuple(e['picks'])
    P = Prof(sets, vals); ro = P.roles(Y)
    ok1 = all(strict_balanced(x) for x in vals)
    nu, mm = P.max_matchings(); best, O = lexmax(mm, P.sigma)
    ok2 = (sum(g is not None for g in Y) == nu and P.pareto_optimal(Y) and P.sigma(Y) == best
           and any(P.sd(o) == Y for o in itertools.permutations(range(P.n))))
    I = mmlib.Inst(sets, vals, m=P.m)
    ok3 = P.one_absorber([frozenset([g]) for g in Y]) is None and not mmlib.oa_absorbers(I, mmlib.base_from_picks(Y))
    ok4 = (all(theta(P, Y, ro, z) for z in ro['U']) and not sprime_cases(P, Y, ro, first=False)
           and not rfb_cases(P, Y, ro))
    oc = P.oc1(Y); sk = sink1_cases(P, Y, ro)
    C['instances'] += 1
    C['1 strict, balanced: %s' % ok1] += 1
    C['2 sigma-maximal maximum matching, PO, SD: %s' % ok2] += 1
    C['3 hard (rklib and mmlib): %s' % ok3] += 1
    C['4 no T0 / S\' / RF-B case: %s' % ok4] += 1
    C['5 OC1: %s, SINK1 applies: %s' % (oc, bool(sk))] += 1
print('$ python3 k4/rkmax/rk_hsmax_cex.py')
for k in sorted(C): print(k, C[k])
