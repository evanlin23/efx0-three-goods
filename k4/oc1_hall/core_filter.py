"""Are the OC1 counterexamples of the TTC session (claude/k4-ttc, results/k4_ttc/oc1_counterexamples.json) cores?
(k4/oc1_hall.md §16).  Peeling as in PROMPT.md L2 at k <= 4: R1 removes an agent whose remaining relevant goods are at
most two, or whose favourite remaining good is worth at least the rest of its remaining goods (it takes that good);
R2 removes an agent whose private remaining goods P (valued by no other remaining agent) have |P| >= 2 and
v(P) >= v(rest) (it takes P); goods valued by no remaining agent are junk (L3).  An instance is a core when nothing
peels.  For non-cores, OC1 (one-absorber completion, k4/sdc/oc_absorb.extends_A; one chain, de_free moves) is tested
on every order of the remaining core (components together).

    python3 k4/oc1_hall/core_filter.py FILE.json
"""
import sys, os, json, itertools, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, base_of_picks
from sdclib import Enc
from oc_absorb import extends_A
import de_free as DF
DF.CHAIN_ONLY = True


def peel(sets, vals):
    n = len(sets); v = [dict(zip(s, x)) for s, x in zip(sets, vals)]
    alive = set(range(n)); goods = set(g for s in sets for g in s); steps = []
    while True:
        moved = False
        for i in sorted(alive):
            R = sorted((g for g in sets[i] if g in goods), key=lambda g: -v[i][g])
            if not R or len(R) <= 2 or v[i][R[0]] >= sum(v[i][g] for g in R[1:]):
                alive.discard(i); goods -= set(R[:1]); steps.append(('R1', i, R[:1])); moved = True; break
            others = set(g for j in alive if j != i for g in sets[j] if g in goods)
            Pv = [g for g in R if g not in others]
            if len(Pv) >= 2 and sum(v[i][g] for g in Pv) >= sum(v[i][g] for g in R if g not in Pv):
                alive.discard(i); goods -= set(Pv); steps.append(('R2', i, Pv)); moved = True; break
        if not moved: break
    valued = set(g for j in alive for g in sets[j] if g in goods)
    return alive, valued, steps


if __name__ == '__main__':
    L = json.load(open(sys.argv[1])); C = collections.Counter()
    for t, d in enumerate(L):
        sets, vals = d['sets'], d['vals']
        alive, valued, steps = peel(sets, vals)
        if len(alive) == len(sets):
            C['already a core'] += 1; print('CORE', t, json.dumps((sets, vals)), flush=True); continue
        C['not a core'] += 1
        C['  first peel: %s' % steps[0][0]] += 1
        if len(alive) < 2: C['  core has fewer than 2 agents'] += 1; continue
        ren = {g: k for k, g in enumerate(sorted(valued))}
        cs = [[ren[g] for g in sets[i] if g in valued] for i in sorted(alive)]
        cv = [[x for g, x in zip(sets[i], vals[i]) if g in valued] for i in sorted(alive)]
        m = len(ren); I = Inst(cs, cv, m); E = Enc(cs, cv, m); bad = 0; seen = set()
        for od in itertools.permutations(range(len(cs))):
            Y = picks(I, od)
            if Y in seen: continue
            seen.add(Y); b = base_of_picks(I, Y)
            if extends_A(E, b, 1): continue
            if not any(extends_A(E, b2, 1) for b2 in DF.moves(E, b)): bad += 1
        C['  remaining core: n = %d' % len(cs)] += 1
        C['  remaining core violates OC1 for some order'] += bool(bad)
        if bad: print('CORE OF', t, 'violates OC1', json.dumps((cs, cv)), flush=True)
    for k in sorted(C): print(k, C[k])
