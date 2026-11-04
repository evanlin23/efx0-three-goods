"""Refined tie-breaks for the robust order after its refutation (k4/de4.md §10.4; ledger K4.DE4V3R.S). EVIDENCE only.

K4.DE4V3R (maxima: the largest level sum Phi among (V3)-valid states, then value-Pareto) is false (refute_rob.py). On
the refuting instance, 9 of the 10 (V3)-valid states of the largest level sum are completable. For each instance this
script takes the (V3)-valid states Y of the largest level sum Phi* and, among them, the maxima of
  sum    the total value  sum_i v_i(Y_i)  (a refinement of value-Pareto, so every lemma proved at the maxima of the
         robust order, Lean ones included, holds at these maxima too);
  lp     the number of lower-pair holders, fewest first, then value-Pareto;
  pareto value-Pareto (the refuted order, as a control);
and counts those maxima that are not completable (leftover goods that cannot all be given out keeping EFX0, checked by
SAT). 'any' counts the instances where no state of level sum Phi* is completable at all.

    python3 k4/de4/refine.py SOURCE PER JOBS SEED
SOURCE: advt0..advt3, advt3x, advt4x (adv_t.py, adv_t3.py, adv_t4.py), rand (dead.random_r1), xhg, hyper (stuck hypergraphs), screen,
json:FILE (a list of [sets, values, ...] instances, e.g. the double-clash instances of the hill-climbs)."""
import sys, os, json, random, collections, multiprocessing as mp, time
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import claimd as CD
CT = CD.CT; T = CD.T; S = CD.S
from de4lib import Inst, leftover, random_profile
from dead import strict_ok


def nlp(I, Y):
    return sum(S.types(I, i, list(Y[i])) == 'LP' for i in range(I.n))


def pareto_max(I, top, key=None):
    V = [CT.vals(I, Y) for Y in top]
    return [Y for k, Y in enumerate(top)
            if not any(all(a >= b for a, b in zip(V[l], V[k])) and V[l] != V[k] for l in range(len(top)))]


def analyse(I, C, ex, tag):
    All, ph, P = CT.states(I)
    v3 = [(Y, p) for Y, p in zip(All, ph) if T.v3ok(I, Y)]
    if not v3:
        return
    P3 = max(p for _, p in v3)
    top = [Y for Y, p in v3 if p == P3]
    Cm = S.Comp(I)
    comp = {}

    def ok(Y):
        k = tuple(tuple(sorted(A)) for A in Y)
        if k not in comp:
            comp[k] = not leftover(I, Y) or Cm.ok([list(A) for A in Y])
        return comp[k]
    C['instances'] += 1
    tot = [sum(CT.vals(I, Y)) for Y in top]
    msum = [Y for Y, t in zip(top, tot) if t == max(tot)]
    lpn = [nlp(I, Y) for Y in top]
    mlp = pareto_max(I, [Y for Y, k in zip(top, lpn) if k == min(lpn)])
    mpar = pareto_max(I, top)
    for name, M in (('sum', msum), ('lp', mlp), ('pareto', mpar)):
        bad = [Y for Y in M if not ok(Y)]
        C['%-6s maxima' % name] += len(M)
        if bad:
            C['%-6s NON-COMPLETABLE maxima' % name] += len(bad)
            C['%-6s instances with a non-completable maximum' % name] += 1
            if name != 'pareto':
                ex.append((name, tag, I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)],
                           [list(A) for A in bad[0]]))
    if not any(ok(Y) for Y in top):
        C['any    instances with no completable state of level sum Phi*'] += 1
        ex.append(('any', tag, I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)], None))


def job(args):
    src, per, seed = args
    rng = random.Random(seed); C = collections.Counter(); ex = []
    if src == 'screen':
        for name, I in S.screen_set():
            analyse(I, C, ex, name)
        return C, ex
    if src.startswith('json:'):
        data = json.load(open(src[5:]))
        for k, d in enumerate(data):
            if k % per != seed % per:
                continue
            sets, vals = d[0], d[1]
            analyse(Inst(sets, vals, 1 + max(max(s) for s in sets)), C, ex, src + ':%d' % k)
        return C, ex
    for _ in range(per):
        if src.startswith('advt'):
            import adv_t, adv_t3, adv_t4
            I = adv_t3.make(rng) if src == 'advt3x' else adv_t4.make(rng) if src == 'advt4x' else adv_t.make(rng, int(src[4:]))
            if I is None:
                continue
        elif src == 'rand':
            I = CD.random_r1(rng)
        else:
            cores = CD.XHG if src == 'xhg' else \
                json.load(open(os.path.join(ROOT, 'results', 'k4_de4', 'stuck_hypergraphs.json')))['hypergraphs']
            s = rng.choice(cores); I = Inst(s, random_profile(s, rng))
        analyse(I, C, ex, src)
    return C, ex


if __name__ == '__main__':
    src, per, jobs, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    print('$ python3 k4/de4/refine.py', ' '.join(sys.argv[1:]))
    if src.startswith('json:'):
        jobs = per
    tot, EX = collections.Counter(), []
    t0 = time.time()
    with mp.Pool(min(jobs, int(os.environ.get('NP', os.cpu_count())))) as p:
        for C, ex in p.imap_unordered(job, [(src, per, seed + k) for k in range(jobs)]):
            tot.update(C); EX += ex
    for k in sorted(tot):
        print('%9d  %s' % (tot[k], k))
    for e in EX[:8]:
        print('EX', json.dumps(e))
    print('time %.0f s' % (time.time() - t0))
