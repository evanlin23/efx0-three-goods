"""NOF-R1 against the existing LB4r machinery (k4/c4_verify_H/lb4r.py, a transcription of lean/EFX/LB4R.lean, and
Lemma K of k4/rulef.md in k4/rulef_model.py).  For the plain neediest-first R1 run (and, if needed, its deferrals): build
the LB4r state with these picks, run need-shrinking upgrades ('shrink') or envy-free ones, and ask
  (O) does LB4r's Output exist for some owner (or none)?  (exact, SAT; Lean's Output with the owner's needs from its bundle)
  (K) is Lemma K's deficit <= 0?
Compared with plain extendability (any completion, SAT).

    python3 k4/sdc/nof_lemmak.py screen|suite|cores:FILES N SEED [--nor1]   (--nor1: the order without R1 priority)"""
import sys, os, collections
import _paths
sys.path.insert(0, os.path.join(_paths.ROOT, 'k4'))
sys.path.insert(0, os.path.join(_paths.ROOT, 'k4', 'c4_verify_H'))
import lb4r as M
import rulef_model as RM
from sdclib import Enc
from sdc_orders import sd, completable
from sdc_need import instances, rule_order


def state_from_picks(inst, Y):
    base = [-1] * inst.m; pick = [-1] * inst.n
    for i, g in enumerate(Y):
        if g is not None:
            base[g] = i; pick[i] = g
    return (tuple(base), tuple(pick), tuple([False] * inst.n))


def certify(inst, Y):
    s0 = state_from_picks(inst, Y)
    res = {}
    for pol in ('shrink', 'envyFree', 'none'):
        s, _ = M.up_run(inst, s0, pol) if pol != 'none' else (s0, [])
        res['O_' + pol] = bool(M.any_output(inst, s, 'bundle'))
        d = RM.deficit_K(inst, s)
        res['K_' + pol] = d <= 0
    return res


if __name__ == '__main__':
    R1 = '--nor1' not in sys.argv
    if not R1: sys.argv.remove('--nor1')
    src = sys.argv[1]; C = collections.Counter()
    print('$ python3 k4/sdc/nof_lemmak.py', *sys.argv[1:], '' if R1 else '--nor1')
    if src.startswith('cores:'):
        import json, gzip, random
        N, seed = int(sys.argv[2]), int(sys.argv[3]); rng = random.Random(seed); items = []
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        from de4lib import random_profile
        os.chdir(cwd)
        cores = []
        for fn in src[6:].split(','):
            cores += [c['sets'] for c in json.load(gzip.open(os.path.join(_paths.ROOT, 'results', fn)))['cores']]
        for t in range(N):
            sets = rng.choice(cores); items.append(('r%d' % t, sets, random_profile(sets, rng), 1 + max(max(x) for x in sets)))
    else:
        items = instances(src)
    for name, sets, vals, m in items:
        if len(sets) > 9: continue
        E = Enc(sets, vals, m); inst = RM.make_inst(sets, vals)
        Y0, pi = rule_order(E, 'need2', R1)
        cands = [('plain', Y0)] + [('defer %d' % o, sd(E, [i for i in pi if i != o] + [o])[0]) for o in pi]
        C['instances'] += 1
        ext_plain = completable(E, Y0)
        r0 = certify(inst, Y0)
        for k, v in r0.items(): C['plain: ' + k] += v
        C['plain: extends'] += ext_plain
        C['plain extends but no LB4r Output (any policy)'] += ext_plain and not any(r0[k] for k in r0 if k.startswith('O_'))
        C['plain extends but Lemma K fails (every policy)'] += ext_plain and not any(r0[k] for k in r0 if k.startswith('K_'))
        okO = any(v for k, v in r0.items() if k.startswith('O_')) or any(any(v for k, v in certify(inst, Y).items() if k.startswith('O_')) for _, Y in cands[1:])
        C['some candidate has an LB4r Output'] += okO
        if not okO: print('NO LB4r OUTPUT FOR ANY CANDIDATE', name, flush=True)
    for k in sorted(C, key=str): print(k, C[k])
