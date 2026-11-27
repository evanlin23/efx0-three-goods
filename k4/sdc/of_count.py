"""Lemma OF candidate (k4/sdc.md §18): the owner-free count of the neediest-first run closes.  For the picks of the
neediest-first order (--r1: with R1 priority), LB4r's state after need-shrinking upgrades (or no upgrades: --none):
threats from the unpicked goods J alone (blocks4j.py), slot places of every agent counted, and
    D = S - need_J,   need_J = least Lemma K service of the J-threatened agents (sharing allowed).
OF says D >= 0: the junk could be handed out if some agent with an empty base, valued by nobody, took the rest.

    python3 k4/sdc/of_count.py screen|suite|special|files|cores:FILES N SEED [--r1] [--none]"""
import sys, os, json, gzip, random, collections, time
R1 = '--r1' in sys.argv; NONE = '--none' in sys.argv
sys.argv = [a for a in sys.argv if a not in ('--r1', '--none')]
import _paths
from sdclib import Enc
from sdc_need import instances, rule_order
import blocks4j as BJ
import blocks4 as B4
from blocks4 import M
from nof_var import SPECIAL
from rd_check import state_of

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/of_count.py', *sys.argv[1:], '--r1' if R1 else '', '--none' if NONE else '', flush=True)
    if src == 'special': items = SPECIAL
    elif src == 'files':
        sys.path.insert(0, os.path.join(_paths.ROOT, 'k4'))
        R = os.path.join(_paths.ROOT, 'results', 'k4_de4'); items = []
        for f in ['robust_failures.json', 'refute_lp_instance.json', 'refute_rob_instance.json', 'shed_failures_found.json',
                  'shed2_near.json', 'unclean_cycles.json']:
            d = json.load(open(os.path.join(R, f)))
            if isinstance(d, dict): d = d.get('instances', [])
            for t, e in enumerate(d):
                sets, vals = (e['sets'], e['vals']) if isinstance(e, dict) else (e[0], e[1])
                items.append(('%s#%d' % (f, t), sets, vals, 1 + max(max(x) for x in sets)))
    elif src.startswith('cores:'):
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
        if len(sets) > 12: continue
        E = Enc(sets, vals, m); v = [[0] * m for _ in sets]
        for i, (S, V) in enumerate(zip(sets, vals)):
            for g, x in zip(S, V): v[i][g] = x
        inst = M.Inst(v)
        s = state_of(inst, rule_order(E, 'need2', R1)[0])
        if not NONE: s = M.up_run(inst, s, 'shrink')[0]
        needs = M.all_needs(inst, s)
        opts, capK = BJ.options_J(inst, s, needs)
        C['instances'] += 1
        if any(not ox for ox in opts.values()):
            C['some J-threatened agent has no option'] += 1; print('NO OPTION', name, json.dumps((sets, vals)), flush=True); continue
        D = sum(capK) - B4.min_service(list(opts.items()))
        C['D = %d' % D if D < 3 else 'D >= 3'] += 1
        if D < 0: print('OF FAILS', name, 'D', D, json.dumps((sets, vals)), flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
