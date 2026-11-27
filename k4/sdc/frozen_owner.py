"""A frozen owner (k4/sdc.md §27).  LB4r's Output forbids an owner whose base is one good that another agent needs
(lb4r.build_model returns None; output_check's 'fr[o]').  Drop that condition: search every owner o, frozen or not,
by brute force over the junk (o takes any number, the others their LB4r caps) for an allocation that is EFX0, checked
directly (rulef_model.check_efx0).  Question: at the plain
neediest-first start after envy-free upgrades, does a frozen-owner output exist when LB4r's does not, and is every
such allocation EFX0?  Also: do the bases extend at all (any placement of the junk, no caps)?

    python3 k4/sdc/frozen_owner.py screen|suite|special|cores:FILES N SEED"""
import sys, os, json, gzip, random, collections, time, itertools
import _paths
from sdclib import Enc
from sdc_need import instances, rule_order
from blocks4 import M, RM
from nof_var import SPECIAL
from rd_check import state_of


def frozen_owner_output(inst, s, o):
    """Brute force over every map of the junk to the agents: owner o keeps its base and takes any junk, every other
    agent keeps its base and takes at most its LB4r cap (0 if its base is one good another agent other than o needs,
    else 2 - |base|); returns the first such allocation that is EFX0 (rulef_model.check_efx0), or None.  With o not
    frozen this is a relaxation of LB4r's Output only in that pairs of non-owners are checked directly."""
    needs = M.all_needs(inst, s)
    bases = [M.base_of(inst, s, i) for i in range(inst.n)]
    J = [g for g in range(inst.m) if s[0][g] == -1]
    cap = []
    for j in range(inst.n):
        if j == o: cap.append(len(J)); continue
        NAo = set().union(*[needs[i] for i in range(inst.n) if i != j])
        cap.append(0 if (len(bases[j]) == 1 and bases[j][0] in NAo) else max(0, 2 - len(bases[j])))
    X = list(s[0])
    for assign in itertools.product([j for j in range(inst.n) if cap[j] > 0], repeat=len(J)):
        cnt = collections.Counter(assign)
        if any(cnt[j] > cap[j] for j in cnt): continue
        for g, a in zip(J, assign): X[g] = a
        if RM.check_efx0(inst, X): return list(X)
    return None


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/frozen_owner.py', *sys.argv[1:], flush=True)
    if src == 'special': items = SPECIAL
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
        if len(sets) > 9: continue
        E = Enc(sets, vals, m); v = [[0] * m for _ in sets]
        for i, (S, V) in enumerate(zip(sets, vals)):
            for g, x in zip(S, V): v[i][g] = x
        inst = M.Inst(v)
        Y, pi = rule_order(E, 'need2', False)
        s = M.up_run(inst, state_of(inst, Y), 'envyFree')[0]
        C['instances'] += 1
        if M.any_output(inst, s, 'bundle'): continue
        C['no LB4r output at the start'] += 1
        found = []
        for o in range(inst.n):
            X = frozen_owner_output(inst, s, o)
            if X is not None:
                ef = RM.check_efx0(inst, X)
                C['relaxed owner step: owners with an EFX0 allocation'] += 1
                C['relaxed owner step: of these, EFX0 (always, by construction)'] += ef
                if ef: found.append(o)
                elif C['shown bad'] < 3:
                    C['shown bad'] += 1; print('NOT EFX0', name, json.dumps((sets, vals)), 'owner', o, 'X', X, flush=True)
        C['relaxed owner step (any owner, frozen or not, caps kept): some EFX0 allocation'] += bool(found)
        # any junk placement at all (bases kept, no caps)
        J = [g for g in range(inst.m) if s[0][g] == -1]; X = list(s[0]); anyX = None
        for assign in itertools.product(range(inst.n), repeat=len(J)):
            for g, a in zip(J, assign): X[g] = a
            if RM.check_efx0(inst, X): anyX = list(X); break
        C['the bases extend (any junk placement, no caps)'] += anyX is not None
        if anyX is not None:
            sizes = sorted((sum(1 for g in range(inst.m) if anyX[g] == i) for i in range(inst.n)), reverse=True)
            C['  first extension found: bundle sizes %s' % sizes] += 1
        if not found: print('NONE', name, json.dumps((sets, vals)), 'extends' if anyX else 'no extension', flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
