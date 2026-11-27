"""Search for a VM1 counterexample that is a connected k = 4 core (k4/vm.md section 7.3), starting from a non-core
VM1 failure (attempts/k4-vm-vm1-noncore.md).  Random mutations (re-draw one agent's values; swap one good of one
agent for another good, existing or new; add a good to an agent with < 4) are kept when the score does not get
worse: from a failing start the walk stays among VM1 failures (margin (0, 0.0) of vmx2_climb.vm1_score, within its
caps) and accepts a mutation when the number of is_core4 violations does not grow.  Goal: a failure with 0
violations.
With --chain the walk keeps going inside the failing cores (no early stop) and tests Conjecture VM1-chain
(vm1_chain.one) at every accepted state; it reports the failing cores visited and any VM1-chain failure.
EVIDENCE only; a hit must be re-checked uncapped (vm1_verify.py) and by an independent replay.
    python3 k4/vm/vm1_core_repair.py JSON STARTS STEPS SEED [--chain]"""
import sys, os, json, random, time, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'c4_verify_H'))
import vmlib as V
import vmx2_climb as C
from hcore import is_core4


def compact(sets):
    used = sorted(set(g for S in sets for g in S)); mp_ = {g: k for k, g in enumerate(used)}
    return [[mp_[g] for g in S] for S in sets]


def score(sets, vals):
    m = 1 + max(max(S) for S in sets)
    viol = len(is_core4(C.dense(sets, vals, m)))
    return C.vm1_score(sets, vals), viol


CHAIN = ['--chain' in sys.argv]


def walk(args):
    J, steps, seed = args
    V.FREE_Z[0] = True
    rng = random.Random(seed); sets, vals = [list(s) for s in J['sets']], [list(w) for w in J['vals']]
    best = score(sets, vals); hit = None; cores = set(); chain_fail = []
    for t in range(steps):
        S2 = [list(x) for x in sets]; W2 = [list(x) for x in vals]; i = rng.randrange(len(S2)); r = rng.random()
        if r < 0.5:
            W2[i] = rng.sample(range(1, 31), len(S2[i]))
        elif r < 0.85:
            m = 1 + max(max(x) for x in S2); k = rng.randrange(len(S2[i])); new = rng.randrange(m + 1)
            if new in S2[i]: continue
            S2[i][k] = new; S2 = compact(S2)
        else:
            if len(S2[i]) >= 4: continue
            m = 1 + max(max(x) for x in S2); new = rng.randrange(m + 1)
            if new in S2[i]: continue
            S2[i].append(new); W2[i].append(rng.randrange(1, 31)); S2 = compact(S2)
        if max(len(s) for s in S2) > 4: continue
        sc = score(S2, W2)
        fail_old = best[0] == (0, 0.0); fail_new = sc[0] == (0, 0.0)
        if (fail_new and (not fail_old or sc[1] <= best[1])) or (not fail_old and not fail_new and sc <= best):
            sets, vals, best = S2, W2, sc
            if fail_new and sc[1] == 0:
                hit = (sets, vals)
                if not CHAIN[0]: break
                k = json.dumps([sets, vals])
                if k not in cores:
                    cores.add(k)
                    import vm1_chain as Ch
                    r = Ch.one(('w', sets, vals, 1 + max(max(x) for x in sets)))
                    V.FREE_Z[0] = True
                    if r[3] == 'FAIL': chain_fail.append(r[4])
    if CHAIN[0]:
        return seed, sets, vals, best, hit, len(cores), chain_fail
    return seed, sets, vals, best, hit


if __name__ == '__main__':
    J = json.loads(sys.argv[1]); starts, steps, seed = map(int, sys.argv[2:5])
    print('$ python3 k4/vm/vm1_core_repair.py', ' '.join(sys.argv[1:])); t0 = time.time()
    with mp.Pool(os.cpu_count()) as pool:
        res = pool.map(walk, [(J, steps, seed * 1000 + s) for s in range(starts)])
    if CHAIN[0]:
        print('walks', len(res), '; distinct failing cores visited (VM1 fails):', sum(r[5] for r in res),
              '; VM1-chain failures among them:', sum(len(r[6]) for r in res))
        for r in res:
            for js in r[6]: print('  VM1-CHAIN FAIL', js)
        print('time %.0f s' % (time.time() - t0)); sys.exit(0)
    res.sort(key=lambda r: (r[3][0] != (0, 0.0), r[3][1]))
    print('walks', len(res), '; failing cores found:', sum(1 for r in res if r[4]))
    for sd, sets, vals, best, hit in res[:6]:
        m = 1 + max(max(S) for S in sets)
        print('  %s violations %d %s' % ('VM1 FAILS' if best[0] == (0, 0.0) else 'margin %s' % (best[0],), best[1],
                                         json.dumps({'sets': sets, 'vals': vals, 'm': m})))
    print('time %.0f s' % (time.time() - t0))
