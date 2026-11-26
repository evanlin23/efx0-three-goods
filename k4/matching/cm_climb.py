"""Adversarial climb against Conjecture CM (k4/matching.md §3).

State: a strict connected k = 4 core (k4/sdc/oc1max_climb.is_core; MC2 forbids two private goods; LOOSE=1 any
instance with 2..4 goods per agent).  For every distinct maximum-matching pick vector that is one-absorber-hard
(raw), count the CM witnesses (P, H0, o): official chain P from a dangerous agent, improving H0, owner o, with
exchange deficiency d_o <= s_o (exchange.ex_value), up to CAP.  Score (maximized):
    10000 * (hard starts violating OC1) + 1000 * (hard starts with no CM witness)
    + sum over hard starts of (2 CAP - witnesses) + (frozen agents whose junk beats their pick) / 10
With SEEDFILES=a.jsonl,b.jsonl (rows of hard_starts.py) each run starts from a random seed instance that passes the
core test (use LOOSE=1 for non-core seeds); otherwise from a random core (k4/sdc/oc1_mc2_rand.gen).
A start with no witness is printed with its OC1 status (raw: does some official move reach a one-absorber completion).
Mutations as in k4/sdc/oc1max_climb.py; accept if the score does not drop.

    python3 k4/matching/cm_climb.py RUNS STEPS SEED NMIN NMAX [MC2]"""
import sys, os, json, random, itertools, collections, time, multiprocessing as mp
import _mpaths  # noqa: F401
from mlib import M, subsets
from exchange import general_chains, apply_chain, ex_value
from oc1max_climb import is_core, mutate
from oc1_mc2_rand import gen

CAP = int(os.environ.get('CAP', '6'))
SEEDS = [json.loads(l) for f in os.environ.get('SEEDFILES', '').split(',') if f for l in open(f)]


def witnesses(I, base, cap):
    J = I.junk(base); fz = set(I.frozen(base)); Y = [b[0] if b else None for b in base]; w = 0
    for P, Hs in general_chains(I, base):
        k, xt = P[0], P[-1]; used = set(g for h in Hs.values() for g in h)
        Pi = [g for g in J if g not in used] + [Y[xt]]
        for H0 in subsets([g for g in Pi if g in I.R[k]], 1):
            if I.V(k, H0) <= I.V(k, base[k]) or (xt in fz and Y[xt] not in H0): continue
            Bp = apply_chain(I, base, P, list(H0), Hs)
            for o in range(I.n):
                d, s, _, _ = ex_value(I, base, P, Bp, o)
                if d <= s:
                    w += 1
                    if w >= cap: return w
    return w


def evaluate(sets, vals):
    I = M(sets, vals); N = I.nu(); score = 0; bad = []
    for Y in set(I.sd(o) for o in itertools.permutations(range(I.n))):
        if sum(1 for y in Y if y is not None) != N: continue
        if any(Y[i] is None for i in range(I.n) if I.sets[i]): continue     # perfect starts only
        base = [[g] if g is not None else [] for g in Y]
        J = I.junk(base)
        score += sum(1 for x in I.dangerous(base) if I.V(x, J) > I.V(x, base[x])) / 10.0   # hardness proxy
        if I.complete(base, 0, 'oa') is not None: continue
        score += CAP
        w = witnesses(I, base, CAP); score += CAP - w
        if w == 0:
            oc1 = any(I.complete(b, 0, 'oa') is not None for b in I.moves(base))
            score += 1000 if oc1 else 10000; bad.append((Y, oc1))
    return score, bad


def run(args):
    steps, seed, n, mc2 = args
    rng = random.Random(seed)
    if SEEDS:
        while True:
            r = rng.choice(SEEDS); sets, vals = r['sets'], r['vals']
            if is_core(sets, vals, mc2): break
    else:
        while True:
            try: sets, vals = gen(n, rng)
            except ValueError: continue
            if is_core(sets, vals, mc2): break
    best, bad = evaluate(sets, vals); found = []
    for _ in range(steps):
        mu = mutate(sets, vals, rng)
        if mu is None or not is_core(*mu, mc2): continue
        sc, bd = evaluate(*mu)
        if bd: found.append((mu[0], mu[1], bd))
        if sc >= best: (sets, vals), best = mu, sc
    return seed, best, sets, vals, found


if __name__ == '__main__':
    RUNS, STEPS, SEED, NMIN, NMAX = map(int, sys.argv[1:6]); MC2 = len(sys.argv) > 6 and sys.argv[6] == 'MC2'
    print('$ python3 k4/matching/cm_climb.py', *sys.argv[1:], '(CAP=%d LOOSE=%s)' % (CAP, os.environ.get('LOOSE', '0')),
          flush=True)
    t0 = time.time(); C = collections.Counter()
    tasks = [(STEPS, SEED * 7919 + t, NMIN + t % (NMAX - NMIN + 1), MC2) for t in range(RUNS)]
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for seed, best, sets, vals, found in pool.imap_unordered(run, tasks):
            C['runs'] += 1
            print('run seed=%d n=%d score=%d %s' % (seed, len(sets), best, json.dumps((sets, vals))), flush=True)
            seen = set()
            for s2, v2, bd in found:
                key = json.dumps((s2, v2))
                if key in seen: continue
                seen.add(key)
                for Y, oc1 in bd:
                    C['CM failures' + (' (OC1 holds)' if oc1 else ' (OC1 FAILS)')] += 1
                    print('CM FAILS', json.dumps({'sets': s2, 'vals': v2, 'picks': Y, 'OC1': oc1}), flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
