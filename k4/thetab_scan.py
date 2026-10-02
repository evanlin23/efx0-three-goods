#!/usr/bin/env python3
"""Theorems W, K and Corollary G1 (with Lemma G) of k4/thetab.md at every def > 0 state with f = 1 (workstream
proof/k4-thetab).

For every profile of the input with f = 1 and omega >= 1 and every min-frozen P with def(P) > 0:
  - setting (H) (exactly two needers of the frozen good g, both big-top on g) or not, and the stage of P: 'T3stage'
    (no (T1) or (T2) move lowers def; at f = 1 there is no (T4) move), 'T1stuck' (no (T1) move does) or 'other';
    states with two or more needers are recorded when in (H) (every stage) or at the T3 stage;
  - the first of Theorem W, Theorem K, Corollary G1 with a plain swap ('G1'), Corollary G1 with one helper ('G1h')
    whose hypotheses hold (k4/thetab_lib.theorems); every conclusion is asserted against the exact deficits, and
    Corollary N3 (W applies) at every n = 3 state in (H);
  - whether some plain swap lowers the deficit (exact), and whether Lemma G (value form, least removal set computed,
    k4/thetab_lib.lemma_g) certifies a plain swap or else a swap with one helper that lowers it (bounds asserted);
  - at a T3-stage state where no plain swap lowers the deficit: whether any (T3) move does (if none: a failure of the
    T3 stage, i.e. of DL_RT4 at f = 1, printed as T3-STAGE-FAILURE);
  - at the states whose frozen good has one needer: whether G1 or G1h applies (conclusion asserted).
usage: python3 k4/thetab_scan.py catalog FILE [--every=E] [--off=O]    (FILE in k4/suite/.cache/gapbench/results/k4_gap)
       python3 k4/thetab_scan.py hunt SEED N [--nmin=4] [--nmax=5] [--tlim=SECONDS]   (structured random instances)
       python3 k4/thetab_scan.py twin SEED N [...]     (the same, two needers with the same goods: gen_twin)
       python3 k4/thetab_scan.py suite | certs FILE --rand=K [--seed=S]               (as k4/dl2_relations.py)"""
import random, sys, time
from thetab_lib import *


# ------------------------------------------------------------------ the structured generator of the hunt
def bal_vals(rng, k, top_first=False, bt=None):
    """k distinct values in 1..15, strictly balanced, strict (distinct subset sums); values[0] is the top if
    top_first; bt (k = 4): True big-top, False not big-top, None either"""
    for _ in range(1000):
        vs = rng.sample(range(1, 16), k)
        vs.sort(reverse=True)
        if not vs[0] < sum(vs[1:]): continue
        if k == 4 and bt is not None and (vs[0] > vs[1] + vs[2]) != bt: continue
        sums = [sum(c) for r in range(1, k + 1) for c in itertools.combinations(vs, r)]
        if len(set(sums)) != len(sums): continue
        if not top_first: rng.shuffle(vs)
        return vs
    return None


def gen(rng, n):
    """agents 0 (x: top 0, three or two lower goods), 1, 2 (big-top on good 0), and n - 3 others on random goods
    (old or new, good 0 with probability 0.15); kept only if it is a strict connected k = 4 core (checked by the
    caller)"""
    nxt = [1]

    def new():
        q = nxt[0]; nxt[0] += 1; return q
    L1 = [new(), new(), new()]
    if rng.random() < 0.3: L2 = list(L1)
    else:
        L2 = list(dict.fromkeys(q if rng.random() < 0.4 else new() for q in L1))
        while len(L2) < 3: L2.append(new())
    old = lambda: list(range(1, nxt[0]))
    kx = 3 if rng.random() < 0.85 else 2
    Lx = []
    while len(Lx) < kx:
        q = rng.choice(old()) if rng.random() < 0.5 else new()
        if q not in Lx: Lx.append(q)
    sets = [[0] + Lx, [0] + L1, [0] + L2]
    for _ in range(n - 3):
        k = rng.choice([3, 4]); S = []
        while len(S) < k:
            r = rng.random()
            q = 0 if r < 0.15 else (rng.choice(old()) if r < 0.75 else new())
            if q not in S: S.append(q)
        sets.append(S)
    vals = [bal_vals(rng, kx + 1, True, (rng.random() < 0.2) if kx == 3 else None),
            bal_vals(rng, 4, True, True), bal_vals(rng, 4, True, True)]
    vals += [bal_vals(rng, len(S)) for S in sets[3:]]
    if any(v is None for v in vals): return None
    return {'sets': sets, 'vals': vals, 'm': nxt[0]}


def gen_twin(rng, n):
    """the configuration of attempts/k4-thetab-plain-swap-t3-stage.md (no plain swap at a T3-stage state): two big-top
    needers with the same goods {0, 1, 2, 3} (g = 0), x = {0, p, q, r} with p, q private (new goods) and r shared with
    the third agents, which take r and old or new goods (never good 0)"""
    sets = [[0, 4, 5, 6], [0, 1, 2, 3], [0, 1, 2, 3]]
    nxt = [7]

    def new():
        q = nxt[0]; nxt[0] += 1; return q
    for t in range(n - 3):
        k = rng.choice([3, 4]); S = [6] if t == 0 or rng.random() < 0.5 else []
        while len(S) < k:
            q = rng.choice([1, 2, 3, 6] + list(range(7, nxt[0]))) if rng.random() < 0.5 else new()
            if q not in S: S.append(q)
        sets.append(S)
    perm = rng.sample(range(3), 3)                    # which of x's lower goods is p, q, r (values)
    vx = bal_vals(rng, 4, True, None)
    if vx is None: return None
    vals = [[vx[0]] + [vx[1 + perm[i]] for i in range(3)], bal_vals(rng, 4, True, True), bal_vals(rng, 4, True, True)]
    vals += [bal_vals(rng, len(S)) for S in sets[3:]]
    if any(v is None for v in vals): return None
    return {'sets': sets, 'vals': vals, 'm': nxt[0]}


def hunt_items(seed, N, nmin, nmax, tlim, twin=False):
    rng = random.Random(seed); t0 = time.time()
    for it in range(N):
        if time.time() - t0 > tlim: return
        d = (gen_twin if twin else gen)(rng, rng.randint(nmin, nmax))
        if d is None: continue
        I = M.Inst(d['sets'], d['vals'], d['m'])
        if I.core_violations() or not I.strict(): continue
        yield d, 'hunt:%d:%d' % (seed, it)


# ------------------------------------------------------------------ the checks at one state
def plain_exact(pr, ctx):
    """some plain swap (any frozen x, any free needer z, any admissible A ⊆ J ∪ B_z) lowers the deficit (exact)"""
    P, Bs = ctx.P, ctx.Bs
    for x in range(ctx.I.n):
        if not P.frozen[x]: continue
        for z in ctx.free_needers(x):
            for A in ctx.admissible(x, P.J | Bs[z]):
                if pr.D[ctx.new(x, z, A)] < ctx.D: return True
    return False


def run(items, label):
    cnt = collections.Counter(); ex = {}
    for d, src in items:
        cnt['profiles'] += 1
        pr = Profile(d)
        if not pr.ok or pr.I.f != 1: continue
        cnt['profiles with f = 1, omega >= 1'] += 1
        I = pr.I
        for Bs in pr.mp:
            if pr.D[Bs] <= 0: continue
            ctx = Ctx(pr, Bs)
            x, g, nd, third = setting(ctx)
            if len(nd) < 2:
                # one needer: W and K need (H); only Corollary G1 (plain or with a helper) can apply, asserted
                thm = theorems(pr, ctx, src)
                cnt[('n=%d' % I.n, 'one needer', 'G1 or G1h applies' if thm != '-' else 'G1 does not apply')] += 1
                continue
            H = in_H(ctx)
            kopt = ctx.key_optimal()
            st = 'T3stage' if kopt else ('T1stuck' if not pr.t1_moves(Bs) else 'other')
            if not H and st != 'T3stage': continue
            typ = '(H)' if H else 'needers ' + '+'.join(sorted(ntype(I, y) for y in nd))
            thm = theorems(pr, ctx, src)
            if H and I.n == 3:
                assert thm == 'W', ('Corollary N3: the hypotheses of Theorem W fail at n = 3', src, Bs, gw1_hyp(ctx))
            exact = plain_exact(pr, ctx)
            cert = 'Lemma G certifies a plain swap' if g_certificates(ctx, pr, plain_moves(ctx), ctx.D) else (
                'Lemma G certifies a swap with helper' if g_certificates(ctx, pr, helper_moves(ctx), ctx.D)
                else 'Lemma G certifies none')
            res = 'plain swap' if exact else 'NO plain swap'
            if not exact and st == 'T3stage':
                if pr.t3_moves(Bs): res += ', a (T3) move with helper'
                else:
                    res += ', NO (T3) MOVE'
                    print('T3-STAGE-FAILURE', src, json.dumps(d), [sorted(bits(B)) for B in Bs], flush=True)
            cnt[('n=%d' % I.n, typ, st, 'theorem ' + thm, cert, res)] += 1
            if thm == '-' or not exact or cert == 'Lemma G certifies none':
                k2 = ('n=%d' % I.n, typ, st, thm, cert, res)
                cand = (I.n, I.m, src, d, [sorted(bits(B)) for B in Bs])
                if k2 not in ex or cand[:2] < ex[k2][:2]: ex[k2] = cand
    print('# input', label)
    for k in sorted(cnt, key=str): print('  %-130s %d' % (' | '.join(map(str, k)) if isinstance(k, tuple) else k, cnt[k]))
    print('smallest state per uncovered cell (no theorem, no certificate, or no plain swap):')
    for k, v in sorted(ex.items(), key=str):
        print('  %s: n=%d m=%d %s %s P=%s' % (' | '.join(map(str, k)), v[0], v[1], v[2], json.dumps(v[3]), v[4]))
    print('no assertion failed', flush=True)


def main(argv):
    print('# command: python3 k4/thetab_scan.py ' + ' '.join(argv), flush=True)
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    args = [a for a in argv if not a.startswith('--')]
    if args[0] == 'catalog':
        recs = json.load(gzip.open(os.path.join(GAP, args[1]), 'rt'))['records']
        recs = recs[int(opt.get('off', 0))::int(opt.get('every', 1))]
        items = (({'sets': r['core']['sets'], 'vals': r['vals'], 'm': r['core']['m']},
                  '%s:%s[m=%d,idx=%d]:%s' % (args[1], r['core']['file'], r['core']['m'], r['core']['idx'],
                                             ','.join(map(str, r['prof'])))) for r in recs)
    elif args[0] in ('hunt', 'twin'):
        items = hunt_items(int(args[1]), int(args[2]), int(opt.get('nmin', 4)), int(opt.get('nmax', 5)),
                           float(opt.get('tlim', 1e9)), twin=args[0] == 'twin')
    else:
        from dl2_relations import items_of
        items = items_of(args[0], args[1:], opt)
    run(items, ' '.join(argv))


if __name__ == '__main__':
    main(sys.argv[1:])
