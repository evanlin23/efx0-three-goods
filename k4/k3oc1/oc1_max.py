"""OC1 at maximum-matching starts at k = 3 (OC1^max, k4/sdc.md §31): the drafts whose picks match nu agents, nu the
maximum matching size of the agent / relevant-good graph (perfect starts: every agent picks).  For each such draft:
does it have a one-absorber completion (lbtest.lb2, exact on DE states), else does one DE trade give one (OT1), else
does one improving move of k4/sdc.md §29 give one (k3lib.chains: additions, chains, rings; a chain never passes an
empty-handed agent, the official rule; exact completion: lb2 on DE states, exhaustive search otherwise)?  Also: does
every least-omega DE trade give one?
    python3 k4/k3oc1/oc1_max.py small:N|certs:N|gen:N:DEAD [SHARD NSHARDS]"""
import sys, os, json, itertools, collections, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, completion, chains, vals, bundles
from de_moves import de_trades
from lbtest import lb2, parts
from oc1_fast import drafts
from oc1_k3 import hypergraphs, profiles

def nu(sets):
    match = {}
    def aug(i, seen):
        for g in sets[i]:
            if g in seen: continue
            seen.add(g)
            if g not in match or aug(match[g], seen):
                match[g] = i; return True
        return False
    return sum(1 for i in range(len(sets)) if aug(i, set()))

def is_de(rk, st):
    return all(not B or (len(B) == 1 and B[0] in rk[i]) or set(B) == {rk[i][1], rk[i][2]} for i, B in enumerate(bundles(st, len(rk))))

def exact(rk, m, st, V):
    if is_de(rk, st): return bool(lb2(rk, m, st))
    return completion(rk, m, st, 1, V) is not None

def sources(src, rng=None):
    if src.startswith('gen:'):
        from gen_all import gen
        from oc1_general import canon
        _, n, dead = src.split(':'); n, dead = int(n), int(dead); reps = {}
        for sets, m in gen(n): reps.setdefault(canon(sets, n), (sets, m))
        for k in sorted(reps): yield reps[k][0], reps[k][1] + dead
    elif src.startswith('mixed:'):   # mixed:N:DEAD -- statement (P)'s class: agents valuing 1-3 goods (perfect_small)
        from perfect_small import gen_mixed, canon
        _, n, dead = src.split(':'); n, dead = int(n), int(dead); reps = {}
        for sets, m in gen_mixed(n): reps.setdefault(canon(sets, n), (sets, m))
        for k in sorted(reps): yield reps[k][0], reps[k][1] + dead
    else:
        yield from hypergraphs(src, rng)

if __name__ == '__main__':
    src = sys.argv[1]; shard, nsh = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (0, 1)
    C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/k3oc1/oc1_max.py', *sys.argv[1:], flush=True)
    for ci, (sets, m) in enumerate(sources(src)):
        if ci % nsh != shard: continue
        n = len(sets); v = nu(sets); C['hypergraphs'] += 1
        for rk in profiles(sets, 0, None):
            C['profiles'] += 1
            for Y in drafts(rk, n):
                npk = sum(1 for g in Y if g is not None)
                if npk != v: continue
                kind = 'perfect' if v == n else 'maximum, not perfect'
                C[kind + ' drafts'] += 1
                b = base_of(Y, m)
                if lb2(rk, m, b): continue
                C[kind + ': hard'] += 1
                mv = de_trades(rk, m, b); ok = [bool(lb2(rk, m, nb)) for nb, d in mv]
                if any(ok):
                    om = [(lambda P: len(P[1]) - len(P[5]))(parts(rk, m, nb)) for nb, d in mv]
                    if not all(o for o, w in zip(ok, om) if w == min(om)):
                        C[kind + ': every least-omega DE trade: FAILS'] += 1
                        print('OMEGAFAIL', kind, json.dumps([list(r) for r in rk]), m, 'picks', Y, flush=True)
                    continue
                V = vals(rk)
                g = any(exact(rk, m, nb, V) for nb, d in chains(rk, m, b, V))
                C[kind + ': no DE trade; one move repairs %s' % g] += 1
                print('NODE' if g else 'OC1MAXFAIL', kind, json.dumps([list(r) for r in rk]), m, 'picks', Y, flush=True)
        if ci % 50 == 0: print('core', ci, dict(C), '%.0f s' % (time.time() - t0), flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
