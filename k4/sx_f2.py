#!/usr/bin/env python3
"""Lemma A⁺ of k4/sx.md §6 (the owner swap along a need chain of frozen agents, one (T3⁺) move) at f >= 2, and the
structure of the configurations maximizing (r', Λ') at the non-completable keys (workstream proof/k4-sx). EVIDENCE.

For every profile of the input with f >= 2 and omega >= 1, every key κ with def*(κ) > 0, and every configuration Q at κ
maximizing (r', Λ') (r' = robust free agents, v_y(Q_y) >= v_y(U_y \\ Q_y) with U_y = R_y \\ 𝒩; Λ' = sum of the free
agents' levels over R_y), the tool records whether a free-valid owner exists (Q_o ∪ L threatens no free agent), how many
frozen agents its bundle threatens, whether some (T3⁺) move from P_Q reaches a state with def < def*(κ), and whether
Lemma A⁺ applies: a free-valid o whose bundle X_o threatens exactly one agent, the frozen x, and a need chain
x = w_0, w_1, ..., w_j of frozen agents (w_i needs phi(w_{i-1})) with o needing phi(w_j), and
theta_o(X_o) <= v_o(phi(w_j)). When it applies, the configuration in which w_i holds phi(w_{i-1}), o holds phi(w_j),
x holds a pair inside X_o with admissible part and owns X_o is built and asserted to be a configuration at its key with x
a valid owner with C = ∅, and its state to have deficit <= 0.

usage: python3 k4/sx_f2.py DUMP.jsonl.gz ... | --inst FILE.json (a list of {sets, vals, m})  [--examples=K]"""
import collections, gzip, itertools, json, os, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, 'suite'))
import model as M
from model import bits, pc, mask
from sx_keygraph import KeyProfile, keyof


def analyse_key(kp, k, cnt, ex, nex):
    I = kp.I
    F = [i for i in range(I.n) if k[i] is not None]
    Nm = mask(k[i] for i in F)
    free = [i for i in range(I.n) if k[i] is None]
    U = {y: I.R[y] & ~Nm for y in range(I.n)}
    cs = I.configs([k])
    lev = lambda c: sum(I.level(y, c.Q[y] & I.R[y]) for y in free)
    rob = lambda c: sum(1 for y in free if c.robust(y))
    best = max((rob(c), lev(c)) for c in cs)
    mx = [c for c in cs if (rob(c), lev(c)) == best]
    ds = kp.dstar[k]
    cnt['keys f=%d' % I.f] += 1
    keyok = False
    for c in mx:
        cnt['Zmax'] += 1
        Bs = tuple((1 << k[i]) if k[i] is not None else (c.Q[i] & U[i]) for i in range(I.n))
        P = kp.PA[Bs]
        X = {o: c.Q[o] | c.L for o in free}
        V = [o for o in free if not any(I.threat(y, X[o], c.hv(y)) for y in free if y != o)]
        cnt['Zmax: free-valid owner exists=%s' % bool(V)] += 1
        for o in V:
            thr = [x for x in F if I.threat(x, X[o], c.hv(x))]
            cnt['free-valid owner: frozen agents threatened=%d' % len(thr)] += 1
        direct = [m for m in kp.t3plus_moves(Bs) if kp.D[m[0]] < ds]
        d4 = [b2 for b2 in kp.t4_moves(Bs) if kp.D[b2] < ds]
        cnt['Zmax: direct T3 move=%s, direct T3+ move=%s, direct T4 move=%s' % (
            any(not m[3] for m in direct), bool(direct), bool(d4))] += 1
        # Lemma A+
        succ = {w: [v for v in F if v != w and P.N[v] & Bs[w]] for w in F}   # w -> v: v needs phi(w)
        ok = False
        for o in V:
            thr = [x for x in F if I.threat(x, X[o], c.hv(x))]
            if len(thr) != 1: continue
            x = thr[0]
            # need chains from x through frozen agents to a frozen w_j whose good o needs
            chains = []
            def walk(path):
                w = path[-1]
                if P.N[o] & Bs[w]: chains.append(list(path))
                for v in succ[w]:
                    if v not in path: walk(path + [v])
            walk([x])
            for ch in chains:
                gl = Bs[ch[-1]]
                if I.threat(o, X[o], I.val(o, gl)): cnt['A+ chain found but theta fails'] += 1; continue
                # build the configuration
                key2 = list(k); key2[x] = None
                for i in range(1, len(ch)): key2[ch[i]] = k[ch[i - 1]]
                key2[o] = next(bits(gl)); key2 = tuple(key2)
                Q2 = {y: c.Q[y] for y in free if y != o}
                pair = None
                for pr in itertools.combinations(list(bits(X[o])), 2):
                    p2 = mask(pr)
                    if p2 & U[x] and I.admissible(x, p2 & U[x], U[x]): pair = p2; break
                assert pair is not None, 'Lemma A+: x has no pair inside X_o'
                Q2[x] = pair
                c2 = M.Config(I, key2, Q2)
                assert key2 in kp.K, ('Lemma A+: not a key', kp.d, k, key2)
                assert all(I.admissible(y, Q2[y] & c2.U(y), c2.U(y)) for y in Q2)
                assert c2.owner(x) == 0, ('Lemma A+ failed', kp.d, k, repr(c), o, ch)
                b2 = tuple((1 << key2[i]) if key2[i] is not None else (Q2[i] & c2.U(i)) for i in range(I.n))
                assert b2 in kp.S and kp.D[b2] <= 0
                cnt['A+ applies, chain length j=%d' % (len(ch) - 1)] += 1
                ok = True
                break
            if ok: break
        cnt['Zmax: Lemma A+ applies=%s' % ok] += 1
        keyok |= ok
        if not ok and len(ex['noAplus']) < nex: ex['noAplus'].append((kp.d, k, repr(c), 'V', V))
    cnt['keys: Lemma A+ at some Zmax=%s' % keyok] += 1


def main(argv):
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    rest = [a for a in argv if not a.startswith('--')]
    nex = int(opt.get('examples', 3))
    print('# command: python3 k4/sx_f2.py ' + ' '.join(argv), flush=True)
    profs = []
    if 'inst' in opt:
        fi = opt['inst']
        profs = [{'sets': d['sets'], 'vals': d['vals'], 'm': d['m']}
                 for d in json.load(gzip.open(fi, 'rt') if fi.endswith('.gz') else open(fi))]
    for fn in rest:
        for line in gzip.open(fn, 'rt'):
            r = json.loads(line)
            if r['f'] >= 2: profs.append({'sets': r['sets'], 'vals': r['vals'], 'm': r['m']})
    cnt = collections.Counter(); ex = collections.defaultdict(list); t0 = time.time()
    for d in profs:
        kp = KeyProfile(d)
        if not kp.ok or kp.I.f < 2: continue
        cnt['profiles f=%d' % kp.I.f] += 1
        for k in kp.K:
            if kp.dstar[k] > 0: analyse_key(kp, k, cnt, ex, nex)
    for k in sorted(cnt): print('%-90s %d' % (k, cnt[k]))
    for k, v in ex.items():
        for e in v: print('EX', k, e)
    print('# time %.1f s' % (time.time() - t0))


if __name__ == '__main__':
    main(sys.argv[1:])
