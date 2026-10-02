#!/usr/bin/env python3
"""The f = 1 single-step DL failure of compute/k4-rc (results/k4_rc/FAILURES.md there) against the route of k4/sx.md
(workstream proof/k4-sx; k4/sx.md §4.4). EVIDENCE tooling.

Input: the 45 failing profiles of core pos 4604 of k4_certs_5_pure (m = 13), as the inst list of compute/k4-rc
(results/k4_sx/rc/rc_fail_inst.json, copied from results/k4_rc/rc_fail_hunt_ranked_pure_inst.json there).
For every profile and every key κ with def*(κ) > 0 it prints:
  - the states of κ with deficit def*(κ), and how many of them have a (T3) move to a state of deficit < def*(κ);
  - the failing state P_fail = ({11},{12},{3,7},{4,8},{5,9}) of FAILURES.md: its deficit, whether it is in κ, and
    whether some (T3) move (sx_keygraph.t3plus_moves, W empty) improves it;
  - the state P_wit = ({11},{6,10},{12},{4,8},{5,9}) of FAILURES.md's key-form witness, and the same facts;
  - every (r', Λ')-maximum Q of Theorem Z′ (k4/c4min_reduce.md §2) at κ: its pairs and pool, the free-valid owners V,
    the terminals T, its state P_Q, whether P_Q is P_fail or P_wit, the deficit of P_Q, the (T3) moves from P_Q to a
    deficit < def*(κ), and the image of Lemma A's owner swap (o in V ∩ T takes {g}; x takes the first admissible set
    inside X_o = Q_o ∪ L) with its deficit;
  - a second computation of the deficits of P_fail, P_wit, P_Q and the Lemma A images with main's k4/c4x_check.rodef
    (removal-only deficit from k4/c4x.md §1, directly), which must agree.

usage: python3 k4/sx_rc_case.py results/k4_sx/rc/rc_fail_inst.json [--verbose=K]   (K profiles printed in full)"""
import collections, itertools, json, os, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, 'suite'))
from model import bits, pc, mask
from sx_keygraph import KeyProfile, keyof
import c4x_check as CX

P_FAIL = ({11}, {12}, {3, 7}, {4, 8}, {5, 9})
P_WIT = ({11}, {6, 10}, {12}, {4, 8}, {5, 9})


def tb(sets): return tuple(mask(sorted(s)) for s in sets)
def sb(Bs): return '(' + ', '.join('{' + ','.join(map(str, sorted(bits(b)))) + '}' for b in Bs) + ')'


def rodef2(d, Bs):
    """the removal-only deficit of the state Bs by main's k4/c4x_check.rodef (no model.py)"""
    n, sets, m = len(d['sets']), d['sets'], d['m']
    vl = [dict(zip(S, V)) for S, V in zip(sets, d['vals'])]
    R = [set(S) for S in sets]
    B = [frozenset(bits(b)) for b in Bs]
    J = frozenset(range(m)) - frozenset().union(*B)
    N = [frozenset(g for g in R[i] - B[i] if vl[i][g] > CX.val(vl[i], B[i])) for i in range(n)]
    NA = frozenset().union(*N)
    fz = [len(B[i]) == 1 and B[i] <= NA for i in range(n)]
    cap = [0 if fz[i] else max(0, 2 - len(B[i])) for i in range(n)]
    return CX.rodef(n, vl, B, J, fz, cap, R, N)


def improving_t3(kp, Bs, ds):
    return [mv for mv in kp.t3plus_moves(Bs) if not mv[3] and kp.D[mv[0]] < ds]


def main(argv):
    if not argv: print(__doc__); return
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    rest = [a for a in argv if not a.startswith('--')]
    verbose = int(opt.get('verbose', 2))
    print('# command: python3 k4/sx_rc_case.py ' + ' '.join(argv), flush=True)
    items = json.load(open(rest[0]))
    cnt = collections.Counter(); t0 = time.time()
    pf, pw = tb(P_FAIL), tb(P_WIT)
    for idx, d in enumerate(items):
        kp = KeyProfile(d)
        if not kp.ok or kp.I.f != 1: cnt['profiles out of scope'] += 1; continue
        I = kp.I
        cnt['profiles'] += 1
        out = idx < verbose
        if out: print('\n## profile %d: %s\n# sets %s vals %s m %d, f %d, omega %d' % (idx, d.get('id'), d['sets'], d['vals'], d['m'], I.f, I.omega))
        for k in sorted(kp.K, key=str):
            ds = kp.dstar[k]
            if ds <= 0: continue
            cnt['keys def*>0'] += 1
            x = next(i for i in range(I.n) if k[i] is not None); g = k[x]; gm = 1 << g
            free = [i for i in range(I.n) if i != x]
            U = {y: I.R[y] & ~gm for y in range(I.n)}
            mins = [b for b in kp.K[k] if kp.D[b] == ds]
            good = [b for b in mins if improving_t3(kp, b, ds)]
            cnt['key states'] += len(kp.K[k]); cnt['key states with def = def*'] += len(mins)
            cnt['key states with def = def* and an improving (T3) move'] += len(good)
            if out:
                print('# key x=%d g=%d def*=%d: %d states, %d with def = def*, %d of these with an improving (T3) move'
                      % (x, g, ds, len(kp.K[k]), len(mins), len(good)))
            for name, b in (('P_fail', pf), ('P_wit', pw)):
                ins = b in kp.S and keyof(kp.PA[b]) == k
                imp = improving_t3(kp, b, ds) if b in kp.S else []
                d1 = kp.D.get(b); d2 = rodef2(d, b)
                assert d1 is None or d1 == d2, ('deficit mismatch', name, d1, d2)
                cnt['%s in the key: %s, def %s, improving (T3) moves %d' % (name, ins, d1, len(imp))] += 1
                if out: print('# %s %s: in the key %s, def %s (rodef %s), improving (T3) moves %d%s' % (
                    name, sb(b), ins, d1, d2, len(imp), (', e.g. ' + sb(imp[0][0]) + ' def %d' % kp.D[imp[0][0]]) if imp else ''))
            cs = I.configs([k])
            lev = lambda c: sum(I.level(y, c.Q[y] & I.R[y]) for y in free)
            rob = lambda c: sum(1 for y in free if c.robust(y))
            best = max((rob(c), lev(c)) for c in cs)
            mx = [c for c in cs if (rob(c), lev(c)) == best]
            cnt['Z′-maxima'] += len(mx)
            for c in mx:
                Bs = tuple(gm if i == x else (c.Q[i] & U[i]) for i in range(I.n))
                X = {o: c.Q[o] | c.L for o in free}
                V = [o for o in free if not any(I.threat(y, X[o], c.hv(y)) for y in free if y != o)]
                T = [z for z in free if kp.PA[Bs].N[z] & gm]
                imp = improving_t3(kp, Bs, ds)
                d2 = rodef2(d, Bs)
                assert kp.D[Bs] == d2
                tag = 'P_fail' if Bs == pf else 'P_wit' if Bs == pw else 'other'
                cnt['Z′-max state = %s' % tag] += 1
                cnt['Z′-max state def %d, improving (T3) moves from it: %s' % (kp.D[Bs], bool(imp))] += 1
                if out:
                    print('# Z′-max: pairs %s pool %s (r′, Λ′) = %s; V %s T %s' % (
                        {y: sorted(bits(c.Q[y])) for y in free}, sorted(bits(c.L)), best, V, T))
                    print('#   P_Q = %s (%s), def %d (rodef %d); %d improving (T3) moves, to %s' % (
                        sb(Bs), tag, kp.D[Bs], d2, len(imp), sorted(set(sb(mv[0]) + ' def %d' % kp.D[mv[0]] for mv in imp))[:6]))
                # Lemma A's owner swap
                for o in [o for o in V if o in T]:
                    done = False
                    for kk in (1, 2):
                        for A in itertools.combinations(list(bits(X[o] & U[x])), kk):
                            A = mask(A)
                            if not I.admissible(x, A, U[x]): continue
                            b2 = list(Bs); b2[o] = gm; b2[x] = A; b2 = tuple(b2)
                            assert b2 in kp.S
                            e2 = rodef2(d, b2)
                            assert e2 == kp.D[b2]
                            cnt['Lemma A image def %d (owner o = %d)' % (kp.D[b2], o)] += 1
                            cnt['Lemma A image = the FAILURES.md witness image'] += b2 == tb(({9}, {6, 10}, {11}, {4, 8}, {12}))
                            if out: print('#   Lemma A, o = %d: x takes %s, image %s def %d (rodef %d)' % (
                                o, sorted(bits(A)), sb(b2), kp.D[b2], e2))
                            done = True; break
                        if done: break
    print()
    for k in sorted(cnt): print('%-100s %d' % (k, cnt[k]))
    print('# time %.1f s' % (time.time() - t0))


if __name__ == '__main__':
    main(sys.argv[1:])
