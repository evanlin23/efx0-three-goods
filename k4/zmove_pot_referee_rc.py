#!/usr/bin/env python3
"""Referee check of the descriptive claims of k4/zmove_pot.md §2 about compute/k4-rc's cores 4515 and 4604 (PR #87
review). EVIDENCE tooling, on main's k4/sx_keygraph.KeyProfile (k4/suite/model.py), the same model as k4/zmove_pot.py.

Core 4515 (n = 5, m = 12, f = 2; results/k4_rc/rc_fail_4515_all_inst.json, all 1,076 profiles):
  - the states without a one-move repair (zm, k4/zmove_pot.md §1) at the keys with def* > 0, per profile and in total;
  - at each: agent 1 not robust (v1({1,8}) < v1({10,11})), agent 2 holds {10,11} and is robust, r' and the key's max r';
  - the trade "agent 1 takes {1,10} or {1,11}, agent 2 takes {3}, {3,10} or {3,11}": a state of the same key? r' after,
    agent 1 robust after, agent 2 robust after, agent 2's value lower?
  - which of them are Pareto-maximal in the key and have every free agent locally optimal (by B_3);
  - the two-helper repair of FAILURES.md §2 (agent 1 {1,10}, agent 2 {3}, agent 3 takes 4, agent 0 takes {0}): its
    deficit, and whether it is the trade followed by one plain (T3) move.
Core 4604 (n = 5, m = 13, f = 1; results/k4_rc/rc_fail_all_inst.json, all 369 profiles): the states without zm, agent 1
non-robust on {12} with good 1 in the junk, and the (T1) re-base to {1,12}: a state of the key with larger r'.

usage: python3 k4/zmove_pot_referee_rc.py [--max=N]     (log: results/k4_zmove_pot/referee_rc.log)"""
import collections, itertools, json, os, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, 'suite'))
from model import bits, pc, mask
from sx_keygraph import KeyProfile, keyof

ROOT = os.path.dirname(HERE)
CNT = collections.Counter()


def lst(b): return tuple(tuple(sorted(bits(B))) for B in b)


def zm(kp, b): return any(kp.D[b2] <= 0 for b2, x, z, W, h in kp.t3plus_moves(b))


def info(kp, k, b):
    I = kp.I
    free = [y for y in range(I.n) if k[y] is None]
    Nm = mask(g for g in k if g is not None)
    U = {y: I.R[y] & ~Nm for y in range(I.n)}
    rob = {y: I.val(y, b[y]) >= I.val(y, U[y] & ~b[y]) for y in free}
    return free, U, rob


def run4515(L):
    for d in L:
        kp = KeyProfile(d); I = kp.I
        CNT['4515 profiles'] += 1
        bad = []
        for k, sts in kp.K.items():
            if kp.dstar[k] <= 0: continue
            CNT['4515 keys with def* > 0'] += 1
            free = [y for y in range(I.n) if k[y] is None]
            for b in sts:
                if not zm(kp, b): bad.append((k, b))
        CNT['4515 states without zm'] += len(bad)
        CNT['4515 profiles with %d states without zm' % len(bad)] += 1
        for k, b in bad:
            free, U, rob = info(kp, k, b)
            sts = kp.K[k]
            rmax = max(sum(info(kp, k, b2)[2].values()) for b2 in sts)
            shape = lst(b)
            CNT['4515 stuck state %s (key %s)' % (str([list(s) for s in shape[:3]] + ['B3'] + [list(shape[4])]), list(k))] += 1
            CNT["4515 stuck: B3 = %s, agent 1 robust %s, agent 2 on {10,11} %s and robust %s, r' %d, key max r' %d"
                % (list(shape[3]) if len(shape[3]) == 2 else 'singleton', rob.get(1), shape[2] == (10, 11), rob.get(2),
                   sum(rob.values()), rmax)] += 1
            # the trade
            res = []; raising = []
            for A1 in ((1, 10), (1, 11)):
                for A2 in ((3,), (3, 10), (3, 11)):
                    if set(A1) & set(A2): continue
                    b2 = list(b); b2[1] = mask(A1); b2[2] = mask(A2); b2 = tuple(b2)
                    if b2 not in kp.S or keyof(kp.PA[b2]) != k:
                        res.append('not a state of the key'); continue
                    f2, U2, rob2 = info(kp, k, b2)
                    res.append("agent 1 %s, agent 2 %s: r' %d -> %d, agent 1 robust %s, agent 2 robust %s, agent 2's value lower %s"
                               % (list(A1), list(A2), sum(rob.values()), sum(rob2.values()), rob2[1], rob2[2],
                                  I.val(2, b2[2]) < I.val(2, b[2])))
                    if sum(rob2.values()) > sum(rob.values()):
                        raising.append((I.val(1, b2[1]) < I.val(1, b[1]), I.val(2, b2[2]) < I.val(2, b[2])))
            CNT["4515 stuck: some trade option keeps agent 2 robust, makes agent 1 robust, lowers agent 2's value: %s"
                % any(r.endswith('agent 1 robust True, agent 2 robust True, agent 2\'s value lower True') for r in res)] += 1
            for r in sorted(set(res)): CNT['4515 trade: ' + r] += res.count(r)
            # Pareto-maximal and locally optimal
            vec = {s: tuple(I.val(y, s[y]) for y in free) for s in sts}
            par = not any(all(a >= c for a, c in zip(vec[s], vec[b])) and vec[s] != vec[b] for s in sts)
            J = kp.PA[b].J
            lo = all(not any(I.val(y, mask(c)) > I.val(y, b[y]) for r in (1, 2)
                             for c in itertools.combinations(list(bits((b[y] | J) & I.R[y])), r)) for y in free)
            CNT['4515 stuck B3 = %s: Pareto-maximal %s, every free agent locally optimal %s' % (list(shape[3]), par, lo)] += 1
            if par and lo: CNT['4515 stuck states Pareto-maximal and locally optimal'] += 1
            kind = ('a Pareto improvement' if any(not a and not c for a, c in raising) else
                    'lowers agent 2 only' if any(c and not a for a, c in raising) else
                    'lowers agent 1 only' if any(a and not c for a, c in raising) else 'lowers both' if raising else 'none')
            CNT["4515 stuck (Pareto-maximal and locally optimal %s): best r'-raising trade %s" % (par and lo, kind)] += 1
            # the two-helper repair: agent 1 {1,10}, agent 2 {3}, agent 3 takes {4}, agent 0 takes {0}
            if shape[1] == (1, 8) and shape[2] == (10, 11):
                t = list(b); t[1] = mask((1, 10)); t[2] = mask((3,)); t = tuple(t)
                fin = list(t); fin[3] = mask((4,)); fin[0] = mask((0,)); fin = tuple(fin)
                ok_t = t in kp.S
                ok_f = fin in kp.S
                df = kp.D[fin] if ok_f else None
                via = ok_t and any(b2 == fin and W == () and h is None for b2, x, z, W, h in kp.t3plus_moves(t))
                CNT['4515 repair: trade state exists %s, final state exists %s, def(final) %s, final = trade + one plain (T3) move %s'
                    % (ok_t, ok_f, df, via)] += 1


def run4604(L):
    for d in L:
        kp = KeyProfile(d); I = kp.I
        CNT['4604 profiles'] += 1
        for k, sts in kp.K.items():
            if kp.dstar[k] <= 0: continue
            CNT['4604 keys with def* > 0'] += 1
            for b in sts:
                if zm(kp, b): continue
                free, U, rob = info(kp, k, b)
                shape = lst(b)
                CNT['4604 stuck state %s key %s' % ([list(s) for s in shape], list(k))] += 1
                J = kp.PA[b].J
                b2 = list(b); b2[1] = b[1] | mask((1,)); b2 = tuple(b2)
                st = b2 in kp.S and keyof(kp.PA[b2]) == k
                r2 = sum(info(kp, k, b2)[2].values()) if st else None
                CNT["4604 stuck: agent 1 robust %s, 1 in J %s, (T1) to B1 + {1} a state of the key %s, r' %d -> %s"
                    % (rob[1], bool(J & 2), st, sum(rob.values()), r2)] += 1


def main(argv):
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    mx = int(opt.get('max', 10 ** 9))
    t0 = time.time()
    print('# command: python3 k4/zmove_pot_referee_rc.py ' + ' '.join(argv), flush=True)
    L = json.load(open(os.path.join(ROOT, 'results/k4_rc/rc_fail_4515_all_inst.json')))[:mx]
    run4515([{'sets': e['sets'], 'vals': e['vals'], 'm': e['m']} for e in L])
    L = json.load(open(os.path.join(ROOT, 'results/k4_rc/rc_fail_all_inst.json')))[:mx]
    run4604([{'sets': e['sets'], 'vals': e['vals'], 'm': e['m']} for e in L])
    for k in sorted(CNT): print('%-150s %d' % (k, CNT[k]))
    print('# time %.1f s' % (time.time() - t0))


if __name__ == '__main__':
    main(sys.argv[1:])
