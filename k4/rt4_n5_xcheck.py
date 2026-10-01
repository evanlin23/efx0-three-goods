#!/usr/bin/env python3
"""Independent check of the n = 5 DL_RT4 failures, of DL on the key graph, and of the widened role swap T3+
(compute/k4-rt4-n5; the coordinator's two checks, xverify.py and xverify2.py, merged into one pass). EVIDENCE tooling.

Model. k4/dl134_xcheck.py's `Prof` on main's k4/c4x_check.py: its own enumeration of every base map, (V1), (V2)
literally, its own removal-only deficit `rodef`, and the move kinds T1, T2, T3p, T3h, T4 written there from the
definitions (k4/dl2.md §3; its R_13 and R_T verdicts are cross-checked state by state against `rel_B` of
k4/dl2_relations_xcheck.py, also written from the definitions). Nothing here calls k4/dlrt4.c, k4/dlrt4_ref.py,
k4/dl2_relations.py or k4/suite/model.py. dl134_xcheck imports dl2_relations_xcheck, which imports dl2_relations (and
through it model.py) without using it in `rel_B`; so while dl134_xcheck is imported an empty stub stands in for
dl2_relations, and the command line run asserts at the end that model.py was never loaded.

Objects, per strict profile with fewest frozen agents f >= 1: the min-frozen class (c4x_check's pre-allocations with
the fewest frozen agents), a *state* is a min-frozen P with def(P) > 0; key(P) = (NA(P), the frozen agents with their
bases) (k4/dl13.md §2.3 Remark); def*(K) = the least deficit over the min-frozen P of key K. A move P -> Q (Q
min-frozen) is classified by ch (the agents whose base changes), U (frozen in P, free in Q), Z (free in P, frozen in
Q), W (frozen in both), Y (free in both) and whether NA(Q) = NA(P).

Part A, DL_RT4 (ledger K4.DL2.RT4): the states at which no min-frozen Q with def(Q) < def(P) is reached by a T1, T2,
  T3 or T4 move (RT4 = T1 + T2 + T3 + T4, `Prof.state`). Per failing state: its deficit, the nearest distance k (the
  least |ch| over all better Q), the number of better Q at distance k, and their shapes "U|W|Z|Y" with NA kept or not;
  a *chain* is the shape 1|1|1|0 with NA kept in which w (W) takes x's (U) good and z (Z) takes w's good.
Part B, DL on the key graph with single T3 / T4 edges (ledger K4.DL13.KEY; k4/dl13.md §2.3 Remark): the keys K with
  def*(K) > 0 such that no state P of K has a T3 (T3p or T3h) or T4 move to a min-frozen Q of a key K' != K with
  def*(K') < def*(K). (T1 and T2 moves keep the key, so they are not edges.)
Part C, the widened role swap T3+ (ledger K4.DL2.RC). T3+(P, Q) holds iff NA(Q) = NA(P); exactly one x in U and one z
  in Z; Y has at most one agent, and it gives up a good of its base; the bases of W + {z} in Q are exactly the bases
  of W + {x} in P (the frozen goods move along W, x leaves the frozen set, z enters it); and z needs its new good in P
  (B_z(Q) inside N_z(B_z(P))). T3 is the case W empty. "T3+-" drops the last clause (reported only to show it is not
  needed on these profiles). R_C = T1 + T2 + T3+ + T4. Reports:
  (C1) the Part A failures some T3+ (T3+-) move to a better Q repairs, and DL_RC at every state of the profile;
  (C2) DL on the key graph with T3+ + T4 edges (and with T3+- + T4 edges): the keys with def* > 0 and those failing.

usage: python3 k4/rt4_n5_xcheck.py INST.json ...   (JSON lists of {"id", "sets", "vals", "m"}, as written by
       k4/dlrt4_ref.py or k4/dlrt4_failures.py --inst, e.g. results/k4_rt4/n5b_failures_inst.json, n5c_fail_inst.json)
Log: results/k4_rt4/xcheck_n5_failures.log. One process; about three minutes for the ten failing profiles (c4x_check's
enumeration of the m = 12 profiles takes most of it)."""
import collections, json, os, sys, time, types
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
_STUB = 'dl2_relations' not in sys.modules
if _STUB: sys.modules['dl2_relations'] = types.ModuleType('dl2_relations')   # unused by rel_B; keeps model.py out
try:
    import dl134_xcheck as X
finally:
    if _STUB: del sys.modules['dl2_relations']


def classes(Pr, P, Q, IP, IQ):
    """(ch, U, W, Z, Y, NA kept) of the move P -> Q"""
    (N1, NA1, fz1), (N2, NA2, fz2) = IP, IQ
    ch = [i for i in range(Pr.n) if P[i] != Q[i]]
    U = [i for i in ch if fz1[i] and not fz2[i]]; Z = [i for i in ch if fz2[i] and not fz1[i]]
    W = [i for i in ch if fz1[i] and fz2[i]]; Y = [i for i in ch if not fz1[i] and not fz2[i]]
    return ch, U, W, Z, Y, NA1 == NA2


def t3plus(Pr, P, Q, IP, IQ):
    """2 if P -> Q is a T3+ move, 1 if only T3+- (z need not need its new good), 0 otherwise"""
    ch, U, W, Z, Y, keep = classes(Pr, P, Q, IP, IQ)
    if not keep or len(U) != 1 or len(Z) != 1 or len(Y) > 1: return 0
    if not all(P[y] - Q[y] for y in Y): return 0
    if sorted(map(sorted, [Q[i] for i in W + Z])) != sorted(map(sorted, [P[i] for i in W + U])): return 0
    return 2 if Q[Z[0]] <= IP[0][Z[0]] else 1


def is_chain(Pr, P, Q, IP, IQ):
    """the chain shape: x (U) frees its good g, w (W) moves from its good h to g, z (Z) takes h; NA kept"""
    ch, U, W, Z, Y, keep = classes(Pr, P, Q, IP, IQ)
    return keep and len(U) == 1 and len(W) == 1 and len(Z) == 1 and not Y and Q[W[0]] == P[U[0]] and Q[Z[0]] == P[W[0]]


_CACHE = {}


def analyse(d):
    """every check above on one profile {"sets", "vals", "m"}; returns a dict (see main for the fields). Cached per
    profile, so k4/rt4_pred.py's four predicates on this tool enumerate each instance once per process."""
    ck = json.dumps([d['sets'], d['vals'], d['m']])
    if ck not in _CACHE: _CACHE[ck] = _analyse(d)
    return _CACHE[ck]


def _analyse(d):
    Pr = X.Prof(d['sets'], d['vals'], d['m'])
    r = {'f': Pr.f, 'omega': Pr.f - (2 * Pr.n - d['m']), 'n_min': len(Pr.mp)}
    if Pr.f < 1 or r['omega'] <= 0:                           # DL_RT4 is about f >= 1 with omega >= 1
        r['skip'] = 'f = %d, omega = %d' % (Pr.f, r['omega']); return r
    info = {P: Pr.info(P) for P, _ in Pr.mp}
    dd = dict(Pr.mp)

    def key(P):
        N, NA, fz = info[P]
        return (NA, tuple(P[i] if fz[i] else None for i in range(Pr.n)))
    K = collections.defaultdict(list)
    for P, _ in Pr.mp: K[key(P)].append(P)
    dstar = {k: min(dd[P] for P in Ps) for k, Ps in K.items()}
    kind = {}                                     # (P, Q) -> (move kinds, T3+ level), computed once

    def mv(P, Q):
        if (P, Q) not in kind:
            kd, _ = Pr.move(P, Q, info[P], info[Q])
            kind[P, Q] = (kd, t3plus(Pr, P, Q, info[P], info[Q]))
        return kind[P, Q]

    # Part A (and C1): every state
    states, fails, rc_fail = 0, [], 0
    for P, dP in Pr.mp:
        if dP <= 0: continue
        states += 1
        flags, holds, t4min, dist, ok = Pr.state(P, dP)
        better = [Q for Q, dQ in Pr.mp if dQ < dP]
        plus = max((mv(P, Q)[1] for Q in better), default=0)
        if not (holds['RT4'] or plus == 2): rc_fail += 1
        if holds['RT4']: continue
        near = [Q for Q in better if sum(1 for a, b in zip(P, Q) if a != b) == dist]
        shapes = collections.Counter()
        for Q in near:
            ch, U, W, Z, Y, keep = classes(Pr, P, Q, info[P], info[Q])
            shapes['%d|%d|%d|%d%s%s' % (len(U), len(W), len(Z), len(Y), '' if keep else ' NA changed',
                                        ' chain' if is_chain(Pr, P, Q, info[P], info[Q]) else '')] += 1
        plus_min = min((sum(1 for a, b in zip(P, Q) if a != b) for Q in better if mv(P, Q)[1] == 2), default=None)
        fails.append({'B': [sorted(B) for B in P], 'def': dP, 'k': dist, 'relB_ok': ok, 'near': len(near),
                      'shapes': dict(shapes), 'frozen': [i for i in range(Pr.n) if info[P][2][i]],
                      'NA': sorted(info[P][1]), 'T3+': plus == 2, 'T3+-': plus >= 1, 'T3+min': plus_min})
    r.update(states=states, fails=fails, rc_fail=rc_fail, keys=len(K))

    # Parts B and C2: the key graph
    pos = [k for k in K if dstar[k] > 0]
    kfail = {'T3/T4': [], 'T3+/T4': [], 'T3+-/T4': []}
    for k in pos:
        found = {'T3/T4': False, 'T3+/T4': False, 'T3+-/T4': False}
        for P in K[k]:
            for Q, _ in Pr.mp:
                kq = key(Q)
                if kq == k or dstar[kq] >= dstar[k]: continue
                kd, plus = mv(P, Q)
                single = kd['t3p'] or kd['t3h'] or kd['t4']
                found['T3/T4'] |= single
                found['T3+/T4'] |= single or plus == 2
                found['T3+-/T4'] |= single or plus >= 1
            if all(found.values()): break
        for e, h in found.items():
            if not h: kfail[e].append({'NA': sorted(k[0]), 'frozen': {i: sorted(b) for i, b in enumerate(k[1]) if b is not None},
                                       'def*': dstar[k], 'states': len(K[k])})
    r.update(keys_pos=len(pos), kfail=kfail)
    return r


def main(argv):
    print('# command: python3 k4/rt4_n5_xcheck.py ' + ' '.join(argv), flush=True)
    print('# model: k4/dl134_xcheck.py Prof on k4/c4x_check.py (dl2_relations stubbed while importing: %s)' % _STUB, flush=True)
    tot = collections.Counter(); kd = collections.Counter(); sh = collections.Counter(); t0all = time.time()
    for fn in argv:
        for e in json.load(open(fn)):
            t0 = time.time()
            r = analyse(e)
            tot['profiles'] += 1
            if 'skip' in r:
                print('P %s skipped: %s' % (e['id'], r['skip']), flush=True); continue
            for s in r['fails']:
                print('  A fail %s def %s k %s | near %d: %s | frozen %s NA %s | T3+ repairs %s (least |ch| %s), T3+- %s | '
                      'relB agrees %s' % (s['B'], s['def'], s['k'], s['near'],
                                          ', '.join('%s x%d' % kv for kv in sorted(s['shapes'].items())), s['frozen'],
                                          s['NA'], s['T3+'], s['T3+min'], s['T3+-'], s['relB_ok']), flush=True)
                kd[(s['def'], s['k'])] += 1
                for x, c in s['shapes'].items(): sh[x] += c
                tot['rt4_fail'] += 1; tot['near'] += s['near']; tot['rep_T3+'] += s['T3+']; tot['rep_T3+-'] += s['T3+-']
                tot['relB_mismatch'] += not s['relB_ok']
                tot['near_chain'] += sum(c for x, c in s['shapes'].items() if x.endswith(' chain'))
            for e_, ks in r['kfail'].items():
                for k in ks:
                    print('  %s key fail (edges %s): NA %s frozen %s def* %s (%d states)' % (
                        'B' if e_ == 'T3/T4' else 'C', e_, k['NA'], k['frozen'], k['def*'], k['states']), flush=True)
            tot['states'] += r['states']; tot['rc_fail'] += r['rc_fail']; tot['keys'] += r['keys']
            tot['keys_pos'] += r['keys_pos']
            for e_, ks in r['kfail'].items(): tot['kfail ' + e_] += len(ks)
            print('P %s f=%d min-frozen=%d states=%d keys=%d (def*>0: %d) | A: RT4 fails at %d | C1: DL_RC fails at %d | '
                  'B: key-graph DL (T3/T4) fails at %d keys | C2: (T3+/T4) at %d, (T3+-/T4) at %d | %.1fs' % (
                      e['id'], r['f'], r['n_min'], r['states'], r['keys'], r['keys_pos'], len(r['fails']), r['rc_fail'],
                      len(r['kfail']['T3/T4']), len(r['kfail']['T3+/T4']), len(r['kfail']['T3+-/T4']),
                      time.time() - t0), flush=True)
    print('TOTAL profiles %d; states (def > 0, f >= 1) %d; keys %d, with def* > 0: %d' % (
        tot['profiles'], tot['states'], tot['keys'], tot['keys_pos']))
    print('A  DL_RT4 fails at %d states, by (def, k): %s; R_13 / R_T against rel_B: %d mismatches' % (
        tot['rt4_fail'], dict(sorted(kd.items())), tot['relB_mismatch']))
    print('A  their better states at the nearest distance: %d, shapes U|W|Z|Y: %s; chains: %d' % (
        tot['near'], dict(sorted(sh.items())), tot['near_chain']))
    print('B  DL on the key graph with single T3 / T4 edges fails at %d of the %d keys with def* > 0' % (
        tot['kfail T3/T4'], tot['keys_pos']))
    print('C1 T3+ repairs %d of the %d DL_RT4 failures (T3+-: %d); DL_RC (T1 + T2 + T3+ + T4) fails at %d of the %d states' % (
        tot['rep_T3+'], tot['rt4_fail'], tot['rep_T3+-'], tot['rc_fail'], tot['states']))
    print('C2 DL on the key graph with T3+ / T4 edges fails at %d of the %d keys with def* > 0 (T3+- / T4: %d)' % (
        tot['kfail T3+/T4'], tot['keys_pos'], tot['kfail T3+-/T4']))
    loaded = sorted(m for m in ('model', 'dl2_classify', 'dl2_relations') if m in sys.modules)
    print('# modules of the model.py side loaded: %s; %.0fs' % (loaded or 'none', time.time() - t0all), flush=True)
    assert not loaded, loaded
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
