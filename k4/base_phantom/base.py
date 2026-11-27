"""The base case "OC1 with phantom constraints": one-move repairs of phantom-class states, classified.

A *base repair* of a state S (present agents, present goods, phantoms holding their T) is an official move of the
present instance (k4/sdc.md section 29; bplib.official_moves) followed by a lifted one-absorber completion (owner
present, every other present agent at most one junk good, phantoms nothing), raw EFX0 in the full instance.

Features of a move P = (x0, .., xt), H0, (H1, .., Ht):
  dang   x0 is dangerous at S
  can    canonical: every x_l (l >= 1) wants x_{l-1}'s single good alone
  early  every link before the last is canonical and those agents take no junk (the last agent x_t may take junk
         and need not want x_{t-1}'s good alone)
  mid    some H_l (l >= 1) is nonempty (a chain agent after x0 takes junk)
  ring   H0 contains the end's good
  len    t + 1;  lastj = |H_t|
The classes, in order (each contains the previous):
  C0  dang and can and not mid        (settlement-shaped moves, rings included; no deletion, no SD requirement)
  ED  dang and early                  (Hall's ED chains, k4/oc1_hall.md section 14: only the end may add junk)
  C1  ED, or dang and can             (adds canonical chains whose middle agents take junk)
  C2  C1, or can                      (any first agent)
  C3  any official move
W1 (in_class only): dang and early and lastj <= 1 (Theorem S's allocation with a weak last link).
"""
import itertools
from bplib import (Inst, State, bits, pc, submasks, wants, dangerous, rounds, lifted_completion, one_absorber,
                   official_moves, frozen)

CLASSES = ['C0', 'ED', 'C1', 'C2', 'C3']


def move_features(I, S, D, P, H0, Hs):
    can = True
    for l in range(1, len(P)):
        b = S.B[P[l - 1]]
        if b == 0 or b & (b - 1) or not wants(I, S.B, P[l], b.bit_length() - 1):
            can = False
            break
    early = True   # every link before the last canonical, with no junk
    for l in range(1, len(P) - 1):
        b = S.B[P[l - 1]]
        if Hs[l - 1] or b == 0 or b & (b - 1) or not wants(I, S.B, P[l], b.bit_length() - 1):
            early = False
            break
    return dict(dang=P[0] in D, can=can, mid=any(Hs), ring=S.B[P[-1]] != 0 and not S.B[P[-1]] & ~H0,
                len=len(P), early=early, lastj=pc(Hs[-1]) if Hs else 0)


def in_class(f, c):
    if c == 'W1':
        return f['dang'] and f['early'] and f['lastj'] <= 1
    if c == 'C0':
        return f['dang'] and f['can'] and not f['mid']
    if c == 'ED':
        return f['dang'] and f['early']
    if c == 'C1':
        return f['dang'] and (f['early'] or f['can'])
    if c == 'C2':
        return (f['dang'] and f['early']) or f['can']
    return True


def base_repairs(I, S, upto='C3', want_all=False, maxlen=None):
    """Least class with a base repair, and a witness (P, H0, Hs, X) [or every repairing move with its features]."""
    D = set(dangerous(I, S))
    moves = []
    for P, H0, Hs, nb in official_moves(I, S, maxlen=maxlen):
        f = move_features(I, S, D, P, H0, Hs)
        moves.append((P, H0, Hs, nb, f))
    allrep = []
    for c in CLASSES:
        for P, H0, Hs, nb, f in moves:
            if not in_class(f, c):
                continue
            if c != 'C0' and in_class(f, CLASSES[CLASSES.index(c) - 1]):
                continue
            X = lifted_completion(I, State(S.alive, S.goods, nb, S.dead))
            if X is not None:
                assert I.efx0(X)
                if not want_all:
                    return c, (P, H0, Hs, X, f)
                allrep.append((c, P, H0, Hs, X, f))
        if c == upto:
            break
    if want_all:
        return allrep
    return None, None


def explore(I, S0, rmax=2, lstar=True, p2=True, maxdepth=9):
    """Every state reachable from S0 by admissible rounds.  Returns (states dict key -> info) where info has
    'complete' (a lifted completion exists), 'succ' (keys of the states after each admissible round), 'state'."""
    seen = {}
    stack = [S0]
    while stack:
        S = stack.pop()
        k = S.key()
        if k in seen:
            continue
        X = lifted_completion(I, S)
        info = {'state': S, 'complete': X is not None, 'succ': [], 'rounds': []}
        seen[k] = info
        if X is None and len(S.dead) < maxdepth:
            for combo, S2 in rounds(I, S, rmax=rmax, lstar=lstar, p2=p2):
                info['succ'].append(S2.key())
                info['rounds'].append(combo)
                if S2.key() not in seen:
                    stack.append(S2)
    return seen


def good_states(seen):
    """good[k]: some sequence of admissible rounds from k ends in a lifted completion."""
    good = {}

    def g(k):
        if k in good:
            return good[k]
        good[k] = False
        info = seen[k]
        r = info['complete'] or any(g(s) for s in info['succ'])
        good[k] = r
        return r
    for k in seen:
        g(k)
    return good


def dead_ends(seen):
    return [k for k, info in seen.items() if not info['complete'] and not info['succ']]


def p3_violations(I, S):
    """(P3): junk goods worth more than tau_phi to a phantom phi."""
    J = S.junk()
    out = []
    for f in S.dead:
        tau = I.V(f, S.B[f])
        for g in bits(J & I.R[f]):
            if I.val[f][g] > tau:
                out.append((f, g))
    return out
