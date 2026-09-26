"""Rotation potentials for k4/c4one.md §4 (route 2: "whenever no owner is valid, some rotation raises the count").

slack(st, o): Theorem A4+'s count for the owner o (k4/c4.md §4c): the slots of the other agents (a rotated agent with
  a one-good base gets a slot, the more generous convention) minus the demand of the agents exposed w.r.t. W_o = B_o + J:
  1 for a free agent holding a pick that can protect itself with its own slot (Lemma 2_4, which needs at most one good
  of R_x in B_o), rho_o(x) (the least number of its junk goods to keep out of W_o) for the others.
Phi(st): the best slack over the non-frozen owners (0 when no owner is needed); Phi >= 0 implies a valid owner.
count(st): the owner-free version, Proposition H's "slots minus forced goods": all slots minus the demand of every agent
  threatened by the junk J alone (with its base).
Both are integers, so a single rotation that makes an owner valid must raise Phi to >= 0."""
import itertools
from c4trace import exposed, rho, threatened

def slack(st, o):
    I = st.I; caps = st.caps(rot_slot=True); fr = st.frozen()
    S = sum(caps) - caps[o]
    W = st.base[o] | st.J
    dem = 0
    for x in exposed(st, o, W):
        if not fr[x] and st.kind[x] == 'pick' and caps[x] >= 1 and len(st.base[o] & I.R[x]) <= 1: dem += 1
        else: dem += rho(st, x, o)
    return S - dem

def Phi(st):
    if st.omega() <= 0: return 0
    fr = st.frozen()
    owners = [o for o in range(st.I.n) if not fr[o]]
    return max(slack(st, o) for o in owners) if owners else -99

def count(st):
    I = st.I; caps = st.caps(rot_slot=True); fr = st.frozen(); dem = 0
    for x in range(I.n):
        if not threatened(I, x, st.J, st.base[x]): continue
        if not fr[x] and st.kind[x] == 'pick' and caps[x] >= 1: dem += 1
        else:
            cand = sorted(st.J & I.R[x])
            dem += next(r for r in range(len(cand) + 1) for T in itertools.combinations(cand, r)
                        if not threatened(I, x, st.J - frozenset(T), st.base[x]))
    return sum(caps) - dem
