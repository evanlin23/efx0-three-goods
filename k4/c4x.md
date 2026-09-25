# C₄∃ by an extremal valid pre-allocation

Workstream `proof/k4-c4x`, ledger rows K4.C4X.* (CONJECTURE / EVIDENCE only), ledger open item 18. A second,
independent attempt at the last open step of the k = 4 case; the other one is the draft PR on `proof/k4-c4`
(`k4/c4.md` there, unreviewed), which follows LB⁺'s counting over runs of Phase 1. This file does not follow that route:
it takes a pre-allocation that is extremal for a potential over *all* valid pre-allocations.

**Target C₄∃.** For every strict profile of every k = 4 core, *some* valid pre-allocation (`k4/lb4.md` §1) has a
completion satisfying (OC₄) in which frozen agents hold their base and only the owner's bundle has more than two
goods. By Theorem 1′₄ (machine-checked, `lean/EFX/PreAllocK.lean`: `SoundCompletion`, `target4_of_completions`),
K4.TIE and K4.CORE this gives TARGET₄.

**Status.** Work in progress; see the summary at the end of the session.

## 1. The space 𝒫 and completability

Fix a strict profile of a k = 4 core (agents with |R_i| ∈ {3, 4}, strictly balanced; all nonempty subset sums of each
R_i distinct).

**Definition (𝒫).** A pre-allocation is a family of pairwise disjoint bases B_i ⊆ R_i with |B_i| ≤ 2. Its junk is
J = M ∖ ⋃ B_i, and the needs of i are the value-based ones, N_i = {g ∈ R_i ∖ B_i : v_i(g) > v_i(B_i)}. It is valid if
(V1) J ∩ NA = ∅ and (V2) no good of a two-good base is in NA, where NA = ⋃ N_i. 𝒫 is the set of valid pre-allocations.

Remarks.
- The needs are the smallest the Definition of `k4/lb4.md` §1 allows, so nothing is lost: a completion that satisfies
  (OC₄) for larger needs does so for these (a larger NA only adds frozen agents and removes slots). With strict types
  they are the pick needs {g : g ≻_i Y} for a one-good base {Y}, and R_i for an empty base.
- Every run of Phase 1 of LB₄ followed by any upgrades, and every rotation of LB₄ʳ whose rotated base has at most two
  goods, is in 𝒫 (`k4/lb4.md` §2, §5), so 𝒫 ≠ ∅.
- (V1) and (V2) say: *every needed good is the whole base of one agent*. Such an agent is frozen (F); the others are
  free, with cap(i) = 2 − |B_i| slots. As in `k4/lb4.md` §1, |F| = |NA| and ω := |J| − S = |F| − σ with σ = 2n − m.

**Definition (completable).** P ∈ 𝒫 is completable if it has a completion in the sense of `lean/EFX/PreAllocK.lean`
(`Completion`, `SoundCompletion`) that satisfies (OC₄): an owner o (a free agent) or none; X_i = B_i ∪ C_i with C_i ⊆ J,
C_i = ∅ for frozen i ≠ o and |B_i| + |C_i| ≤ 2 for free i ≠ o; X_o = B_o ∪ (the rest of J); the owner's needs taken
from its bundle, N_o^X = {g ∈ R_o ∖ X_o : v_o(g) > v_o(X_o)} (frozen status and slots recomputed with them); and
v_j(X_o ∖ h) ≤ v_j(X_j) for all j ≠ o, h ∈ X_o. By Theorem 1′₄ such an X is EFX₀ with at most one bundle of more than
two goods. If ω ≤ 0, the completion without owner exists.

**Removal-only completability.** A sufficient condition: some owner o and C ⊆ J such that X_o = B_o ∪ (J ∖ C)
threatens no agent x ≠ o *holding its base alone* (max_h v_x(X_o ∖ h) ≤ v_x(B_x)), and |C| ≤ S_o(C), the number of
slots of the agents other than o with frozen status computed from the owner's needs N_o^X. Then C can go into those
slots in any way. Its *deficit* is def(P) := |J| − S if that is ≤ 0, and otherwise the least value of |C| − S_o(C) over
the free owners o and the sets C ⊆ J that leave nobody threatened; P is removal-only completable iff def(P) ≤ 0.
