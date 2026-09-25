# Hunting for a counterexample to C₄ᵐⁱⁿ

Workstream `compute/k4-c4min-hunt` (the refuter side; the prover side is `proof/k4-c4min`, PR #41), ledger rows
K4.C4MINH.* (EVIDENCE only). Target: conjecture C₄ᵐⁱⁿ of `k4/c4x.md` §5 (PR #36, branch `proof/k4-c4x`, row
K4.C4X.MIN there): for every strict profile of every k = 4 core, some valid pre-allocation in 𝒫 with the fewest frozen
agents has deficit ≤ 0 (is removal-only completable, with the owner's needs from its bundle).

**Status (work in progress; numbers below are final only where a log is cited).** No counterexample found.

Nothing here changes K4.D or K4.T.

## 1. Definitions and tools

Notation of `k4/c4x.md` §1 and `k4/lb4.md` §1. For one strict profile of a k = 4 core:
- 𝒫: bases B_i ⊆ R_i with |B_i| ≤ 2, pairwise disjoint; needs N_i = {g ∈ R_i ∖ B_i : v_i(g) > v_i(B_i)}; valid iff
  every good of NA = ⋃ N_i is the whole base of one agent; frozen agents F (a one-good base in NA), |F| = |NA|;
  cap(i) = 0 for frozen i, else 2 − |B_i|; S = Σ cap; J = the goods in no base.
- def(P) = |J| − S if that is ≤ 0; otherwise the least |C| − S_o(C) over free owners o and C ⊆ J such that
  X_o = B_o ∪ (J ∖ C) threatens no j ≠ o holding B_j alone (max_{h ∈ X_o} v_j(X_o ∖ h) > v_j(B_j)), S_o(C) the slots of
  the agents other than o with frozen status recomputed from the owner's needs N_o^X = {g ∈ R_o ∖ X_o : v_o(g) >
  v_o(X_o)} (variant `-w0`: from its base, S_o = S − cap(o)); +∞ if no (o, C) works.
- f* = the least |F| over 𝒫; d* = the least def over the P ∈ 𝒫 with |F| = f*. **C₄ᵐⁱⁿ holds at the profile iff
  d* ≤ 0.** Since |J| − S = |F| − σ (σ = 2n − m), every min-frozen P has def = f* − σ ≤ 0 when f* ≤ σ: C₄ᵐⁱⁿ can only
  fail where f* > σ ("an owner is needed").
- Weaker forms tracked: (W1) some min-frozen P is completable (exact test, any deficit; `k4/c4x.md` §1's
  "completable"); (W2) K4.D (an EFX₀ allocation with at most one bundle of more than two goods).

Tools (all in `k4/`):
- `c4min_hunt.c`: an exact C₄ᵐⁱⁿ test written from the definitions above; it shares no code with `k4/c4x.c`.
  - Valid pre-allocations are enumerated by a depth-first search with |NA| bounded (static agent order for n ≤ 6,
    dynamic most-constrained-agent order above); f* by branch and bound; then the pre-allocations with |F| = f* are
    enumerated until one has deficit ≤ 0.
  - The deficit is a branch and bound over C: at a node, a threatened agent j is chosen and one branches on the
    nonempty sets D of junk goods of X_o ∩ R_j to move into C (or on making X_o ⊆ R_j). Every threat-free C* contains
    a leaf of this search, and |C| − S_o(C) only grows with C (S_o is non-increasing in C), so the least leaf value is
    the deficit. `-D` replaces it by the plain enumeration of every C ⊆ J; both agree on every profile tested (below).
  - Exhaustive mode (`-E`): the profiles are processed in *slices* (all types of the last agent L at once, as a
    bitmask). A certificate (P, owner o, C) found by the exact search at one profile is turned into a *template*: the
    base options, the need sets of every agent, o and C. Its validity at another profile depends on each agent's type
    only through per-agent conditions: agent i's need set for its base option (so validity, NA, F and S are
    unchanged), "j is not threatened by X_o" for j ≠ o, the owner's slot count S_o(C) (through o's type), and, when
    the template has f > σ frozen agents, f*(profile) ≥ f (computed per slice as a mask: the types of L for which some
    valid P has |NA| ≤ f − 1). Each of these is a mask over L's types, so one template covers many profiles at
    once; templates are cached across slices. A profile is either covered by a template whose conditions hold there
    (so C₄ᵐⁱⁿ holds there) or solved exactly; failures are printed. `-V` re-solves every profile from scratch and
    stops at the first disagreement with the masks.
  - `-1` (one profile: f*, d*, counts, (W1)), `-1q` (f*, holds, a certificate), `-R` (random profiles), `-H`
    (hill-climbing, §3).
- `c4min_brute.py`: a brute-force referee written from the definitions, sharing no code with the C tools or with
  PR #36's `k4/c4x_check.py`: every tuple of bases (itertools), deficits over every C ⊆ J with threats computed
  literally (every h ∈ X_o), completability by every map of the junk goods to agents with (OC₄) checked literally and
  every completion re-checked EFX₀ by the raw definition; K4.D by every allocation; and `verify_certificate` (a
  certificate (bases, owner, C) re-checked literally, the completion built and checked EFX₀).
- `c4min_crosscheck.py` (the three implementations profile by profile), `c4min_hunt_run.py` (exhaustive runs over the
  certificate files of K4.R3–R5c), `c4min_climb.py` (climbing), `c4min_sample.py` (random profiles on families),
  `c4min_families.py` (H_t and other gadget families; random cores), `c4min_common.py`.

## 2. Exhaustive checks

(to be filled)

## 3. Adversarial search

(to be filled)

## 4. Structured families

(to be filled)

## 5. Reproduce

(to be filled)
