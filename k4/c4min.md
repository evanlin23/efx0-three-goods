# C₄ᵐⁱⁿ: all-pairs configurations at the fewest frozen agents

Workstream `proof/k4-c4min`, ledger rows K4.C4MIN.* (CONJECTURE / EVIDENCE only), ledger open item 18. Starting
point: conjecture C₄ᵐⁱⁿ of `k4/c4x.md` §5 (PR #36, branch `proof/k4-c4x`), with its space 𝒫 of valid pre-allocations,
its completability test and its deficit. Notation as there and in `k4/lb4.md` §1. This file does not edit #36's files.

**Target (C₄ᵐⁱⁿ).** For every strict profile of every k = 4 core, some P ∈ 𝒫 with the fewest frozen agents has
deficit ≤ 0 (a removal-only completion). By Theorem 1′₄ (`lean/EFX/PreAllocK.lean`), K4.TIE and K4.CORE it implies
TARGET₄.

**Status.** Not a proof of C₄ᵐⁱⁿ. What is here:
- **A reformulation** (§1, Lemma 1): at the fewest frozen agents f, C₄ᵐⁱⁿ holds on a profile iff some *configuration*
  is completable. A configuration keeps a needed set 𝒩 of size f fixed. The frozen agents hold its goods. Every other
  agent holds a *pair* of goods outside 𝒩 that is admissible (it needs only goods of 𝒩). The ω leftover goods form a
  *pool* that goes to the owner. Lemma 1(a) (configuration ⟹ deficit ≤ 0) is proved. The converse is checked
  computationally: the configuration test and the deficit of `k4/c4x.md` agree on every profile tested.
- **Theorem Z** (§3, written proof, not yet reviewed): **C₄ᵐⁱⁿ holds on every strict profile whose fewest frozen
  agents is 0.** Take an all-pairs allocation that maximizes the number of *robust* agents (agents that hold at least
  half their value), then the sum of levels. Its owner-to-threatened map is a permutation whenever no owner is valid
  (Lemma P). Rotating pairs along a cycle of it produces a robust agent (Lemma R), unless every agent holds its top
  with a good it does not value; then the pool is worthless to everyone, which a core forbids. This covers the cores
  H_t for every t (`k4/c4.md` §7 on PR #33), the family on which LB₄ʳ with any fixed number of rotations fails.
  Every step is checked by brute force (§3.5), and the theorem exhaustively on every profile with n ≤ 3.
- **Theorem F** (§3.6, written proof, not yet reviewed): the same holds whenever some configuration at the fewest
  frozen agents has only *robust* frozen agents (each values its frozen good at least as much as all its goods outside
  the needed set). Such agents are never threatened, Theorem Z's argument runs among the free agents, and a cycle of
  frozen agents replaces the last step.
- **Conjecture Φ′** (§4): in general, every configuration maximizing Φ′ = (−#frozen agents threatened by the pool
  alone, #robust agents, Σ levels, −#pool goods valued by frozen agents) is completable. Evidence: every profile with
  n ≤ 3, every profile of the n = 4 cores with one 4-good agent, and samples of every class with n = 4 and 5.
  - Its first form Φ, without the last term, is false: two n = 4 profiles.
  - Theorems Z and F cover 38–99% of the profiles with ω ≥ 1 at n ≤ 5, depending on the class: 94% at n = 3, and 56–89% at
    n = 4 (§4 table). What remains is the
    profiles where every configuration has an *exposed* frozen agent, including every profile with f = 1.
  - §4 also gives an *exchange digraph* whose cycles unify all the moves used so far, the measured move catalogue, the
    exact gap, and a roadmap for f = 1.
- **k = 3:** C₄ᵐⁱⁿ follows from Theorem K3 of `k4/c4x.md` (§4, last paragraph).

Nothing here changes K4.D or K4.T.

## 1. Configurations

Fix a strict profile of a k = 4 core (agents with |R_i| ∈ {3, 4}, strictly balanced, all nonempty subset sums of
each R_i distinct; every good relevant to some agent). 𝒫, needs, validity, frozen agents F, slots, ω = |J| − S =
|F| − σ (σ = 2n − m) and the deficit are those of `k4/c4x.md` §1. Let f be the fewest frozen agents over 𝒫. If
f ≤ σ, then ω ≤ 0 at a min-frozen P, and its completion without owner has deficit ≤ 0; so assume ω = f − σ ≥ 1.

**Needed sets are rigid at the minimum.** If P ∈ 𝒫 has f frozen agents and P′ ∈ 𝒫 has NA(P′) ⊆ NA(P), then
NA(P′) = NA(P), since |F(P′)| = |NA(P′)| ≥ f = |NA(P)|. So a *needed set* 𝒩 := NA(P) of a min-frozen P determines a
class 𝒫_𝒩 = {P′ ∈ 𝒫 : NA(P′) ⊆ 𝒩} of min-frozen pre-allocations. Inside it, moves are free to lower an agent's
value as long as its new needs lie in 𝒩. An example is LB⁺'s rotation (`proofs/lb_last_step.md` Theorem B) with any
admissible base for the rotated agent: the chain start takes an admissible set, every chain agent moves up, and the
terminal at the end becomes frozen.

For an agent i and a needed set 𝒩 write U_i = R_i ∖ 𝒩. A set A ⊆ U_i with |A| ≤ 2 is *admissible* (for 𝒩) if every
good of U_i ∖ A is worth less to i than A, i.e. N_i(A) ⊆ 𝒩. A set worth more to i than an admissible set is
admissible. With 𝒩 = ∅ (f = 0), admissible means: A contains i's top, or A is a pair worth more than i's top (a
*rich pair*).

**Definition (configuration).** A configuration at a needed set 𝒩 of a min-frozen P consists of:
- the frozen agents F of such a P with their goods φ(x) (x ∈ F), so φ(F) = 𝒩;
- for every other agent y (*free*), a pair Q_y ⊆ M′ := M ∖ 𝒩 of two goods with Q_y ∩ U_y admissible, the pairs
  pairwise disjoint;
- the *pool* L := M′ ∖ ⋃ Q_y, with |L| = |M′| − 2(n − f) = ω.

A free agent o is a *valid owner* if some C ⊆ X := Q_o ∪ L has the following properties.
- X ∖ C contains an admissible set of o.
- |C| is at most the number of frozen agents that stop being frozen when the owner's needs are taken from X ∖ C:
  agents x whose φ(x) is needed by no agent other than o, and not by o's needs from its bundle
  (N_o^X = {g ∈ R_o ∖ X : v_o(g) > v_o(X ∖ C)}).
- No agent x ≠ o strongly envies X ∖ C while holding H_x: H_x = {φ(x)} for x ∈ F, H_y = Q_y for free y. That is,
  max_{h ∈ X∖C} v_x((X ∖ C) ∖ h) ≤ v_x(H_x).

The configuration is *completable* if it has a valid owner.

**Lemma 1.** (a) If some configuration of a profile is completable, C₄ᵐⁱⁿ holds on that profile.
(b) (computational, not proved) Conversely, if C₄ᵐⁱⁿ holds on a profile with ω ≥ 1, some configuration is completable.
`k4/c4min.c -X` compares the two on every profile it runs (the deficit of every min-frozen P against the
configuration test). 0 mismatches: all 189,216 profiles with n = 2, and 153,000 random profiles with n = 3
(`results/k4_c4min_xcheck.log`).

*Proof of (a).* Let o be a valid owner with its set C. Define P by these bases:
- B_x = {φ(x)} for x ∈ F;
- B_y = Q_y ∩ U_y for free y ≠ o;
- B_o = an admissible set of o inside X ∖ C.

Each frozen agent's needs are those it has in the min-frozen pre-allocation the configuration comes from, so they lie
in 𝒩. The free agents' needs lie in 𝒩 by admissibility. So NA(P) ⊆ 𝒩, every good of 𝒩 is a one-good base, P is
valid, and it has f frozen agents (rigidity). Its junk is J = M′ ∖ ⋃ B_i. The removal set C_P := C ∪
⋃_{y ≠ o free} (Q_y ∖ U_y) leaves the owner exactly B_o ∪ (J ∖ C_P) = X ∖ C. It fits:
- the goods of Q_y ∖ U_y fill the 2 − |B_y| slots of the free agents y ≠ o;
- the goods of C fill one slot each of the agents that the owner's bundle unfreezes.

So |C_P| ≤ S_o(C_P). No agent other than o is threatened by X ∖ C holding its base: for a free y, v_y(B_y) = v_y(Q_y).
Hence def(P) ≤ 0. ∎

At f = 0 there are no frozen agents, C = ∅, and a configuration is an *all-pairs allocation* (§3). The unfreezing
clause matters in general: without it the configuration test fails on 720 profiles with n = 2 on which the deficit is
≤ 0. In those profiles two 4-good agents share their top, the holder is frozen only because the owner needs it, and
the owner's bundle is worth more than that good.

## 2. Evidence for C₄ᵐⁱⁿ in configuration form, and the potentials

`k4/c4min.c` enumerates, for every strict profile of a core, the valid pre-allocations. It finds the fewest frozen
agents and the keys (𝒩, φ), enumerates every configuration of every key, tests each one exactly, and computes
potentials. `k4/c4min_run.py` drives it over the certificate files `results/k4_certs_*.json.gz`. `k4/c4min_lib.py` is a
separate Python implementation of 𝒫, the deficit and the exact completability test, written from the definitions.
All potentials are maximized; lexicographic ones are written as tuples.

Features of a configuration:
- r (robust agents): frozen x with U_x (plus a good x does not value) not threatening φ(x), and free y with
  v_y(Q_y) ≥ v_y(U_y ∖ Q_y);
- Σℓ: the sum of the levels of the holdings, ℓ_i(S) = #{T ⊆ R_i : v_i(T) < v_i(S)};
- t: the number of frozen agents strongly envying the pool L plus a good they do not value, i.e. threatened by L
  alone whoever the owner is.

(The evidence table is in §5.)

## 3. Theorem Z: no frozen agent

Throughout this section the profile has fewest frozen agents 0 and m ≥ 2n + 1 (for m ≤ 2n, ω ≤ 0 and there is nothing
to prove). So some P ∈ 𝒫 has no needs at all: its bases are pairwise disjoint admissible sets (𝒩 = ∅).

### 3.1 Definitions

- An **all-pairs allocation** (APA) is a family of pairwise disjoint pairs Q_1, …, Q_n ⊆ M, |Q_i| = 2, such that
  Q_i ∩ R_i is admissible: it contains i's top a_i, or it is a pair of R_i worth more than a_i. Its **pool** is
  L = M ∖ ⋃ Q_i, with |L| = m − 2n = ω ≥ 1.
- Agent i is **threatened by** o ≠ i if max_{h ∈ X} v_i(X ∖ h) > v_i(Q_i), where X := Q_o ∪ L. The agent o is a
  **valid owner** if it threatens nobody.
- i is **robust** if v_i(Q_i) ≥ v_i(R_i ∖ Q_i).
- The APA is **pool-optimal** if v_i(Q_i) ≥ v_i(S) for every agent i and every pair S ⊆ Q_i ∪ L.
- r(Q) is the number of robust agents, and Λ(Q) = Σ_i ℓ_i(Q_i ∩ R_i).

**Lemma Z0 (soundness).** If o is a valid owner of an APA, the allocation X_i = Q_i (i ≠ o), X_o = Q_o ∪ L is EFX₀,
and its only bundle with more than two goods is X_o. The pre-allocation with bases Q_i ∩ R_i has no frozen agent and
deficit ≤ 0, so C₄ᵐⁱⁿ holds on the profile.

*Proof.* Take i ≠ j with j ≠ o. Then X_j ∖ h is a single good g. If g ∉ R_i, v_i(g) = 0. Otherwise g ∉ Q_i, and
admissibility gives v_i(g) < v_i(Q_i ∩ R_i) ≤ v_i(X_i). For j = o, the claim is validity. For C₄ᵐⁱⁿ: the bases
B_i = Q_i ∩ R_i have empty needs, so no agent is frozen. The goods of Q_i ∖ R_i fill i's slots (i ≠ o), and the owner
keeps B_o ∪ (J ∖ C) = Q_o ∪ L. Lemma 1(a) with C = ∅. ∎

**Lemma Z1 (existence).** An APA exists. A pair worth more to i than an admissible pair of i is admissible. An APA
maximizing (r, Λ) lexicographically is pool-optimal.

*Proof.* Take pairwise disjoint admissible sets A_i. There are m − Σ|A_i| ≥ Σ(2 − |A_i|) + 1 other goods, so each A_i
can be completed to a pair with other goods. Adding a good keeps admissibility: if g ∈ R_i ∖ A_i is added, the pair is
worth more than A_i, hence more than every good outside it. For the second claim, let v_i(S) > v_i(Q_i) with Q_i ∩ R_i
admissible, and g ∈ R_i ∖ S. If g ∈ Q_i, then v_i(g) ≤ v_i(Q_i) < v_i(S). If g ∉ Q_i, then v_i(g) < v_i(Q_i) < v_i(S).

For the third claim, suppose some agent i has a pair S ⊆ Q_i ∪ L with v_i(S) > v_i(Q_i). Replace Q_i by S and put
the rest of Q_i into the pool. This is an APA (S is admissible). Nobody else changes. i's level rises strictly, since
Q_i ∩ R_i itself counts in ℓ_i(S). i stays robust if it was: v_i(S) > v_i(Q_i) and v_i(R_i ∖ S) < v_i(R_i ∖ Q_i). So
(r, Λ) rises, a contradiction. ∎

### 3.2 Who can be threatened (Lemma Z2)

Every admissible pair of a 3-good agent with two goods of R_i is robust: {a, x} against one good, and {b, c} against
a < b + c (balance). A 4-good agent holding {a, b} or {a, c} is robust (a + b > c + d, a + c > b + d). So an agent i
that is **not robust** is of one of these three *kinds*:
- **(T)** Q_i ∩ R_i = {a_i}: i holds its top and a good it does not value (3-good or 4-good);
- **(D)** Q_i = {a_i, d_i}, i 4-good, v(a_i) + v(d_i) < v(b_i) + v(c_i);
- **(R)** Q_i = {p_i, q_i} ⊆ R_i ∖ {a_i}, i 4-good, a rich pair (p + q > a) that is not robust. Write s_i for i's fourth
  good (R_i = {a_i, p_i, q_i, s_i}).

**Lemma Z2.** Let the APA be pool-optimal, and o ≠ i.
- (a) A robust agent is threatened by nobody.
- (b) If i is of kind (T), then L ∩ R_i = ∅. i is threatened by o iff Q_o ⊆ R_i ∖ {a_i} and v_i(Q_o) > v_i(a_i).
- (c) If i is of kind (D), i is threatened by o iff Q_o = {b_i, c_i}.
- (d) If i is of kind (R), i is threatened by o iff a_i ∈ Q_o, s_i ∈ Q_o ∪ L and v(a_i) + v(s_i) > v(p_i) + v(q_i).
- (e) Every agent is threatened by at most one o.

*Proof.* Let X = Q_o ∪ L; |X| ≥ 3 and X ∩ R_i ⊆ R_i ∖ Q_i.
- (a) Every h has v_i(X ∖ h) ≤ v_i(X ∩ R_i) ≤ v_i(R_i ∖ Q_i) ≤ v_i(Q_i).
- (b) A good g ∈ L ∩ R_i would give the pair {a_i, g} ⊆ Q_i ∪ L, worth more than Q_i, so L ∩ R_i = ∅. As L ≠ ∅,
  X ⊄ R_i, so the threat is v_i(X ∩ R_i) = v_i(Q_o ∩ R_i) > v_i(a_i). Every good of R_i ∖ {a_i} is worth less than
  a_i, so both goods of Q_o are in R_i ∖ {a_i}.
- (c) Pool-optimality puts b_i, c_i outside L ({a, b} beats {a, d}), so X ∩ R_i ⊆ {b_i, c_i} ∩ Q_o. One good is worth
  less than a_i. So both are in Q_o, and the threat is b + c > a + d.
- (d) X ∩ R_i ⊆ {a_i, s_i}. A single good is worth at most a_i < p + q (rich pair), so both a_i and s_i lie in X, and,
  as |X| ≥ 3, the threat is v(a_i) + v(s_i). a_i ∉ L by pool-optimality ({a_i, p_i} beats {p_i, q_i}), so a_i ∈ Q_o.
- (e) Robust agents: none. (T): two such o would hold disjoint pairs inside R_i ∖ {a_i}, which has at most three goods.
  (D): Q_o = {b_i, c_i}. (R): o holds a_i. ∎

**Lemma P (the threat map is a permutation).** If a pool-optimal APA has no valid owner, choose for every agent o an
agent σ(o) that o threatens. Then σ is a permutation of N without fixed points, every agent is threatened (by exactly
one agent), and no agent is robust.

*Proof.* σ(o) ≠ o, and σ is injective by Lemma Z2(e). So it is a bijection of the finite set N, and every agent is
threatened, hence not robust by Z2(a). ∎

### 3.3 Rotations (Lemma R)

**Lemma R.** Let a pool-optimal APA have no valid owner, σ as in Lemma P, and c_1, …, c_k a cycle of σ
(σ(c_j) = c_{j+1}, indices mod k). The *rotation* gives c_{j+1} the pair Q_{c_j} for every j. The other agents and the
pool do not change. The rotation is an APA, and:
- (i) if c_{j+1} is a 3-good agent, or of kind (D), it is robust after the rotation;
- (ii) if c_{j+1} is of kind (R) and s := s_{c_{j+1}} ∈ Q_{c_j}, it is robust after the rotation;
- (iii) if c_{j+1} is of kind (R) and s ∈ L, the *modified rotation* is an APA in which c_{j+1} is robust. It is the
  rotation except that c_{j+1} gets {a_{c_{j+1}}, s}, and the other good y of Q_{c_j} goes to the pool in place of s.

*Proof.* The pairs are permuted along the cycle, so they stay pairwise disjoint. In (iii), s leaves the pool, y enters
it, and nothing else changes. c_{j+1} is threatened by c_j, and Lemma Z2 gives admissibility.
- Kind (T): Q_{c_j} ⊆ R_{c_{j+1}} ∖ {a} is worth more than a, a rich pair. A 3-good agent holding two of its goods is
  robust.
- Kind (D): Q_{c_j} = {b, c}, rich (b + c > a + d > a) and robust against {a, d}.
- Kind (R): a ∈ Q_{c_j}, so the new pair contains the top. In (ii) the pair is {a, s}, robust by Z2(d)'s threat
  inequality a + s > p + q. In (iii) it is {a, s}, admissible and robust for the same reason.

All other agents keep their pairs. ∎

### 3.4 The theorem

**Theorem Z.** Let the profile (of a k = 4 core, strict) have fewest frozen agents 0 and m ≥ 2n + 1. Every APA that
maximizes (r, Λ) lexicographically has a valid owner. Hence (Lemma Z0) C₄ᵐⁱⁿ holds on the profile, and it has an
EFX₀ allocation in which at most one bundle has more than two goods.

*Proof.* Let Q maximize (r, Λ). It is pool-optimal (Lemma Z1). Suppose it has no valid owner. By Lemma P, r(Q) = 0,
so no APA has a robust agent. By Lemma P every agent lies on a cycle of σ, and by Lemma R an APA with a robust agent
would exist if some agent were 3-good or of kind (D) or (R). So every agent is a 4-good agent of kind (T). By Lemma
Z2(b), L ∩ R_i = ∅ for every i. The goods of L (there are ω ≥ 1 of them) are then relevant to no agent. That
contradicts the definition of a core (every good is relevant to some agent). ∎

*What is used.* Strict values; |R_i| ≤ 4; balance of 3-good agents (so that {b, c} is admissible and robust); every
good relevant to someone; m ≥ 2n + 1. The private-goods rule of cores and connectivity are not used.

*An algorithm.* The proof is effective. Starting from any APA:
1. apply pool improvements until the APA is pool-optimal (each raises Λ and keeps r, so there are at most 15n of
   them, as each level is below 2⁴);
2. if no owner is valid, then r = 0 (Lemma P), and one rotation of Lemma R gives an APA with r ≥ 1;
3. apply pool improvements again (r never drops).

Now the APA is pool-optimal with r ≥ 1, so some owner is valid by Lemma P. At most one rotation is needed. Finding
the first APA, i.e. disjoint admissible sets, is the only step not shown to be polynomial.

**Corollary Z.** C₄ᵐⁱⁿ holds on every H_t (t ≥ 1), the cores of `k4/c4.md` §7 (PR #33) on which LB₄ʳ with index
insertion needs ⌈2t/3⌉ nested rotations. H_t has fewest frozen agents 0: y_j takes {a_{j,1}}, x_{j,1} its private pair
{b_{j,1}, c_{j,1}} (6 + 4 > 8), x_{j,2} and x_{j,3} their tops, ℓ takes g_1. These bases are pairwise disjoint and
admissible. Also m = 10t + 3 ≥ 2(4t + 1) + 1.

### 3.5 Checks against brute force

`k4/c4min_z.py` (Python, from the definitions of §3.1, independent of `k4/c4min.c`) enumerates every APA of every
profile with fewest frozen agents 0 and ω ≥ 1, and checks:
- **A:** Lemma Z2(e) at every pool-optimal APA, and Z2(a) at every APA;
- **B:** Lemma P and Lemma R at every pool-optimal APA without a valid owner (σ is a permutation; the rotation of each
  cycle is an APA with a robust agent unless the cycle is all 4-good (T));
- **C:** no pool-optimal APA has only 4-good agents of kind (T);
- **D:** Theorem Z itself: every (r, Λ)-maximum has a valid owner.

`k4/c4min.c` checks D again (potential `9,16` with `-f 0`), exhaustively.

(Results in §5.)

### 3.6 Extension: frozen agents that are robust (Theorem F)

Now let f ≥ 0 be arbitrary. A frozen agent x of a configuration is **robust** if v_x(U_x) ≤ v_x(φ(x)): all its goods
outside 𝒩 together are worth at most its frozen good. Every owner's bundle lies in M′, so X ∩ R_x ⊆ U_x and a robust
frozen agent is never threatened, whoever the owner is and whatever it keeps. A configuration is **frozen-robust** if
all its frozen agents are robust. Robustness of free agents, pool-optimality, r and Λ are defined as in §3.1 with the
free agents' pairs. r counts the robust frozen agents too, and Λ adds the frozen agents' levels ℓ_x({φ(x)}).

**Theorem F.** Suppose some configuration at the fewest frozen agents is frozen-robust (ω ≥ 1). Take a frozen-robust
configuration that maximizes (r, Λ) among frozen-robust configurations. Then it has a valid owner with C = ∅ (no
unfreezing is needed). So C₄ᵐⁱⁿ holds on the profile.

At f = 0 every configuration is frozen-robust, and Theorem F is Theorem Z. Every frozen agent at f = 1 is non-robust:
its frozen good is its top (all goods above it are in 𝒩, which has one good), and balance gives v(U_x) = v(R_x) −
v(top) > v(top). So Theorem F says nothing about f = 1.

*Proof.* The proof of §3.2–§3.4 carries over with these changes.
- **Pool-optimality.** A pool improvement of a free agent keeps 𝒩 and φ, so the configuration stays frozen-robust
  (robustness of a frozen agent does not depend on the pool), and (r, Λ) rises as in Lemma Z1. A pair worth more than
  an admissible pair of y is admissible (Lemma Z1 with U_y in place of R_y).
- **Kinds (Lemma Z2 with U_y).**
  - A free agent with |U_y| ≤ 2 is robust.
  - With |U_y| = 3, every admissible pair inside U_y is robust (a pair of U_y against one good; {u₂, u₃} is admissible
    only if worth more than u₁). So the only non-robust state is **(T3)**: y holds u₁ (the top of U_y) and a good
    outside U_y, with v(u₁) < v(u₂) + v(u₃). Pool-optimality gives L ∩ U_y = ∅. y is threatened by o iff
    Q_o = {u₂, u₃}, since X ∩ R_y = X ∩ U_y ⊆ Q_o because X ⊆ M′.
  - With |U_y| = 4, U_y = R_y and the kinds (T4) (the old (T) for 4-good agents), (D) and (R) and their threat
    conditions are those of Lemma Z2.

  So every free agent is threatened by at most one owner, and frozen agents by none.
- **Lemma P** becomes: without a valid owner, σ is a permutation of the free agents, and no free agent is robust.
- **Lemma R.** A (T3) agent that receives Q_{c_j} = {u₂, u₃} is robust (a pair of U_y against u₁ < u₂ + u₃). (D) and
  (R) are as before. The rotations do not touch the frozen agents. The modified rotation changes the pool, which does
  not matter because robust frozen agents are never threatened. So at the maximum every free agent is of kind (T4): a
  4-good agent with all four goods outside 𝒩, holding its top.
- **The last step.** Now every free agent holds its top and needs nothing.
  - If f = 0, the pool is worthless to everyone, as in Theorem Z.
  - If f ≥ 1, every good of 𝒩 is needed (the fewest frozen agents), and only frozen agents can need it. So every
    frozen agent's good is needed by another frozen agent, and there is a cycle x₁, …, x_k of frozen agents with
    φ(x_i) ∈ N_{x_{i+1}}. Rotate it: x_{i+1} takes φ(x_i). Every rotated agent gets a better good of 𝒩, so its needs
    shrink (they stay in 𝒩), it stays robust, and it is still frozen (its good is in 𝒩 = NA by rigidity). The free
    agents and the pool do not change. The new configuration is frozen-robust, r does not drop, and Λ rises strictly.
    That is a contradiction. ∎

The proof is effective in the same way as Theorem Z's: pool improvements, rotations of Lemma R, and rotations of
frozen cycles each raise (r, Λ) and keep the configuration frozen-robust. As r ≤ n and Λ ≤ 15n, O(n²) moves reach a
configuration with a valid owner from any frozen-robust configuration.

*Checks.* `k4/c4min_f.py` checks Theorem F and its lemmas on every frozen-robust configuration of the profiles it
examines. It checks the analogues of A–D, and for C that a frozen improving cycle exists when every free agent is
(T4). `k4/c4min.c` checks the maximum of (allrobF, r, Λ) (potential `23,9,16`) on the profiles that have a
frozen-robust configuration (`-A`).

(Results in §5.)

## 4. Exposed frozen agents: the conjecture and the gap

Theorems Z and F leave the profiles on which every configuration at the fewest frozen agents has an **exposed**
frozen agent x, i.e. v_x(U_x) > v_x(φ(x)). These include every profile with f = 1: the frozen agent sits on its top,
and balance makes it exposed. Coverage of the profiles with ω ≥ 1 (`k4/c4min.c` counters covZ / covF / f1 /
uncovered):

| class | profiles (ω ≥ 1) | Theorem Z (f = 0) | Theorem F (f ≥ 2, frozen-robust) | f = 1 | f ≥ 2, not frozen-robust | log |
|---|---|---|---|---|---|---|
| n = 2, every profile | 105,120 | 103,824 | 0 | 1,296 | 0 | `k4_c4min_z_n3.log`, `k4_c4min_phi_n3.log` |
| n = 3, every profile | 119,640,516 | 112,040,608 | 315,364 | 7,284,544 | 0 | the same |
| n = 4, one 4-good agent, every profile | 102,434 | 31,104 | 26,942 | 28,478 | 15,910 | `k4_c4min_n4.log` |
| n = 4, two 4-good agents, 1,000 per core | 41,625 | 30,490 | 1,944 | 8,367 | 824 | the same |
| n = 4, three, 1,000 per core | 103,540 | 87,331 | 1,730 | 13,717 | 762 | the same |
| n = 4, pure, 1,000 per core | 102,033 | 90,011 | 751 | 10,819 | 452 | the same |
| n = 5, one 4-good agent, 50 per core | 475 | 50 | 133 | 118 | 174 | the same |
| n = 5, two, 50 per core | 9,539 | 4,461 | 1,160 | 2,760 | 1,158 | the same |
| n = 5, pure, 50 per core | 78,992 | 63,328 | 1,141 | 13,209 | 1,314 | the same |

**Conjecture Φ (first form, false).** Every configuration at the fewest frozen agents that maximizes Φ = (−t, r, Λ)
(lexicographic) has a valid owner. Here t is the number of frozen agents threatened by the pool alone
(v_x(L ∩ U_x) > v_x(φ(x))), and r and Λ are the robust count and the level sum of §3.6.
- It holds on every profile with n ≤ 3 and on every profile of the n = 4 cores with one 4-good agent.
- It fails on two sampled profiles with n = 4 (smallest n; instance 7 of `attempts/k4-c4min-potentials.md`, replayed
  by both implementations).
- There, two Φ-maxima with no valid owner differ from a completable one only in *which* good, worthless to it, a robust
  free agent keeps in its pair. That good protects a frozen agent when it stays out of the pool, and Φ does not see
  it.

**Conjecture Φ′ (K4.C4MIN.PHI).** For every strict profile of every k = 4 core with ω ≥ 1, every configuration at the
fewest frozen agents that maximizes

  Φ′ = (−t, r, Λ, −p)  (lexicographic),  p = Σ over frozen x of |L ∩ U_x|,

has a valid owner. It implies C₄ᵐⁱⁿ (Lemma 1(a)).
- At f = 0, t = p = 0 and Φ′ is Theorem Z's potential.
- Φ′ only breaks Φ's ties, so its maxima are Φ-maxima, and Φ′ holds wherever Φ does.
- At the tested maxima no unfreezing is needed: the owner test with C = ∅ gives the same result for n ≥ 3 (`-U0`). At
  n = 2 unfreezing is needed, on 720 profiles.

Evidence (every maximum of Φ′ completable; §5):
- every profile with n ≤ 3;
- every profile of the n = 4 cores with one 4-good agent;
- 1,000 random profiles per core for the other n = 4 classes, then 4,000 per core with f ≥ 1 (both Φ counterexamples
  included);
- 50 per core at n = 5, then 150 or 60 per core with f ≥ 1.

The tie-break "fewest frozen agents threatened by some owner" works on the same samples.

Simpler potentials fail. Their failing instances, replayed by the independent Python implementation, are in
`attempts/k4-c4min-potentials.md`:
- r alone fails at f = 0 (n = 3);
- (r, Λ) and Λ fail at f = 1 (n = 3), where the pool completes a frozen agent's threatening triple;
- (−t, Λ) fails at f = 2 (n = 3);
- Pareto-maximality fails at f ≥ 1 (n = 3);
- Φ = (−t, r, Λ) and (−t, leximin) fail at f = 2 (n = 4).

**Structure at the maxima** (n = 3, f ≥ 1, 1,209 maxima; n = 4 samples, 872 maxima; `k4/c4min_moves.py --maxima`,
`results/k4_c4min_moves.log`):
- every maximum is pool-optimal and has t = 0;
- at n = 3 every agent is threatened by at most one owner;
- at n = 4 a frozen 4-good agent can be threatened by two owners (4 maxima), and 40–45% of the maxima have a frozen
  agent threatened by some owner;
- none needs the unfreezing clause.

So Lemma P's pigeonhole fails as stated, but it is not needed for the cycle argument below.

**The exchange digraph (what a proof would use).** In a configuration without a valid owner, draw
- an edge o → x for each free agent o and each agent x it threatens (a *threat edge*); and
- an edge x → z for each frozen agent x and each agent z that needs φ(x) (a *need edge*; every frozen agent has one).

Every vertex has an out-edge, so there is a cycle. Moving holdings one step along the cycle is always a configuration
at the same needed set:
- across a threat edge o → y, y takes its best admissible pair from Q_o ∪ L (the rest of Q_o goes to the pool);
- across a need edge x → z, z takes φ(x).

Each vertex gives away exactly what it held. A free vertex has an out-going threat edge and gives its pair. A frozen
vertex has an out-going need edge and gives its good. This one move contains Lemma R's rotation (all threat edges),
the rotation of frozen cycles (all need edges), LB⁺'s rotation (a need chain closed by one threat edge; Theorem B of
`proofs/lb_last_step.md`) and Theorem K3's cycle move (`k4/c4x.md` §3).

Every agent on the cycle gains, with two exceptions:
- a frozen agent of type a > b + c crossing a threat edge becomes free on a pair worth less than its top;
- two receivers can compete for the same pool good.

In any case t and r can move either way: a terminal crossing a need edge becomes frozen and may be exposed. Measured
on the non-completable configurations of sampled profiles with n = 3 and f ≥ 1 (`k4/c4min_moves.py --moves`,
`results/k4_c4min_moves.log`): 403 of 440 have a
Φ-raising (hence Φ′-raising) *pool move* (one free agent improves its pair from the pool without raising t), 36 more a Φ-raising cycle
move, and 1 needs a third kind. In that one the pool move is blocked, because the released good completes a frozen
agent's threatening triple in the pool. A two-agent exchange passes that good to the other free agent instead of the
pool.

**The gap, precisely.** A proof of Conjecture Φ′, hence of C₄ᵐⁱⁿ and TARGET₄, needs a *local improvement lemma*: every
configuration without a valid owner admits a Φ-raising move from a fixed finite catalogue. Pool moves, the cycle moves
above and pool-assisted two-agent exchanges suffice on every non-completable configuration of the samples; which
cycle to take is the open part. Theorems Z and F are the cases where the catalogue is proved sufficient: pool moves,
Lemma R's rotations and frozen cycles. There the exposed frozen agents, the only source of t, of blocked pool moves and
of the exceptions above, are absent.

**Roadmap for f = 1 (not a proof).** Let 𝒩 = {g}, x the frozen agent (on its top g), and A the free agents. Take a
Φ-maximum without a valid owner, and **assume** it is pool-optimal with t = 0 (both hold at every sampled maximum, but
neither is proved). Assume also that x has three goods, so U_x = {b_x, c_x}.
- x is threatened by at most one owner (t = 0 keeps b_x, c_x out of the pool together). Free agents are threatened by
  at most one owner (Lemma Z2). So σ: A → N is injective.
- If x ∉ σ(A), σ permutes A, and every free agent is threatened. A terminal τ (a free agent needing g) exists, and
  with |U_τ| = 2 it would be robust, hence untouchable. So τ is 4-good of kind (T3). The plain rotation of its
  σ-cycle makes τ robust without touching the pool, and Φ rises. Contradiction.
- So x ∈ σ(A). σ is a path w → p₁ → … → x from the unique unthreatened free agent w, plus cycles. A cycle containing
  an agent of kind (T3), (D), or (R) with s in the predecessor's pair rotates plainly and raises r. So the cycles
  contain only (T4) agents and (R) agents with s in the pool, and terminals lie on the path.
- Close the path at a terminal τ = p_j with the need edge x → τ. Rotate: p_{i+1} takes Q_{p_i}, x takes {b_x, c_x}
  (free, robust, needs nothing), τ takes g. Then x gains one unit of r and τ loses at most one. Λ rises except at (R)
  agents, which take {a, y}.

**Open steps:**
- (i) pool-optimality and t = 0 at a maximum;
- (ii) t after the move (τ is newly frozen; its goods b_τ, c_τ must not both end in the pool, and the plain rotation
  sends b_τ ∈ Q_τ to p_{j+1});
- (iii) (R) agents on the path;
- (iv) a 4-good x, which can be threatened by two owners.

**k = 3.** For cores whose agents all have three goods, C₄ᵐⁱⁿ follows from Theorem K3 of `k4/c4x.md` §3 (written
proof, not yet reviewed). Take P Pareto-maximal inside the class 𝒫_𝒩 of a min needed set (§1). Every pre-allocation
that K3's proof constructs (upgrades, frozen cycles, LB⁺'s rotation, the cycle move) makes every moved agent strictly
better off, so its needs shrink and it stays in 𝒫_𝒩. So the contradiction of K3 is reached inside 𝒫_𝒩, and P (with
f frozen agents) is completable, removal-only with the owner's needs from its base.

## 5. Evidence and logs

All counts are strict profiles of the certified core lists `results/k4_certs_*.json.gz` (types from `k4/check4.py`).
"Every max" means every maximum of the potential is completable (the failure count is 0). "ω ≥ 1" profiles are those
where an owner is needed at all.

| claim | scope | result | log |
|---|---|---|---|
| Lemma 1(b) | all n = 2; 153,000 random n = 3 | configuration test = deficit ≤ 0 on every profile | `results/k4_c4min_xcheck.log` |
| Theorem Z (`9,16`, `-f 0`) | every profile with n ≤ 3: 103,824 (n = 2) + 112,040,608 (n = 3) with f = 0, ω ≥ 1; 4.74·10⁹ configurations at n = 3 | every max completable; r alone fails on 7,968 (n = 3); every Pareto-maximum completable (321,213,444 at n = 3) | `results/k4_c4min_z_n3.log` |
| Theorem Z lemmas A–D (Python) | all n = 2 (103,824 profiles with f = 0, ω ≥ 1); 10,000 random profiles per n = 3 core (173,126 with f = 0, ω ≥ 1) | 0 violations; 991,329 pool-optimal APAs, 6,053 of them without a valid owner, each with a rotation of Lemma R giving a robust agent | `results/k4_c4min_zf_python.log` |
| Theorem F lemmas (Python) | 10,000 random profiles per n = 3 core with f ≥ 1 (1,681 have a frozen-robust configuration, all with f = 2); 30 per n = 4 core | 0 violations; at n = 4, 6 pool-optimal frozen-robust configurations without a valid owner, each resolved by a rotation (plain or modified) | `results/k4_c4min_zf_python.log`, `results/k4_c4min_f_n4.log` |
| Theorem F (`23,9,16`, `-A -U0`) | every profile with n ≤ 3, f ≥ 1, having a frozen-robust configuration: 315,364 (all at n = 3, f = 2) | every max completable without unfreezing | `results/k4_c4min_f_n3.log` |
| Conjecture Φ′ (`8,9,16,3`; Φ is `8,9,16`) | every profile with n ≤ 3 and f ≥ 1: 1,296 (n = 2) + 7,599,908 (n = 3) with ω ≥ 1; 1.43·10⁸ configurations at n = 3 | every max of Φ completable, hence of Φ′; also (−t, leximin) and (−t, r, leximin); (r, Λ) fails on 56,928, and on 128 no maximum of it is completable | `results/k4_c4min_phi_n3.log` |
| Theorems Z, F, Conjectures Φ, Φ′ | n = 4: every profile of the 135 cores with one 4-good agent (102,434 with ω ≥ 1); 1,000 random profiles per core for two, three, four 4-good agents; n = 5: 50 per core (one and two 4-good agents, pure) | Theorems Z and F: every max completable everywhere. Φ: one failure (pure n = 4); (−t, leximin): 4 failures (n = 4, one 4-good agent) | `results/k4_c4min_n4.log` |
| Conjecture Φ′ (`8,9,16,3`) | f ≥ 1 only: 4,000 random profiles per core for n = 4 with two, three, four 4-good agents (157,483 with ω ≥ 1); 150 or 60 per core for n = 5 (115,844) | every max of Φ′ completable (Φ fails once more, n = 4 three 4-good agents) | `results/k4_c4min_phi2.log` |
| H_1, H_2 | one profile each | every max of (r, Λ) completable | §3.4 (rerun with `k4/c4min.c`) |
| failing potentials | 7 instances | replayed by both implementations | `results/k4_c4min_attempts.log` |
| structure and moves | n = 3, 4 samples | §4 | `results/k4_c4min_moves.log` |

Independence:
- The C tool `k4/c4min.c` and the Python modules `k4/c4min_lib.py`, `k4/c4min_cfg.py`, `k4/c4min_z.py`,
  `k4/c4min_f.py` share no code, only the type generator `k4/check4.py` and the core lists.
- `k4/c4min.c -X` recomputes the deficit of `k4/c4x.md` §1 directly on every min-frozen pre-allocation.
- #36's `k4/c4x.c` found C₄ᵐⁱⁿ on every profile with n ≤ 3 by a third implementation.

## 6. Reproduce

Each log starts with the `# command:` lines that wrote it. `k4/c4min_run.py` compiles `k4/c4min.c` into the temporary
directory under a name made from a hash of the source (`C4MIN_BIN` overrides the path). Options of `k4/c4min.c`:
- `-p "f,f;f"`: potentials, as feature indices, lexicographic, maximized. Index 8 is −t, 9 is r, 16 is Λ, 17 is
  leximin, 20 pool-optimality, 23 "all frozen robust"; the full list is `fname` in `k4/c4min.c`.
- `-f K` only profiles with fewest frozen agents K, and `-F1` only those with K ≥ 1.
- `-A` only profiles with a frozen-robust configuration.
- `-U0` the owner test without unfreezing.
- `-Q` Pareto-maxima.
- `-X` the cross-check with the deficit.
- `-R0` only profiles where no configuration has a robust agent.
- `-x N` examples.

Times on 4 CPUs:
```
python3 k4/c4min_run.py results/k4_certs_2.json.gz -X -p 9,16 --jobs=1              # Lemma 1(b), n = 2: ~3 s
python3 k4/c4min_run.py results/k4_certs_2.json.gz results/k4_certs_3.json.gz -f 0 -Q -p "9,16;9;16" --jobs=3   # Theorem Z, n <= 3: ~35 min
python3 k4/c4min_run.py results/k4_certs_2.json.gz results/k4_certs_3.json.gz -F1 -p "8,9,16;8,17;8,9,17;9,16" --jobs=3
python3 k4/c4min_run.py results/k4_certs_2.json.gz results/k4_certs_3.json.gz -F1 -A -U0 -p "23,9,16" --jobs=3
python3 k4/c4min_z.py results/k4_certs_2.json.gz                                     # lemmas of Theorem Z: ~70 s
python3 k4/c4min_f.py results/k4_certs_3.json.gz --rand=10000 --seed=22 --minf=1      # lemmas of Theorem F
python3 k4/c4min_moves.py results/k4_certs_3.json.gz --rand=100 --seed=45 --moves     # §4 move catalogue
python3 attempts/k4_c4min_attempts.py                                                # attempts: ~1 min
```
