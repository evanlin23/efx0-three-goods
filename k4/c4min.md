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
  Every step is checked by brute force (§3.5).
- **Conjecture Φ** (§4): in general (frozen agents allowed), every configuration maximizing Φ = (−#frozen agents
  threatened by the pool alone, #robust agents, Σ levels) is completable. Evidence: every profile with n = 2, samples
  with n = 3 and 4. The proof of Theorem Z breaks at frozen agents in two places, and §4 names both.

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
good relevant to someone; m ≥ 2n + 1. The private-goods rule of cores and connectivity are not used. The proof is by
contradiction, but it is effective: a maximum can be reached by pool improvements and rotations. Each pool
improvement raises (r, Λ). A rotation of Lemma R raises r when r = 0, since every agent was non-robust.

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

## 4. Frozen agents

(In progress.)

## 5. Evidence and logs

(In progress.)
