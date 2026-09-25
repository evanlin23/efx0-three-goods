# LB₄: construction LB⁺ carried to four goods

Workstream `proof/k4-lb4`, ledger open item 15 (the LB₄ route of `k4/SCOUT.md` §5, steps (a)–(d)). Notation as in
`proofs/construction.md` and `proofs/lb_last_step.md` (k = 3), and `k4/SCOUT.md` (k = 4 cores). Tools:
`k4/lb4.c` (the construction and an exhaustive tester), `k4/lb4_run.py` (driver), `k4/lb4_brute.py` (every EFX₀
allocation of a small instance, by brute force).

**Status.** Work in progress. §1 (soundness) is a written proof, not yet reviewed. Nothing else here is proved.

## 0. Setting

An *instance* has agents N = [n] and goods M = [m], additive valuations, and relevant sets R_i = {g : v_i(g) > 0}.
Each agent has a fixed strict order ≻_i on R_i that is consistent with its values (v_i(g) > v_i(h) ⇒ g ≻_i h; ties
broken by index). In a k = 4 core |R_i| ∈ {3, 4} and every agent is strictly balanced, but §1 uses neither. An
allocation X is EFX₀ if v_i(X_i) ≥ v_i(X_j ∖ {h}) for all i ≠ j and h ∈ X_j. A bundle of one good is never strongly
envied.

## 1. Pre-allocations and their soundness (any k)

**Definition.** A *pre-allocation* P assigns to every agent i a *base* B_i ⊆ R_i, the bases pairwise disjoint. Its
*junk* is J = M ∖ ⋃ B_i. The *needs* of i are
- N_i = {g ∈ R_i : g ≻_i Y} if B_i = {Y} (one good), and N_i = R_i if B_i = ∅;
- N_i = {g ∈ R_i ∖ B_i : v_i(g) > v_i(B_i)} if |B_i| ≥ 2.

NA = ⋃ N_i is the *needed-alone set*. P is *valid* if
- **(V1)** J ∩ NA = ∅, and
- **(V2)** B_i ∩ NA = ∅ whenever |B_i| ≥ 2.

In a valid P every good of NA is the whole base of exactly one agent. Such an agent is *frozen* (F). The others are
*free*. A free agent with |B_i| ≤ 2 has cap(i) = 2 − |B_i| *slots*; frozen agents have cap 0.

At k = 3 this is `proofs/lb_last_step.md` §2: picks are one-good bases, and an upgraded agent u has B_u = {b_u, c_u},
whose needs are empty because a_u < b_u + c_u.

**Completions.** Let o be a free agent (the *owner*) or no agent. A completion places every junk good: X_i = B_i ∪ C_i
for i ≠ o, with C_i ⊆ J and |C_i| ≤ cap(i); X_o = B_o ∪ (the rest of J). With no owner, all of J goes to slots, and
then every base has at most 2 goods. The owner's needs may be taken from its final bundle:
N_o^X = {g ∈ R_o ∖ X_o : v_o(g) > v_o(X_o)}. This only shrinks N_o (if |B_o| = 1, v_o(g) > v_o(X_o) ≥ v_o(Y) gives
g ≻_o Y; if |B_o| ≥ 2, v_o(X_o) ≥ v_o(B_o)), so the pre-allocation with N_o replaced by N_o^X is still valid, and it may
have fewer frozen agents and more slots. Below, NA, F and the slots are those after this replacement.

The completion satisfies the *owner constraint* (OC₄) if for every agent j ≠ o and every h ∈ X_o,
v_j(X_o ∖ {h}) ≤ v_j(X_j).

**Theorem 1′₄ (soundness).** Let P be valid, and X a completion of P that satisfies (OC₄), in which only the owner's
bundle may have more than 2 goods and frozen agents hold exactly their base. Then X is EFX₀.

*Proof.* Fix i and j ≠ i with |X_j| ≥ 2. If j = o, (OC₄) is the claim. Otherwise |X_j| = 2 and j is free, so X_j
consists of goods of B_j and of J. Neither meets NA: J by (V1); B_j by (V2) if |B_j| = 2, and if B_j = {Y_j}, because
j is not frozen. For h ∈ X_j, X_j ∖ {h} is one good g, and v_i(g) ≤ v_i(X_i) is needed. If g ∉ R_i, v_i(g) = 0.
Otherwise g ∈ R_i ∖ N_i, and g ∉ B_i (bases are disjoint and g ∈ X_j).
- If B_i = ∅: N_i = R_i, impossible.
- If B_i = {Y}: g ⊁_i Y and g ≠ Y, so Y ≻_i g and v_i(g) ≤ v_i(Y) ≤ v_i(X_i).
- If |B_i| ≥ 2 and i ≠ o: v_i(g) ≤ v_i(B_i) ≤ v_i(X_i) by definition of N_i.
- If i = o with needs N_o^X: g ∉ X_o and g ∉ N_o^X give v_o(g) ≤ v_o(X_o). ∎

Only additivity was used: no balance, no bound on |R_i|, no ordinality. The proof is `proofs/lb_last_step.md`
Theorem 1′ with its two uses of "a_i < b_i + c_i" (an upgraded agent is envy-free, and the pair {b_i, c_i} is the only
threat) replaced by the definition of N_i for bases of two goods and by (OC₄).

**What changes at k = 4.** At k = 3, (OC₄) reduces to (OC): an agent x ∉ U holding its top a_x is threatened iff
{b_x, c_x} ⊆ X_o. At k = 4 the threat depends on the type (`k4/SCOUT.md` K4.OT):
- x holds B_x = {a_x} with lower goods b > c > d. Write Q = X_o ∩ R_x. If X_o ⊄ R_x, x is threatened iff
  v_x(Q) > v_x(X_x); if X_o ⊆ R_x, iff v_x(Q ∖ {d_Q}) > v_x(X_x), with d_Q the least good of Q. Against X_x = {a}, the
  minimal threatening sets are, by the position of a among the pair sums c + d < b + d < b + c:
  a > b + c: only {b, c, d}; b + d < a < b + c: {b, c}; c + d < a < b + d: {b, c}, {b, d}; a < c + d ("flat"): every
  pair. So one good kept out of X_o removes every threat, except for flat agents, which need two.
- x holds B_x = {b_x}: threatened iff {c, d} ⊆ X_o and v(c) + v(d) > v_x(X_x), which depends on the type.
- x holds B_x = {c_x} or {d_x}: never threatened. 3-good agents: as at k = 3.
- Agents with bases of two goods are threatened by type-dependent pairs of their remaining goods.
