# DL on the key graph at one frozen agent: repair lemmas from Theorem Z′'s configuration

Workstream `proof/k4-sx` (PR #80), `k4/dl13.md` §6 item 1 (branch `proof/k4-dl13`, PR #75). Ledger rows K4.SX.*:
written proofs nobody else has checked are CONJECTURE ("written proof in `k4/sx.md` §x, not yet refereed"), data rows
EVIDENCE. Nothing here changes K4.D or K4.T.

**Target.** DL on the key graph (`k4/dl13.md` §2.3, Remark): every key κ with least deficit def*(κ) > 0 has a key κ′,
reached by one move of a fixed class from some state of κ, with def*(κ′) < def*(κ). The class was (T3) ∪ (T4); after
the coordinator's refutation at n = 5, f = 3 (below) it is (T3⁺) ∪ (T4) at f ≥ 2. At f = 1 the two coincide: (T4) is
empty and (T3⁺) is (T3). The route asked for is Theorem Z′ (`k4/c4min_reduce.md` §2, K4.C4MIN.RED.Z, PROVED).

**Status.** DL on the key graph is not proved here, at f = 1 or at f ≥ 2. What is here:

- **The f = 1 target is C₄ᵐⁱⁿ at f = 1, per needed good** (§1, Remark 1.2). A (T3) move keeps the frozen good, so DL on
  the key graph at f = 1 makes some key of every needed good completable. A proof of it would therefore also settle the
  big-top case that `k4/c4min_f1.md` §3 and `k4/c4min_reduce.md` §5.1 leave open.
- **The structure at a non-completable key** (§2, Lemma F). Take a configuration at κ that maximizes Theorem Z′'s
  potential (r′, Λ′). Its threats among the free agents form a forest of out-trees. The leaves are exactly the free-valid
  owners, and each leaf threatens the frozen agent x. Every terminal (an agent that needs g) is either a leaf or has a
  threat path down to a leaf. Lemma S: a leaf's bundle never threatens a terminal that holds g.
- **Five repair lemmas** (§3), each a single move with its smallest move class:
  - **A** (owner swap): a terminal leaf takes g, and x owns that leaf's bundle. One (T3) move, no helper. Exception
    θ-b: the leaf is big-top on g, all its lower goods are in its bundle, and ω ≥ 2.
  - **B** (generalized path move): along a threat path τ → q₁ → … → q_k = o from a terminal τ to a leaf o, every
    q_i takes its threatener's pair, τ takes g, and x owns o's whole bundle. For k = 1 this is one (T3) move with
    helper o. For k ≥ 2 it changes k + 2 agents, and it still gives a key (g, τ) with def* ≤ 0, but that key is not
    shown to be a (T3) neighbour. Exception: o is of kind (R) with its fourth good in the pool.
  - **B′** (the modified path move for that exception): it works when the good o gives up is valued by nobody but x.
  - **C** and **C′** (θ-b leaves): another leaf owns. **C**: a θ-b terminal leaf τ₁ takes g, x takes a robust pair
    meeting τ₁'s goods, and another leaf owns the rest. **C′**: the same with two terminals, paid for by unfreezing
    τ₁. Each is one (T3) move without helper, under a hypothesis saying that the goods τ₁ releases are not valued by
    third agents.

  In every case the move ends at a state P′ with def(P′) ≤ 0, so the neighbouring key has def* ≤ 0 < def*(κ).
- **Coverage (EVIDENCE, §4):** every configuration maximizing (r′, Λ′) at every non-completable f = 1 key of the data
  satisfies the hypotheses of A, B (k = 1), B′ (k = 1), C or C′. The data are #53's whole n = 3 catalogue and every
  non-completable key that `k4/red.c` finds in large random n = 4 and n = 5 samples. So on these data, DL on the key
  graph at f = 1 holds through these five lemmas, each applied once from Theorem Z′'s configuration. Every lemma is
  asserted against exact deficits there, with no violation.
- **What remains at f = 1** (§5): a proof that one of A, B₁, B₁′, C, C′ always applies. The open cases are θ-b leaves
  whose released goods third agents value, (R)-leaves whose released good third agents value, and terminals at
  distance ≥ 2 from every leaf (there the target key is completable by B, but (T3)-adjacency is open). Each has its
  data count.
- **f ≥ 2** (§6): the key-graph runs with (T3⁺) ∪ (T4) edges on the catalogues and hunts (EVIDENCE), the coordinator's
  refutation of the (T3) ∪ (T4) form, which this file's tool reproduces, and Lemma A⁺: the owner swap along a need
  chain of frozen agents, which is one (T3⁺) move.
- **Conjecture SX** (`k4/dl13.md` §2.3) is not needed by this route: the lemmas start from Theorem Z′'s configuration,
  not from a deficit-minimal state. It is not proved here.

## 1. Setting

Notation of `k4/c4x.md` §1, `k4/c4min.md` §1, `k4/c4min_reduce.md` §1–§2 and `k4/dl2.md` §4. A strict profile of a
k = 4 core with fewest frozen agents f ≥ 1 and ω = f − (2n − m) ≥ 1. The *key* κ(P) of a min-frozen P ∈ 𝒫 is its set of
frozen agents with their goods. def*(κ) := min{def(P) : P min-frozen, κ(P) = κ} (removal-only deficit, `k4/c4x.md` §1;
Lemma H1: def(P) = ω + 2 − Val*(P)). For a class E of moves, N_E(κ) is the set of keys κ(P′) of the min-frozen P′
reached from some state P of κ by one move of E. **DLK_E** is the statement "every key κ with def*(κ) > 0 has some
κ′ ∈ N_E(κ) with def*(κ′) < def*(κ)". With E = (T3) ∪ (T4) it is `k4/dl13.md`'s DL on the key graph; it implies
TARGET₄ for any E (`k4/dl13.md` §2.3 Remark, with `EFX.C4min.target4_of_defLocal`, K4.STRAT.DL2.LEAN, and Theorem Z at
f = 0). The move classes, with ch the agents whose base changes (both states min-frozen, NA′ = NA):
- **(T3)** exactly one x ∈ ch frozen in P and free in P′; exactly one z free in P and frozen in P′, with B′_z = B_x
  and B_x ⊆ N_z(B_z); no agent of ch frozen in both; at most one more agent h (the *helper*), free in both, with
  B_h ⊄ B′_h (`k4/dl2.md` §3);
- **(T3⁺)** the same, except that W := the agents of ch frozen in both may be nonempty. Then the bases of W ∪ {z} in P′
  are those of W ∪ {x} in P, and z takes a good it needs in P (the coordinator's frozen-chain role swap);
- **(T4)** every agent of ch is frozen in P and in P′.

At f = 1, W = ∅ and there is no (T4) move, so N_{T3⁺ ∪ T4} = N_{T3} = N_{T3 ∪ T4}.

**f = 1.** By `k4/c4min_reduce.md` Lemma K the keys are the pairs (g, x) with g the top of x for which the reduced
instance has disjoint admissible sets. The configurations at (g, x) are the families of disjoint pairs Q_y ⊆ M′ = M ∖ {g}
(y ≠ x) with admissible parts H_y := Q_y ∩ U_y, U_y = R_y ∖ {g}; the pool is L, with |L| = ω. We write A := N ∖ {x}
(the free agents), H_x := {g}, X_o := Q_o ∪ L for o ∈ A, and "o threatens w" (w ≠ o) when θ_w(X_o) > v_w(H_w),
θ_w(Z) := max_{h ∈ Z} v_w(Z ∖ h). A *terminal* is a z ∈ A with g ∈ R_z and v_z(Q_z) < v_z(g); every terminal has top g
(`k4/c4min_reduce.md` Lemma T). P_Q is the state of Q: bases {g} for x and H_y for y ∈ A. A *candidate* (an agent with
top g holding g, every other agent holding a pair of M′ with admissible part, all disjoint) is a configuration at the key
of that agent (`k4/c4min_f1.md` Lemma 1(c), K4.C4MIN.F1). We use that fact for every move below.

**Lemma 0 (per-key form of `k4/c4min.md` Lemma 1).** For every key κ (any f, ω ≥ 1): def*(κ) ≤ 0 iff some
configuration at κ is completable. If a configuration Q at κ has an owner valid with C = ∅, then def(P_Q) ≤ 0.

*Proof.* The proofs of Lemma 1(a) and (b) of `k4/c4min.md` (K4.C4MIN.CFG, PROVED) keep the key. (a) builds, from a
configuration at κ with a valid owner o and set C, a min-frozen P with the same frozen agents and goods and
def(P) ≤ 0. (b) builds, from a min-frozen P with def(P) ≤ 0, a completable configuration at the key of P. In (a) with
C = ∅ the owner's base may be taken to be H_o, which is admissible; then P = P_Q. ∎

**Remark 1.2 (what DLK means at f = 1).** A (T3) move keeps the needed set, so at f = 1 every neighbour of (g, x) is a
key (g, z) with the same good. Following DLK from any key of g, def* falls at each step, and the walk ends at a key of
g with def* ≤ 0. So DLK at f = 1 implies: *for every good g that is the frozen good of some key, some key (g, ·) is
completable*. This implies C₄ᵐⁱⁿ at f = 1, including the big-top profiles of `k4/c4min_reduce.md` §5.1
(K4.C4MIN.RED.BT, CONJECTURE). A proof of DLK at f = 1 thus closes C₄ᵐⁱⁿ at f = 1, which is open. Conversely, on the data
(K4.SX.KGE) every non-completable key has a completable neighbour, i.e. one step always suffices.

## 2. The configuration of Theorem Z′ at a non-completable key

Throughout §2–§3: f = 1, κ = (g, x), def*(κ) > 0. A *Z′-maximum* is a configuration at κ that maximizes (r′, Λ′),
where r′ is the number of robust free agents (v_y(Q_y) ≥ v_y(U_y ∖ Q_y)) and Λ′ = Σ_{y ∈ A} ℓ_y(H_y) with
ℓ_y(S) = #{T ⊆ R_y : v_y(T) < v_y(S)}. Λ′ increases strictly with each v_y(H_y), as Theorem Z′ requires.

**Lemma F (the threat forest).** Let Q be a Z′-maximum at κ, and V the set of free agents that threaten no free agent.
- (a) Q is pool-optimal. Every free agent is threatened by at most one free agent, a robust one by none. A non-robust
  free agent y is of one of the kinds (T3), (Tg), (T4), (D), (R) of `k4/c4min_f1.md` Lemma 3 and is threatened exactly
  as listed there.
- (b) No cycle o₁ → o₂ → … → o_k → o₁ of threats among free agents exists.
- (c) Every free agent threatens somebody, V ≠ ∅, and every o ∈ V threatens x.
- (d) Some terminal exists.

Hence the threats among free agents form a disjoint union of out-trees, each vertex of in-degree at most one. Its
leaves are exactly the agents of V, every robust free agent is a root, and from every free agent a threat path leads
down to a leaf.

*Proof.* (a) Theorem Z′(ii) (K4.C4MIN.RED.Z) gives pool-optimality. `k4/c4min_f1.md` Lemma 3 (K4.C4MIN.F1) gives the
kinds and their threat conditions for a pool-optimal configuration, each with at most one threatener. A robust agent is
threatened by nobody (first line of the proof of Theorem Z′).
(b) `k4/c4min_f1.md` Lemma 5: the rotation of such a cycle, modified at one receiver if needed, is a configuration at
the same key with larger Ψ = (r, Λ). At a fixed key, Ψ is (r′, Λ′ + ℓ_x({g})), since x is never robust
(`k4/c4min_f1.md` Lemma 1(a)). This contradicts maximality.
(c) A free agent that threatens nobody is a valid owner with C = ∅, and then κ would be completable (Lemma 0). V ≠ ∅ is
Theorem Z′(ii). An o ∈ V threatens somebody (just shown), and that is not a free agent, so it is x.
(d) Lemma T of `k4/c4min_reduce.md`.
For the forest: in-degree ≤ 1 and no cycle. A vertex without out-edge inside A has an out-edge to x by (c), so it lies
in V. Conversely, a vertex of V has no out-edge inside A. Following out-edges inside A from any vertex terminates, by
finiteness and (b), and it terminates at a leaf. ∎

**Lemma S (leaves spare the terminals).** Let Q be pool-optimal at κ, τ a terminal, and o ≠ τ a free agent that
threatens no free agent. Then θ_τ(X_o) < v_τ(g): X_o does not threaten τ holding g.

*Proof.* g ∉ X_o and Q_τ ∩ X_o = ∅, so X_o ∩ R_τ ⊆ U_τ ∖ H_τ. Every good of U_τ is worth less than v_τ(g) (Lemma T).
If |X_o ∩ R_τ| ≤ 1, then θ_τ(X_o) is at most one such good. A 3-good τ has U_τ = {u₁, u₂} and H_τ ∋ u₁ (an admissible
set contains u₁, as {u₂} alone is worth less than u₁), so |U_τ ∖ H_τ| ≤ 1. For a 4-good τ, |U_τ ∖ H_τ| ≥ 2 only if
H_τ = {u₁}. In that case pool-optimality keeps u₂ and u₃ out of L ({u₁, u_i} would beat Q_τ). So X_o ∩ R_τ = {u₂, u₃}
forces Q_o = {u₂, u₃}. As |X_o| = ω + 2 ≥ 3, X_o ⊄ R_τ and θ_τ(X_o) = v_τ(u₂) + v_τ(u₃). This is at most v_τ(H_τ) = v_τ(u₁),
since o does not threaten τ, and v_τ(u₁) < v_τ(g). ∎

## 3. Repair lemmas

Each lemma assumes f = 1, ω ≥ 1 and a configuration Q at κ = (g, x) that is pool-optimal; Lemma F's structure is
assumed only where stated. Each builds a configuration Q′ at a key (g, z) in which some owner is valid with C = ∅, so
def*(g, z) ≤ 0 and def(P_{Q′}) ≤ 0 (Lemma 0), and says which move P_Q → P_{Q′} is. Throughout, a *pair for x inside Z*
is a pair Q′_x ⊆ Z whose part Q′_x ∩ U_x is admissible for x (`k4/c4min.md` §1). If Z threatens x holding g, such a
pair exists. Indeed, some h has v_x(Z ∖ h) > v_x(g), and S := (Z ∖ h) ∩ U_x is worth more than g, hence more than
every good of U_x. If |S| ≤ 2, S is admissible. Otherwise S = U_x, and its two best goods are admissible (`k4/dl13.md`
Lemma 9, first part). Add a good of Z if S has one good: a set worth more than an admissible set is admissible. A set
B ⊆ R_y is *robust* for y if v_y(B) ≥ v_y(U_y ∖ B). A robust holding is never threatened by a bundle inside M′, since
θ_y(Z) ≤ v_y(Z ∩ U_y) ≤ v_y(U_y ∖ B) for Z ∩ B = ∅.

Write **θ-b(o)** for: ω ≥ 2, o has four goods, g ∈ R_o, o is big-top on g (v_o(g) > v_o(u₁) + v_o(u₂), where
u₁, u₂, u₃ are its goods of U_o in decreasing value), and U_o ⊆ X_o. For a pool-optimal terminal o with θ-b(o),
Q_o = {u₁, u₂}: its best pair in X_o. Also u₃ ∈ L, and o is robust.

**Lemma A (owner swap).** Let o be a terminal that threatens no free agent and threatens x, with not θ-b(o). Q′: o
holds g, x holds a pair Q′_x for x inside X_o, every other free agent keeps its pair, and the pool is X_o ∖ Q′_x. Then x
is a valid owner of Q′ with C = ∅, and P_Q → P_{Q′} is a (T3) move with z = o and no helper.

*Proof.* Q′ is a candidate for o (o's top is g), hence a configuration at (g, o). x's bundle is X_o. It threatens no
free agent other than x and o, by hypothesis. For o holding g: X_o ∩ R_o ⊆ U_o.
- If |X_o ∩ R_o| ≤ 2, then X_o ⊄ R_o (|X_o| ≥ 3), and θ_o(X_o) = v_o(X_o ∩ R_o). This set lies in a pair S ⊆ X_o, and
  pool-optimality gives v_o(S) ≤ v_o(Q_o) < v_o(g).
- Otherwise o has four goods, g ∈ R_o and U_o ⊆ X_o. Pool-optimality gives v_o(u₁) + v_o(u₂) ≤ v_o(Q_o) < v_o(g), so o
  is big-top on g. If ω = 1, X_o = U_o and θ_o(X_o) = v_o(u₁) + v_o(u₂) < v_o(g). If ω ≥ 2 this is θ-b(o), excluded.

The move changes o (H_o → {g}; o needs g in P_Q) and x ({g} → Q′_x ∩ U_x ⊆ X_o ⊆ H_o ∪ J(P_Q)), nobody else. ∎

**Lemma B (generalized path move).** Assume Lemma F's structure (a). Let τ be a terminal and τ = q₀ → q₁ → … →
q_k = o (k ≥ 1) a threat path through distinct free agents, with o ∈ V threatening x. Assume o is not of kind (R) with
its fourth good s_o ∈ L. Q′: τ holds g; q_i holds Q_{q_{i−1}} (1 ≤ i ≤ k); x holds a pair for x inside X_o; the other
free agents keep their pairs; the pool is X_o ∖ Q′_x. Then x is a valid owner of Q′ with C = ∅, so def*(g, τ) ≤ 0. For
k = 1, P_Q → P_{Q′} is a (T3) move with z = τ and helper o.

*Proof.* *Validity.* Each receiver q_i is threatened, hence not robust, and of a kind of Lemma F(a).
- (T3), (T4): Q_{q_{i−1}} ⊆ R ∖ {a}, worth more than a.
- (Tg): Q_{q_{i−1}} = {u₂, u₃}, worth more than u₁.
- (D): Q_{q_{i−1}} = {b, c}, worth more than {a, d}.
- (R): a ∈ Q_{q_{i−1}}.

In each case the new pair's admissible part is worth more than the old holding, or contains the top, so it is
admissible. τ's top is g, and the pairs are disjoint (x's pair and the pool come from X_o). So Q′ is a candidate for τ.

*Safety of X_o.*
- Free agents off the path keep their pairs, and o threatens none of them.
- τ holding g: Lemma S.
- q_i for 1 ≤ i < k, holding Q_{q_{i−1}}:
  - for kinds (T3), (T4), (Tg), (D), θ_{q_i}(X_o) ≤ v(Q_{q_i}) (o ∈ V), and v(Q_{q_i}) < v(Q_{q_{i−1}}) by the threat
    condition;
  - for kind (R), R_{q_i} = {a, p, q, s} with a ∈ Q_{q_{i−1}} and {p, q} = Q_{q_i}, and neither pair meets X_o (i < k).
    So X_o ∩ R_{q_i} ⊆ {s}, and θ ≤ v(s) < v(a).
- o, holding Q_{q_{k−1}}:
  - (T3), (T4): Q_o = {a, f} with f ∉ R_o, and pool-optimality gives L ∩ R_o = ∅. So θ_o(X_o) ≤ v(a) < v(Q_{q_{k−1}}).
  - (Tg): L ∩ U_o = ∅ (pool-optimality) and g ∉ X_o, so X_o ∩ R_o = {u₁}, and u₁ < u₂ + u₃.
  - (D): X_o ∩ R_o = {a, d} (b and c are q_{k−1}'s), and a + d < b + c.
  - (R) with s_o ∉ L: the threat needs s_o ∈ Q_{q_{k−1}}, so o receives {a, s}, and X_o ∩ R_o = {p, q} with
    p + q < a + s (o is not robust).

So X_o threatens nobody in Q′.

*The move for k = 1.* τ: H_τ → {g} (τ needs g). o: H_o → Q_τ ∩ U_o ⊆ H_τ ∪ J; it gives up H_o, which is nonempty and
disjoint from Q_τ. x: {g} → Q′_x ∩ U_x ⊆ X_o ⊆ H_o ∪ J. ∎

**Lemma B′ (the modified path move).** As Lemma B, but o is of kind (R) with s_o ∈ L: R_o = {a, p, q, s},
Q_o = {p, q}, a ∈ Q_{q_{k−1}} = {a, y}. Assume (H_B′): no agent other than x values y, and
X″ := (X_o ∖ {s}) ∪ {y} contains a pair for x. Q″: as Q′ of Lemma B, except that o holds {a, s}, x holds a pair for x
inside X″, and the pool is X″ minus that pair. Then x is a valid owner of Q″ with C = ∅. For k = 1 the move is (T3) with
helper o.

*Proof.* {a, s} contains o's top, so it is admissible, and the pairs are disjoint and cover M′. For every agent w ∉ {x, o}:
y ∉ R_w, so θ_w(X″) ≤ v_w(X″ ∖ y) = v_w(X_o ∖ s) ≤ θ_w(X_o). Removing the worthless y is optimal, and X_o ∖ s is one of
the sets in the maximum defining θ_w(X_o). Every bound of the proof of Lemma B for w ≠ o is a bound on θ_w(X_o), so it
carries over. For o holding {a, s}: L ∩ R_o ⊆ {s} (pool-optimality puts a outside L, and p, q are o's), and y ∉ R_o.
So X″ ∩ R_o = {p, q}, and θ ≤ p + q < a + s. ∎

**Lemma C (another leaf owns).** Let τ₁ be a terminal with θ-b(τ₁) that threatens no free agent, and o ≠ τ₁ a free agent
that threatens no free agent. Let P_x ⊆ X_{τ₁} be a pair for x that is robust for x (v_x(P_x) ≥ v_x(U_x ∖ P_x)) and
meets U_{τ₁}. Assume (H): no agent other than x, o and τ₁ values a good of Q_{τ₁} ∖ P_x. Q′: τ₁ holds g, x holds
P_x, every other free agent keeps its pair, and the pool is X_{τ₁} ∖ P_x. Then o is a valid owner of Q′ with C = ∅, and
P_Q → P_{Q′} is a (T3) move with z = τ₁ and no helper.

*Proof.* Q′ is a candidate for τ₁. o's bundle is Y = Q_o ∪ (X_{τ₁} ∖ P_x), which contains H_o.
- x holding P_x: Y ∩ R_x ⊆ U_x ∖ P_x, and P_x is robust.
- τ₁ holding g: U_{τ₁} ⊆ X_{τ₁} misses Q_o, so Y ∩ R_{τ₁} ⊆ U_{τ₁} ∖ P_x, which has at most two goods since P_x
  meets U_{τ₁}. Such a set is worth at most v(u₁) + v(u₂) < v_{τ₁}(g) (big-top).
- Any other free y: by (H), Y ∩ R_y ⊆ X_o ∩ R_y. X_o ⊄ R_y: |X_o| = ω + 2 ≥ 4, and X_o = R_y would leave y's pair
  without a good of U_y. Then θ_y(Y) ≤ v_y(Y ∩ R_y) ≤ v_y(X_o ∩ R_y) = θ_y(X_o) ≤ v_y(Q_y).

The move changes τ₁ (needs g) and x (new base P_x ∩ U_x ⊆ X_{τ₁} ⊆ H_{τ₁} ∪ J) only. ∎

**Lemma C′ (two terminals, paid for by unfreezing).** Let the terminals be exactly τ₁ ≠ τ₂, with θ-b(τ₁), and let τ₂
threaten no free agent. Let P ⊆ X_{τ₁} be a pair for x, robust for x, with v_x(P) > v_x(g). Let w ∈ U_{τ₁} ∖ P, and
Y := (X_{τ₂} ∪ Q_{τ₁}) ∖ (P ∪ {w}) with U_{τ₂} ⊆ Y. Assume (H′): no agent other than x, τ₁, τ₂ values a good of
Q_{τ₁} ∖ (P ∪ {w}). Let P′ be P_Q with τ₁ on {g} and x on P ∩ U_x. Then def(P′) ≤ 0, and P_Q → P′ is a (T3) move with
z = τ₁ and no helper.

*Proof.* By `k4/dl2.md` Lemma 6 (K4.DL2.MOVES), P′ is min-frozen with frozen agent τ₁: τ₁ needs g, and P ∩ U_x is
admissible. Y is a bundle of τ₂ in P′. It contains H_{τ₂} ⊆ Q_{τ₂}, since P and w lie in X_{τ₁}, which misses Q_{τ₂}.
Its other goods lie in (Q_{τ₂} ∖ H_{τ₂}) ∪ L ∪ (Q_{τ₁} ∖ P) ⊆ J(P′). The union X_{τ₂} ∪ Q_{τ₁} has ω + 4 goods and
contains P ∪ {w} ⊆ X_{τ₁}, so |Y| = ω + 1. Safety in P′:
- τ₁ holding g: Y ∩ R_{τ₁} ⊆ U_{τ₁} ∖ {w}.
- x: P is robust.
- A third y: (H′) and the argument of Lemma C.

τ₁ is counted in u_{τ₂}(Y) (`k4/dl2.md` §4): U_{τ₂} ⊆ Y gives v_{τ₂}(Y) > v_{τ₂}(g) by balance, so g ∉ N_{τ₂}(Y). Also
g ∉ N_x(P ∩ U_x) because v_x(P) > v_x(g), N_{τ₁}({g}) = ∅, and no other agent needs g. Lemma H1 (K4.HALL.COVER):
def(P′) ≤ ω + 2 − (|Y| + 1) = 0. ∎

**Theorem 1 (DL on the key graph at f = 1, under hypotheses).** Let f = 1, κ = (g, x) with def*(κ) > 0, and Q a
Z′-maximum at κ. Suppose that Lemma A, Lemma C or Lemma C′ applies to Q, or that Lemma B or B′ applies with k = 1.
Then one (T3) move from P_Q reaches a state P′ with def(P′) ≤ 0. So the key κ′ of P′ is a (T3)-neighbour of κ with
def*(κ′) ≤ 0 < def*(κ), and DLK holds at κ. If instead Lemma B or B′ applies only with paths of length k ≥ 2, the key
(g, τ) has def*(g, τ) ≤ 0, but it is not shown to lie in N_{T3}(κ).

*Proof.* The lemmas, with Lemma F(a) for Lemmas B and B′. ∎

Which lemma applies is decided by Lemma F's forest. If some terminal is a leaf without θ-b, Lemma A applies. If some
terminal is not a leaf, it has a threat path down to a leaf (Lemma F), and B or B′ applies unless that leaf is an (R)
with s ∈ L and (H_B′) fails. If every terminal is a θ-b leaf, Lemmas C and C′ are the candidates.

## 4. Evidence

Tools (EVIDENCE tooling; every assertion below is checked against exact deficits, with no violation):
- `k4/sx_keygraph.py`: per profile, every key with def* and its neighbours for the edge sets T3, T3⁺, T3 ∪ T4,
  T3⁺ ∪ T4 (moves generated from every min-frozen state, deficits by Lemma H1 on `k4/suite/model.py`);
- `k4/sx_xcheck.py`: a second implementation (main's `k4/c4x_check.py` enumeration and direct removal-only deficit,
  pairwise move classification, no shared code with the first);
- `k4/sx_hunt.py`: non-completable f = 1 keys from PR #51's C tool `k4/red.c` (counter `key_noncompletable`) on random
  strict profiles;
- `k4/sx_zprime.py`: at every non-completable f = 1 key, every Z′-maximum. It asserts Theorem Z′, Lemma F
  (forest, kinds), Lemma A (when not θ-b), Lemma B (every path whose leaf is not (R) with s ∈ L) and Lemmas B′, C, C′
  (whenever their hypotheses hold): the configuration built is a configuration, the owner is valid with C = ∅, def* ≤ 0
  at the target key, and the (T3) image has def ≤ 0. It also records which lemma applies first, in the order A, B (k = 1),
  C, C′, B′ (k = 1), then B or B′ with longer paths.

(Tables: §4.1 key graph, §4.2 coverage. Filled in from `results/k4_sx/`.)

## 5. What remains at f = 1

(To be filled in from the data.)

## 6. f ≥ 2

(To be filled in.)

## 7. Reproduce

```
mkdir -p k4/suite/.cache/gapbench && git archive 245040b results/k4_gap | tar -x -C k4/suite/.cache/gapbench
python3 k4/sx_runs.py                 # key graph on #53's catalogues, resumable chunks -> results/k4_sx/chunks/
python3 k4/sx_runs.py --sum           # results/k4_sx/keys_summary.md
sh k4/sx_hunt_runs.sh                 # non-completable f = 1 keys with k4/red.c -> results/k4_sx/hunt/
python3 k4/sx_zprime.py results/k4_sx/hunt/*.jsonl.gz results/k4_sx/chunks/gap_n3_c*.jsonl.gz   # §4.2
```
