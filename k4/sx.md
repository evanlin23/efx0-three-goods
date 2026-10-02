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

Counters summed per input: `results/k4_sx/SUMMARY.md` (`python3 k4/sx_summary.py`) and `results/k4_sx/keys_summary.md`
(`python3 k4/sx_runs.py --sum`).

### 4.1 Where the non-completable f = 1 keys are

`k4/sx_hunt.py` runs `k4/red.c` with its own driver (seeded as `k4/red_run.py`) and keeps every profile that has a key
with no completable configuration. By Lemma 0 these are exactly the keys with def* > 0. `k4/sx_keygraph.py` recomputes
def* for every key of these profiles with an independent deficit, `k4/sx_zprime.py` asserts def*(κ) > 0, and the counts
agree with PR #51's (`k4/c4min_reduce.md` §4.1: 62,208 hopeless keys at n ≤ 3).

| input (`results/k4_sx/hunt/`) | strict profiles | f = 1 profiles (ω ≥ 1) | keys | non-completable keys (= profiles) |
|---|---|---|---|---|
| n = 3, every strict profile of every core (`n3_all_*`) | 299,837,376 | 7,284,544 | 14,256,832 | 62,208 |
| n = 4, two 4-good agents, 20,000 per core (`n4_2_r20k`) | 6,180,000 | 165,045 | 303,564 | 0 |
| n = 4, three, 40,000 per core (`n4_3_r40k`) | 13,560,000 | 551,666 | 1,044,381 | 59 |
| n = 4, pure, 40,000 per core (`n4_pure_r40k`) | 8,760,000 | 430,765 | 844,132 | 240 |
| n = 5, two / three / four 4-good agents, 200 per core | 1,093,600 / 1,972,200 / 1,969,200 | 10,719 / 51,240 / 82,386 | 19,971 / 96,226 / 157,244 | 0 / 0 / 0 |
| n = 5, pure, 1,000 per core (`n5_pure_r1000_*`) | 4,674,000 | 263,852 | 516,100 | 11 |

At n = 2 every key is completable (`k4/c4min_reduce.md` §4.1). Every n ≤ 3 profile with a non-completable key has exactly
one: 62,208 keys in 62,208 profiles. The catalogue runs of `k4/sx_keygraph.py` find no non-completable key in
#53's catalogues of the n = 4 cores with one or two 4-good agents (`results/k4_sx/keys_summary.md`), and none at f = 2
there.

### 4.2 Coverage by the repair lemmas (f = 1)

At every Z′-maximum of every non-completable key of §4.1 (`results/k4_sx/zprime/*.log`):

| input | keys | Z′-maxima | first lemma that applies: A | B (k = 1) | C | C′ | B′ (k = 1) | none |
|---|---|---|---|---|---|---|---|---|
| n = 3, exhaustive | 62,208 | 116,248 | 104,372 | 7,824 | 4,052 | 0 | 0 | **0** |
| n = 4 hunts | 299 | 565 | 494 | 58 | 5 | 2 | 6 | **0** |
| n = 5 hunts | 11 | 13 | 13 | 0 | 0 | 0 | 0 | **0** |

- *Every assertion held.* The checks cover:
  - Lemma F: a forest, in-degree ≤ 1, V the leaves, robust agents unthreatened, kinds as listed;
  - Lemma A at every non-θ-b terminal leaf;
  - Lemma B at every path whose leaf is not an (R) with s ∈ L (n = 3: 33,264 paths, all of length 1; n = 4: also 10
    paths of length 2);
  - Lemmas B′, C, C′ wherever their hypotheses hold.

  Each assertion says that the configuration built is a configuration at its key, that the owner is valid with C = ∅
  (for C′: the deficit), that def* ≤ 0 at the target key, and that the (T3) image of P_Q has deficit ≤ 0.
- *DL on the key graph at f = 1 holds on these data in its strong form*: every non-completable key has a (T3) neighbour
  with def* ≤ 0. Every Z′-maximum even has a direct (T3) move to a state of deficit ≤ 0 (counter "Zmax with a direct T3
  move" = all maxima).
- *The regimes.* At n = 3, 105,128 maxima have a terminal leaf (regime I). There Lemma A applies unless every terminal
  leaf is θ-b (27,944 θ-b leaf–maximum pairs), and then Lemma C does (4,052 maxima, all with two terminal leaves).
  7,824 maxima have no terminal leaf (regime II): one terminal τ, one leaf o, the path τ → o of length 1, x big-top,
  and Lemma B applies.
- *Paths of length 2* occur only in the n = 4 hunts (10 paths). There Lemma B's target key is a (T3) neighbour as well,
  but at those maxima another lemma applies first.
- *Second implementation.* `k4/sx_xcheck.py` (main's `k4/c4x_check.py` enumeration and direct deficit) agrees with
  `k4/sx_keygraph.py` on every key's def* and on the DLK verdicts of all four edge sets. It ran on #53's n = 3 catalogue
  dump and samples of the n = 4 hunts, with 0 mismatches (`results/k4_sx/xcheck_*.log`).

## 5. What remains at f = 1

Theorem 1 reduces DL on the key graph at f = 1 to one statement:

> **Conjecture K4.SX.COVER.** At every Z′-maximum of every non-completable key with f = 1, one of Lemmas A, B (k = 1),
> B′ (k = 1), C, C′ applies.

It holds on every strict profile with n ≤ 3 and on the n = 4, 5 hunts (§4.2). Where a proof has to go, by Lemma F:
1. *Some terminal is a leaf without θ-b.* Lemma A applies.
2. *Every terminal leaf is θ-b.* Such a leaf is robust, hence an isolated vertex of the forest. Lemmas C and C′ need
   - a robust pair of x inside X_{τ₁} meeting U_{τ₁} (C), or worth more than g (C′);
   - the hypotheses (H) or (H′) on third agents.

   A proof needs the existence of that pair, from x's threat by X_{τ₁} (`k4/c4min_f1.md` Lemma 4 gives a robust pair
   worth more than g for x not big-top, but not one meeting U_{τ₁}), and a replacement for (H)/(H′) when third agents
   value τ₁'s pair. At n = 3 the hypotheses (H), (H′) are void, and on the data the pair exists.
3. *Some terminal is not a leaf.* Lemma B applies along a path to a leaf, except for (R) leaves with s ∈ L that fail
   (H_B′). The open part is a path of length ≥ 2, where Lemma B's key (g, τ) has def* ≤ 0 but (T3)-adjacency to κ is not
   proved. On the data every such key is a (T3) neighbour, and the case never arises alone.

So a proof of K4.SX.COVER needs (2) and (3); (1) is done. With it, DL on the key graph at f = 1 follows, and with
Remark 1.2, C₄ᵐⁱⁿ at f = 1.

## 6. f ≥ 2

**The (T3) ∪ (T4) form is false; the target is (T3⁺) ∪ (T4).** The coordinator checked the DL_RT4 failures of
compute/k4-rt4-n5b and -n5c (67 states in 10 profiles, all with f = 3, def = 1 and nearest distance 3) on
`k4/dl134_xcheck.py`'s model. In each profile some key with def* = 1 has no neighbour of smaller def* by one (T3) or
(T4) move from any of its states. Every repair there is a (T3⁺) move: x frees g, a frozen w moves from h to g, and a
free z takes h. `k4/sx_keygraph.py` reproduces this on the smallest profile, core pos 3206 of `k4_certs_5_n4_4`
(`python3 k4/sx_keygraph.py one '{"m": 9, "sets": [[0,2,4,7],[1,4,7,8],[3,6,8],[5,6,7,8],[5,6,7,8]], "vals":
[[6,3,5,7],[4,2,8,7],[2,4,3],[4,8,1,6],[2,7,8,4]]}'`). The key (7, 8, –, –, 6) has def* = 1. Its (T3) ∪ (T4) neighbours
all have def* = 1, and DLK holds there with (T3⁺) edges. The ledger status of that refutation is the coordinator's.

**Lemma A⁺ (the owner swap along a need chain; one (T3⁺) move).** Let f ≥ 1 and ω ≥ 1, and let κ = (𝒩, φ) be a key
with frozen set F. Let Q be a pool-optimal configuration at κ (U_y = R_y ∖ 𝒩). Let o be a free agent such that
X_o = Q_o ∪ L threatens no free agent and exactly one frozen agent x. Let x = w₀, w₁, …, w_j (j ≥ 0) be distinct frozen
agents with φ(w_{i−1}) ∈ N_{w_i}({φ(w_i)}) for 1 ≤ i ≤ j (w_i needs w_{i−1}'s good), with φ(w_j) ∈ N_o(H_o), and with
θ_o(X_o) ≤ v_o(φ(w_j)). Q′: w_i holds φ(w_{i−1}) (1 ≤ i ≤ j), o holds φ(w_j), x holds a pair for x inside X_o, the other
agents keep their holdings, and the pool is X_o ∖ Q′_x. Then Q′ is a configuration at the key with frozen set
F ∖ {x} ∪ {o}, x is a valid owner of Q′ with C = ∅, and P_Q → P_{Q′} is one (T3⁺) move with W = {w₁, …, w_j}. For j = 0
it is a (T3) move, and at f = 1 it is Lemma A. The condition on θ_o holds automatically when |X_o ∩ R_o| ≤ 2: pool-optimality
bounds every pair of X_o by v_o(H_o) < v_o(φ(w_j)).

*Proof.*
- *A pair for x.* Some h has v_x(X_o ∖ h) > v_x(φ(x)). Every good of U_x is worth less than φ(x) to x: one worth more
  would be a need of x outside 𝒩. So S := (X_o ∖ h) ∩ U_x, or its two best goods, is a set whose needs lie in 𝒩. Complete
  it inside X_o as in §3.
- *Q′ is a configuration.* The state P_{Q′} has these bases.
  - The frozen agents off the chain keep their needs.
  - Each w_i holds a good worth more to it than before, so its needs shrink (`k4/dl2.md` (M2)).
  - o holds φ(w_j), which it needed. Every good of R_o worth more than φ(w_j) is worth more than H_o, so it lies in
    N_o(H_o) ⊆ 𝒩.
  - x's new base and the unchanged free bases need only goods of 𝒩.

  So NA(P_{Q′}) ⊆ 𝒩. Every good of 𝒩 is the one-good base of an agent of F ∖ {x} ∪ {o}, and the free bases miss 𝒩. By
  (V), P_{Q′} ∈ 𝒫, and |F(P_{Q′})| = |NA(P_{Q′})| ≤ f. Minimality forces NA(P_{Q′}) = 𝒩, with frozen set F ∖ {x} ∪ {o}.
- *x is valid.* X_o threatens none of these:
  - the unchanged free agents (o threatens no free agent);
  - the frozen agents off the chain other than x (x is the only frozen agent X_o threatens);
  - w_i holding φ(w_{i−1}), since θ_{w_i}(X_o) ≤ v(φ(w_i)) < v(φ(w_{i−1}));
  - o holding φ(w_j), by hypothesis.

  Lemma 0 then gives def(P_{Q′}) ≤ 0.
- *The move.* x goes from frozen to free, o from free to frozen and takes a good it needs in P_Q, and the agents of W
  stay frozen. The bases of W ∪ {o} in P_{Q′} are those of W ∪ {x} in P_Q, there is no helper, and NA is unchanged. ∎

**Data (EVIDENCE, `k4/sx_f2.py`).** At every key with def* > 0 of the 10 profiles of compute/k4-rt4-n5b and -n5c
(`results/k4_sx/f2/rt4_n5b.log`, `rt4_n5c.log`; instance lists `results/k4_sx/f2/rt4_n5*_inst.json`, copied from the
coordinator's checks), at every maximum of (r′, Λ′), a free-valid owner exists. At n5b, at all 15 keys and all 81
maxima, its bundle threatens one frozen agent and Lemma A⁺ applies: 24 times with j = 0 and 57 with j = 1. 15 of the 81
maxima have no direct (T3) repair but a (T3⁺) one. At n5c, Lemma A⁺ applies at 86 of 118 maxima and at some maximum of
19 of the 26 keys. The other 7 keys are the failed candidate `attempts/k4-sx-aplus-f3.md`. There some free-valid
owner's bundle threatens two frozen agents (35 owner–maximum pairs), or the owner at the chain's end is threatened by
its own bundle (35 chains, the analogue of θ-b). DLK with (T3⁺) ∪ (T4) edges holds at all of them (`k4/sx_keygraph.py`,
`k4/sx_xcheck.py`). The repairs there have the shape of Lemmas C and C′: another free-valid owner owns after the swap.

**What f ≥ 2 still needs.**
- A form of Lemma F: Theorem Z′'s free-valid owner exists at every f ≥ 2 key on these data, but it is not proved. The
  last step of Theorem Z′ uses f = 1. At f ≥ 2 it yields either a free-valid owner, or free agents all of kind (T4)
  whose frozen goods are needed only by frozen agents, i.e. a cycle of the frozen need digraph and hence a (T4) move.
- The analogues of Lemmas B, C and C′ along need chains.
- A count of the frozen agents a leaf's bundle threatens: at f = 1 it is one by definition, and at f ≥ 2 it is two in
  the failing case above.

## 7. Reproduce

```
mkdir -p k4/suite/.cache/gapbench && git archive 245040b results/k4_gap | tar -x -C k4/suite/.cache/gapbench
python3 k4/sx_runs.py                 # key graph on #53's catalogues, resumable chunks -> results/k4_sx/chunks/
python3 k4/sx_runs.py --sum           # results/k4_sx/keys_summary.md
sh k4/sx_hunt_runs.sh                 # non-completable f = 1 keys with k4/red.c -> results/k4_sx/hunt/
python3 k4/sx_zprime.py results/k4_sx/hunt/*.jsonl.gz results/k4_sx/chunks/gap_n3_c*.jsonl.gz   # §4.2
```
