# DL on the key graph at one frozen agent: repair lemmas from Theorem Z′'s configuration

Workstream `proof/k4-sx` (PR #80), `k4/dl13.md` §6 item 1 (on main since PR #75). Ledger rows K4.SX.*: the written
proofs of §1–§3 and §6 were refereed in the PR #80 review (K4.SX.KEY, K4.SX.REP, K4.SX.APLUS: PROVED); Conjecture
K4.SX.COVER (§5) is open (CONJECTURE); data rows are EVIDENCE. Nothing here changes K4.D or K4.T.

**Target.** DL on the key graph (`k4/dl13.md` §2.3, Remark): every key κ with least deficit def*(κ) > 0 has a key κ′,
reached by one move of a fixed class from some state of κ, with def*(κ′) < def*(κ). The class was (T3) ∪ (T4); after
its refutation at n = 5, f = 3 (K4.DL13.KEY, REFUTED; §6) it is (T3⁺) ∪ (T4), the key-graph form of K4.DL2.RC. At f = 1 the two coincide: (T4) is
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
  - **B′** (the modified path move for that exception): o takes its top a and its fourth good s_o, and x's bundle is
    X″ = (X_o ∖ {s_o}) ∪ {y}, with y the other good of o's threatener's pair. It needs X″ to contain a pair for x, and
    (H_B′): X″ threatens no agent other than x and o. (H_B′) holds when nobody but x values y.
  - **C** and **C′** (θ-b leaves): another leaf owns. **C**: a θ-b terminal leaf τ₁ takes g, x takes a robust pair
    meeting τ₁'s goods, and another leaf owns the rest. **C′**: the same with two terminals, paid for by unfreezing
    τ₁. Each is one (T3) move without helper, under a hypothesis saying that the goods τ₁ releases are not valued by
    third agents.

  In every case but B and B′ with k ≥ 2 a single (T3) move ends at a state P′ with def(P′) ≤ 0, so the neighbouring
  key has def* ≤ 0 < def*(κ). For k ≥ 2 the construction changes k + 2 agents at once and only gives a key with
  def* ≤ 0.
- **Coverage (EVIDENCE, §4; K4.SX.COV).** At every configuration maximizing (r′, Λ′) at every non-completable f = 1
  key of the data, A, B (k = 1), B′ (k = 1), C or C′ applies. The data are:
  - every strict profile of every core with n ≤ 3: 62,208 such keys, all of the hopeless keys of `k4/c4min_reduce.md`
    §4.1, covered by A, B and C;
  - every non-completable key that `k4/red.c` finds in random samples with n = 4 (2,661 keys) and n = 5 (11 keys);
  - the 1,241 non-completable keys among the profiles of `k4/dl13.md`'s T1-stuck states.

  At 5 keys of the largest n = 4 sample, B′ and C need their exact hypotheses: the structural ones fail there
  (`attempts/k4-sx-cover-structural.md`). So on these data DL on the key graph at f = 1 holds, in the strong form "a
  neighbour with def* ≤ 0", through these five lemmas, each applied once from Theorem Z′'s configuration. Every lemma is
  asserted against exact deficits there, with no violation.
- **The f = 1 failure of single-step DL** (compute/k4-rc; §4.4). In 45 profiles of one n = 5 core, a state P_fail with
  def 1 has no improving (T1)–(T4) move. Theorem Z′'s state P_Q of its key is a different state, one (T1) step from
  P_fail and not the coordinator's (T3h) witness state. Lemma A applies at P_Q: one (T3) move without helper, to
  deficit 0. That move's image is one of the 6 nearest better states of P_fail (distance 3).
- **What remains at f = 1** (§5): Conjecture K4.SX.COVER, that one of A, B₁, B₁′, C, C′ always applies. The open cases
  are:
  - θ-b leaves: the robust pair that C and C′ need, and their hypotheses on third agents;
  - (R) leaves whose released good third agents value;
  - terminals at distance ≥ 2 from every leaf. There B's key is completable, but (T3)-adjacency is open.
- **f ≥ 2** (§6):
  - the coordinator's refutation of the (T3) ∪ (T4) form, which this file's two implementations reproduce (10 keys
    fail, one per profile);
  - the (T3⁺) ∪ (T4) form on the same profiles: it holds at all 41 keys;
  - Lemma F⁺: the forest of Lemma F at every f. A free-valid owner exists at every maximum of (r′, Λ′) at a
    non-completable key;
  - Lemma A⁺, the owner swap along a need chain of frozen agents, and Lemma B⁺, the path move along one. A⁺ is one
    (T3⁺) move, and so is B⁺ for path length k = 1. On the data B⁺ never applies where A⁺ fails, so A⁺ alone reaches
    what both reach: 34 of those 41 keys from some Z′-type maximum, 156 of the 196 f ≥ 2 keys of the T1-stuck
    profiles, and 18 of the 67 f = 2 keys of the n = 4 catalogues and hunts. At the remaining keys
    (`attempts/k4-sx-aplus-f3.md`, smallest n = 4, m = 8, f = 2) a leaf threatens two frozen agents, the free needers are
    off the path, or θ fails at the chain's end. At 173 of the 174 maxima left uncovered a plain (T3) move without helper
    repairs, of the shape of Lemma C or of C′'s mechanism (§6): the missing lemmas are C and C′ at f ≥ 2;
  - DLK holds with every edge set on all f = 2 data (§4.3).
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
- **(T3⁺)** as (T3), except that W := the agents of ch frozen in both may be nonempty, and B′_z need not be B_x: the
  bases of W ∪ {z} in P′ are those of W ∪ {x} in P (as sets of bases), and B′_z = {g′} with g′ ∈ N_z(B_z) (the
  coordinator's frozen-chain role swap);
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
(K4.SX.KGE; EVIDENCE, not proved) every non-completable key has a completable neighbour, i.e. there one step always
suffices.

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
H_τ = {u₁}. Then |X_o ∩ R_τ| = 2 means X_o ∩ R_τ = {u₂, u₃}. Pool-optimality keeps u₂ and u₃ out of L
({u₁, u_i} would beat Q_τ), so Q_o = {u₂, u₃}. As |X_o| = ω + 2 ≥ 3, X_o ⊄ R_τ and θ_τ(X_o) = v_τ(u₂) + v_τ(u₃). This is
at most v_τ(H_τ) = v_τ(u₁), since o does not threaten τ, and v_τ(u₁) < v_τ(g). ∎

## 3. Repair lemmas

Each lemma assumes f = 1, ω ≥ 1 and a configuration Q at κ = (g, x) that is pool-optimal; Lemma F's structure is
assumed only where stated. Lemmas A, B, B′ and C build a configuration Q′ at a key (g, z) in which some owner is valid
with C = ∅, so def*(g, z) ≤ 0 and def(P_{Q′}) ≤ 0 (Lemma 0). Lemma C′ instead builds a state P′ with def(P′) ≤ 0
directly (Lemma H1, paid for by unfreezing τ₁; no owner with C = ∅ is claimed). Each lemma says which move P_Q → P′
is. Throughout, a *pair for x inside Z*
is a pair Q′_x ⊆ Z whose part Q′_x ∩ U_x is admissible for x (`k4/c4min.md` §1). If Z threatens x holding g, such a
pair exists. Indeed, some h has v_x(Z ∖ h) > v_x(g), and S := (Z ∖ h) ∩ U_x is worth more than g, hence more than
every good of U_x. So S has at least two goods. If |S| = 2, S is admissible and is the pair. Otherwise S = U_x, and its
two best goods are admissible (`k4/dl13.md` Lemma 9, first part) and form the pair. A set
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
Q_o = {p, q}, a ∈ Q_{q_{k−1}} = {a, y}. Let X″ := (X_o ∖ {s}) ∪ {y}, and assume it contains a pair for x. Q″: as Q′ of
Lemma B, except that o holds {a, s}, x holds a pair for x inside X″, and the pool is X″ minus that pair. Assume
(H_B′): X″ threatens no agent other than x and o in Q″. Then x is a valid owner of Q″ with C = ∅. For k = 1 the move is
(T3) with helper o. (H_B′) holds in particular under (H_B′*): no agent other than x values y.

*Proof.* {a, s} contains o's top, so it is admissible, and the pairs are disjoint and cover M′. For o holding {a, s}:
L ∩ R_o ⊆ {s} (pool-optimality puts a outside L, and p, q are o's), and y ∉ R_o. So X″ ∩ R_o = {p, q}, and
θ ≤ p + q < a + s. The other agents are (H_B′).

For (H_B′*) ⟹ (H_B′): let w ∉ {x, o}. Then y ∉ R_w, so θ_w(X″) ≤ v_w(X″ ∖ y) = v_w(X_o ∖ s) ≤ θ_w(X_o). Removing the
worthless y is optimal, and X_o ∖ s is one of the sets in the maximum defining θ_w(X_o). Every bound of the proof of
Lemma B for w ≠ o is a bound on θ_w(X_o), so it carries over. ∎

**Lemma C (another leaf owns).** Let τ₁ be a terminal with θ-b(τ₁), and o ≠ τ₁ a free agent that threatens no free
agent. (τ₁ need not be a leaf; in the case of §5 where C is needed it is one.) Let P_x ⊆ X_{τ₁} be a pair for x that is robust for x (v_x(P_x) ≥ v_x(U_x ∖ P_x)) and
meets U_{τ₁}. Let Y := Q_o ∪ (X_{τ₁} ∖ P_x), and assume (H): Y threatens no free agent other than o and τ₁. Q′: τ₁
holds g, x holds P_x, every other free agent keeps its pair, and the pool is X_{τ₁} ∖ P_x. Then o is a valid owner of
Q′ with C = ∅, and P_Q → P_{Q′} is a (T3) move with z = τ₁ and no helper. (H) holds in particular under (H*): no agent
other than x, o and τ₁ values a good of Q_{τ₁} ∖ P_x.

*Proof.* Q′ is a candidate for τ₁. o's bundle is Y, which contains H_o.
- x holding P_x: Y ∩ R_x ⊆ U_x ∖ P_x, and P_x is robust.
- τ₁ holding g: U_{τ₁} ⊆ X_{τ₁} misses Q_o, so Y ∩ R_{τ₁} ⊆ U_{τ₁} ∖ P_x, which has at most two goods since P_x
  meets U_{τ₁}. Such a set is worth at most v(u₁) + v(u₂) < v_{τ₁}(g) (big-top).
- Any other free y: (H). For (H*) ⟹ (H): by (H*), Y ∩ R_y ⊆ X_o ∩ R_y. X_o ⊄ R_y: |X_o| = ω + 2 ≥ 4, and X_o = R_y
  would leave y's pair without a good of U_y. Then θ_y(Y) ≤ v_y(Y ∩ R_y) ≤ v_y(X_o ∩ R_y) = θ_y(X_o) ≤ v_y(Q_y).

The move changes τ₁ (needs g) and x (new base P_x ∩ U_x ⊆ X_{τ₁} ⊆ H_{τ₁} ∪ J) only. ∎

**Lemma C′ (two terminals, paid for by unfreezing).** Let the terminals be exactly τ₁ ≠ τ₂, with θ-b(τ₁), and let τ₂
threaten no free agent. Let P ⊆ X_{τ₁} be a pair for x, robust for x, with v_x(P) > v_x(g). Let w ∈ U_{τ₁} ∖ P, and
Y := (X_{τ₂} ∪ Q_{τ₁}) ∖ (P ∪ {w}) with U_{τ₂} ⊆ Y. Assume (H′): Y threatens no free agent other than τ₁ and τ₂.
Let P′ be P_Q with τ₁ on {g} and x on P ∩ U_x. Then def(P′) ≤ 0, and P_Q → P′ is a (T3) move with z = τ₁ and no
helper. (H′) holds in particular under (H′*): no agent other than x, τ₁, τ₂ values a good of Q_{τ₁} ∖ (P ∪ {w}).

*Proof.* By `k4/dl2.md` Lemma 6 (K4.DL2.MOVES), P′ is min-frozen with frozen agent τ₁: τ₁ needs g, and P ∩ U_x is
admissible. Y is a bundle of τ₂ in P′. It contains H_{τ₂} ⊆ Q_{τ₂}, since P and w lie in X_{τ₁}, which misses Q_{τ₂}.
Its other goods lie in (Q_{τ₂} ∖ H_{τ₂}) ∪ L ∪ (Q_{τ₁} ∖ P) ⊆ J(P′). The union X_{τ₂} ∪ Q_{τ₁} has ω + 4 goods and
contains P ∪ {w} ⊆ X_{τ₁}, so |Y| = ω + 1. Safety in P′:
- τ₁ holding g: Y ∩ R_{τ₁} ⊆ U_{τ₁} ∖ {w}, a set of at most two goods of U_{τ₁}, worth at most
  v(u₁) + v(u₂) < v_{τ₁}(g) (big-top).
- x: P is robust.
- A third y: (H′). (H′*) ⟹ (H′) by the argument of Lemma C, with τ₂ ∈ V and |X_{τ₂}| ≥ 4.

τ₁ is counted in u_{τ₂}(Y) (`k4/dl2.md` §4): U_{τ₂} ⊆ Y gives v_{τ₂}(Y) > v_{τ₂}(g) by balance, so g ∉ N_{τ₂}(Y). Also
g ∉ N_x(P ∩ U_x) because v_x(P) > v_x(g), N_{τ₁}({g}) = ∅, and no other agent needs g. Lemma H1 (K4.HALL.COVER):
def(P′) ≤ ω + 2 − (|Y| + 1) = 0. ∎

**Theorem 1 (DL on the key graph at f = 1, under hypotheses).** Let f = 1, κ = (g, x) with def*(κ) > 0, and Q a
Z′-maximum at κ. Suppose that Lemma A, Lemma C or Lemma C′ applies to Q, or that Lemma B or B′ applies with k = 1.
Then one (T3) move from P_Q reaches a state P′ with def(P′) ≤ 0. So the key κ′ of P′ is a (T3)-neighbour of κ with
def*(κ′) ≤ 0 < def*(κ), and DLK holds at κ. If instead Lemma B or B′ applies only with paths of length k ≥ 2, the key
(g, τ) has def*(g, τ) ≤ 0, but it is not shown to lie in N_{T3}(κ).

*Proof.* The lemmas, with Lemma F(a) for Lemmas B and B′. ∎

**The move shapes.** ch is the set of changed agents. U is frozen → free (here {x}), Z is free → frozen, W is frozen in
both, and Y is free in both. NA′ = NA in every case.

| lemma | Z | W | Y | class | reaches |
|---|---|---|---|---|---|
| A (owner swap) | {o}, o a leaf | ∅ | ∅ | (T3), no helper | a state with def ≤ 0 |
| B, path length k | {τ} | ∅ | {q₁, …, q_k}, each giving up its pair | (T3) with one helper if k = 1; k helpers otherwise | a key with def* ≤ 0 (a state with def ≤ 0) |
| B′, path length k (X″ contains a pair for x; (H_B′)) | {τ} | ∅ | {q₁, …, q_k} | as B | as B |
| C | {τ₁} | ∅ | ∅ | (T3), no helper | a state with def ≤ 0 |
| C′ | {τ₁} | ∅ | ∅ | (T3), no helper | a state with def ≤ 0 |
| A⁺ (§6, any f) | {o} | {w₁, …, w_j} | ∅ | (T3⁺), no helper; (T3) if j = 0 | a state with def ≤ 0 |
| B⁺ (§6, any f), path length k | {τ} | {w₁, …, w_j} | {q₁, …, q_k} | (T3⁺) with one helper if k = 1 | a key with def* ≤ 0 |

Which lemma applies is decided by Lemma F's forest. If some terminal is a leaf without θ-b, Lemma A applies. If some
terminal is not a leaf, it has a threat path down to a leaf (Lemma F). If that path has length k = 1, B applies, or B′
when the leaf is an (R) with s ∈ L, provided X″ contains a pair for x and (H_B′) holds; for k ≥ 2, B and B′ give a key
with def* ≤ 0 whose (T3)-adjacency to κ is not proved. If every terminal is a θ-b leaf, Lemmas C and C′ are the
candidates.

**The global target these lemmas aim at.** The source is compute/k4-portfolio's `results/k4_portfolio/TABLE.md` (commit
5111ea3 of that branch, EVIDENCE). Every key-graph form of the table survives on its 71,596 keys with def* > 0 except
the control K1, (T3) ∪ (T4), which fails at 22. The strongest survivor is K3b_noT4:
- edges are (T3⁺) moves with |W| ≤ 1 that change at most three agents;
- there are no (T4) edges.
- *At f = 1* K3b_noT4, K3b, K3, K2 and K1 all coincide with the (T3) edges, because (T4) is empty and (T3⁺) = (T3).
  Every lemma of K4.SX.COVER (A, B₁, B₁′, C, C′) is a (T3) move changing at most three agents: x, z and at most one
  helper. So the f = 1 statement of this file (Theorem 1 with COVER) is the K3b_noT4 form.
- *At f ≥ 2*:
  - A⁺ with a chain of length j ≤ 1 is a K3b_noT4 edge (x, w₁, o). With j ≥ 2 it is only a K2 edge ((T3⁺), |W| = j).
  - B⁺ with j = 1 and k = 1 changes four agents (x, w₁, τ, q₁). It is a K3 edge without (T4), but not a K3b edge.

  On every f ≥ 2 input of §6 where A⁺ or B⁺ applies, j ≤ 1 and k = 1 (`results/k4_sx/f2/*.log`,
  `results/k4_sx/t3stage/f2.log`).
- compute/k4-rc's 45 profiles (§4.4) are not in that table. There the single-step form of K4.DL2.RC fails, and the
  (T3) key-graph form holds at all 45 keys. At f = 1 that form is every K-form of the table.

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
| n = 4, pure, 400,000 per core, another seed (`n4_pure_r400k`) | 87,600,000 | 4,310,853 | 8,443,995 | 2,363 (2,362 distinct, in 2,347 profiles) |
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
| n = 4, pure, 400,000 per core | 2,362 | 3,645 | 3,390 | 135 | 73 (+ 2 with the exact (H) only) | 30 | 12 (+ 3 with the exact (H_B′) only) | **0** |
| n = 5 hunts | 11 | 13 | 13 | 0 | 0 | 0 | 0 | **0** |
| n = 5, compute/k4-rc's 45 single-step DL failures (§4.4) | 45 | 45 | 45 | 0 | 0 | 0 | 0 | **0** |

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
- *The regimes.* At n = 3, 108,424 maxima have a terminal leaf (regime I; `results/k4_sx/SUMMARY.md`). There Lemma A
  applies unless every terminal leaf is θ-b (27,944 θ-b leaf–maximum pairs), and then Lemma C does (4,052 maxima, all
  with two terminal leaves).
  7,824 maxima have no terminal leaf (regime II): one terminal τ, one leaf o, the path τ → o of length 1, x big-top,
  and Lemma B applies.
- *Paths of length 2* occur only in the n = 4 hunts (10 paths). There Lemma B's target key is a (T3) neighbour as well,
  but at those maxima another lemma applies first.
- *Second implementation.* `k4/sx_xcheck.py` (main's `k4/c4x_check.py` enumeration and direct deficit) agrees with
  `k4/sx_keygraph.py` on every key's def* and on the DLK verdicts of all four edge sets. It ran on #53's n = 3 catalogue
  dump and samples of the n = 4 hunts, with 0 mismatches (`results/k4_sx/xcheck_*.log`).

### 4.3 The key graph on #53's catalogues and on the T1-stuck profiles of `k4/dl13.md`

`k4/sx_keygraph.py` computes every key, its def*, and its neighbours for the four edge sets. DLK fails for **no** edge set
on any of these inputs, and SKG (a neighbour with def* ≤ 0) holds wherever a key has def* > 0. Sources:
`results/k4_sx/keys_summary.md` and the logs under `results/k4_sx/chunks/`; T1-stuck profiles:
`results/k4_sx/t3stage/keys.log`.

| input | profiles (f ≥ 1, ω ≥ 1) | keys | keys with def* > 0 |
|---|---|---|---|
| #53's n = 3 catalogue, every record (f = 1) | 74,256 | 147,658 | 1,204 |
| n = 4, one 4-good agent, every record (f = 1, 2) | 44,388 | 53,128 + 55,232 | 0 |
| n = 4, two 4-good agents, 4,000 per core (f = 1, 2) | 36,164 | 60,422 + 11,190 | 0 |
| n = 4, three 4-good agents / pure, 4,000 per core, the f = 2 records | 3,023 / 1,767 | 10,025 / 5,704 | 3 / 7 |
| n = 4 hunts (three / four 4-good agents), the f = 2 records; hard hunt | 58 / 332; 117 | 254 / 1,412; 450 | 1 / 41; 15 |
| profiles of the 13,971 T1-stuck state records of `k4/dl13.md` §1 (n ≤ 5, f = 1, 2, 3) | 2,674 | 7,216 | 1,241 / 191 / 5 (f = 1 / 2 / 3) |

On the T1-stuck profiles (`results/k4_sx/t3stage/zprime_f1.log`), every Z′-maximum of each of the 1,241
non-completable f = 1 keys is covered by Lemma A, B, C or C′ with the structural hypotheses: A 1,133, B 80, C 539,
C′ 4 of 1,756 maxima. So every T3-stage state of `k4/dl13.md` §2.3 at f = 1 lies in a key that these lemmas repair. The
second implementation agrees on def* and on the DLK verdicts:
- #53's n = 3 catalogue: 1,204 keys with def* > 0 (`results/k4_sx/xcheck_gap_n3.log`);
- every 50th n = 3 hunt profile: 1,246 (`xcheck_hunt_n3.log`);
- the n = 4 hunts: 299 (`xcheck_hunt_n4.log`);
- the T1-stuck profiles with m ≤ 10: 1,412 (`t3stage/xcheck.log`);
- the f = 3 profiles: 41 (`f2/xcheck_rt4_n5*.log`).

0 mismatches.

### 4.4 The f = 1 failure of single-step DL, seen from Theorem Z′'s state

compute/k4-rc (`results/k4_rc/FAILURES.md` on that branch; three implementations there) found 45 strict profiles of one
n = 5 core, pos 4604 of `k4_certs_5_pure` (m = 13, sets
`[[0,2,9,11],[1,6,10,12],[3,7,11,12],[4,8,11,12],[5,9,10,12]]`). Each has the state

  P_fail = ({11}, {12}, {3,7}, {4,8}, {5,9}),

with f = 1 and def 1, from which no (T1), (T2), (T3) or (T4) move lowers the deficit. So DL from *every* state (DL_RT4,
DL_RC) is false already at f = 1. A proof of DL on the key graph must choose its starting state inside the key; this
is the first instance where that choice is needed. The route of this file makes the choice by Theorem Z′.

The tools of §4 on these 45 profiles (`k4/sx_rc_case.py`; `results/k4_sx/rc/`) give:
- *One key with def* > 0 per profile*: κ = (11, agent 0), def* = 1, 35 states. 31 of them have deficit 1 and 4 have
  deficit 2, by both implementations (counters "key states with def = 1 / 2" of `results/k4_sx/rc/case.log`). The 31
  are the list in compute/k4-rc's `rc_failures_n5_keyform.log`. **compute/k4-rc's FAILURES.md says the key's 35 states
  all have def = 1; that is not so: 4 have def 2.** Of the 31, 30 have a (T3) move to deficit ≤ 0. P_fail is the only
  one without.
- *Theorem Z′'s configuration*: (r′, Λ′) has a unique maximum at κ, the same in all 45 profiles:
  - pairs Q₁ = {1,12}, Q₂ = {3,7}, Q₃ = {4,8}, Q₄ = {5,9}, pool L = {0,2,6,10}, (r′, Λ′) = (4, 26);
  - free-valid owners (leaves) V = {1,2,3,4}; terminals T = {2,3}, the two needers of 11 (regime I);
  - neither terminal is θ-b. Both are big-top on 11, but 12 ∉ X₂, X₃.

  Its state is P_Q = ({11}, {1,12}, {3,7}, {4,8}, {5,9}), with deficit 1.
- *P_Q is neither P_fail nor the state of the coordinator's (T3h) witness*, P_wit = ({11}, {6,10}, {12}, {4,8}, {5,9}).
  It is one (T1) step from P_fail: agent 1 adds the pool good 1 to its base {12}.
- *Lemma A applies at P_Q* (main case A in all 45 profiles; `results/k4_sx/rc/zprime.log`). The terminal leaf o = 2
  (or o = 3) takes {11}, and x = 0 takes {0,2} ⊆ X_o and owns X_o. This is one (T3) move without helper. Its image is
  ({0,2}, {1,12}, {11}, {4,8}, {5,9}) for o = 2, or ({0,2}, {1,12}, {3,7}, {11}, {5,9}) for o = 3. Both have deficit 0
  by both implementations and lie in keys with def* = −1.

  The second image is FAILURES.md's example of the 6 nearest better states of P_fail, at distance 3, where "helper 1
  grows {12} by a junk good". So the role swap that no single move from P_fail makes is a (T1) step inside κ to Theorem Z′'s state, followed
  by Lemma A's owner swap.

So at the one instance where the start inside the key matters, Theorem Z′'s configuration chooses a state from which the
simplest repair lemma works. In Lean, PR #79's `dlKeyAt_of_keyMin_key` lets a repair lemma start from any state of
the key. `k4/sx_xcheck.py` on the 45 profiles finds 135 keys, 45 with def* > 0, 0 mismatches, and DLK for every edge
set (`results/k4_sx/rc/xcheck.log`). `k4/sx_rc_case.py` recomputes every deficit it prints with main's
`k4/c4x_check.rodef`.

## 5. What remains at f = 1

Theorem 1 reduces DL on the key graph at f = 1 to one statement:

> **Conjecture K4.SX.COVER.** At some Z′-maximum of every non-completable key with f = 1, one of Lemmas A, B (k = 1),
> B′ (k = 1), C, C′ applies, with all its hypotheses, in their exact form: for B′, that X″ contains a pair for x and
> (H_B′); for C, (H); for C′, (H′).

Evidence (K4.SX.COV), in two implementations (`k4/sx_zprime.py` on model.py, and the PR #80 referee's
`k4/sx_indep.py`, which shares no repository code):
- It holds on every strict profile with n ≤ 3, on the n = 4, 5 hunts, on the T1-stuck profiles and on compute/k4-rc's
  45 profiles (§4.2, §4.4).
- At n ≤ 3, and in the first n = 4, 5 hunts, it holds even at *every* Z′-maximum and with the structural hypotheses
  (H_B′*), (H*), (H′*).
- The structural form fails in the larger n = 4 hunt. There 5 Z′-maxima, each the unique maximum of its key, are covered
  only with the exact hypotheses (`attempts/k4-sx-cover-structural.md`, K4.SX.X).
- B′'s hypothesis that X″ contains a pair for x is needed: it fails at 2 Z′-maxima of the 400,000-per-core n = 4 hunt
  (`results/k4_sx/indep_n4_pure_r400k.log`, the "NOTE B′ no pair for x" lines). An example: sets
  [[0,2,6,7],[1,3,6,8],[4,5,7,8],[4,5,7,8]], values [[5,6,4,8],[6,3,5,7],[6,3,2,10],[4,3,2,8]], m = 9, key (8, 1),
  path 3 → 0, where X″ ∩ U_x = {3} is not admissible. Other lemmas cover those keys.

Where a proof has to go, by Lemma F:
1. *Some terminal is a leaf without θ-b.* Lemma A applies.
2. *Every terminal leaf is θ-b.* Such a leaf is robust, hence an isolated vertex of the forest. Lemma C needs
   - a robust pair of x inside X_{τ₁} meeting U_{τ₁};
   - another leaf o, and the hypothesis (H) on third agents.

   Lemma C′ needs
   - exactly two terminals τ₁, τ₂, with τ₂ a leaf;
   - a robust pair P of x inside X_{τ₁} worth more than g;
   - a good w ∈ U_{τ₁} ∖ P with U_{τ₂} ⊆ Y = (X_{τ₂} ∪ Q_{τ₁}) ∖ (P ∪ {w});
   - the hypothesis (H′) on third agents.

   A proof needs the existence of that pair, from x's threat by X_{τ₁} (`k4/c4min_f1.md` Lemma 4 gives a robust pair
   worth more than g for x not big-top, but not one meeting U_{τ₁}), and a replacement for (H)/(H′) when third agents
   value τ₁'s pair. At n = 3 the hypotheses (H), (H′) are void, and on the data the pair exists.
3. *Some terminal is not a leaf.* Lemma B applies along a path to a leaf, except for (R) leaves with s ∈ L, where B′
   needs X″ to contain a pair for x and (H_B′) to hold. The open part is a path of length ≥ 2, where Lemma B's key
   (g, τ) has def* ≤ 0 but (T3)-adjacency to κ is not proved. On the data every such key is a (T3) neighbour, and the
   case never arises alone.

So a proof of K4.SX.COVER needs (2) and (3). Case (1) is done by Lemmas F and A (K4.SX.KEY, K4.SX.REP, PROVED). With
COVER, DL on the key graph at f = 1 follows (Theorem 1), and with Remark 1.2, C₄ᵐⁱⁿ at f = 1. The f ≥ 2 analogues
are in §6 ("What f ≥ 2 still needs").

## 6. f ≥ 2

**The (T3) ∪ (T4) form is false (K4.DL13.KEY); the target is (T3⁺) ∪ (T4) (K4.DL2.RC).** The coordinator checked the
DL_RT4 failures of compute/k4-rt4-n5b and -n5c (K4.DL2.RT4) (67 states in 10 profiles, all with f = 3, def = 1 and nearest distance 3) on
`k4/dl134_xcheck.py`'s model. In each profile some key with def* = 1 has no neighbour of smaller def* by one (T3) or
(T4) move from any of its states. Every repair there is a (T3⁺) move: x frees g, a frozen w moves from h to g, and a
free z takes h. `k4/sx_keygraph.py` reproduces this on the smallest profile, core pos 3206 of `k4_certs_5_n4_4`
(`python3 k4/sx_keygraph.py one '{"m": 9, "sets": [[0,2,4,7],[1,4,7,8],[3,6,8],[5,6,7,8],[5,6,7,8]], "vals":
[[6,3,5,7],[4,2,8,7],[2,4,3],[4,8,1,6],[2,7,8,4]]}'`). The key (7, 8, –, –, 6) has def* = 1. Its (T3) ∪ (T4) neighbours
all have def* = 1, and DLK holds there with (T3⁺) edges. On all 10 profiles both implementations of this file
(`results/k4_sx/f2/keys_rt4_n5*.log`, `xcheck_rt4_n5*.log`) find the 10 failing keys of K4.DL13.KEY, and the
(T3⁺) ∪ (T4) form holding at all 41 keys with def* > 0, as K4.DL2.RC reports.

**Lemma F⁺ (the threat forest at any f).** Let f ≥ 1 and ω ≥ 1, and let κ = (𝒩, φ) be a key with def*(κ) > 0. Let Q
maximize (r′, Λ′) over the configurations at κ: r′ counts the robust free agents, v_y(Q_y) ≥ v_y(U_y ∖ Q_y) with
U_y = R_y ∖ 𝒩, and Λ′ is the sum of the free agents' levels. Then:
- Q is pool-optimal;
- every free agent is threatened by at most one free agent, a robust one by none;
- there is no cycle of threats among free agents;
- every free agent threatens somebody.

Hence the threats among the free agents form a forest of out-trees. Its leaves, which exist since f ≤ n − 1
(`k4/dl13.md` §1, Remark), are exactly the free-valid owners (V ≠ ∅), and every leaf threatens at least one frozen agent.

*Proof.* As for Lemma F, with `k4/c4min.md` §3.6 (the lemmas of Theorem F, K4.C4MIN.F) in place of the f = 1 lemmas.
- A pool improvement keeps the key and raises (r′, Λ′).
- For the kinds: a free agent with |U_y| ≤ 2 is robust. With |U_y| = 3 the only non-robust holding is u₁ with a good
  outside U_y; it is threatened exactly by the owner holding {u₂, u₃}. With |U_y| = 4 we have the kinds (T4), (D) and
  (R) of Lemma Z2. Each kind has at most one threatener.
- A cycle of threats among free agents rotates, plain or modified at one (R) receiver as in `k4/c4min.md` Lemma R, into
  a configuration at the same key. There a receiver of kind |U| = 3, (D) or (R) becomes robust, or, if all receivers are
  of kind (T4), every receiver's level rises. Robustness of agents off the cycle depends only on their own pairs. So
  (r′, Λ′) rises, against maximality.
- A free agent that threatens nobody would be a valid owner with C = ∅, and κ would be completable (Lemma 0). ∎

So the existence of a free-valid owner at the maxima, which Theorem Z′ proves at f = 1 (K4.C4MIN.RED.Z), holds at every
f once the key is not completable (Lemma F⁺, K4.SX.APLUS, PROVED). At f = 1 it also follows this way. The f ≥ 2 data
(all 199 maxima below have one) is explained.

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

**Lemma B⁺ (the path move along a need chain).** Let f ≥ 1, ω ≥ 1 and κ = (𝒩, φ), with Q maximizing (r′, Λ′) at κ
(so Lemma F⁺ applies). Let:
- o be a leaf whose bundle X_o threatens exactly one frozen agent, x;
- x = w₀, …, w_j be a need chain of frozen agents as in Lemma A⁺;
- τ ≠ o be a free agent with φ(w_j) ∈ N_τ(H_τ);
- τ = q₀ → … → q_k = o (k ≥ 1) be a threat path, with o not of kind (R) with its fourth good in L.

Q′: w_i holds φ(w_{i−1}), τ holds φ(w_j), q_i holds Q_{q_{i−1}}, x holds a pair for x inside X_o, and the pool is
X_o ∖ Q′_x. Then Q′ is a configuration at its key, and x is a valid owner with C = ∅. For k = 1, P_Q → P_{Q′} is one
(T3⁺) move with W = {w₁, …, w_j} and helper o. It is (T3) if j = 0, and at f = 1 it is Lemma B.

*Proof.* Validity is as in Lemma A⁺: τ takes a good it needs, so its needs stay in 𝒩, and the receivers are handled as
in Lemma B with the kinds of Lemma F⁺. Safety of X_o:
- the receivers, the free agents off the path, and the frozen agents off the chain: as in Lemmas B and A⁺;
- w_i, whose value rises;
- τ holding φ(w_j) (Lemma S⁺). X_o ∩ R_τ ⊆ U_τ ∖ H_τ, and each of these goods is worth less than H_τ, which is worth
  less than φ(w_j). Since τ values φ(w_j) ∈ 𝒩, |U_τ| ≤ 3, so two such goods occur only for H_τ = {u₁}, and there
  Lemma S's argument (pool-optimality, o not threatening τ) bounds them by v_τ(u₁).

The move for k = 1 is checked as in Lemmas A⁺ and B. ∎

**Data (EVIDENCE, `k4/sx_f2.py`).** At every key with def* > 0 of the 10 profiles of compute/k4-rt4-n5b and -n5c
(`results/k4_sx/f2/rt4_n5b.log`, `rt4_n5c.log`; instance lists `results/k4_sx/f2/rt4_n5*_inst.json`, copied from the
coordinator's checks), at every maximum of (r′, Λ′), a free-valid owner exists. At n5b, at all 15 keys and all 81
maxima, its bundle threatens one frozen agent and Lemma A⁺ applies: 24 times with j = 0 and 57 with j = 1. 15 of the 81
maxima have no direct (T3) repair but a (T3⁺) one. At n5c, Lemma A⁺ applies at 86 of 118 maxima and at some maximum of
19 of the 26 keys. Lemma B⁺ applies at 28 maxima, all of them maxima where Lemma A⁺ applies too (path length 1, need chains of length 1). The other 7 keys are the failed candidate `attempts/k4-sx-aplus-f3.md`, where neither applies. There some free-valid
owner's bundle threatens two frozen agents (35 owner–maximum pairs), or the owner at the chain's end is threatened by
its own bundle (35 chains, the analogue of θ-b). DLK with (T3⁺) ∪ (T4) edges holds at all of them (`k4/sx_keygraph.py`,
`k4/sx_xcheck.py`). The repairs there have the shape of Lemmas C and C′: another free-valid owner owns after the swap.

The f = 2 keys with def* > 0 of §4.3 give the same picture. Lemma F⁺ held at every maximum (asserted by `k4/sx_f2.py`)
and DLK with every edge set holds. The coverage by Lemmas A⁺, B⁺ is partial, and is not proved to be complete:

| input | keys (maxima) | A⁺ or B⁺ at some maximum | why not, per maximum without either (an owner–maximum may count twice) |
|---|---|---|---|
| f = 2 keys of the n = 4 catalogues and hunts (`results/k4_sx/f2/catalogues_f2.log`) | 67 (110) | 18 keys | a leaf threatens two frozen agents 45; the free needers are off the path to the leaf 25; θ fails at the chain's end or an (R) leaf 18 |
| T1-stuck profiles, f = 2, 3 (`results/k4_sx/t3stage/f2.log`) | 196 (411) | 156 keys | 41 / 13 / 18 |

**What f ≥ 2 still needs.**
- Lemma F⁺ gives the forest and the leaves. What is missing is the analogue of Lemma T, a *free* needer of a frozen
  good reached by a need chain from the threatened frozen agent. At f ≥ 2 every good of 𝒩 may be needed by frozen
  agents only. Then the frozen need digraph has a cycle, which is a (T4) move (`k4/dl13.md` Lemma 12), but that move
  is not shown to lower def*.
- The analogues of Lemmas B, C and C′ along need chains.
- A leaf's bundle may threaten two frozen agents (the failing case above); at f = 1 it threatens only x.

## 7. Reproduce

One process at a time. Every script resumes where it stopped: a piece whose log is complete is skipped. The times are
on a shared 4-CPU machine.
```
mkdir -p k4/suite/.cache/gapbench && git archive 245040b results/k4_gap | tar -x -C k4/suite/.cache/gapbench
sh k4/sx_hunt_runs.sh        # non-completable f = 1 keys with k4/red.c -> results/k4_sx/hunt/ (n = 3, all: ~6 min)
sh k4/sx_zprime_runs.sh      # §4.2: the repair lemmas at every Z′-maximum -> results/k4_sx/zprime/ (n = 3: ~1 h)
sh k4/sx_more_runs.sh        # T1-stuck profiles of k4/dl13.md, the catalogues (key graph, f >= 2), cross-checks
python3 k4/sx_summary.py     # results/k4_sx/SUMMARY.md
python3 k4/sx_runs.py --sum  # results/k4_sx/keys_summary.md
python3 k4/sx_f2.py --inst=results/k4_sx/f2/rt4_n5c_inst.json        # §6: Lemmas F+, A+, B+ at f = 3 (seconds)
python3 attempts/k4_sx_attempts.py                                   # K4.SX.X, two implementations (seconds)
python3 k4/sx_keygraph.py inst results/k4_sx/rc/rc_fail_inst.json --dump=results/k4_sx/rc/keys.jsonl.gz  # §4.4 (seconds)
python3 k4/sx_zprime.py results/k4_sx/rc/keys.jsonl.gz; python3 k4/sx_rc_case.py results/k4_sx/rc/rc_fail_inst.json
python3 k4/sx_xcheck.py results/k4_sx/rc/keys.jsonl.gz               # §4.4, second implementation (~1 min)
python3 k4/sx_keygraph.py one '{"sets": ..., "vals": ..., "m": ...}'  # one profile: keys, def*, neighbours
```
