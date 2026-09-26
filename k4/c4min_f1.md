# C₄ᵐⁱⁿ with one frozen agent (f = 1)

Workstream `proof/k4-c4min-f1`, building on `k4/c4min.md` (PR #41): its configurations (§1), Theorem Z (§3),
Theorem F (§3.6), and the f = 1 roadmap (§4). Ledger rows K4.C4MIN.F1* (CONJECTURE / EVIDENCE only), open item 23.
Other PRs are cited in §6.

**Target.** The local improvement lemma of `k4/c4min.md` §4 for configurations with an exposed frozen agent, for
f = 1: every configuration at the fewest frozen agents without a valid owner has a move that raises a potential.
Then every maximum of the potential is completable, and C₄ᵐⁱⁿ holds.

**Status.** Written proofs, not yet reviewed; every lemma is checked by brute force (§4). Nothing here changes K4.D or
K4.T.
- **Theorem F1** (§2): on every strict profile with fewest frozen agents 1 (and ω ≥ 1), every configuration that
  maximizes Ψ = (#robust agents, Σ levels) and whose frozen agent is **not big-top** has an owner, even without the
  unfreezing clause. Big-top: four goods, top worth more than the next two together. The proof is Theorem Z's
  (`k4/c4min.md` §3) plus one new move:
  - the *path move* takes the pairs one step along the threat path from a terminal to the frozen agent x;
  - x takes its best pair and becomes free and robust;
  - the terminal takes g and becomes frozen.

  The frozen agent is exposed at f = 1, which Theorems Z and F excluded. Status by type of x:
  - 3-good x: complete.
  - 4-good x that is not big-top: complete except one sub-case (Lemma 7, double case (E′)), which needs n ≥ 7 agents.
    So the proof is complete for n ≤ 6, and the sub-case never occurs on the samples (§4).
- **The big-top case** (§3): a Ψ-maximum without an owner has a big-top frozen agent, and every path move from it is a
  tie in Ψ. When some terminal is not big-top, the tied move is again a Ψ-maximum, with a frozen agent that is not
  big-top, so Theorem F1 makes it completable. The remaining profiles are those where every Ψ-maximum has a big-top
  frozen agent. On some of them no Ψ-maximum is completable (the smallest: n = 3, §3), so no potential that starts
  with (r, Λ) can work there. Protecting only big-top frozen agents first (Φ_BT) fails at n = 4. Conjecture Φ′ of
  `k4/c4min.md` §4, which protects every frozen agent first, has no failure at f = 1 on the runs here, but PR #53
  refutes it at f = 2. This case stays open; after the strategy change of 2026-09-26 no new potential is proposed
  here (§6).

## 1. Setting

Fix a strict profile of a k = 4 core whose fewest frozen agents is f = 1, with ω = f − (2n − m) = m − 2n + 1 ≥ 1.
Configurations are those of `k4/c4min.md` §1 at a needed set 𝒩 = {g} of a min-frozen pre-allocation:
- the frozen agent x holds g;
- every other (free) agent y holds a pair Q_y ⊆ M ∖ {g} whose part H_y = Q_y ∩ R_y is admissible. Admissible means
  every good of U_y = R_y ∖ {g} outside Q_y is worth less than H_y, i.e. y needs no good other than g;
- the pool L = (M ∖ {g}) ∖ ⋃ Q_y has ω goods.

All configurations at all min needed sets are compared together. H_x = {g}, a_i is i's top good, v_i(S) the value of
S ∩ R_i. The owner test is that of `k4/c4min.md` §1; with C = ∅ it reads: o threatens nobody, where o *threatens* z if
max_{h ∈ X} v_z(X ∖ h) > v_z(H_z) for X = Q_o ∪ L.

- A free agent y is **robust** if v_y(Q_y) ≥ v_y(U_y ∖ Q_y). A robust agent is threatened by nobody, since every owner's
  bundle meets R_y inside U_y ∖ Q_y.
- **Levels:** ℓ_i(S) = #{T ⊆ R_i : v_i(T) < v_i(S)}.
- **Potential:** r = number of robust agents (x is never robust, Lemma 1), Λ = Σ_i ℓ_i(H_i), Ψ = (r, Λ)
  lexicographically. These are r and Λ of `k4/c4min.md` §3.6 at f = 1.
- A **terminal** is an agent z ≠ x with g ∈ N_z(H_z), i.e. z needs g.
- x is **big-top** if |R_x| = 4 and v(a) > v(b) + v(c) (goods of R_x in decreasing value a, b, c, d); by balance
  v(a) < v(b) + v(c) + v(d) still.

**Lemma 1.** In every configuration:
- (a) g = a_x, and x is exposed: v_x(U_x) > v_x(g). In particular x is not robust in the sense of `k4/c4min.md` §3.6.
- (b) every terminal z has a_z = g.
- (c) Every *candidate* has an agent that needs g. A candidate is: an agent x′ with top g holding g, every other agent
  holding a pair outside g with admissible part, pairwise disjoint. So every candidate is a configuration at {g}, with
  x′ frozen.

*Proof.*
- (a) x's needs lie in 𝒩 = {g}, and g is its base. So no good of R_x is worth more than g. Balance gives
  v(R_x) − v(a_x) > v(a_x).
- (b) If a_z ≠ g, then a_z ∈ U_z, and admissibility gives v_z(H_z) ≥ v_z(a_z) > v_z(g) (a_z is in H_z, or is worth
  less than H_z).
- (c) The bases {g} (for x′) and H_y (for the others) form a pre-allocation whose needs lie in {g}. If nobody needed
  g, it would be valid with no frozen agent, contradicting f = 1. So g is needed and is a one-good base: the
  pre-allocation is valid, x′ is its only frozen agent, and it is min-frozen. ∎

Lemma 1(c) is what makes the moves below legitimate. The frozen agent may change, and nobody has to check that g
stays needed.

## 2. Theorem F1: the frozen agent is not big-top

**Lemma 2 (pool moves).** If a free agent y has a pair S ⊆ Q_y ∪ L with v_y(S) > v_y(Q_y), then replacing Q_y by S (the
rest of Q_y goes to the pool) gives a configuration with larger Ψ. Hence a Ψ-maximum is *pool-optimal*: no such S
exists.

*Proof.* `k4/c4min.md` Lemma Z1 with U_y in place of R_y:
- S is admissible, being worth more than an admissible set;
- y's level rises;
- y stays robust if it was, since v_y(U_y ∖ S) < v_y(U_y ∖ Q_y);
- nobody else changes;
- the result is a candidate, hence a configuration (Lemma 1(c)). ∎

**Lemma 3 (who can be threatened).** Let the configuration be pool-optimal, and y a free agent that is not robust. Then
y has one of these kinds:
- **(T3)** three goods, g ∉ R_y, H_y = {a_y};
- **(Tg)** four goods, g ∈ R_y, H_y = {u₁} where u₁ > u₂ > u₃ are its goods of U_y, and u₁ < u₂ + u₃;
- **(T4)** four goods, g ∉ R_y, H_y = {a_y};
- **(D)** four goods, g ∉ R_y, H_y = {a_y, d_y}, a + d < b + c;
- **(R)** four goods, g ∉ R_y, H_y = {p_y, q_y} ⊆ R_y ∖ {a_y} with p + q > a but p + q < a + s, where s_y is its fourth
  good.

A 3-good agent that values g is always robust. y is threatened by at most one owner o, in these ways:
- (T3), (T4): Q_o ⊆ R_y ∖ {a_y} with v_y(Q_o) > v_y(a_y);
- (Tg): Q_o = {u₂, u₃};
- (D): Q_o = {b_y, c_y};
- (R): a_y ∈ Q_o, s_y ∈ Q_o ∪ L and a + s > p + q.

*Proof.* For g ∉ R_y this is `k4/c4min.md` Lemma Z2: its proof uses only y's goods, pool-optimality and |Q_o ∪ L| ≥ 3.
For g ∈ R_y the agent's goods outside g are U_y:
- If |R_y| = 3, U_y = {u₁, u₂}, and an admissible H_y contains u₁, so y is robust.
- If |R_y| = 4, the admissible holdings are those containing u₁, or {u₂, u₃} when u₂ + u₃ > u₁. Each of them is robust
  except {u₁} with u₁ < u₂ + u₃.
- Then pool-optimality keeps u₂ and u₃ out of L. A single good cannot threaten, so the threat needs Q_o = {u₂, u₃}. ∎

**Lemma 4 (threats on x, not big-top).** Let x not be big-top, and let X = Q_o ∪ L threaten x. Then X contains a pair
P ⊆ U_x with v_x(P) > v_x(g). Every such P is admissible for x, and robust: v_x(P) ≥ v_x(U_x ∖ P). If x is 3-good,
P = U_x.

*Proof.* X ∩ R_x ⊆ U_x and |X| ≥ 3.
- If |X ∩ U_x| ≤ 1, every X ∖ h is worth at most one good of U_x, which is less than v(g).
- If |X ∩ U_x| = 2, X also holds a good outside R_x. Dropping it leaves X ∩ U_x, so P = X ∩ U_x.
- If |X ∩ U_x| = 3 (x 4-good), then P = {b_x, c_x}, which is worth more than g because x is not big-top.

U_x ∖ P is at most one good, and each good of U_x is worth less than g < P. ∎

**Lemma 5 (rotations).** Let the configuration be pool-optimal, and o₁ → o₂ → … → o_k → o₁ a cycle of free agents,
o_{j+1} threatened by o_j. The *rotation* gives o_{j+1} the pair Q_{o_j}, except at most one receiver of kind (R) whose
s lies in L. That receiver takes {a, s} instead, and the other good of Q_{o_j} goes to the pool; this modification is
used only when no receiver becomes robust by the plain rotation. The rotation gives a configuration with larger Ψ.

*Proof.* Every agent on the cycle is threatened, so none is robust. By Lemma 3 each receiver gets:
- (T3), (Tg), (D), or (R) with s ∈ Q_{o_j}: a pair worth more than before, on which it is robust (balance for
  (T3); u₂ + u₃ > u₁ for (Tg); `k4/c4min.md` Lemma R for (D) and (R));
- (T4): a pair worth more than before;
- (R) with s ∈ L: the pair {a, y′}, which contains its top.

Every new pair is admissible, so the result is a candidate, hence a configuration.
- If some receiver becomes robust, r rises.
- Otherwise, if some receiver is (R) with s ∈ L, the modified one becomes robust ({a, s}, as in Lemma R(iii)), and r
  rises.
- Otherwise every receiver is (T4), all values rise, and Λ rises while r does not fall. ∎

**Lemma 6 (the threat forest).** Let the configuration be pool-optimal, without an owner valid with C = ∅, and without
cycles of threat edges through free agents only. Then:
- every free agent threatens someone;
- every free agent is threatened by at most one owner (Lemma 3), and a robust one by none;
- from every free agent, following threat edges reaches x.

For a terminal τ let dist(τ) be the least number of free agents after τ on a threat path from τ to x.

*Proof.* The walk along threat edges through free agents cannot repeat an agent, since there is no cycle, and it
cannot stop at a free agent, since every free agent threatens someone. So it ends at x. ∎

**The path move.** Let τ = q₀ → q₁ → … → q_k → x be a threat path (q_j free, q_{j+1} threatened by q_j, and x by q_k),
with τ a terminal.
- P_x is x's best pair inside (Q_{q_k} ∪ L) ∩ U_x.
- For j = 1, …, k, q_j receives Q_{q_{j−1}}.
- x receives P_x and becomes free. The goods of Q_{q_k} ∖ P_x go to the pool, and the goods of P_x ∩ L leave it.
- τ receives g and becomes frozen.

Two rules apply only when no receiver becomes robust by the plain move:
- (*modification*) as in Lemma 5, at most one receiver of kind (R) with s ∈ L ∖ P_x takes {a, s} instead, and the
  other good goes to the pool;
- (*recycling*) otherwise, if the last receiver q_k is of kind (R), it takes its top together with its better good of
  Q_{q_k} ∖ P_x, instead of Q_{q_{k−1}}; the other good of Q_{q_{k−1}} goes to the pool.

**Lemma 7 (path moves, x not big-top).** Let the configuration be as in Lemma 6, with x not big-top. Let τ be a
terminal with dist(τ) minimal, and τ = q₀ → … → q_k → x a threat path with k = dist(τ). Then the path move gives a
configuration with larger Ψ, except possibly in case (E′) below. In case (E′), the path move along the walk of a second
terminal raises Ψ, unless that walk is in case (E′) too. That double case requires x to have four goods and n ≥ 7.

*Proof.* **Validity.**
- Receivers of kinds (T3), (T4), (Tg), (D), or (R) with s in the pair get a pair worth more than their holding, hence
  admissible.
- A receiver of kind (R) with s ∈ L, plain, modified or recycled, gets a pair containing its top.
- x gets P_x, admissible (Lemma 4).
- τ gets g = a_τ (Lemma 1(b)).
- The pairs stay disjoint. x's goods come from Q_{q_k} and L, which no other receiver gets. The modified receiver takes
  s ∉ P_x, and the recycled one keeps a good of Q_{q_k} ∖ P_x.

So the result is a candidate, hence a configuration with frozen agent τ (Lemma 1(c)).

**Changes.**
- x: robust after the move (Lemma 4), and its level rises, since v_x(P_x) > v_x(g).
- τ: its level rises, since it needed g. Frozen at f = 1 it is not robust (Lemma 1(a)), so r loses 1 if τ was robust.
- q₁, …, q_k were threatened, so none was robust. Their values rise, except (R) receivers with s ∈ L that are not
  modified.

The cases:
- **(A)** τ not robust: r rises by at least 1 (x), whatever the receivers do.
- **(B)** some receiver becomes robust by the plain move (kinds (T3), (Tg), (D), or (R) with s in the pair): r rises
  by at least 1 + 1 − 1.
- **(C)** otherwise, some receiver of kind (R) has s ∈ L ∖ P_x: the modified receiver is robust, and r rises by at
  least 1.
- **(D)** otherwise, every receiver is (T4): all levels on the path rise, r does not fall, and Λ rises by at least 2.
- **(E)** what remains: τ robust, every receiver of kind (T4) or (R) with s ∈ L ∩ P_x, and at least one of the
  latter. If the last receiver q_k is of kind (R), recycling makes it robust, and r rises by at least 1:
  - q_k holds {p, q} ⊆ R ∖ {a}, and s < q by pool-optimality;
  - it gets its top a (in Q_{q_{k−1}}, Lemma 3) and e ∈ {p, q};
  - v(a + e) ≥ v(R_{q_k} ∖ {a, e}), since a exceeds the other good of {p, q} and e > s.

  So the open case is **(E′)**: τ robust, every receiver of kind (T4) or (R) with s ∈ L ∩ P_x, at least one of the
  latter, and q_k of kind (T4).

**Case (E′) with a single threatening owner of x is impossible.**
1. Free agents are threatened by at most one owner, and x only by q_k. So the threat walk from any terminal, read
   backwards from x, is q_k, q_{k−1}, …, q₁, τ.
2. τ is robust, hence unthreatened, so the walk starts at τ.
3. Hence τ is the only terminal. The receivers are of kinds (T4) and (R), which do not value g.
4. After the plain path move nobody needs g: x holds P_x, worth more than g; τ holds g; nobody else changed or values
   g. This contradicts Lemma 1(c).

**A 3-good x has at most one threatening owner in case (E′).** Case (E′) has a receiver, so k ≥ 1 and, since
dist(τ) is minimal, no terminal threatens x. If both goods of U_x lay in L, every owner would threaten x. So at most
one of them lies in L, and x is threatened exactly by the holder of U_x ∖ L (Lemma 4: P = U_x). So case (E′) does not
occur for 3-good x. ∎

**Case (E′) for 4-good x.**

*Structure.*
- x has at least two threatening owners.
- A second terminal z exists: apply Lemma 1(c) to the plain move. Nobody on τ's path needs g after it, since the
  receivers of kinds (T4) and (R) do not value g.
- z's walk to x is disjoint from τ's path, since threatened agents have one threatener and τ has none. It enters x
  through another owner o₂, and o₂ ≠ z because dist(z) ≥ k ≥ 1.
- Cases (A)–(D), and (E) with recycling, did not use the minimality of dist(τ). So the path move along z's walk raises
  Ψ unless that walk is in case (E′) as well.
- Each walk in case (E′) has a terminal, an (R) receiver and a (T4) last receiver. So the double case needs n ≥ 7:
  six free agents on the two walks, and x.
- In the double case every (R) receiver on both walks has the same fourth good s, the only good of U_x in L.
  U_x = {s, u₁, u₂}, with u₁ held by q_k and u₂ by o₂.

*What is missing (double case (E′), n ≥ 7).* The plain move changes r by +1 (x) − 1 (τ) = 0, and Λ by

  (x's gain ≥ 1) + (τ's gain ≥ 1) + (≥ 1 per (T4) receiver) − Σ over (R) receivers of 1 + [p + s > a] + [q + s > a],

in each receiver's own values. Each loss term is at most 3, since s is the receiver's least good by pool-optimality.
This sum is not positive in general. The modified move would need a robust admissible pair of x without s, which may
not exist.

*Evidence.* Case (E′) never occurs on the samples of §4 (the counter L7rconf is 0 at n ≤ 6), and case (E) is always
resolved by recycling (L7recycle).

*What would close it.* A proof that in the double case the plain move of one of the two walks raises Ψ, or that the
double case contradicts f = 1. Lemma 1(c) is the natural tool: it already rules out a single threatening owner.

**Theorem F1.** Let a strict profile of a k = 4 core have fewest frozen agents 1 and ω ≥ 1. Let c maximize Ψ = (r, Λ)
over all configurations. If c's frozen agent x is 3-good, then some owner of c is valid with C = ∅, and C₄ᵐⁱⁿ holds on
the profile (`k4/c4min.md` Lemma 1(a)). The same holds when x has four goods and is not big-top, given the double case
(E′) of Lemma 7, in particular whenever n ≤ 6.

*Proof.* Suppose no owner is valid with C = ∅.
- By Lemma 2, c is pool-optimal.
- By Lemma 5, the threat digraph has no cycle through free agents.
- By Lemma 1(c) some terminal exists, and by Lemma 6 every terminal reaches x.
- Lemma 7 gives a configuration with larger Ψ (along τ's path or a second terminal's walk), a contradiction. ∎

*An algorithm.* The proof is effective, as for Theorem Z. Repeat until an owner is valid:
- pool improvements;
- then a rotation (Lemma 5) or a path move (Lemma 7).

Each step raises Ψ, which takes at most (n + 1)(16n + 1) values (r ≤ n, and each level is below 2⁴).

*What is used.* Strict values, |R_i| ≤ 4, balance, f = 1 (Lemma 1(c)), ω ≥ 1. The core's private-goods rule is not
used; nor is the rule that every good is relevant to someone, which Theorem Z needed.

## 3. The big-top case

**Lemma 8.** Let x be big-top (goods a > b + c, b > c > d).
- (a) X = Q_o ∪ L threatens x iff U_x ⊆ X and X ≠ U_x, i.e. iff U_x ⊆ X and ω ≥ 2. Every pair of U_x is worth less
  than g.
- (b) At a Ψ-maximum without an owner valid with C = ∅, some owner threatens x. So Theorem F1 also holds for a big-top x
  when ω = 1, and whenever no owner threatens x.
- (c) At such a maximum, let τ be a terminal at minimal distance and consider the path move along a shortest path
  (P_x = {b_x, c_x}). Then, except in case (E′) of Lemma 7:
  - τ is robust and threatens x directly (k = 0);
  - the move is a tie in Ψ: r is unchanged, x's level falls by exactly 1 and τ's rises by exactly 1.
- (d) In that tie, if τ is not big-top, the moved configuration c′ is again a Ψ-maximum whose frozen agent is not
  big-top. So c′ has an owner by Theorem F1, and C₄ᵐⁱⁿ holds on the profile.

*Proof.*
- (a) X ∩ R_x ⊆ U_x. If U_x ⊄ X, every X ∖ h is worth at most a pair of U_x, and b + c < a. If U_x ⊆ X, dropping a
  good outside U_x leaves b + c + d > a (balance), while X = U_x leaves at most b + c.
- (b) If nobody threatened x, every owner would threaten a free agent. Free agents are threatened by at most one owner
  (Lemma 3), so this map from the free agents to themselves would be injective, hence a permutation, and it would have
  a cycle. That contradicts Lemma 5.
- (c) By (a), X_{q_k} ⊇ U_x, so P_x = {b, c} is available. It is admissible and robust, and
  ℓ_x({b, c}) = ℓ_x({g}) − 1: the subsets of R_x worth less than a are the seven proper subsets of {b, c, d}, and
  {b, c} is the largest of them. Cases (A)–(C) of Lemma 7, and case (E) when recycling applies, raise r as before. In
  case (D), Λ changes by
  −1 + (τ's gain) + (a gain of at least 1 for each receiver), which is positive unless k = 0 and τ gains exactly one
  level.
- (d) Ψ(c′) = Ψ(c) is maximal. ∎

**No potential that starts with (r, Λ) handles every big-top profile.** In the smallest counterexample, n = 3 (core 46
of `results/k4_certs_3.json.gz`), no Ψ-maximum is completable. The three agents are all big-top with top 6, and share
good 7:
- agent 0 values 0:3, 2:6, 6:10, 7:2;
- agent 1 values 1:3, 4:4, 6:8, 7:2;
- agent 2 values 3:3, 5:4, 6:8, 7:2.

The profile has 76 configurations, 52 of them completable. Its three Ψ-maxima (Ψ = (2, 19)) all have the same shape:
- one agent is frozen on 6;
- the other two hold their two best goods;
- the pool is the frozen agent's other three goods, so every owner threatens it.

For example: agent 2 frozen, agent 0 on {0, 2}, agent 1 on {1, 4}, pool {3, 5, 7}. A completable configuration: agent 1
takes {1, 7} instead of {1, 4}. Good 7 then protects agent 2, and agent 0 is a valid owner. Agent 1 gives up level (its
second good drops from value 4 to 2) to protect the frozen agent, which Ψ cannot see.

**Protecting only big-top frozen agents is not enough either.** The potential Φ_BT = (−t, r, Λ, −p), with t and p
counted only when the frozen agent is big-top, agrees with Ψ on configurations whose frozen agent is not big-top.
- It has no failure on any strict profile with n ≤ 3, core 46 included (`results/k4_c4min_f1_phibt.log`).
- It fails at n = 4: 7 profiles of the pure n = 4 sample, and one at n = 5.
- The smallest failure is core 210 of `results/k4_certs_4_pure.json.gz`, with values
  - 0:5, 2:4, 8:2, 10:8;
  - 1:6, 5:3, 8:2, 10:10;
  - 3:6, 6:3, 9:2, 10:10;
  - 4:5, 7:4, 9:2, 10:8.

  Its two Φ_BT-maxima have a frozen agent (agent 0 or 3) that is not big-top, and no valid owner. The path moves out
  of them lead to an unprotected big-top frozen agent, which Φ_BT ranks lower. The Ψ-maxima of the same profile are
  completable, consistent with Theorem F1.

Both implementations confirm it (`attempts/k4-c4min-f1-bigtop.md`).

This is the same phenomenon as the counterexample to Conjecture Φ (`attempts/k4-c4min-potentials.md` instance 7).

Theorem F1 says that at f = 1 a non-completable Ψ-maximum has a big-top frozen agent. That is the (r, Λ) counterpart
of PR #46's conjecture K4.HALL.BT for Pareto-maxima (`k4/hall.md` §5). PR #52 refutes K4.HALL.BT at n = 4 with two
frozen agents that are not big-top, so its instance has f = 2 and does not bear on Theorem F1. Conjecture Φ′ =
(−t, r, Λ, −p) of `k4/c4min.md` §4 puts the frozen agent's protection first. It has no failure at f = 1 on the runs of
§4 and `results/k4_c4min_f1_phibt.log`, but PR #53 refutes it at f = 2.

## 4. Evidence

All counters come from `k4/c4min_f1.c` (driver `k4/c4min_f1_run.py`). It enumerates the valid pre-allocations and the
configurations as `k4/c4min.md`'s tool does, and everything after that is written from this file's definitions:
potentials, owners with and without the unfreezing clause, kinds, threat digraph, rotations, path moves, Φ′.
- Its count of profiles with f = 1 (7,284,544 at n = 3) equals `k4/c4min.c`'s.
- Its Φ′ counter agrees with `results/k4_c4min_phi_n3.log`: 0 failures.
- An independent Python checker of the same lemma steps (`k4/c4min_f1_proof.py`, on `k4/c4min_cfg.py`) agrees on the
  samples of `results/k4_c4min_f1_python.log`.

**Theorem F1 and its lemmas, every strict profile with n ≤ 3** (`results/k4_c4min_f1_n3.log`):

| | n = 2 | n = 3 |
|---|---|---|
| profiles with f = 1, ω ≥ 1 | 1,296 | 7,284,544 |
| configurations | 8,496 | 138,471,840 |
| … without an owner valid with C = ∅ (lemmas checked on each) | 5,616 | 30,290,192 |
| Theorem F1 (with Lemma 8(b)) failures | 0 | 0 |
| Lemma 2: value-raising pool moves / not raising Ψ | 7,920 / 0 | 72,477,432 / 0 |
| pool-optimal ones without owner | 1,440 | 1,407,032 |
| Lemma 3 (kinds, at most one threatener) violations | 0 | 0 |
| Lemma 5: rotations / not raising Ψ | 0 / 0 | 367,488 / 0 |
| Lemma 7: shortest path moves, x not big-top / not raising Ψ / case (E) recycled / case (E′) | 0 / 0 / 0 / 0 | 671,672 / 0 / 0 / 0 |
| Lemma 8 (x big-top): path moves with k = 0 raising / tied; k ≥ 1 raising / not; recycled; case (E′) | 0 / 1,440; 0 / 0; 0; 0 | 304,512 / 112,992; 226,320 / 0; 27,072; 0 |
| coverage: a Ψ-maximum with a 3-good frozen agent | 0 | 60,974 |
| … else one with a 4-good frozen agent that is not big-top | 0 | 3,422,442 |
| … else every Ψ-maximum big-top with ω = 1 (Lemma 8(b)) | 576 | 2,035,664 |
| … else every Ψ-maximum big-top, ω ≥ 2 (§3): some Ψ-maximum completable / none | 720 / 0 | 1,765,336 / 128 |
| Φ′ = (−t, r, Λ, −p): profiles with a non-completable maximum | 0 | 0 |

So Theorem F1 and Lemma 8(b) prove C₄ᵐⁱⁿ on 5,519,080 of the 7,284,544 n = 3 profiles with f = 1 (75.8%). The double case
(E′) cannot occur for n ≤ 6 (§2), so these proofs are complete there. With Theorems Z and F (`k4/c4min.md` §4 table), the
written proofs cover 117,875,052 of the 119,640,516 n = 3 profiles with ω ≥ 1 (98.5%). The rest are exactly the
1,765,464 f = 1 profiles whose Ψ-maxima all have a big-top frozen agent and ω ≥ 2; n = 3 has no f ≥ 2 profile without
a frozen-robust configuration.

The 128 profiles without a completable Ψ-maximum are all on core 46 (the n = 3 example of §3). A job with a failure
prints an example (`-x 3`), and only core 46's jobs do.

**Every strict profile of the n = 4 cores with one 4-good agent** (`results/k4_c4min_f1_n4.log`): 28,478 profiles
with f = 1.
- 0 failures of Theorem F1 and of every lemma.
- Coverage 100%: 24,102 by a 3-good frozen agent, 1,436 by a 4-good one, 2,940 by Lemma 8(b).
- With Theorems Z and F, the written proofs cover 86,524 of the 102,434 profiles of this class with ω ≥ 1. The rest
  have f ≥ 2 without a frozen-robust configuration.

**Samples** (`results/k4_c4min_f1_samples.log`): random profiles per core of every class, 100,000 per core at
n = 4, 1,500 at n = 5, 200 at n = 6 (one 4-good agent).

| class | profiles with f = 1 | F1 failures | lemma failures | covered: 3-good / 4-good / Lemma 8(b) | big-top only (ω ≥ 2): some Ψ-max completable / none |
|---|---|---|---|---|---|
| n = 4, two 4-good agents | 828,304 | 0 | 0 | 530,990 / 152,268 / 111,113 | 33,933 / 0 |
| n = 4, three | 1,379,221 | 0 | 0 | 462,800 / 511,769 / 226,797 | 177,855 / 0 |
| n = 4, pure | 1,076,769 | 0 | 0 | 0 / 609,794 / 190,059 | 276,912 / 4 |
| n = 5, one | 3,079 | 0 | 0 | 2,621 / 156 / 302 | 0 / 0 |
| n = 5, two | 81,177 | 0 | 0 | 58,522 / 11,246 / 10,164 | 1,245 / 0 |
| n = 5, three | 382,878 | 0 | 0 | 193,822 / 108,595 / 60,378 | 20,083 / 0 |
| n = 5, four | 622,121 | 0 | 0 | 160,002 / 278,732 / 113,285 | 70,102 / 0 |
| n = 5, pure | 395,570 | 0 | 0 | 0 / 241,741 / 76,266 | 77,562 / 1 |
| n = 6, one | 631 | 0 | 0 | 552 / 28 / 51 | 0 / 0 |

Other observations on these samples:
- Case (E′) never occurs (L7rconf = 0).
- Case (E) occurs 9 times at n = 5, always resolved by recycling (L7recycle).
- Φ′ has no failure on any sample.
- Φ_BT (§3) fails once at n = 5. Its n = 4 failures are in `results/k4_c4min_f1_phibt.log`.

## 5. Reproduce

```
python3 k4/c4min_f1_run.py results/k4_certs_2.json.gz -L -x 3                  # seconds
python3 k4/c4min_f1_run.py results/k4_certs_3.json.gz -L -x 3 --split=8        # ~10 min on 4 CPUs
python3 k4/c4min_f1_run.py results/k4_certs_4_n4_1.json.gz -L -x 3             # ~20 s
python3 k4/c4min_f1_run.py results/k4_certs_4_pure.json.gz -L -x 3 --rand=100000 --seed=91   # samples; see the log headers
python3 k4/c4min_f1_proof.py results/k4_certs_3.json.gz --rand=1500 --seed=31  # the independent Python checker
python3 k4/c4min_f1.py results/k4_certs_3.json.gz --maxima --rand=3000         # potentials at the maxima, by type of x
python3 k4/c4min_f1_bt.py results/k4_certs_3.json.gz --rand=1000               # the big-top ties (Lemma 8)
python3 k4/c4min_f1_run.py results/k4_certs_3.json.gz --split=8 -x 2           # Phi_BT without lemma checks (results/k4_c4min_f1_phibt.log)
python3 attempts/k4_c4min_f1_bigtop.py                                         # the failing potentials of §3
```

The RESULT counters of `k4/c4min_f1.c` are described in its header comment.

## 6. Relation to other pull requests

- **#41** (`k4/c4min.md`): the framework. Its referee fix batch measures the robustness of free agents against
  U_y = R_y ∖ 𝒩, as this file does from the start.
- **#46** (`k4/hall.md`, merged): K4.HALL.BT is compared in §3. It is refuted by **#52** at n = 4 (f = 2), which does
  not bear on Theorem F1. #52 also introduces the "downgrade swap" (a frozen agent passes its top to its needer).
  Theorem F1's catalogue does not need it at f = 1: its moves suffice at every Ψ-maximum with a frozen agent that is
  not big-top (§4).
- **#51** (`k4/c4min_reduce.md`, under review): its Lemma PM treats this file's path move under the potential
  (r′, −t, Λ), and lets a receiver keep part of its pair. The recycling rule of §2 is the case used here. #51's referee
  found that its local improvement lemma LIL fails on a non-core instance, so it must use the core's private-goods
  rule. Theorem F1's proof does not appeal to that rule, but all of its brute-force checks are on cores only.
- **#53** (compute/k4-gap): refutes Φ′ at f = 2 (pure n = 4, `attempts/k4-gap-phi-prime.md` on its branch).
- **Strategy (2026-09-26).** The project owner asked that the exposed-frozen gap no longer be attacked by new
  potentials or move families. This file therefore stops at Theorem F1, its open double case (E′), and the recorded
  failures for the big-top case. The choice of a single target statement is left to the strategy session
  (proof/k4-strategy).

