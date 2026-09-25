# C₄ᵐⁱⁿ with one frozen agent (f = 1)

Workstream `proof/k4-c4min-f1`, building on `k4/c4min.md` (PR #41, under review): its configurations (§1), Theorem Z
(§3), Theorem F (§3.6), Conjecture Φ′ and the f = 1 roadmap (§4). Ledger rows K4.C4MIN.F1.* (CONJECTURE / EVIDENCE
only). PR #46 (`k4/hall.md`, an independent attack by covering/Hall counting) is cited where it is used or compared.

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
  - 4-good x that is not big-top: complete except one sub-case (Lemma 7, case E), which needs n ≥ 5 agents. It never
    occurs on any sampled profile with n ≤ 5 (§4).
- **The big-top case** (§3): a Ψ-maximum without an owner has a big-top frozen agent, and every path move from it is a
  tie in Ψ. When some terminal is not big-top, the tied move is again a Ψ-maximum, with a frozen agent that is not
  big-top, so Theorem F1 makes it completable. The remaining profiles are those where every Ψ-maximum has a big-top
  frozen agent. On some of them no Ψ-maximum is completable (the smallest: n = 3, §3), so no potential that starts
  with (r, Λ) can work there. This is PR #46's big-top obstruction (K4.HALL.BT), met from the other side.
  Conjecture Φ′ of `k4/c4min.md` §4, which puts x's protection first, has no failure there.

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

As in Lemma 5, at most one receiver of kind (R) with s ∈ L ∖ P_x takes {a, s} instead, the other good going to the
pool, and only when no receiver becomes robust by the plain move.

**Lemma 7 (path moves, x not big-top).** Let the configuration be as in Lemma 6, with x not big-top. Let τ be a
terminal with dist(τ) minimal, and τ = q₀ → … → q_k → x a threat path with k = dist(τ). Then the path move gives a
configuration with larger Ψ. The one possible exception is case (E) below, which requires x to have four goods and at
least two threatening owners.

*Proof.* **Validity.**
- Receivers of kinds (T3), (T4), (Tg), (D), or (R) with s in the pair get a pair worth more than their holding, hence
  admissible.
- A receiver of kind (R) with s ∈ L gets a pair containing its top.
- x gets P_x, admissible (Lemma 4).
- τ gets g = a_τ (Lemma 1(b)).
- The pairs stay disjoint: x's goods come from Q_{q_k} and L, which nobody else receives, and the modified receiver
  takes s ∉ P_x.

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
  latter.

**Case (E) with a single threatening owner of x is impossible.**
1. Free agents are threatened by at most one owner, and x only by q_k. So the threat walk from any terminal, read
   backwards from x, is q_k, q_{k−1}, …, q₁, τ.
2. τ is robust, hence unthreatened, so the walk starts at τ.
3. Hence τ is the only terminal. The receivers are of kinds (T4) and (R), which do not value g.
4. After the plain path move nobody needs g: x holds P_x, worth more than g; τ holds g; nobody else changed or values
   g. This contradicts Lemma 1(c).

**A 3-good x has at most one threatening owner in case (E).** Case (E) has a receiver, so k ≥ 1 and, since
dist(τ) is minimal, no terminal threatens x. If both goods of U_x lay in L, every owner would threaten x. So at most
one of them lies in L, and x is threatened exactly by the holder of U_x ∖ L (Lemma 4: P = U_x). So case (E) does not
occur for 3-good x. ∎

**Case (E) for 4-good x (open, checked).** x has at least two threatening owners. By the argument above, a second
terminal's walk reaches x through another owner, disjoint from τ's path. So n ≥ 5 (τ, an (R) receiver, x, a second
terminal and a second threatening owner). Case (E) never occurs on the samples of §4, including n = 5 (the counter
L7rconf, which counts shortest paths in case (E), is 0).

**Theorem F1.** Let a strict profile of a k = 4 core have fewest frozen agents 1 and ω ≥ 1. Let c maximize Ψ = (r, Λ)
over all configurations. If c's frozen agent x is 3-good, then some owner of c is valid with C = ∅, and C₄ᵐⁱⁿ holds on
the profile (`k4/c4min.md` Lemma 1(a)). The same holds when x has four goods and is not big-top, given case (E) of
Lemma 7.

*Proof.* Suppose no owner is valid with C = ∅.
- By Lemma 2, c is pool-optimal.
- By Lemma 5, the threat digraph has no cycle through free agents.
- By Lemma 1(c) some terminal exists, and by Lemma 6 every terminal reaches x.
- Lemma 7 gives a configuration with larger Ψ, a contradiction. ∎

*An algorithm.* The proof is effective, as for Theorem Z. Repeat until an owner is valid:
- pool improvements;
- then a rotation (Lemma 5) or a path move (Lemma 7).

Each step raises Ψ, which takes at most (n + 1) · 16n values.

*What is used.* Strict values, |R_i| ≤ 4, balance, f = 1 (Lemma 1(c)), ω ≥ 1. The core's private-goods rule is not
used; nor is the rule that every good is relevant to someone, which Theorem Z needed.

## 3. The big-top case

(In progress.)

## 4. Evidence

(In progress.)

## 5. Reproduce

```
python3 k4/c4min_f1_run.py results/k4_certs_3.json.gz -L            # C, every profile with n = 3 (Theorem F1, lemmas)
python3 k4/c4min_f1_proof.py results/k4_certs_3.json.gz --rand=300  # the independent Python checker, a sample
```
