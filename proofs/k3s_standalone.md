# K3S is correct: a self-contained proof

Workstream `proof/k3-simplify`. The algorithm is `k3/simplify/k3s.py`, function `k3s` with its default arguments,
described in `proofs/k3_simple.md` §1.

**Status.** Written proof; not refereed, not machine-checked. It replaces `proofs/k3_simple.md` §3, which is a list of
changes to the proof of LB⁺ in `paper/k3/long.tex`. This document uses nothing from the paper: every notion is defined
and every step is proved below. The differences from the paper's proof are listed at the end.

**Main theorem.** Let n ≥ 1 agents have additive, nonnegative values over a finite set of goods, and let every agent
value at most three goods positively. Then K3S returns an allocation of all goods that is EFX₀ and in which every
bundle except one (the absorber's) has at most two goods.

The proof holds for every choice the algorithm leaves open: which peelable agent goes next, which agent leads, the
order of the upgrades, and which shared good HitSet uses. The code makes these choices by smallest index (§2).

## 1. Model

**Instances.** There is a finite set N of n ≥ 1 agents and a finite set M of goods, both numbered. Agent i has an
additive valuation v_i with v_i(g) ≥ 0, and R_i = {g : v_i(g) > 0} is the set of goods it *values*; we assume
|R_i| ≤ 3. Agent i's *ranking* lists R_i by value, larger first, ties broken by smaller index. We write g ≻_i h if g
comes before h; then v_i(g) ≥ v_i(h). The first, second and third goods of the ranking (those that exist) are a_i,
b_i, c_i. The code receives v[i] as a dictionary of the positive values, so its list `rk[i]` is this ranking.

**EFX₀.** An allocation X = (X_i) is a partition of M into bundles, some possibly empty. The *threat* of a set B of
goods to agent i is θ_i(B) = v_i(B) − min over h ∈ B of v_i(h), and θ_i(∅) = 0. Agent i is *safe* in X if
v_i(X_i) ≥ θ_i(X_j) for every j ≠ i, and X is *EFX₀* if every agent is safe. By additivity this is the usual
definition, v_i(X_i) ≥ v_i(X_j ∖ {h}) for all j ≠ i and all h ∈ X_j, including goods h that i values at 0.

**Lemma 1 (threats).** For every agent i and set B: (a) θ_i(B) = 0 if |B| ≤ 1; (b) θ_i(B) ≤ v_i(B ∩ R_i);
(c) θ_i({g, h}) = max(v_i(g), v_i(h)) for goods g ≠ h.

*Proof.* (a) θ_i({h}) = v_i(h) − v_i(h). (b) The minimum is at least 0, and v_i(B) = v_i(B ∩ R_i).
(c) v_i(g) + v_i(h) − min(v_i(g), v_i(h)). ∎

**Types of agents.** Agent i is *balanced* if |R_i| = 3 and v_i(a_i) ≤ v_i(b_i) + v_i(c_i); *strict* if |R_i| = 3 and
v_i(a_i) < v_i(b_i) + v_i(c_i); and *easy* if it is not strict, that is, if |R_i| ≤ 2, or |R_i| = 3 and
v_i(a_i) ≥ v_i(b_i) + v_i(c_i). Every strict agent is balanced. An easy agent with v_i(a_i) = v_i(b_i) + v_i(c_i) is
balanced too.

**Lemma 2 (when an agent is safe: the half we need).** Let X be an allocation and i an agent.
- (a) If i is balanced and b_i, c_i ∈ X_i, then i is safe.
- (b) Let y ∈ X_i ∩ R_i, or y = ⊥, and let D = {g ∈ R_i : g ≻_i y}, with D = R_i if y = ⊥. Suppose that no bundle X_j
  with j ≠ i and |X_j| ≥ 2 contains a good of D. Then i is safe, unless
  (∗) i is strict, y = a_i, and one bundle X_j with j ≠ i and |X_j| ≥ 3 contains both b_i and c_i.

*Proof.* Fix j ≠ i. If |X_j| ≤ 1, then θ_i(X_j) = 0 by Lemma 1(a). So let |X_j| ≥ 2 and T = X_j ∩ R_i; then
θ_i(X_j) ≤ v_i(T) by Lemma 1(b).
(a) X_j is disjoint from X_i, which contains b_i and c_i, so T ⊆ {a_i} and
v_i(T) ≤ v_i(a_i) ≤ v_i(b_i) + v_i(c_i) ≤ v_i(X_i).
(b) If y = ⊥, then T ⊆ R_i = D, so T = ∅ by hypothesis and θ_i(X_j) ≤ v_i(T) = 0. Otherwise y ∈ X_i. A good
g ∈ T is not in D and is not y (which lies in X_i), so y ≻_i g and v_i(g) ≤ v_i(y) ≤ v_i(X_i). If |T| ≤ 1, then
v_i(T) ≤ v_i(X_i). If |T| ≥ 2, then y and two goods ranked below it are three goods of R_i; as |R_i| ≤ 3, this forces
y = a_i and T = {b_i, c_i}. If |X_j| = 2, then X_j = {b_i, c_i} and θ_i(X_j) = v_i(b_i) ≤ v_i(a_i) ≤ v_i(X_i) by
Lemma 1(c). If |X_j| ≥ 3 and i is easy, then (as |R_i| = 3) θ_i(X_j) ≤ v_i(b_i) + v_i(c_i) ≤ v_i(a_i) ≤ v_i(X_i). If
|X_j| ≥ 3 and i is strict, (∗) holds. ∎

In words: an agent holding its b and c is safe (a); an agent is safe as long as the goods it ranks above a good it
holds stay alone (b), and the only exception is a strict agent holding its top whose b and c lie together in a bundle
of at least three goods. Theorem S shows that the outputs of K3S meet these conditions.

**Peeling.** For a set G of goods, agent i is *peelable at G* if R_i ∩ G = ∅, or the ≻_i-first good of R_i ∩ G is
worth to i at least as much as the other goods of R_i ∩ G together.

**Lemma 3 (who is peelable).** Agent i is peelable at G if and only if i is easy or R_i ⊄ G.

*Proof.* Let F = R_i ∩ G. If |F| ≤ 1, the other goods of F are worth 0 together. If |F| = 2, the first good of F is
worth at least the second. If |F| = 3, then F = R_i, and i is peelable if and only if v_i(a_i) ≥ v_i(b_i) + v_i(c_i),
that is, if and only if i is not strict. So i is not peelable if and only if |F| = 3 and i is strict, which (since a
strict agent has |R_i| = 3) means: i is strict and R_i ⊆ G. ∎

## 2. The algorithm

**States.** A *pre-allocation* (Y, U) consists of
- a *pick* Y_i ∈ R_i ∪ {⊥} for every agent i (⊥ means no pick), no good being picked twice; and
- a set U of *upgraded* agents; each u ∈ U is balanced, has Y_u = b_u and also holds c_u; the goods c_u (u ∈ U) are
  distinct and are nobody's pick.

The *leftover* goods are J = M ∖ (picks ∪ {c_u : u ∈ U}). For i ∉ U, the *needs* of i are
N_i = {g ∈ R_i : g ≻_i Y_i}, and N_i = R_i if Y_i = ⊥; an upgraded agent needs nothing. NA, the set of goods *needed
alone*, is the union of the sets N_i over i ∉ U. An agent i ∉ U is *frozen* if Y_i ≠ ⊥ and Y_i ∈ NA, and *free*
otherwise; upgraded agents are neither. The *base* of i is {Y_i} (∅ if Y_i = ⊥) if i ∉ U, and {b_i, c_i} if i ∈ U.

**The test for an absorber.** Let o be a free or upgraded agent.
- The agents *exposed* for o are
  E_o = {x : x is strict, x ∉ U, x ≠ o, Y_x = a_x, and b_x, c_x ∈ J ∪ base(o)}. For x ∈ E_o, π_x = {b_x, c_x} ∩ J.
- F_o is the number of free agents other than o.
- HitSet(E_o) is a list. Let one(z) = b_z if b_z ∈ J, and c_z otherwise. If two distinct agents x, y ∈ E_o have a
  common good g ∈ π_x ∩ π_y, take the first such triple in the code's loop order (x, then y, in index order, then g
  among b_x, c_x); the list is g followed by one(z) for every z ∈ E_o ∖ {x, y}. Otherwise it is one(z) for every
  z ∈ E_o. H_o is the set of goods on the list.
- The *test for o* passes if (T1) π_x ≠ ∅ for every x ∈ E_o, and (T2) |H_o| ≤ F_o.
- Complete(o) gives every pick to its picker and c_u to every u ∈ U, gives the goods of H_o one each to distinct free
  agents other than o (in index order), and gives every other leftover good to o.

**K3S.**
1. *Draft.* Let G = M. While some agent is unprocessed: if some unprocessed agent is peelable at G, the next agent i
   is one of them (a *peel turn*); otherwise i is any unprocessed agent (a *leader turn*, and i is a *leader*).
   Agent i picks Y_i = its ≻_i-first good of R_i ∩ G, or Y_i = ⊥ if R_i ∩ G = ∅, and Y_i leaves G.
2. *Upgrades.* Let U = ∅. While some balanced agent k ∉ U has Y_k = b_k, c_k ∈ J and b_k ∉ NA (J and NA for the
   current U), add one such k to U.
3. *Absorber.* Let r be the last agent of the draft not in U. If the test for r passes, return Complete(r).
4. *Rotation.* Let k be the agent of E_r that comes last in the draft. Build a list C: start with C = (k); for each
   agent j after k, in draft order, if the last agent ℓ of C is frozen, j ∉ U and Y_ℓ ∈ N_j, append j to C. (Frozen
   and N_j refer to (Y, U).) Write C = (x₀, x₁, …, xₜ) with x₀ = k. The *rotated* state (Y′, U′) has
   Y_xₛ′ = Y_xₛ₋₁ for 1 ≤ s ≤ t, Y_k′ = b_k, U′ = U ∪ {k}, and every other agent keeps its pick. Return Complete(k)
   for (Y′, U′).

**Correspondence with the code** (`k3/simplify/k3s.py`).

| Text | Code |
|---|---|
| peelable; draft; leader = smallest unprocessed index | `peelable`, lines 43–49, `lead_index` |
| N_i, NA, J | `needs`, `NA`, `junk` |
| free (one slot each); F_o | `caps` (1 if free, else 0); F_o = sum(cap) − cap[o] |
| upgrades, smallest index first | lines 69–74 |
| E_o, HitSet | `exposed`, `hitset` |
| (T1); (T2) after removing repeated entries; Complete | `absorb`: line 93; lines 96–97; lines 98–108 |
| r; k; the scan; the rotation | line 111; line 120; lines 121–126; lines 127–130 |

If the test for k fails in step 4, the code returns `None`. Theorem B shows that this never happens.

## 3. The draft

Number the turns of the draft; "x before y" means that x's turn precedes y's. *Block 0* is the run of turns before the
first leader turn (possibly empty). For β ≥ 1, *block β* is the β-th leader turn followed by the peel turns up to the
next leader turn. Let Λ be the number of leaders. Every agent lies in exactly one block, blocks 1, …, Λ are non-empty,
and the leader of block β ≥ 1 is its first agent. J₀ is the set of goods never picked in the draft.

**Lemma 4 (draft invariants).**
- (I1) If g ∈ R_i and (Y_i = ⊥ or g ≻_i Y_i), then g was picked before i's turn.
- (I2) If g ∈ R_i ∩ J₀, then Y_i ≠ ⊥ and Y_i ≻_i g.
- (B1) At each leader turn, before the leader picks, every unprocessed agent (the leader included) is strict and has
  all its goods unpicked. In particular a leader picks its top.
- (I3) A strict agent whose goods are all unpicked at its turn is a leader.
- (B2) If g ∈ R_j and (Y_j = ⊥ or g ≻_j Y_j), then g was picked by an agent of j's block before j.

*Proof.* (I1) At its turn, i took the ≻_i-first unpicked good of R_i, or nothing if none was left; so every good of
R_i ranked higher (every good of R_i, if i took nothing) was already picked. (I2) g was unpicked at i's turn, so i
took the ≻_i-first unpicked good of R_i, which is not g (g is never picked) and so is ranked above g. (B1) At a leader
turn no unprocessed agent is peelable; apply Lemma 3. A strict agent with all its goods unpicked takes a_i. (I3) At a
peel turn the agent is peelable, and by Lemma 3 a strict agent with all its goods unpicked is not. (B2) By (I1), g was
picked before j's turn. If j is in block 0, every earlier turn is in block 0, because block 0 is a prefix of the
draft. If j is in block β ≥ 1, then j was unprocessed when the leader turn of β began, so g was unpicked then by (B1);
hence g was picked during block β, before j's turn. ∎

## 4. The upgrades give a valid state

**Lemma 5 (upgrades).** The upgrade loop stops after at most n rounds, whatever order it uses. During the loop (Y, U)
is a pre-allocation, and NA only shrinks. When the loop stops:
- (V1) J ∩ NA = ∅;
- (V2) b_u ∉ NA and c_u ∉ NA for every u ∈ U;
- (UT) no balanced agent k ∉ U has Y_k = b_k, c_k ∈ J and b_k ∉ NA.

*Proof.* Each round adds a new agent to U. The picks are distinct goods of their pickers. An agent u is upgraded only
if it is balanced, Y_u = b_u and c_u ∈ J, so c_u is neither a pick nor an earlier c-good, and then c_u leaves J; so
the goods c_u are distinct and are not picks. Upgrading k removes N_k from the union and changes no other need, so NA
shrinks. (V1) J ⊆ J₀. If g ∈ J₀ and i ∉ U, then g ∉ R_i, or Y_i ≻_i g by (I2); either way g ∉ N_i. (V2) c_u ∈ J₀, so
c_u ∉ NA as in (V1). When u was upgraded, b_u ∉ NA, and NA only shrank afterwards. (UT) is the stopping condition. ∎

A pre-allocation with (V1) and (V2) is *valid*. So the state after step 2 is valid.

## 5. Soundness

Let (Y, U) be a pre-allocation and o a free or upgraded agent. A *completion with absorber o* is an allocation X with
X_i = base(i) ∪ C_i, where the sets C_i ⊆ J are disjoint with union J, |C_i| ≤ 1 for every free agent i ≠ o, and
C_i = ∅ for every other agent i ≠ o (C_o is unrestricted). It is an allocation of M, because M is the disjoint union
of the picks, the goods c_u (u ∈ U) and J, and each pick and each c_u lies in exactly one base. X satisfies the
*owner constraint* (OC) if no strict agent x ∉ U, x ≠ o, with Y_x = a_x has b_x, c_x ∈ X_o.

**Theorem S (soundness).** Let (Y, U) be valid and X a completion with absorber o. Then every bundle other than X_o
has at most two goods. If X satisfies (OC), then X is EFX₀.

*Proof.* *Sizes.* For i ≠ o: if i is frozen, X_i = {Y_i}; if i ∈ U, X_i = {b_i, c_i}; if i is free, X_i is at most
one pick plus at most one leftover good.

*No good of NA lies in a bundle of two or more goods.* Let |X_j| ≥ 2. By the sizes, j is not frozen if j ≠ o, and o
is free or upgraded by definition; so j is free or upgraded. X_j consists of j's pick if j is free, which is not in NA
by the definition of free, or of b_j and c_j if j ∈ U, which are not in NA by (V2), and of leftover goods, which are
not in NA by (V1).

*Safety.* Let i be an agent. If i ∈ U, then i is balanced and holds b_i and c_i, so i is safe by Lemma 2(a). If i ∉ U,
apply Lemma 2(b) with y = Y_i, which lies in X_i ∩ R_i or is ⊥. Then D = N_i ⊆ NA, so no bundle of two or more goods
contains a good of D. If (∗) held, i would be strict with Y_i = a_i, and b_i, c_i would lie in a bundle X_j, j ≠ i,
with at least three goods; by the sizes j = o, so i ≠ o, and (OC) excludes exactly this. So i is safe. ∎

*Easy agents.* An easy agent is safe even when it holds its top and the absorber holds its b and c (Lemma 2(b)). This
is why (OC), and hence exposure, concerns strict agents only. An easy agent with v_i(a_i) = v_i(b_i) + v_i(c_i) may be
upgraded; Lemma 2(a) needs only balance.

## 6. The absorber r

**Lemma 6 (the test).** Let (Y, U) be valid and o free or upgraded.
- (a) HitSet(E_o) has |E_o| − 1 entries if two of the sets π_x (x ∈ E_o) meet, and |E_o| entries otherwise. If (T1)
  holds, its entries are leftover goods and H_o meets {b_x, c_x} for every x ∈ E_o.
- (b) If the test for o passes, Complete(o) is a completion with absorber o that satisfies (OC). Hence it is EFX₀, and
  every bundle other than X_o has at most two goods (Theorem S).

*Proof.* (a) The code looks for g ∈ {b_x, c_x} with g ∈ J and g ∈ {b_y, c_y}, that is, g ∈ π_x ∩ π_y; it finds one
exactly when two of the sets meet, and the list then has 1 + (|E_o| − 2) entries. The shared good g is in J. The good
one(z) is b_z if b_z ∈ J, and otherwise c_z, which is in J because π_z ≠ ∅. The pairs of x and y contain g, and the
pair of every other z contains one(z).
(b) By (a), H_o ⊆ J. By (T2), there are at least |H_o| free agents other than o, so Complete(o) gives the goods of H_o
to distinct free agents other than o, one each. So it is a completion with absorber o, and X_o = base(o) ∪ (J ∖ H_o).
Suppose a strict agent x ∉ U, x ≠ o, with Y_x = a_x has b_x, c_x ∈ X_o. Then b_x, c_x ∈ J ∪ base(o), so x ∈ E_o, and
by (a) H_o contains b_x or c_x. That good is leftover, so it is not in base(o), and it was given to an agent other than
o; so it is not in X_o, a contradiction. ∎

From now until the end of §7, (Y, U) is the state after steps 1 and 2, which is valid (Lemma 5), and B\* is the block
of the last agent of the draft.

**Lemma 7 (a free agent in every block).**
- (a) The first agent of every non-empty block is not upgraded.
- (b) For a non-empty block β, let z_β be its last agent not in U. Then z_β is free.
- (c) r = z_B\*. So r exists, r is free, and every agent after r in the draft is upgraded.

*Proof.* (a) Let u ∈ U. Then a_u ≻_u b_u = Y_u, so by (B2) a_u was picked by an agent of u's block before u. (b) z_β
exists by (a). If z_β were frozen, some j ∉ U would need its pick; by (B2), that pick was picked by an agent of j's
block before j, and this agent is z_β. So j would be an agent of β after z_β and not in U, against the choice of z_β.
(c) By (a), the first agent of B\* is not upgraded, so the last agent of the draft not in U lies in B\*: it is z_B\*. ∎

**Lemma 8 (exposed agents are leaders).** Every x ∈ E_r comes before r in the draft, is a leader, and has π_x ≠ ∅.
Hence (T1) holds for r, and |E_r| ≤ Λ.

*Proof.* x ∉ U and x ≠ r, so x comes before r (Lemma 7(c)). At x's turn, a_x was unpicked (x picks it), every
leftover good was unpicked (it is never picked), and Y_r was unpicked if it exists (r picks it later). Since
base(r) ⊆ {Y_r} and b_x, c_x ∈ J ∪ base(r), all of R_x was unpicked at x's turn. As x is strict, it is a leader by
(I3). Since b_x ≠ c_x, at most one of them is Y_r, and the other lies in J. Distinct agents of E_r are distinct
leaders. ∎

**Lemma 9 (need chains).** Let x₀, …, xₜ be agents such that x₀, …, xₜ₋₁ are frozen and each xₛ₊₁ ∉ U needs the
pick of xₛ. Then all of them lie in x₀'s block, each after the previous one. A *need chain* from x is such a sequence
with x₀ = x, t ≥ 1 and xₜ free. Every frozen agent x has a need chain, and every need chain from x ends at a free
agent of x's block.

*Proof.* The pick Y_xₛ exists because xₛ is frozen. By (B2) applied to xₛ₊₁, Y_xₛ was picked by an agent of
xₛ₊₁'s block before xₛ₊₁, and that agent is xₛ. Induction on s gives the first claim. If x is frozen, some j ∉ U
needs Y_x; append it, and repeat while the last agent is frozen. Each step moves later in the draft, so this stops,
at an agent outside U that is not frozen, that is, at a free agent. ∎

**Theorem A (when the test for r fails).** Suppose the test for r fails. Then:
- (a) (Lemma T) Block 0 is empty. Every leader is exposed for r, so |E_r| = Λ. The sets π_x (x ∈ E_r) are pairwise
  disjoint. The free agents other than r are exactly the agents z_β with β ≠ B\*; so r is the only free agent of B\*.
- (b) The leader k of B\* is the agent of E_r that comes last in the draft, which is the agent k of step 4. It is
  frozen, and every need chain from k lies in B\* and ends at r.
- (c) The scan of step 4 produces a need chain from k, which ends at r.

*Proof.* (a) Let ε = 1 if block 0 is non-empty and ε = 0 otherwise, so there are Λ + ε non-empty blocks. The agents
z_β are free (Lemma 7(b)), lie in different blocks, and z_B\* = r (Lemma 7(c)), so F_r ≥ Λ + ε − 1. (T1) holds for r
(Lemma 8), so (T2) fails: |H_r| ≥ F_r + 1. By Lemma 8 and Lemma 6(a),

  Λ ≥ |E_r| ≥ (number of entries of HitSet(E_r)) ≥ |H_r| ≥ F_r + 1 ≥ Λ + ε.

So all these are equalities. Then ε = 0. |E_r| = Λ, and E_r consists of leaders, so every leader is exposed. HitSet
has |E_r| entries, so no two sets π_x meet (Lemma 6(a)). F_r = Λ − 1, and the Λ − 1 agents z_β with β ≠ B\* are free
agents other than r, so there are no others; they lie outside B\*.
(b) As block 0 is empty and Λ ≥ F_r + 1 ≥ 1, B\* is block Λ, and its leader k is exposed by (a). All agents of E_r
are leaders, and the other leaders come before k, so k is the last agent of E_r in the draft. k ∉ U, k ≠ r (by
definition r ∉ E_r) and k ∈ B\*, so by (a) k is not free: it is frozen. By Lemma 9, every need chain from k ends at a
free agent of B\*, which is r by (a).
(c) Every appended agent j is not in U, comes after the agent ℓ before it, and needs Y_ℓ, where ℓ is frozen. Let ℓ be
the last agent of C when the scan ends, and suppose ℓ is frozen. Then some j ∉ U needs Y_ℓ, and j comes after ℓ by
(I1), since Y_ℓ was picked at ℓ's turn. ℓ was the last agent of C from the moment the scan passed ℓ (from the start,
if ℓ = k) to the end; so when the scan reached j, it appended j, a contradiction. Hence ℓ is free. As k is frozen,
ℓ ≠ k. So C is a need chain from k, and it ends at r by (b). ∎

*Remark (the test is exact; not used below).* If the test for r fails, then no completion with absorber r satisfies
(OC). Indeed, let X be one, and let Q be the set of leftover goods given to agents other than r; |Q| ≤ F_r. If Q
missed π_x for some x ∈ E_r, then b_x and c_x would both lie in base(r) ∪ (J ∖ Q) ⊆ X_r, against (OC). So Q meets
every π_x; these sets are non-empty (Lemma 8) and pairwise disjoint (Theorem A(a)), so |Q| ≥ |E_r| = Λ = F_r + 1, a
contradiction. So K3S rotates only when no completion with absorber r satisfies (OC). The code tests the list after
removing repeated entries; this only shortens it, and Theorem A starts from the test exactly as the code runs it.

## 7. The rotation

Suppose the test for r fails, and let k and C = (x₀, …, xₜ), x₀ = k, xₜ = r, be as in Theorem A. Let
W = J ∪ base(r). As k ∈ E_r, b_k, c_k ∈ W. No agent of C is in U: k is exposed, and the scan appends only agents
outside U. A prime marks the notions of the rotated state (Y′, U′): J′, NA′, N_i′, E_k′, π_x′, F_k′.

**Theorem B (the rotation).**
- (a) (Y′, U′) is a pre-allocation, and J′ = W ∖ {b_k, c_k}.
- (b) NA′ ⊆ NA.
- (c) (Y′, U′) is valid.
- (d) Every free agent of (Y, U) outside B\* is free in (Y′, U′).
- (e) E_k′ ⊆ E_r ∖ {k}.
- (f) π_x′ ≠ ∅ for every x ∈ E_k′.
- (g) |E_k′| ≤ F_k′.

Hence the test for k passes in (Y′, U′), and Complete(k) is EFX₀, with every bundle other than k's of at most two
goods.

*Proof.* (a) Each xₛ (s ≥ 1) needs Y_xₛ₋₁, so Y_xₛ′ ∈ R_xₛ; and Y_k′ = b_k ∈ R_k. The picks of Y′ are the picks of Y
other than Y_r, each kept or moved one step along C, together with b_k. W contains no pick of Y other than Y_r, so
b_k ∈ W is none of the others, and no good is picked twice. No c_u (u ∈ U) lies in W, since c_u is neither leftover
nor a pick. So c_k ∈ W differs from every c_u, and also from b_k, so it is not a pick of Y′; and no c_u is a pick of Y′.
k is strict, hence balanced, with Y_k′ = b_k; every u ∈ U is off C, so Y_u′ = b_u. Finally, M is the disjoint union
of the picks of Y, the goods c_u (u ∈ U) and J; removing the picks of Y′ and the goods c_u (u ∈ U′) leaves
(J ∪ base(r)) ∖ {b_k, c_k} = W ∖ {b_k, c_k}.
(b) For s ≥ 1, xₛ ∉ U′ needs Y_xₛ′, so xₛ ranks Y_xₛ′ above Y_xₛ, or Y_xₛ = ⊥; hence N_xₛ′ ⊆ N_xₛ. Agent k ∈ U′ needs
nothing. Every other agent keeps its pick and its status, hence its needs.
(c) Y_r ∉ NA, because r is free (Lemma 7(c)), and J ∩ NA = ∅ by (V1); so W ∩ NA = ∅. (V1) for (Y′, U′): J′ ⊆ W and
NA′ ⊆ NA. (V2): for u ∈ U, b_u, c_u ∉ NA ⊇ NA′ by (V2); and b_k, c_k ∈ W.
(d) C lies in B\* (Theorem A(b)). A free agent y outside B\* keeps its pick and stays outside U′; if Y_y ≠ ⊥, then
Y_y ∉ NA ⊇ NA′. So y is free in (Y′, U′).
(e) base′(k) = {b_k, c_k}, so J′ ∪ base′(k) = W by (a). Let x ∈ E_k′: x is strict, x ∉ U′, x ≠ k, Y_x′ = a_x and
b_x, c_x ∈ W.
- If x is not on C, then Y_x = Y_x′ = a_x, x ∉ U, x ≠ r, and b_x, c_x ∈ J ∪ base(r). So x ∈ E_r ∖ {k}.
- x = xₛ with 1 ≤ s < t is impossible. Such an x is frozen, so Y_x ≠ ⊥, and a_x = Y_x′ ≻_x Y_x since x needs Y_x′. So
  Y_x is b_x or c_x. But Y_x is a pick of Y other than Y_r, so Y_x ∉ W, while b_x, c_x ∈ W.
- x = r is impossible. Then r would be strict (as r ∈ E_k′), hence balanced with |R_r| = 3. As r needs the pick of
  xₜ₋₁, N_r ≠ ∅, so Y_r ≠ a_r. If Y_r = ⊥ or Y_r = c_r, then b_r ∈ N_r, so by (I1) b_r is the pick of an agent before
  r; it is neither leftover nor Y_r, so b_r ∉ W. If Y_r = b_r, then r ∉ U and b_r = Y_r ∉ NA because r is free; so
  (UT), which applies because r is balanced, gives c_r ∉ J; and c_r ≠ Y_r, so c_r ∉ W. In both cases b_r, c_r ∈ W
  fails.

(f) Let x ∈ E_k′. If b_x, c_x ∈ {b_k, c_k}, then {b_x, c_x} = {b_k, c_k}; as x ∈ E_r ∖ {k} by (e), π_x = π_k, which
is non-empty (Lemma 8), against the disjointness in Theorem A(a). So b_x or c_x lies in W ∖ {b_k, c_k} = J′.
(g) By Theorem A(a), the Λ − 1 agents z_β (β ≠ B\*) are free in (Y, U) and lie outside B\*. By (d) they are free in
(Y′, U′), and they differ from k ∈ B\*. So F_k′ ≥ Λ − 1 = |E_r| − 1 ≥ |E_k′| by (e).

Finally, (T1) for k is (f). By Lemma 6(a) and (g), |H_k′| ≤ |E_k′| ≤ F_k′, which is (T2). (Y′, U′) is valid by
(c) and k ∈ U′, so Lemma 6(b) applies. ∎

## 8. Conclusion

*Proof of the main theorem.* Step 1 has n turns, and step 2 stops after at most n rounds with a valid state (Lemma 5).
r exists and is free (Lemma 7(c)). If the test for r passes, Complete(r) is EFX₀ and only X_r can have more than two
goods (Lemma 6(b)). Otherwise, by Theorem A, E_r is non-empty, so step 4's k exists, and the scan gives a need chain
from k to r; by Theorem B the test for k passes after the rotation, so the code does not return `None`, and Complete(k)
is EFX₀ with only X_k of more than two goods. No step used which peelable agent, leader, upgrade or shared good was
chosen. ∎

## Changes from the paper's proof

Compared with the proof of LB⁺ in `paper/k3/long.tex` §5 and the list of changes in `proofs/k3_simple.md` §3:
1. **One draft.** There is no Stage R: the draft serves peelable agents first, and Lemma 3 says who they are. Block 0,
   the turns before the first leader, is new; (B2) holds for it because it is a prefix of the draft (Lemma 4), and
   Theorem A shows that it is empty when r fails.
2. **Easy agents** take part in the whole algorithm. Lemma 2(b) makes them safe even when the absorber holds their b and
   c, so (OC) and exposure concern strict agents only. Easy agents with a = b + c may be upgraded.
3. **Safety.** Lemma 2 proves only the "safe" half of the paper's case analysis of safety (its Lemma L5), with ties and
   a = b + c allowed. The paper's soundness proof inlines the same argument.
4. **No overflow ω, one slot per free agent.** The absorber always takes every leftover good except H_o; the owner
   criterion (Lemma 6(b)) never needed the other slots to be full, and the counting uses only one slot per free agent.
5. **Lemma 7** replaces the paper's Lemma r and the terminals τ(x): the last non-upgraded agent z_β of each block is
   free. Its part (a) covers every block, block 0 included, through (B2).
6. **Theorem A** is proved by the counting of Lemma T, one chain of inequalities, instead of the paper's case analysis
   with Lemma count. It gives the paper's bad case (k frozen, every need chain from k ends at r, the sets π_x pairwise
   disjoint) and more: block 0 is empty, every leader is exposed, and r is the only free agent of its block. It also
   shows that "the last exposed agent" is the paper's k\*, "the first exposed agent of r's block".
7. **Proposition O is not used.** Theorem A starts from the failure of the code's own test, after the removal of
   repeated entries. Its exactness is the remark after Theorem A.
8. **(UT) only for a strict r.** In Theorem B(e), case x = r, (UT) is applied to r only when r is exposed, hence strict
   and balanced; an easy r is never exposed. Theorem B(g) counts the agents z_β instead of the terminals τ(x).
