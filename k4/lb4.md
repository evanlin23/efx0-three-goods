# LB₄: construction LB⁺ carried to four goods

Workstream `proof/k4-lb4`, ledger open items 15 and 18 (the LB₄ route of `k4/SCOUT.md` §5: steps (a) and (b) done, (c)
not done, (d) partial; LB₄'s P-step and upgrade rules depart from SCOUT §5's suggestions, §2). Notation as in
`proofs/construction.md` and `proofs/lb_last_step.md` (k = 3), and `k4/SCOUT.md` (k = 4 cores). Tools:
`k4/lb4.c` (the construction and an exhaustive tester), `k4/lb4_run.py` (driver), `k4/lb4_brute.py` (every EFX₀
allocation of a small instance, by brute force).

**Status.** LB₄ (§2) is defined, implemented, and tested exhaustively: it never fails on any strict profile of any
certified k = 4 core (n ≤ 4, and n = 5 with at most two 4-good agents; 1.14·10¹² profiles), nor on any tied profile
with n ≤ 3 (§4; EVIDENCE, single implementation, outputs re-checked by `k4/check4.py` where stored). Its soundness
(Theorem 1′₄, any k), the shape of its outputs (§2), the self-protection lemma (Lemma 2₄, |R_x| ≤ 4) and the exactness
of its owner search (Lemma 3₄) are written proofs, not yet reviewed. That LB₄ never fails is a
conjecture (K4.LB4): **there is no proof of K4.D here.** LB⁺'s Theorems A and B do not carry over (§5), and several
smaller variants, including LB⁺'s own shape, fail on small cores (§3, `attempts/lb4-*.md`).

## 0. Setting

An *instance* has agents N = [n] and goods M = [m], additive valuations, and relevant sets R_i = {g : v_i(g) > 0}.
Each agent has a fixed strict order ≻_i on R_i that is consistent with its values (v_i(g) > v_i(h) ⇒ g ≻_i h; ties
broken by index). In a k = 4 core |R_i| ∈ {3, 4} and every agent is strictly balanced. Theorem 1′₄ and the counting
of §1 use neither; Lemma 2₄ uses |R_x| ≤ 4, and Lemma 3₄ (§2) both. An
allocation X is EFX₀ if v_i(X_i) ≥ v_i(X_j ∖ {h}) for all i ≠ j and h ∈ X_j. A bundle of one good is never strongly
envied.

## 1. Pre-allocations and their soundness

**Definition.** A *pre-allocation* P assigns to every agent i a *base* B_i ⊆ R_i, the bases pairwise disjoint. Its
*junk* is J = M ∖ ⋃ B_i. The *needs* of i are a set N_i with
{g ∈ R_i ∖ B_i : v_i(g) > v_i(B_i)} ⊆ N_i ⊆ R_i ∖ B_i. LB₄ uses N_i = {g ∈ R_i : g ≻_i Y} when B_i = {Y} is a pick
(the goods ranked above it, as at k = 3), N_i = R_i when B_i = ∅, and the value-based set otherwise.

NA = ⋃ N_i is the *needed-alone set*. P is *valid* if
- **(V1)** J ∩ NA = ∅, and
- **(V2)** B_i ∩ NA = ∅ whenever |B_i| ≥ 2.

In a valid P every good of NA is the whole base of exactly one agent. Such an agent is *frozen* (F). The others are
*free*. A free agent i has cap(i) = 2 − |B_i|, and max(cap(i), 0) *slots*; frozen agents have cap 0. (cap(i) < 0
only for a base of three or more goods, which only the owner may have.)

At k = 3 this is `proofs/lb_last_step.md` §2: picks are one-good bases, and an upgraded agent u has B_u = {b_u, c_u},
whose needs are empty because a_u < b_u + c_u.

**Completions.** Let o be a free agent (the *owner*) or no agent. A completion places every junk good: X_i = B_i ∪ C_i
for i ≠ o, with C_i ⊆ J and |C_i| ≤ cap(i); X_o = B_o ∪ (the rest of J). With no owner, all of J goes to slots; then
every bundle has at most 2 goods, provided every base has at most 2. The owner's needs may be taken from its final
bundle: N_o^X = {g ∈ R_o ∖ X_o : v_o(g) > v_o(X_o)}. This only shrinks N_o (v_o(g) > v_o(X_o) ≥ v_o(B_o) puts g in
the value-based set, which N_o contains), so (V1)–(V2) still hold with N_o replaced by N_o^X, and there may be fewer
frozen agents and more slots. N_o^X is not a set of needs in the Definition's sense (it may omit goods of R_o ∖ B_o
worth more than B_o); this is why the proof below treats i = o separately. Below, NA, F and the slots are computed with
the owner's needs used: N_o, or N_o^X.

The completion satisfies the *owner constraint* (OC₄) if for every agent j ≠ o and every h ∈ X_o,
v_j(X_o ∖ {h}) ≤ v_j(X_j).

**Theorem 1′₄ (soundness, any k).** Let P be valid and X a completion of P with owner o (or none) such that only X_o
may have more than 2 goods, frozen agents hold exactly their base, and (OC₄) holds. The owner's needs may be N_o or
N_o^X (with validity, F and the slots computed accordingly). Then X is EFX₀.

*Proof.* Fix i and j ≠ i with |X_j| ≥ 2. If j = o, (OC₄) is the claim. Otherwise |X_j| = 2 and j is free, so X_j
consists of goods of B_j and of J. Neither meets NA: J by (V1); B_j by (V2) if |B_j| = 2, and if B_j = {Y_j}, because
j is not frozen. For h ∈ X_j, X_j ∖ {h} is one good g, and v_i(g) ≤ v_i(X_i) is needed. If g ∉ R_i, v_i(g) = 0.
Otherwise g ∈ R_i ∖ N_i, and g ∉ B_i (bases are disjoint and g ∈ X_j).
Since N_i contains every good of R_i ∖ B_i worth more than B_i, v_i(g) ≤ v_i(B_i) ≤ v_i(X_i). If i = o with needs
N_o^X, the same argument with X_o in place of B_o gives v_o(g) ≤ v_o(X_o). ∎

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

**Counting (any k).** In a valid P every good of NA is the base of one frozen agent, so |F| = |NA|. With
S = Σ cap(i) and ω = |J| − S, counting goods gives ω = m − 2n + |NA| = |NA| − σ, σ = 2n − m, as in
`proofs/construction.md` Lemma 2, for any bases provided cap(i) = 2 − |B_i| is counted with its sign (a base of b goods
uses b goods and 2 − b slots, negative for b ≥ 3). At k = 4, σ can
be negative. If ω ≤ 0, the completion without an owner has all bundles of at most 2 goods. Otherwise an owner with
|B_o| ≤ 2 gets |B_o| + cap(o) + ω = ω + 2 goods when all the other slots are filled (slots counted before its needs
are replaced). Taking the owner's needs from its bundle lowers |NA|, so it may
free slots: the owner needs fewer goods alone, not the others.

**Lemma 2₄ (self-protection).** Let P be valid and o an owner with |B_o| ≤ 1. Consider the free agents x ≠ o with
|R_x| ≤ 4 whose base is a pick {Y_x} with the needs of a pick, N_x = {g ∈ R_x : g ≻_x Y_x}. Fill their slots one
agent at a time, each taking its ≻-best good of R_x among the junk not yet placed (any good if none is left). Then no
such agent is threatened by X_o, whatever else is placed. (It fails for |R_x| = 5: values 10, 9, 8, 7, 6, x picks the
top and takes the second, and X_o gets the other three, worth 21 > 19.)

*Proof.* Goods of N_x are bases of frozen agents, so X_o ∩ R_x consists of goods ranked below Y_x (the pick of x), and
contains at most one good of B_o. If Y_x is c_x or d_x (or b_x of a 3-good agent), at most one good of R_x lies below
it, and v_x(g) ≤ v_x(Y_x) for it; no threat. If Y_x = b_x of a 4-good agent, the goods below are c_x and d_x. If x took
one of them, X_o ∩ R_x has at most the other one; if x took neither, both were already placed elsewhere or are not
junk, and X_o ∩ R_x ⊆ B_o has at most one good. If Y_x = a_x: when x took b_x or c_x, x holds {a, b} or {a, c}, which
is worth at least the rest of R_x (a + b > c + d and a + c > b + d; for 3 goods a + b > c and a + c > b), so x envies
no bundle. When x took d_x, or nothing of R_x, the goods b_x and c_x were placed before or are not junk, so
X_o ∩ R_x ⊆ B_o has at most one good. Later placements only remove goods from X_o. ∎

So with an owner whose base has one good, the agents with a pick base constrain the owner only through their own
slots: if each such slot takes its agent's ≻-best junk good, only frozen agents and agents with a two-good base remain,
as the exposed agents do at k = 3. But these need goods kept out of X_o, those goods also go into slots of free agents,
and an agent whose slot holds such a good may lose its own protection; the lemma does not settle that conflict. At k = 3 each exposed agent needs one such good. At k = 4 a frozen agent
holding its top needs one good kept out if it is not flat, and two if it is flat with b, c, d all available.

## 2. Construction LB₄

LB₄ searches a small, explicit space of valid pre-allocations built by serial dictatorship, and returns the first
completion that satisfies (OC₄).

**Shape.** Every base LB₄ builds has at most 2 goods (picks, upgraded pairs, and the rotated agent's base O when
|O| ≤ 2), except O when |O| ≥ 3, and then the rotated agent is the owner (see Rotation). Frozen agents get no slot, and
every other agent at most 2 − |base| slot goods. So every bundle other than the owner's has at most 2 goods, and by
Theorem 1′₄ every allocation LB₄ returns is EFX₀ with at most one bundle of more than 2 goods.

**Implementation.** The text fixes which configurations are tried, hence whether LB₄ succeeds. `k4/lb4.c` with options
`-i2 -u1 -r1 -w1 -c1` implements it (except for the rotated agent, see Rotation), with these orders where the text leaves a choice: the sets C (and O) of one size
in decreasing order of their bit masks over the goods; chain successors in index order; protecting goods matched to
agents by augmenting paths, goods in index order; the other slot goods to agents in index order. These fix the
allocation returned (and the "largest bundle" column of §4).

**Phase 1(τ): serial dictatorship with priority to agents that lost a good.** G = M. While an agent is unprocessed:
- *P-step:* if some unprocessed agent has lost a good (R_i ⊄ G), the next agent is the one with the smallest key
  (rank of its favourite good of R_i ∩ G, or d_i if none; |R_i ∩ G|; index), LB's key;
- *insertion step:* otherwise every unprocessed agent has all its goods, and the next agent is the τ_j-th unprocessed
  agent in index order, at the j-th insertion step.

The agent takes its ≻-favourite good of R_i ∩ G as its pick Y_i (none if R_i ∩ G = ∅). Invariants (I1), (I2), (I3),
(B1), (B2) of `proofs/lb_last_step.md` §1 hold verbatim: their proofs never use |R_i| = 3, only that an agent processed
in a P-step has lost a good. (At k = 3 "lost a good" is exactly the R1 step "at most two goods left".) The bases are
B_i = {Y_i} (∅ if none), the junk is J₀ = G.

**Upgrades.** Repeat: take the smallest-index agent k with B_k = {Y_k}, Y_k ∉ NA and N_k ≠ ∅ that has a junk good
g ∈ R_k ∩ J with N′ = {x ∈ N_k : v_k(x) > v_k(Y_k) + v_k(g)} ≠ N_k, take the ≻_k-best such g, and set
B_k = {Y_k, g}, N_k = N′. Validity is kept: NA only shrinks, Y_k ∉ NA, and g is junk. At k = 3 this is "b_k takes c_k"
(N′ = ∅ because a < b + c). At k = 4 the pair need not be envy-free, and N′ may stay nonempty (for example Y_k = c_k
and g = d_k with b < c + d < a: the base {c_k, d_k} has N′ = {a_k}).

**Owner step.** Compute F, the slots and ω. If ω ≤ 0, return the completion without owner. Otherwise try the owners
in the order: r, the last-processed agent that is not upgraded (its base has at most one good), if it is free; then
every other free agent with a slot or a two-good base, latest-processed first. For an owner o, try every C ⊆ J of size
min(|J|, S − cap(o)), then every larger one: X_o = B_o ∪ (J ∖ C), the owner's needs N_o^X, and with them F and the
slots. C must fit into the slots of
the free agents other than o; every agent without a slot must be unthreatened by X_o; every agent with one slot that
X_o threatens when it holds its base alone must receive a good of C that protects it (a system of distinct
representatives, by augmenting paths). The rest of C fills the remaining slots. For a given C this test is exact, and
Lemma 3₄ below shows that trying only these sizes of C loses nothing, except for one kind of owner.

**Lemma 3₄ (the owner search is exact).** Let s₀ be the number of slots of the agents other than o counted with the
owner's needs N_o (before the replacement by N_o^X; in `lb4.c`, S − cap(o), where a rotated agent has no slot). Let o
be a strictly balanced agent with |R_o| ≤ 4 and either |B_o| + cap(o) = 2 and ω ≥ 1 (every owner of the owner step, and
every owner after a rotation other than the rotated agent with |O| = 1), or o the rotated agent with |O| ≥ 3. If some
completion with owner o satisfies (OC₄) with the owner's needs N_o^X, then one does whose slot goods C have
|C| ≥ min(|J|, s₀), so the owner step finds one.

*Proof.* Take such a completion with |C| < min(|J|, s₀). The agents free under N_o are free under N_o^X with at least as
many slots, so one of them, x ≠ o, has an unused slot; and J ∖ C ⊆ X_o is not empty. Moving a good of X_o into x's slot
shrinks X_o and enlarges X_x, so (OC₄) still holds (max over h of v_j(L ∖ {h}) only drops when L shrinks); it remains to
keep N_o^X, hence F and the slots, unchanged.
- If some g ∈ J ∖ C is not in R_o, move it: v_o(X_o) does not change.
- Otherwise X_o ⊆ R_o. Counting goods, |X_o| = |B_o| + |J| − |C|. In the first case |J| = s₀ + cap(o) + ω > s₀, so
  |X_o| > |B_o| + cap(o) + ω = 2 + ω ≥ 3. In the second case the rotated agent has no slot, so |J| − s₀ = ω: if
  |J| > s₀, then |X_o| > |O| + ω ≥ 4, impossible inside R_o; if |J| ≤ s₀, then |X_o| ≥ |O| + 1 ≥ 4. Either way
  X_o = R_o has 4 goods, more than |B_o|. Move the least good ℓ of X_o ∖ B_o. The rest, R_o ∖ {ℓ}, contains o's top, and is worth more than ℓ: by strict
  balance if ℓ is the top, and otherwise because it contains the top and two more goods. So N_o^X stays empty.

Repeat until |C| ≥ min(|J|, s₀). ∎

For a rotated owner with |O| = 1 the count gives only |X_o| ≥ 3, and moving a good can then put o's missing good into
N_o^X; for such owners the search is sufficient, not shown exact.

**Rotation.** If the owner step fails, try every frozen agent k (latest-processed first), every need chain
k = x₀, x₁, …, x_t (x₁, …, x_{t−1} frozen, Y_{x_{i−1}} ∈ N_{x_i}, and x_t free with a base of at most one good, or
with a two-good base: an upgraded agent that still needs Y_{x_{t−1}}), and every nonempty O ⊆ R_k ∩ (J ∪ B_{x_t})
(pairs first, then triples, single goods, quadruples):
- every x_i (i ≥ 1) takes Y_{x_{i−1}} as its base (with the needs of a pick), and B_{x_t} goes back to the junk;
- k takes the base O, with value-based needs.

If the result is valid (checked), run the owner step on it: with owner k when |O| ≥ 3; otherwise without an owner if
ω ≤ 0, else with owner k and then the other free agents in index order. `lb4.c` marks the rotated agent as upgraded:
(V2) is required of O even when |O| = 1, so it is never frozen, and it has no slot when ω and s₀ are computed; the owner
test with the owner's needs from its bundle recomputes the slots of the other agents and then gives a one-good O one
slot. The text's rule (cap(k) = 2 − |O|, (V2) only for |O| ≥ 2) would try more configurations; the evidence of §4 is
for the code's rule, a subset up to Lemma 3₄ (for |O| = 1 the code also tries one smaller size of C for the other
owners). At k = 3 LB⁺'s rotation is the case k = k*, x_t = r,
O = {b_k, c_k}.

**Search.** Try the insertion sequences τ in lexicographic order; for each, Phase 1, upgrades, owner step, rotation.
Return the first allocation found. LB₄ *fails* if no τ gives one.

**LB₄ᴸ: searching only the last block's leader.** For an insertion sequence τ, let LB₄ᴸ(τ) run LB₄'s steps on τ,
and if that fails, on τ with the leader of its *last* block replaced by each other agent of that block in turn (index
order; later insertion steps, if the new block does not absorb every remaining agent, take the first agent). This is
at most n runs of Phase 1. `-i8` is LB₄ᴸ(index order), with at most n runs of Phase 1; `-i9` tests LB₄ᴸ(τ) for every τ.
Both fail at n = 4 (§3): LB₄ᴸ(τ) for some τ when three agents have 4 goods, and LB₄ᴸ(index order) on 4 pure cores.
So LB₄ keeps the search over all insertion sequences.

## 3. Why each ingredient is there (rejected variants)

Each smaller variant fails, and each failure is confirmed: a brute force over all n^m allocations with explicit
integer values (`k4/lb4_brute.py`) finds EFX₀ allocations with at most one large bundle at the failing profile, so it is
the construction that fails, not K4.D. One file each in `attempts/`, reproduced by `python attempts/lb4_variants.py`.

| variant | smallest failure | file |
|---|---|---|
| LB⁺'s shape: index insertion, need-shrinking upgrades, owner r, else one rotation (any chain, any subset) | n = 2, m = 5 | `attempts/lb4-lbplus-shape.md` |
| the same with envy-free upgrades only (SCOUT §5's rule) | n = 3, m = 6 | `attempts/lb4-lbplus-shape.md` |
| no rotation (everything else searched, including every insertion sequence) | n = 3, m = 5 | `attempts/lb4-no-rotation.md` |
| a fixed insertion rule (index, block lookahead, least ω, "a > b + c first", r leads the last block), otherwise LB₄ with one rotation | n = 2, m = 5 | `attempts/lb4-fixed-insertion.md` |
| index insertion, one rotation, every upgrade policy | n = 3, m = 6 | `attempts/lb4-fixed-insertion.md` |
| the owner's needs from its base, as at k = 3 (everything else searched) | n = 4, m = 8 (pure) | `attempts/lb4-owner-needs-from-base.md` |
| only the last block's leader searched, for every run of Phase 1 (LB₄ᴸ(τ) for all τ) | n = 4, m = 8, three 4-good agents (smallest found: pure n = 4 not run) | `attempts/lb4-last-block-leader.md` |
| only the last block's leader searched, for the index run (LB₄ᴸ(index), at most n runs of Phase 1) | pure n = 4, m = 8 | `attempts/lb4-last-block-leader.md` |

What each failure shows:
1. *Upgrades can hurt* (n = 2): the k = 4 pair {b, c} is not always envy-free, so an upgraded agent can be threatened
   by a + d in the large bundle, and an upgrade that removes a need can leave no valid owner.
2. *The rotation is needed* (n = 3): a flat agent must end with its two private goods, which serial dictatorship with
   priority to agents that lost a good never gives it (it always picks a shared good); a rotation does. (Plain serial
   dictatorship can: order 1, 2, 0 in that core gives agent 0 its private good 1, and junk completes the D2 solution
   {0, 1, 2} | {4} | {3}, the shape of K4.SDJ; the priority rule puts agent 0 before agent 2.) With LB₄'s single upgrade policy, chains must be allowed
   to end at an upgraded agent that still needs a good: without that (`-i2 -u1 -r1 -w1 -c0`), 2 pure n = 4, m = 8 cores
   fail (9,280 profiles); trying the other upgrade policies as well (`-i2 -u3 -r1 -w1 -c0`) also repairs them (pure
   n = 4, m = 8 and 9; `results/k4_lb4_variants.log`).
3. *With one rotation, the insertion order matters* (n = 3): unlike LB⁺ (Theorem C holds for every insertion order),
   some profiles need an agent to end below the good it picked, and one rotation moves every agent of its chain up.
   Every fixed rule tested fails with one rotation. Two rotations in a row can do it: with up to three nested
   rotations and every upgrade policy, index insertion fails nowhere on any core with n ≤ 4 (`-i0 -u3 -r3 -w1 -c1`,
   `results/k4_lb4_nested_n4.log`, `results/k4_lb4_nested_pure4.log`), though with LB₄'s single upgrade policy it still
   fails at n ≤ 3 (`-i0 -u1 -r3 -w1 -c1`, 15 cores). See §5 for this lead.
4. *The owner's large bundle can remove its own needs* (n = 4): with {b, c, d} worth more than a, the owner no longer
   needs its top alone, which frees the agent holding that top.
5. *Earlier blocks matter* (n = 4): choosing only the leader of the last block, the analogue of Theorem A's focus on
   the last block, fails for some run of Phase 1 (smallest found: n = 4, m = 8, three 4-good agents, the run
   τ = (1, 0); `results/k4_lb4_i9_run.log`), and for the index run on 4 pure cores (119,200 profiles,
   `results/k4_lb4_i8.log`). In both smallest cases the run's last block
   is one agent, and the first block's leader must change. LB₄ᴸ(index order) (at most n runs of Phase 1) holds for n ≤ 3 (with
   ties), n = 4 with at most three 4-good agents, and n = 5 with at most two.

## 4. Exhaustive tests

**Method.** `k4/lb4.c` runs LB₄ on every profile of a core without listing the profiles one by one. Per agent, the
types of the same tie-broken ranking form a set (12 strict types per ranking of 4 goods, 1 of 3 goods; up to 72 with
ties), and a set is split only when LB₄ asks a comparison v_i(S) vs v_i(T) on which its types disagree. A leaf is a
product of type sets on which LB₄ runs identically. Each leaf's allocation is checked against the raw EFX₀ definition
for every type in every agent's set, with the types' integer representatives (`k4/check4.py`'s enumeration of the
strict balanced types, or all balanced weak types with `--ties`; for an agent with two private goods p, q only the
types with p + q < s + t), and for the shape (at most one bundle of more than 2 goods). The driver asserts that the
leaves' sizes add up to the number of profiles of every core. Cores are those of the certificate files of K4.R3–R5
(`results/k4_certs_*.json.gz`, complete by `check4.py`'s orbit count).

**Validation of the tester** (`k4/test_lb4.py`, `results/k4_lb4_test.log`): with the owner constraint ignored (`-s`),
the raw check reports failures at n = 2 and 3; the lazy branching and brute force (every profile its own leaf, `-b`)
give the same failure counts on every core with n ≤ 3, for a variant that fails and for LB₄; and the rejected variants
of §3 reproduce. For n ≤ 3 (strict and ties) and n = 4 with at most three 4-good agents, LB₄'s leaf allocations are
written as certificates (`results/k4_lb4_certs_*.json.gz`, 50 to 185,108 allocations per file) and accepted by the
independent `k4/check4.py`: coverage of every profile, raw EFX₀, core lists complete, D2
(`results/k4_lb4_check.log`). What `check4.py` confirms independently is that LB₄'s outputs are EFX₀ with the D2
shape and together cover every profile. That LB₄ produced an output for every profile (never failed) is `lb4.c`'s own
count, for every class: the leaves' sizes add up to all profiles and no leaf failed. A profile where LB₄ failed could
still be covered by another output. For pure n = 4 and n = 5 no certificate is stored (they would be about 1 MB for
pure n = 4 and for n = 5 with one 4-good agent, and about 10 MB for n = 5 with two, as measured in the coordinator's
review); for these classes every claim rests on `lb4.c` alone (single implementation).

**Results (EVIDENCE for K4.LB4).** `-i2 -u1 -r1 -w1 -c1`; logs `results/k4_lb4_run_2_3_4mixed.log`,
`results/k4_lb4_run_4pure_5.log`. Columns "no large bundle" to "rotation": how LB₄ ended, counted in profiles (the
first success in the search order); they add up to the profiles. "A later insertion sequence" counts the profiles where
the first sequence failed, and overlaps them.

| cores | number | profiles | LB₄ fails | raw-check failures | no large bundle | owner r | other owner | rotation | a later insertion sequence | largest bundle |
|---|---|---|---|---|---|---|---|---|---|---|
| n = 2 | 5 | 189,216 | 0 | 0 | 81,216 | 94,860 | 9,900 | 3,240 | 300 | 4 |
| n = 3 | 51 | 299,837,376 | 0 | 0 | 164,554,896 | 115,740,504 | 9,356,572 | 10,185,404 | 160,060 | 6 |
| n = 2, ties | 5 | 3,590,173 | 0 | 0 | 1,592,563 | 1,788,838 | 174,424 | 34,348 | 2,720 | 4 |
| n = 3, ties | 51 | 24,690,461,987 | 0 | 0 | 14,298,849,204 | 9,295,905,004 | 634,159,617 | 461,548,162 | 6,855,672 | 6 |
| n = 4, one 4-good agent | 135 | 7,247,232 | 0 | 0 | 6,684,788 | 408,122 | 34,626 | 119,696 | 0 | 5 |
| n = 4, two | 309 | 724,847,616 | 0 | 0 | 605,246,694 | 95,800,864 | 8,447,556 | 15,352,502 | 14,464 | 6 |
| n = 4, three | 339 | 34,971,844,608 | 0 | 0 | 24,936,692,912 | 8,531,257,150 | 673,979,838 | 829,914,708 | 1,231,288 | 7 |
| n = 4, pure | 219 | 1,022,496,473,088 | 0 | 0 | 597,697,715,888 | 369,380,197,424 | 27,251,673,892 | 28,166,885,884 | 58,127,420 | 8 |
| n = 5, one | 1735 | 574,615,296 | 0 | 0 | 547,530,330 | 22,252,578 | 1,396,116 | 3,436,272 | 4 | 6 |
| n = 5, two | 5468 | 80,025,864,192 | 0 | 0 | 72,445,142,204 | 6,412,114,474 | 492,511,856 | 676,095,658 | 97,796 | 7 |

LB₄ never fails: 1,139,100,918,624 strict profiles of the 8,261 cores (every core with n ≤ 4, and n = 5 with at most
two 4-good agents), and all 24,694,052,160 tied profiles with n ≤ 3. The hard cases are rare: a later insertion sequence is needed
for 0.006% of the pure n = 4 profiles (and for none with n = 4 and one 4-good agent), a rotation for 2.8%, an owner other than r
for 2.7%.

## 5. Toward a proof: what carries over from LB⁺, and the gap

**Carries over (proved above or verbatim).** The Phase 1 invariants (I1)–(I3), (B1), (B2); validity after the
upgrades; soundness of every completion in which only the owner's bundle has more than 2 goods and (OC₄) holds
(Theorem 1′₄, any k); the counting ω = |NA| − σ; the owner test: Lemma 1 of `proofs/lb_last_step.md` (a hitting-set
criterion) is replaced by an exhaustive search in which a protecting good must go into the threatened agent's own slot
(§2, exact by Lemma 3₄ except for a rotated owner with a one-good base); self-protection of free agents with a pick
base (Lemma 2₄, |R_x| ≤ 4), the k = 4 counterpart of "a terminal holding its top is its own τ(x)", valid when those
agents' slots take their best junk goods.

**Does not carry over.** Theorem A (the owner r) and Theorem B (the rotation) of `proofs/lb_last_step.md`. Their
counting pairs every exposed agent with a terminal of its own block, and needs one good per exposed agent. At k = 4:
1. *(A1)'s proof fails:* an upgraded agent may keep a need (N′ ≠ ∅), and if it was processed after r, r may be frozen.
   At k = 3 upgraded agents need nothing. (LB₄ tries r only when r is free.)
2. *(A3)'s proof fails:* an agent holding its top is threatened by a *type-dependent* set of lower goods, and when that
   set misses one of its goods, the agent may have lost that good before its turn. So the argument that exposed agents
   are block leaders, one per block, no longer applies. (Not checked whether this happens in LB₄'s runs.)
3. *One good per exposed agent fails:* a flat frozen agent (a < c + d) with b, c, d all free needs two goods kept out of
   the large bundle, and an agent holding b_x is exposed when c + d > b. Agents with a two-good base can be exposed.
4. *Any insertion order fails with one rotation* (`attempts/lb4-fixed-insertion.md`): Theorem C's "for every run of
   Phase 1" is false at k = 4 with one rotation, and so are its weakenings "for every run, up to the choice of the last
   block's leader" and "for the index run, up to that choice" (`attempts/lb4-last-block-leader.md`). Both last-block
   restrictions fail, which is evidence that, with one rotation, a proof must choose more of the insertion sequence
   than the last block's leader, or use a move that lets an agent go below its pick (two rotations in a row can).

**A lead: nested rotations with any insertion order.** With every upgrade policy and up to three rotations in a row
(LB₄ʳ below), a fixed insertion order suffices on the data. Index insertion never fails on any certified core (n ≤ 4,
and n = 5 with at most two 4-good agents; 1.14·10¹² profiles; `results/k4_lb4_variants.log` for n ≤ 3,
`results/k4_lb4_nested_n4.log`, `results/k4_lb4_nested_pure4.log`, `results/k4_lb4_nested_n5.log`). On n ≤ 3 and on
n = 4 no run of Phase 1 fails, whatever its insertion order (2.1·10¹¹ run–profile pairs for n ≤ 3 and mixed n = 4,
`results/k4_lb4_nested_every.log`; 5.89·10¹² for pure n = 4, `results/k4_lb4r_i1_pure4.log`); n = 5 and beyond: the
stress tests below. That is the shape of LB⁺'s
Theorem C (every run of Phase 1 works, after upgrades and rotations), with up to three rotations instead of one; it may
be a better proof target than LB₄'s search over insertion sequences. (It is refuted at n = 21 by PR #33 (`k4/c4.md`
§7, Proposition H, confirmed by an independent second encoding; not yet on main): the cores H_t need unboundedly many
rotations at index order; see "Simpler candidates" below.)

**LB₄ʳ(τ), precisely** (`k4/lb4.c -u3 -r3 -w1 -c1`, with `-i0` for τ = index order and `-i1` for every τ). Run
Phase 1 with the insertion sequence τ. Then try the three upgrade policies in turn, each from the Phase 1 state:
need-shrinking upgrades (LB₄'s rule), envy-free upgrades only (the same scan, but a pair {Y_k, g} is taken only if
v_k(Y_k) + v_k(g) ≥ v_k(R_k ∖ {Y_k, g})), and no upgrades. For each, run LB₄'s owner step, and if it fails the rotation
search R(1), where R(d) is:
- try every frozen agent k of the current state (latest-processed first), every need chain k = x₀, x₁, …, x_t of
  distinct agents with x₁, …, x_{t−1} frozen, Y_{x_{i−1}} ∈ N_{x_i}, and x_t not frozen, and every nonempty
  O ⊆ R_k ∩ (J ∪ B_{x_t}) (pairs, triples, single goods, quadruples). The chain end x_t may have a base of at most one
  good, be upgraded, or be an agent rotated earlier (marked upgraded, with the value-based needs of its base O′); an
  upgraded or rotated end releases its whole base to the junk and takes Y_{x_{t−1}} as a pick. Rotated agents are
  never frozen, so they are never a chain's start or middle;
- apply the rotation as in LB₄ (§2): k is marked upgraded with base O, even when |O| = 1;
- the result must satisfy (V1), and (V2) for every agent marked upgraded, and at most one base may have three or more
  goods; otherwise it is discarded;
- if one base has three or more goods, its agent is the owner and only it is tried; otherwise the owner step runs as
  after LB₄'s rotation (without an owner if ω ≤ 0, else owner k, then the other free agents in index order);
- if that fails and d < 3, run R(d + 1) from this state.

The first allocation found is returned; LB₄ʳ(τ) fails if no policy gives one. Every base of three or more goods is the
owner's, so by Theorem 1′₄ every output is EFX₀ with at most one bundle of more than two goods; `lb4.c` also checks
each against the raw definition. The rotation depth is reset for every profile.

With `-d1` the rotation bound is deepened for each policy (0, 1, 2, 3 in turn), and with `-d2` it is outermost (every
policy at bound 0, then every policy at bound 1, …). Both succeed exactly when LB₄ʳ does, since each bound's search
contains the previous one's; they change only the allocation returned and what the histograms count: `-d1` gives the
policy LB₄ʳ ends with and the fewest rotations under it, `-d2` the fewest rotations over all policies.

**LB₄ʳ under stress (EVIDENCE; one implementation).** No run of LB₄ʳ failed, and no output failed the raw EFX₀ check,
in any test below. The n = 5 core lists with three or more 4-good agents are those of PR #26 (`compute/k4-frontier` at
2809bb4, not yet on main); the random cores are drawn by `k4/lb4_randcores.py` and committed as
`results/k4_lb4r_cores_*.json.gz`.
- *Exhaustive.* Every insertion order on every core with n ≤ 4 (above); every order on the two n = 5 cores below on
  which need-shrinking needs a third rotation (8.41·10¹¹ run–profile pairs, `results/k4_lb4r_deep.log`). Index order
  on every certified core (above), and on n = 5 with three 4-good agents, all 9,861 cores
  (6.4·10¹² profiles, no failure; `results/k4_lb4r_ex_5_n4_3.log`).
- *Random profiles* (seeded from each core; `results/k4_lb4r_samples.log`, `results/k4_lb4r_random.log`). n = 5 with
  three to five 4-good agents (24,381 cores; with at most two, exhaustive above): index order 6.3·10⁸ profiles, every
  order 8.0·10⁷ profiles (8.0·10⁸ runs). n = 6 with one 4-good agent (26,866 cores of PR #26): index order
  1.3·10⁸. Random cores, index order and every order: n = 6, 4,200 cores (8.4·10⁷ profiles; 3.4·10⁶ profiles,
  7.7·10⁷ runs); n = 7, 1,500 cores (1.5·10⁷; 3·10⁵ profiles, 1.6·10⁷ runs); n = 8, 300 cores (3·10⁶, index only).
- *Adversarial* (`results/k4_lb4r_weak.log`, `results/k4_lb4r_adversarial.log`). First the cores where a weaker
  variant fails: need-shrinking upgrades only (`attempts/lb4r-need-shrinking-only.md`) fail on 149 cores with n ≤ 4
  at index order, 262 for every order, and 376 of the n = 5 cores (5,000 random profiles each); one rotation fails on
  91 and 21. On those cores (276 with n ≤ 4, 396 with n = 5), on 5,000 cores grown from them by one or two random agents
  (n = 4 to 7), and on the random n = 6 and n = 7 cores, hill-climbing (`-H`: change one agent's type, undo the change
  if the profile got easier, restart every 500 steps) toward three kinds of hardness: the policy LB₄ʳ ends with, then
  its rotations, then its rotation attempts; the number of policies that fail on their own (`-P1`); the fewest
  rotations over all policies (`-P2 -d2`). In all, 1.8·10⁸ profiles (3.1·10⁸ runs), 0 failures. The climbs never
  found a profile on which two policies fail on their own, nor one needing a third rotation with the policy free.
- *What LB₄ʳ uses* (`-d1` and `-d2`; histograms in `results/k4_lb4r_hist.log` and in the logs of runs made with `-d1`
  or `-d2`; the three largest runs, `results/k4_lb4r_i1_pure4.log`, `results/k4_lb4r_ex_5_n4_3.log` and
  `results/k4_lb4r_samples.log`, predate the histograms).
  "No upgrades" is never the policy LB₄ʳ ends with: wherever need-shrinking fails, envy-free upgrades succeed (at n = 3,
  index order, 147,240 of 3·10⁸ profiles need them; `results/k4_lb4r_weak.log`). With every policy allowed, no run
  with a rotation histogram (`-d2`) needs a third rotation;
  two are needed rarely (at n = 3, every order, 25,240 of 1.0·10⁹ run–profile pairs). Under need-shrinking alone, 2 runs
  of the n = 5 sample (four 4-good agents, m = 9; `results/k4_lb4r_deep.log`) need three rotations, and envy-free
  upgrades then need one; on those two cores LB₄ʳ with at most two rotations never fails, for every order and profile.
  Every order on n ≤ 4 with at most three 4-good agents (2.09·10¹¹ run–profile pairs): LB₄ʳ ends with need-shrinking
  upgrades except in 4,841,440 pairs (envy-free upgrades), and under that policy needs 0, 1, 2, 3 rotations in
  98.99 %, 1.01 %, 690,140 and 5,760 pairs; with the policy free (`-d2`), 2 rotations in 101,272 pairs and 3 in none.
  Index order (`-d2`) on every certified core with n ≤ 4 and at most three 4-good agents or n = 5 and at most two
  (1.17·10¹¹ profiles): 2 rotations in 44,404, 3 in none; pure n = 4
  (1.02·10¹² profiles): 2 rotations in 1,497,520, 3 in none.
- *Simpler candidates.* LB₄ʳ with at most two rotations (`-r2`) fails nowhere tested: every order on n ≤ 4 with at most
  three 4-good agents (exhaustive) and on the n = 5 sample (3,000 profiles per core, three to five 4-good agents,
  every order). Even one policy
  suffices on every test run so far, if it is not need-shrinking: envy-free upgrades only with at most two rotations
  (`-u2 -r2`) fail on no profile, for every order on n ≤ 4 with at most three 4-good agents (exhaustive,
  2.1·10¹¹ run–profile pairs), on pure n = 4 (every order, 20,000 random profiles per core), on n = 5 (index order
  1.6·10⁸ profiles, every order 7.3·10⁶), on the random n = 6, 7 cores (index order 2.3·10⁷) and under hill-climbing
  on the hard n = 5 cores and the grown cores (`results/k4_lb4r_simple.log`). No upgrades at all (`-u0`)
  also fails on none of these kinds of test: index order on n ≤ 4 with at most three 4-good agents (exhaustive,
  3.6·10¹⁰ profiles), every order on n ≤ 3 (exhaustive) and on pure n = 4 (sampled), n = 5 (index 9.5·10⁷ profiles,
  every order 7.3·10⁶), random n = 6, 7 cores (every order 1.35·10⁶), hill-climbing; it never needs a third rotation.
  So on the cores tested (n ≤ 7; n = 8 was not run with `-u2` or `-u0`) every run of Phase 1 works with one policy
  (envy-free upgrades, or none) and at most two rotations; need-shrinking upgrades are the one policy that cannot
  stand alone. This does not extend to all n: H_4 (n = 17) needs three rotations under every policy at index order
  (the review of PR #32, `-d2` in `k4/c4_lb4w.c`, `-w0`), so `-r2`, `-u2 -r2` and `-u0 -r2` all fail there; and
  on the cores H_t of `k4/c4.md` §7 (n = 4t + 1; Proposition H, PR #33, confirmed by an independent second encoding) LB₄ʳ with index insertion
  needs ⌈2t/3⌉ nested rotations, so it fails on H_5 (n = 21) with three, and no fixed bound works for every run of
  Phase 1. The tests here reach n ≤ 8, where only H_1 (n = 5) fits, and it needs one rotation.
- *Some insertion order (∃τ), the question H_t leaves.* On H_t, random insertion sequences (a uniformly random
  candidate at each insertion step; `k4/lb4r_tau.c`, which is `k4/c4_lb4w.c` of proof/k4-c4, lb4.c with 64-bit masks,
  plus this sampling; `results/k4_lb4r_tau_H.log`) mostly need no rotation, and none failed with at most three: with no,
  one, two rotations (fewest, every policy allowed) 784, 216, 0 of 1,000 sequences for t = 1; 807, 92, 101 of 1,000 for
  t = 2; 414, 31, 55 of 500 for t = 3; with no, one, two, three: 174, 8, 2, 16 of 200 for t = 4 (n = 17);
  t = 5 (n = 21): all 10 sequences sampled in 30 minutes need none; t = 6 (n = 25): all 8 sampled in 30 minutes need none
  (every t with the owner's needs from its base, `-w0`, as `k4/c4.md` §7 does from t = 4, where the search with
  needs from the bundle is out of reach; a `-w0` completion is also a `-w1` completion, `k4/c4.md` §7, so these
  counts are upper bounds on the rotations LB₄ʳ, which uses `-w1`, needs). On small cores, hill-climbing with `-P3` (score: the fewest
  rotations over all insertion sequences, then the share of sequences that need one) on the hard n ≤ 5 cores, the n = 5
  classes with four or five 4-good agents, grown and random cores up to n = 7 (6.3·10⁶ profiles, 6.3·10⁷ runs;
  `results/k4_lb4r_tau_climb.log`) found profiles on which every sequence needs a rotation (already at n = 3, m = 5, as
  `attempts/lb4-no-rotation.md` implies), but none on which every sequence needs two, and none on which no sequence
  succeeds with three.
- *The profiles of PR #30* (`k4/gm4.md`; `k4/lb4r_profiles.py`, `results/k4_lb4r_gm4.log`), where two exposed agents
  need the same pool good kept out of the large bundle: the eleven named instances A–H, P, Q, S, the 148 profiles whose
  level-sum maxima are all dead ends, and the two-agent neighbourhoods of the seven GM₄ seeds (2,260,332 runs over the
  2,247,609 distinct profiles of `k4/gm4.md`) and of the 148 (17,003,520 runs). LB₄ʳ fails on none, with index order or
  every order (every order: 9.0·10⁷ run–profile pairs; index order: 1.9·10⁷ profiles). They are strict profiles of n = 4 cores, which the exhaustive every-order run
  above covers as well.
- *The hardest profiles found* (the logs give each with its run's insertion order, picks, upgrades and frozen agents):
  (values listed in the order of each agent's goods, which are sorted)
  - fewest rotations over all policies 2, with 128 rotation attempts in all: n = 5, m = 9, agents {0, 2, 7, 8},
    {1, 3, 4, 6}, {3, 4, 6, 8}, {5, 6, 7, 8}, {5, 7, 8}, values (2, 7, 8, 4), (5, 6, 3, 7), (5, 4, 8, 6), (2, 8, 4, 7), (2, 3, 4),
    insertion order 1, 2, 0, 4, 3 (`-P2 -d2`);
  - need-shrinking fails, envy-free upgrades need one rotation, 394 rotation attempts in all: n = 5, m = 10, agents
    {0, 2, 5, 9}, {1, 4, 5, 6}, {3, 4, 7, 8}, {3, 7, 8, 9}, {6, 7, 8, 9}, values (4, 3, 8, 10), (4, 2, 7, 10), (4, 2, 7, 8),
    (3, 6, 10, 8), (3, 5, 6, 7), order 0, 3, 2, 4, 1;
  - need-shrinking needs three rotations (envy-free upgrades one): n = 5, m = 9, agents {0, 1, 2, 3}, {0, 2, 3, 8},
    {1, 6, 8}, {4, 5, 6, 7}, {4, 5, 7, 8}, values (6, 10, 3, 8), (4, 6, 8, 1), (3, 2, 4), (4, 5, 8, 2), (6, 3, 5, 7),
    order 4, 1, 0, 2, 3;
  - at n = 6 (`-P2 -d2`), two rotations with the policy free: m = 15, agents {1, 11, 12, 13}, {0, 4, 9, 14},
    {1, 2, 7, 13}, {5, 8, 9, 10}, {4, 5, 6, 13}, {1, 3, 9, 13}, values (10, 4, 8, 3), (4, 5, 8, 6), (6, 4, 1, 8),
    (10, 7, 2, 4), (3, 10, 6, 8), (4, 2, 10, 7), order 1, 3, 4, 0, 2, 5.

**The gap, precisely.** By Theorem 1′₄, K4.D follows from
- **Conjecture K4.LB4.** For every k = 4 core and every strict profile, LB₄ does not fail: some insertion sequence
  gives a Phase 1 run whose upgraded pre-allocation, or one rotation of it, has a completion satisfying (OC₄).

By K4.TIE it suffices for strict profiles; LB₄ is tested with ties too. A proof along LB⁺'s lines needs a Theorem A₄
that counts the goods the frozen and two-good-base agents need kept out of X_o against the slots (Lemma 2₄ covers the
pick-base agents only when their slots take their best junk goods, which competes with those counted goods), a
Theorem B₄ for the general rotation, and a rule, or an exchange argument, for the
insertion sequence. §4's counters say how rare each hard case is: they are the cases a proof must handle.

**Not done.** The analogue of conjecture S2.K (what the large bundle contains) was not tested: LB₄ returns the first
completion found, not a canonical one. Tests beyond the certified cores (n = 5 with three or more 4-good agents, pure
n = 5) were not run for LB₄; LB₄ʳ's are above.

## 6. Reproduce

```
python3 k4/lb4_run.py results/k4_certs_3.json.gz -i2 -u1 -r1 -w1 -c1     # LB4 on every strict profile, n = 3: seconds
python3 k4/lb4_run.py results/k4_certs_3_ties.json.gz --ties -i2 -u1 -r1 -w1 -c1   # ties: ~1 min
python3 k4/lb4_run.py results/k4_certs_4_pure.json.gz -i2 -u1 -r1 -w1 -c1 # pure n = 4: 31 min on 4 CPUs
python3 k4/lb4_run.py FILE ... --cert=OUT.json.gz                        # also write LB4's outputs as a certificate
python3 k4/check4.py results/k4_lb4_certs_3.json.gz --expect 3:any:51    # independent check of those outputs
python3 k4/test_lb4.py                                                   # sensitivity, lazy vs brute force, attempts
python3 attempts/lb4_variants.py                                         # the rejected variants' smallest failures
python3 k4/lb4_brute.py '[[0,2,3,4],[1,2,3,4]]' '[[1,4,6,8],[2,4,5,8]]'  # every EFX0 allocation of one instance
```
`lb4_run.py` compiles `k4/lb4.c` with gcc into the temporary directory, under a name made from a hash of the source
(`LB4_BIN` overrides the path); it takes ties from the certificate file and rejects a mismatched `--ties`. Options of
`lb4.c`: `-i0` index insertion, `-i1` every insertion sequence separately, `-i2` every insertion sequence until one
succeeds (LB₄), `-i3` block lookahead, `-i4` least ω, `-i5` "a > b + c" first, `-i6` index with at most one insertion
step changed, `-i7` index then the last block led by r, `-i8` index then every leader of the last block (LB₄ᴸ), `-i9`
every run of Phase 1 then every leader of its last block; `-u0/-u1/-u2/-u3` no upgrades, need-shrinking, envy-free
only, all three in turn; `-o0` every owner, `-o1` r only, `-o2` r then rotation; `-rN` up to N rotations in a row (a
base of three or more goods is then the owner's, and two such bases are rejected); `-w1` owner needs from its bundle;
`-c1` chains may end at upgraded agents; `-d2` iterative deepening with the rotation bound outermost (bound 0 with every
policy, then bound 1, …: the same successes as `-rN`, and the fewest rotations over all policies); `-d1` iterative
deepening on the rotation bound (0, 1, …, N for each policy:
the same successes as `-rN`, and the least number of rotations); `-s` sensitivity (owner constraint ignored); `-b` brute
force (every profile its own leaf); `-a` print the leaf allocations; `-SN` N random strict profiles per core (seeded from
the core); `-HN` N hill-climbing steps per core (below); `-P1` with `-H`: hardness by how many of the three policies fail on their own (LB₄ʳ must succeed whenever some policy does); `-P2`: by the least number of rotations first; `-P3` with `-i1` (∃τ): by the fewest rotations over all insertion sequences (the least only with `-d2`; failing sequences are counted in `runs` but not in the histograms, which sum to the successful runs); `-TN`: report every run needing at least N rotations (in `k4/lb4r_tau.c`, `-TN` is instead the number of random
insertion sequences sampled). The driver's `--checkpoint=PATH` resumes an interrupted run,
`--badcores=PATH` writes the cores with a failure as a core list it can read back, and every result line ends with the
policy and rotation histograms (`pol_*`, `rot*`: in `-S` and `-H` modes per run, otherwise per run–profile pair).
`k4/lb4_randcores.py` draws random cores (`k4/check4.py`'s `is_core`), or grows the cores of a core list by random
agents (`--extend`, `--add`). `k4/lb4r_profiles.py` runs `lb4.c` on given profiles or on K-agent neighbourhoods of
seed profiles (restricted type domains); `k4/lb4r_tau.c` runs LB₄ʳ on one profile under random insertion sequences
(64-bit masks, from `k4/c4_lb4w.c` of proof/k4-c4). `-rN` allows N ≤ 8 (`MAXROT`).
```
python3 k4/lb4_run.py results/k4_certs_4_pure.json.gz -i1 -u3 -r3 -w1 -c1 --checkpoint=ck.jsonl   # LB4r, every order: ~1.8 h
python3 k4/lb4_run.py results/k4_certs_3.json.gz -i0 -u1 -r3 -w1 -c1 --badcores=hard.json.gz      # cores a weaker variant fails
python3 k4/lb4_run.py hard.json.gz -i1 -u3 -r3 -w1 -c1 -d1 -H2000                                 # hill-climb LB4r there
python3 k4/lb4_randcores.py 6 300 rc6.json.gz --n4=4 --seed=4                                    # random n = 6 cores
```
