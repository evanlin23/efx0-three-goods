# LB₄: construction LB⁺ carried to four goods

Workstream `proof/k4-lb4`, ledger open item 15 (the LB₄ route of `k4/SCOUT.md` §5, steps (a)–(d)). Notation as in
`proofs/construction.md` and `proofs/lb_last_step.md` (k = 3), and `k4/SCOUT.md` (k = 4 cores). Tools:
`k4/lb4.c` (the construction and an exhaustive tester), `k4/lb4_run.py` (driver), `k4/lb4_brute.py` (every EFX₀
allocation of a small instance, by brute force).

**Status.** LB₄ (§2) is defined, implemented, and tested exhaustively: it never fails on any strict profile of any
certified k = 4 core (n ≤ 4, and n = 5 with at most two 4-good agents; 1.14·10¹² profiles), nor on any tied profile
with n ≤ 3 (§4; EVIDENCE, single implementation, outputs re-checked by `k4/check4.py` where stored). Its soundness
(Theorem 1′₄, any k) and the self-protection lemma are written proofs, not yet reviewed. That LB₄ never fails is a
conjecture (K4.LB4): **there is no proof of K4.D here.** LB⁺'s Theorems A and B do not carry over (§5), and five
smaller variants, including LB⁺'s own shape, fail on small cores (§3, `attempts/lb4-*.md`).

## 0. Setting

An *instance* has agents N = [n] and goods M = [m], additive valuations, and relevant sets R_i = {g : v_i(g) > 0}.
Each agent has a fixed strict order ≻_i on R_i that is consistent with its values (v_i(g) > v_i(h) ⇒ g ≻_i h; ties
broken by index). In a k = 4 core |R_i| ∈ {3, 4} and every agent is strictly balanced, but §1 uses neither. An
allocation X is EFX₀ if v_i(X_i) ≥ v_i(X_j ∖ {h}) for all i ≠ j and h ∈ X_j. A bundle of one good is never strongly
envied.

## 1. Pre-allocations and their soundness (any k)

**Definition.** A *pre-allocation* P assigns to every agent i a *base* B_i ⊆ R_i, the bases pairwise disjoint. Its
*junk* is J = M ∖ ⋃ B_i. The *needs* of i are a set N_i with
{g ∈ R_i ∖ B_i : v_i(g) > v_i(B_i)} ⊆ N_i ⊆ R_i ∖ B_i. LB₄ uses N_i = {g ∈ R_i : g ≻_i Y} when B_i = {Y} is a pick
(the goods ranked above it, as at k = 3), N_i = R_i when B_i = ∅, and the value-based set otherwise.

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
N_o^X = {g ∈ R_o ∖ X_o : v_o(g) > v_o(X_o)}. This only shrinks N_o (v_o(g) > v_o(X_o) ≥ v_o(B_o) puts g in
the value-based set, which N_o contains), so the pre-allocation with N_o replaced by N_o^X is still valid, and it may
have fewer frozen agents and more slots. Below, NA, F and the slots are those after this replacement.

The completion satisfies the *owner constraint* (OC₄) if for every agent j ≠ o and every h ∈ X_o,
v_j(X_o ∖ {h}) ≤ v_j(X_j).

**Theorem 1′₄ (soundness).** Let P be valid, and X a completion of P that satisfies (OC₄), in which only the owner's
bundle may have more than 2 goods and frozen agents hold exactly their base. Then X is EFX₀.

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
`proofs/construction.md` Lemma 2, whatever the bases (a base of b goods uses b goods and 2 − b slots). At k = 4, σ can
be negative. If ω ≤ 0, the completion without an owner has all bundles of at most 2 goods. Otherwise an owner with
|B_o| ≤ 2 gets |B_o| + cap(o) + ω = ω + 2 goods when all the other slots are filled (slots counted before its needs
are replaced). Taking the owner's needs from its bundle lowers |NA|, so it may
free slots: the owner needs fewer goods alone, not the others.

**Lemma 2₄ (self-protection).** Let P be valid, o an owner with |B_o| ≤ 1, and fill the slots of the free agents with
one-good bases one agent at a time, each taking its ≻-best good of R_x among the junk not yet placed (any good if none
is left). Then no such agent x is threatened by X_o, whatever else is placed.

*Proof.* Goods of N_x are bases of frozen agents, so X_o ∩ R_x consists of goods ranked below Y_x (the pick of x), and
contains at most one good of B_o. If Y_x is c_x or d_x (or b_x of a 3-good agent), at most one good of R_x lies below
it, and v_x(g) ≤ v_x(Y_x) for it; no threat. If Y_x = b_x of a 4-good agent, the goods below are c_x and d_x. If x took
one of them, X_o ∩ R_x has at most the other one; if x took neither, both were already placed elsewhere or are not
junk, and X_o ∩ R_x ⊆ B_o has at most one good. If Y_x = a_x: when x took b_x or c_x, x holds {a, b} or {a, c}, which
is worth at least the rest of R_x (a + b > c + d and a + c > b + d; for 3 goods a + b > c and a + c > b), so x envies
no bundle. When x took d_x, or nothing of R_x, the goods b_x and c_x were placed before or are not junk, so
X_o ∩ R_x ⊆ B_o has at most one good. Later placements only remove goods from X_o. ∎

So with an owner whose base has one good, only frozen agents and agents with a two-good base constrain the owner, as
the exposed agents do at k = 3; they need goods kept out of X_o, and those goods use up slots of the free agents,
which then may no longer protect themselves. At k = 3 each exposed agent needs one such good. At k = 4 a frozen agent
holding its top needs one good kept out if it is not flat, and two if it is flat with b, c, d all available.

## 2. Construction LB₄

LB₄ searches a small, explicit space of valid pre-allocations built by serial dictatorship, and returns the first
completion that satisfies (OC₄). By Theorem 1′₄ every returned allocation is EFX₀ with at most one bundle of more
than 2 goods. The search order is fixed, so LB₄ is deterministic. `k4/lb4.c` with options `-i2 -u1 -r1 -w1 -c1`
implements it.

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
(N′ = ∅ because a < b + c). At k = 4 the pair need not be envy-free, and N′ may stay nonempty (for example {c, d} with
b < c + d < a).

**Owner step.** Compute F, the slots and ω. If ω ≤ 0, return the completion without owner. Otherwise try the owners
in the order: r, the last-processed agent that is not upgraded (its base has at most one good), if it is free; then
every other free agent with a slot or a two-good base, latest-processed first. For an owner o, try every C ⊆ J of size
min(|J|, S − cap(o)), then every larger one: X_o = B_o ∪ (J ∖ C), the owner's needs N_o^X, and with them F and the
slots. C must fit into the slots of
the free agents other than o; every agent without a slot must be unthreatened by X_o; every agent with one slot that
X_o threatens when it holds its base alone must receive a good of C that protects it (a system of distinct
representatives, by augmenting paths). The rest of C fills the remaining slots in any order. With the owner's needs
taken from its base, this is an exact test: a completion with owner o exists iff one of these C passes (a smaller C
can be extended into free slots, which only shrinks X_o). With the needs taken from its bundle, a smaller C could make
X_o worth more, free agents the owner needs, and add slots; those C are not tried, so the test is sufficient, not
exact.

**Rotation.** If the owner step fails, try every frozen agent k (latest-processed first), every need chain
k = x₀, x₁, …, x_t (x₁, …, x_{t−1} frozen, Y_{x_{i−1}} ∈ N_{x_i}, and x_t free with a base of at most one good, or
with a two-good base: an upgraded agent that still needs Y_{x_{t−1}}), and every nonempty O ⊆ R_k ∩ (J ∪ B_{x_t})
(pairs first, then triples, single goods, quadruples):
- every x_i (i ≥ 1) takes Y_{x_{i−1}} as its base (with the needs of a pick), and B_{x_t} goes back to the junk;
- k takes the base O, with value-based needs.

If the result is valid (checked), run the owner step on it: with owner k when |O| ≥ 3; otherwise without an owner if
ω ≤ 0, else with owner k and then the other free agents in index order. The rotated agent counts as upgraded: no slot
when ω and the size of C are computed, even if |O| = 1 (the owner test with the owner's needs from its bundle recomputes
the slots and gives a one-good base one slot). At k = 3 LB⁺'s rotation is the case k = k*, x_t = r,
O = {b_k, c_k}.

**Search.** Try the insertion sequences τ in lexicographic order; for each, Phase 1, upgrades, owner step, rotation.
Return the first allocation found. LB₄ *fails* if no τ gives one.

**LB₄ᴸ: searching only the last block's leader.** For an insertion sequence τ, let LB₄ᴸ(τ) run LB₄'s steps on τ,
and if that fails, on τ with the leader of its *last* block replaced by each other agent of that block in turn (index
order; later insertion steps, if the new block does not absorb every remaining agent, take the first agent). This is
at most n runs of Phase 1. `-i8` is LB₄ᴸ(index order), a polynomial construction; `-i9` tests LB₄ᴸ(τ) for every τ.
Both fail at n = 4 (§3): LB₄ᴸ(τ) for some τ when three agents have 4 goods, and LB₄ᴸ(index order) on 4 pure cores.
So LB₄ keeps the search over all insertion sequences.

## 3. Why each ingredient is there (rejected variants)

Each smaller variant fails, and each failure is confirmed: a brute force over all n^m allocations with explicit
integer values (`k4/lb4_brute.py`) finds EFX₀ allocations with at most one large bundle at the failing profile, so it is
the construction that fails, not K4.D. One file each in `attempts/`, reproduced by `python attempts/lb4_variants.py`.

| variant | smallest failure | file |
|---|---|---|
| LB⁺'s shape: index insertion, owner r, else one rotation (any chain, any subset) | n = 2, m = 5 | `attempts/lb4-lbplus-shape.md` |
| no rotation (everything else searched, including every insertion sequence) | n = 3, m = 5 | `attempts/lb4-no-rotation.md` |
| a fixed insertion rule (index, block lookahead, least ω, "a > b + c first", r leads the last block) with one rotation | n = 3, m = 6 | `attempts/lb4-fixed-insertion.md` |
| the owner's needs from its base, as at k = 3 (everything else searched) | n = 4, m = 8 (pure) | `attempts/lb4-owner-needs-from-base.md` |
| only the last block's leader searched: for every run of Phase 1 (LB₄ᴸ(τ) for all τ), or for the index run (LB₄ᴸ(index), polynomial) | n = 4, m = 8 (three 4-good agents; pure for the index run) | `attempts/lb4-last-block-leader.md` |

What each failure shows:
1. *Upgrades can hurt* (n = 2): the k = 4 pair {b, c} is not always envy-free, so an upgraded agent can be threatened
   by a + d in the large bundle, and an upgrade that removes a need can leave no valid owner.
2. *The rotation is needed* (n = 3): a flat agent must end with its two private goods, which serial dictatorship never
   gives it (it always picks a shared good); a rotation does. With LB₄'s single upgrade policy, chains must be allowed
   to end at an upgraded agent that still needs a good: without that (`-i2 -u1 -r1 -w1 -c0`), 2 pure n = 4, m = 8 cores
   fail (9,280 profiles); trying the other upgrade policies as well (`-i2 -u3 -r1 -w1 -c0`) also repairs them (pure
   n = 4, m = 8 and 9; `results/k4_lb4_variants.log`).
3. *With one rotation, the insertion order matters* (n = 3): unlike LB⁺ (Theorem C holds for every insertion order),
   some profiles need an agent to end below the good it picked, and one rotation moves every agent of its chain up.
   Every fixed rule tested fails with one rotation. Two rotations in a row can do it: with up to three nested
   rotations and every upgrade policy, index insertion fails nowhere at n ≤ 3, nor on n = 4 with at most three 4-good
   agents (`-i0 -u3 -r3 -w1 -c1`, `results/k4_lb4_nested_n4.log`; pure n = 4 not tested), though with LB₄'s single
   upgrade policy it still fails at n ≤ 3 (`-i0 -u1 -r3 -w1 -c1`, 15 cores).
4. *The owner's large bundle can remove its own needs* (n = 4): with {b, c, d} worth more than a, the owner no longer
   needs its top alone, which frees the agent holding that top.
5. *Earlier blocks matter* (n = 4): choosing only the leader of the last block, the analogue of Theorem A's focus on
   the last block, fails for some runs of Phase 1 (three 4-good agents, `results/k4_lb4_i9_run.log`), and for the
   index run on 4 pure cores (119,200 profiles, `results/k4_lb4_i8.log`). In both smallest cases the run's last block
   is one agent, and the first block's leader must change. The polynomial LB₄ᴸ(index order) holds for n ≤ 3 (with
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
`results/k4_lb4_run_4pure_5.log`. Columns: how LB₄ ended, counted in profiles (the first success in the search order).

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
two 4-good agents), and all 24,694,052,160 tied profiles with n ≤ 3. The hard cases are rare but present everywhere: a
later insertion sequence is needed for 0.006% of the pure n = 4 profiles, a rotation for 2.8%, an owner other than r
for 2.7%.

## 5. Toward a proof: what carries over from LB⁺, and the gap

**Carries over (proved above or verbatim).** The Phase 1 invariants (I1)–(I3), (B1), (B2); validity after the
upgrades; soundness of every completion that satisfies (OC₄) (Theorem 1′₄, any k); the counting ω = |NA| − σ; the
owner test (§2: Lemma 1 of `proofs/lb_last_step.md` with (OC₄); exact with the owner's needs from its base,
sufficient with slots that depend on the owner's bundle);
self-protection of free agents with one-good bases (Lemma 2₄), the k = 4 counterpart of "a terminal holding its top
is its own τ(x)".

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
   block's leader" and "for the index run, up to that choice" (`attempts/lb4-last-block-leader.md`). A proof must choose the insertion sequence, or use a move
   that lets an agent go below its pick (two rotations in a row can; untested beyond n = 3).

**The gap, precisely.** By Theorem 1′₄, K4.D follows from
- **Conjecture K4.LB4.** For every k = 4 core and every strict profile, LB₄ does not fail: some insertion sequence
  gives a Phase 1 run whose upgraded pre-allocation, or one rotation of it, has a completion satisfying (OC₄).

By K4.TIE it suffices for strict profiles; LB₄ is tested with ties too. A proof along LB⁺'s lines needs a Theorem A₄
that counts the goods the frozen and two-good-base agents need kept out of X_o against the slots (Lemma 2₄ disposes of
the one-good-base agents), a Theorem B₄ for the general rotation, and a rule, or an exchange argument, for the
insertion sequence. §4's counters say how rare each hard case is: they are the cases a proof must handle.

**Not done.** The analogue of conjecture S2.K (what the large bundle contains) was not tested: LB₄ returns the first
completion found, not a canonical one. Tests beyond the certified cores (n = 5 with three or more 4-good agents, pure
n = 5) were not run.

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
`-c1` chains may end at upgraded agents; `-s` sensitivity (owner constraint ignored); `-b` brute force (every profile
its own leaf); `-a` print the leaf allocations.
