# LB₄: construction LB⁺ carried to four goods

Workstream `proof/k4-lb4`, ledger open item 15 (the LB₄ route of `k4/SCOUT.md` §5, steps (a)–(d)). Notation as in
`proofs/construction.md` and `proofs/lb_last_step.md` (k = 3), and `k4/SCOUT.md` (k = 4 cores). Tools:
`k4/lb4.c` (the construction and an exhaustive tester), `k4/lb4_run.py` (driver), `k4/lb4_brute.py` (every EFX₀
allocation of a small instance, by brute force).

STATUS_PLACEHOLDER

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
|B_o| ≤ 2 gets ω + 2 goods when all slots are filled. Taking the owner's needs from its bundle lowers |NA|, so it may
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
no bundle. When x took d_x, or nothing of R_x, the goods b_x, c_x were placed before or are not junk, and X_o ∩ R_x ⊆
B_o ∪ {d_x} minus x's own good has at most one good. Later placements only remove goods from X_o. ∎

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
in the order: r, the last-processed agent with a one-good base, if it is free; then every other free agent with a slot
or a two-good base, latest-processed first. For an owner o, try every C ⊆ J (first those of size S − cap(o), then the
larger ones): X_o = B_o ∪ (J ∖ C), the owner's needs N_o^X, and with them F and the slots. C must fit into the slots of
the free agents other than o; every agent without a slot must be unthreatened by X_o; every agent with one slot that
X_o threatens when it holds its base alone must receive a good of C that protects it (a system of distinct
representatives, by augmenting paths). The rest of C fills the remaining slots in any order. This is an exact test:
a completion with owner o exists iff one of these C passes.

**Rotation.** If the owner step fails, try every frozen agent k (latest-processed first), every need chain
k = x₀, x₁, …, x_t (x₁, …, x_{t−1} frozen, Y_{x_{i−1}} ∈ N_{x_i}, and x_t free with a one-good base, or with a
two-good base: an upgraded agent that still needs Y_{x_{t−1}}), and every nonempty O ⊆ R_k ∩ (J ∪ B_{x_t}) (pairs
first, then triples, single goods, quadruples):
- every x_i (i ≥ 1) takes Y_{x_{i−1}} as its base, and B_{x_t} goes back to the junk;
- k takes the base O, with value-based needs.

If the result is valid, run the owner step on it, with k as the owner when |O| ≥ 3, and otherwise first without an
owner if ω ≤ 0, then with owner k, then with the other owners. At k = 3 LB⁺'s rotation is the case k = k*, x_t = r,
O = {b_k, c_k}.

**Search.** Try the insertion sequences τ in lexicographic order; for each, Phase 1, upgrades, owner step, rotation.
Return the first allocation found. LB₄ *fails* if no τ gives one.

## 3. Why each ingredient is there (rejected variants)

Each smaller variant fails, and each failure is confirmed: a brute force over all n^m allocations with explicit
integer values (`k4/lb4_brute.py`) finds EFX₀ allocations with at most one large bundle at the failing profile, so it is
the construction that fails, not K4.D. One file each in `attempts/`, reproduced by `python attempts/lb4_variants.py`.

| variant | smallest failure | file |
|---|---|---|
| LB⁺'s shape: index insertion, owner r, else one rotation (any chain, any subset) | n = 2, m = 5 | `attempts/lb4-lbplus-shape.md` |
| no rotation (everything else searched, including every insertion sequence) | n = 3, m = 5 | `attempts/lb4-no-rotation.md` |
| a fixed insertion rule (index, block lookahead, "a > b + c first", least ω), with every upgrade policy, every owner, up to 3 rotations | n = 3, m = 6 | `attempts/lb4-fixed-insertion.md` |
| the owner's needs from its base, as at k = 3 (everything else searched) | n = 4, m = 8 (pure) | `attempts/lb4-owner-needs-from-base.md` |

What each failure shows:
1. *Upgrades can hurt* (n = 2): the k = 4 pair {b, c} is not always envy-free, so an upgraded agent can be threatened
   by a + d in the large bundle, and an upgrade that removes a need can leave no valid owner.
2. *The rotation is needed* (n = 3): a flat agent must end with its two private goods, which serial dictatorship never
   gives it (it always picks a shared good); a rotation does. With LB₄'s single upgrade policy, chains must be allowed
   to end at an upgraded agent that still needs a good: without that (`-c0`), 2 pure n = 4, m = 8 cores fail
   (9,280 profiles); trying the other upgrade policies as well (`-u3 -c0`) also repairs them.
3. *The insertion order matters* (n = 3): unlike LB⁺ (Theorem C holds for every insertion order), some profiles need an
   agent to end below the good it picked, and a need-chain rotation only moves agents up. Every fixed rule tested fails.
4. *The owner's large bundle can remove its own needs* (n = 4): with {b, c, d} worth more than a, the owner no longer
   needs its top alone, which frees the agent holding that top.

## 4. Exhaustive tests

RESULTS_PLACEHOLDER

## 5. Toward a proof: what carries over from LB⁺, and the gap

**Carries over (proved above or verbatim).** The Phase 1 invariants (I1)–(I3), (B1), (B2); validity after the
upgrades; soundness of every completion that satisfies (OC₄) (Theorem 1′₄, any k); the counting ω = |NA| − σ; the
exact owner test (§2 is Lemma 1 of `proofs/lb_last_step.md` with (OC₄) and slots that depend on the owner's bundle);
self-protection of free agents with one-good bases (Lemma 2₄), the k = 4 counterpart of "a terminal holding its top
is its own τ(x)".

**Does not carry over.** Theorem A (the owner r) and Theorem B (the rotation) of `proofs/lb_last_step.md`. Their
counting pairs every exposed agent with a terminal of its own block, and needs one good per exposed agent. At k = 4:
1. *(A1) can fail:* an upgraded agent may keep a need (N′ ≠ ∅), for its top, and so r may be frozen. At k = 3 upgraded
   agents need nothing.
2. *(A3) fails:* an agent holding its top is threatened by a *type-dependent* set of lower goods, and when that set
   misses one of its goods, the agent may have lost that good before its turn. So exposed agents need not be block
   leaders, and one block can contain several.
3. *One good per exposed agent fails:* a flat frozen agent (a < c + d) with b, c, d all free needs two goods kept out of
   the large bundle, and an agent holding b_x is exposed when c + d > b. Agents with a two-good base can be exposed.
4. *Any insertion order fails* (`attempts/lb4-fixed-insertion.md`): Theorem C's "for every run of Phase 1" is false at
   k = 4 for the rotations tested; a proof must choose the insertion sequence, or use a move that lets an agent go
   below its pick.

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
python3 k4/lb4_run.py results/k4_certs_4_pure.json.gz -i2 -u1 -r1 -w1 -c1 # pure n = 4: RUNTIME_PURE on 4 CPUs
python3 k4/lb4_run.py FILE ... --cert=OUT.json.gz                        # also write LB4's outputs as a certificate
python3 k4/check4.py results/k4_lb4_certs_3.json.gz --expect 3:any:51    # independent check of those outputs
python3 k4/test_lb4.py                                                   # sensitivity, lazy vs brute force, attempts
python3 attempts/lb4_variants.py                                         # the rejected variants' smallest failures
python3 k4/lb4_brute.py '[[0,2,3,4],[1,2,3,4]]' '[[1,4,6,8],[2,4,5,8]]'  # every EFX0 allocation of one instance
```
`lb4_run.py` compiles `k4/lb4.c` with gcc into the temporary directory (`LB4_BIN` overrides the path). Options of
`lb4.c`: `-i0` index insertion, `-i2` every insertion sequence, `-i3` block lookahead, `-i4` least ω, `-i5` "a > b + c"
first; `-u0/-u1/-u2/-u3` no upgrades, need-shrinking, envy-free only, all three in turn; `-o0` every owner, `-o1` r
only, `-o2` r then rotation; `-rN` up to N rotations; `-w1` owner needs from its bundle; `-c1` chains may end at
upgraded agents; `-s` sensitivity (owner constraint ignored); `-b` brute force (every profile its own leaf); `-a`
print the leaf allocations.
