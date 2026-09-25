# k = 4 scout: EFX₀ when every agent has at most four relevant goods

Workstream `compute/k4-scout`. Ledger rows `K4.*`. Everything here is one of: argued in this file (marked *proof*;
written but not yet reviewed, so the ledger lists these as CONJECTURE until a review), certified by an exhaustive
search with an independently checked certificate, or marked EVIDENCE / CONJECTURE.

**TARGET₄.** Every instance with nonnegative real additive valuations in which every agent has |R_i| ≤ 4 has a
complete EFX₀ allocation.

**Summary.**
- *Literature* (§1): ordinary EFX for k = 4 is claimed by Viswanathan–Mehta (proof sketch only). EFX₀ for k = 4
  is open in every paper read.
- *Reduction* (§2, written, not yet reviewed): L1, L2, L3, L6, L9, L10, L11 carry over. TARGET₄ reduces to
  k = 4 cores. These have agents with 3 or 4 goods, strictly balanced, with up to 2 private goods (then p + q < s + t),
  and m ≤ 3n. L5 fails. The additive order types of 4 goods replace it: 1,519 weak, 288 strict balanced (12 per
  ranking, all behaviorally distinct), with integer representatives ≤ 10. Ties reduce to strict types.
- *Certified* (§3): every k = 4 core with n ≤ 4 (1,058 cores), and with n = 5 and at most two 4-good agents
  (7,203), has for every strict profile an EFX₀ allocation with at most one bundle of more than 2 goods (D2). n ≤ 3
  also holds with ties. Checked by an independent checker, and the core lists are complete by orbit counting.
- *Refuted* (§4, brute-force confirmed): all bundles ≤ 3 suffice (fails at n = 3); the large bundle stays at
  the counting bound (it needs 2n goods at n = 3, m = 8).
- *Evidence*: D2 on 140,220 random profiles of pure n = 5 cores. Serial dictatorship plus junk (LB's shape)
  worked on every sampled profile for n ≤ 4.
- *Conjecture K4.D*: D itself (≤ 1 bundle of more than two goods) holds for k ≤ 4. Recommended route (§5): LB₄,
  construction LB⁺ carried to four goods, with type-dependent owner constraints and private pairs in the large
  bundle.

## 1. Literature position (only what `proofs/citations.md` records as read)

- **Ordinary EFX for k = 4 is claimed; EFX₀ is not.** Viswanathan–Mehta (AAMAS 2024, extended abstract, read):
  EFX exists, by a polynomial-time algorithm, when every agent values at most 4 goods positively ("4-limited").
  Their EFX is the ordinary notion (the removed good must be worth > 0 to the envier), and the algorithm ends by
  giving goods that everyone values at 0 to an arbitrary agent. That last step can break EFX₀, so the result
  does not give TARGET₄. The text is a 3-page abstract with a proof sketch only, and `proofs/citations.md` does
  not record which valuation class the theorem assumes (PROMPT.md §2 reads it as additive) [valuation class
  unverified]. L1 does not transfer it to EFX₀: L1 is about classes fixed by (n, m), and perturbing zero values
  leaves the 4-limited class.
- **Pieces of TARGET₄ that follow from papers read in full** (each through the k = 4 core reduction of §2):
  - Mahara, arXiv 2107.09901, Theorem 3: EFX₀ for general monotone valuations when m ≤ n + 3. This covers every
    k = 4 core with m ≤ n + 3.
  - Afshinmehr et al., arXiv 2606.18665: EFX₀ on multigraphs for cancelable valuations (additive included). This
    covers every instance in which each good is positively valued by at most two agents, for every k.
  - Alkassar–Fouz–Mehlhorn, arXiv 2608.08590: EFX₀ for four additive agents and at most nine goods.
  - Lianeas–Sgouritsa–Sotiriou, arXiv 2608.03171: EFX on hypergraphs of girth ≥ 4, general monotone valuations.
    `proofs/citations.md` does not record whether this is EFX or EFX₀ [notion unverified here].
  - Chaudhury–Garg–Mehlhorn (three additive agents): [unverified]. With L1 it would give EFX₀ for n = 3.
- **This repository:** TARGET (k = 3) is proved, and covers every k = 4 instance whose core (§2) has only agents
  with 3 relevant goods.
- So, as far as the papers read go, **EFX₀ for k = 4 is open**. The read papers cover only the special cases
  above: m ≤ n + 3, at most two valuers per good, or four agents with at most nine goods.

## 2. Reduction: which of L1–L11 carry over to k ≤ 4

The numbering follows PROMPT.md §3 and `proofs/lemmas.md`.

| Lemma | k ≤ 4 | Why |
|---|---|---|
| L1 perturbation | carries over verbatim | it is about all instances with a given (n, m); it never used k |
| L2 peeling R1, R2 | carries over verbatim | the proof uses only "the other bundles meet R_i inside R_i ∖ P" and "P is a singleton or worthless to the rest" |
| L2c (≤ 2 goods ⟹ serial dictatorship) | unchanged | |
| L3 junk to an envy-graph source | carries over verbatim | never used k |
| CORE | **changes**: see K4.CORE below | agents with 3 goods remain, and an agent may keep 2 private goods |
| L4 counting | changes: m ≤ 2n₃ + 3n₄ ≤ 3n | below |
| L5 ordinality | **fails**: the ranking no longer suffices, and 12 order types per ranking replace it | K4.OT below |
| L6 components | carries over verbatim | |
| L7 slack | the identity carries over; slack 2n − m can now be negative | below |
| L8 two own goods ⟹ safe | **fails**; "all but one own good ⟹ envy-free" replaces it | below |
| L9 size-2 criterion | carries over verbatim (any additive valuations) | but needs m ≤ 2n |
| L10 insertion | carries over verbatim | only uses v_i(a_i) ≥ v_i(g) for every g |
| L11 shapes | carries over | an agent with 2 private goods becomes a degree-2 vertex |

**K4.CORE (proof).** Apply R1, R2 and L3 until none applies, exactly as in the CORE theorem of
`proofs/lemmas.md`, whose induction never uses k. What remains, if it has ≥ 2 agents, is a *k = 4 core*:
- every agent has 3 or 4 relevant goods among the remaining ones. With ≤ 2 left, R1 applies;
- every agent is strictly balanced: v(a) < v(R_i) − v(a) for its top good a. Otherwise R1 applies, and ties count
  as top-heavy;
- an agent with 3 goods has at most 1 private good (a good no other remaining agent values). One with 4 goods has at
  most 2, and if it has two, p and q, then v(p) + v(q) < v(s) + v(t) for its shared goods s and t. With 3 or 4
  private goods, R2 applies to P = the private goods, or else the single shared good is top-heavy and R1 applies.
  With 2, R2 applies exactly when v(p) + v(q) ≥ v(s) + v(t);
- every good is relevant to some agent (L3).

If every k = 4 core has an EFX₀ allocation, TARGET₄ holds. Cores whose agents all have 3 goods are k = 3 cores,
covered by TARGET (proved). So the new cores are the connected ones with agent degrees in {3, 4}, at least one 4.

**New features compared with k = 3.** (i) An agent can keep two private goods. The tempting fix, merging p and q
into one good, is not sound: if they end up in another agent's bundle B, then v_i(B ∖ p) keeps q's value. Nor may
one assume that i holds its private goods: moving p into X_i can create strong envy toward X_i ∪ {p}, since
removing p leaves all of X_i. (ii) Agents with 3 goods appear in k = 4 cores. They come from 4-good agents that
lost a good to peeling.

**L4 for k = 4 (proof).** Σ_i d_i = 2m − π + Σ over shared goods of (deg − 2), with π ≤ n₃ + 2n₄ private goods
(n_d = number of agents with d goods). So 2m ≤ Σ d_i + π ≤ 4n₃ + 6n₄, that is m ≤ 2n₃ + 3n₄ ≤ 3n. For a connected core,
β = Σ d_i − n − m + 1, which is 3n − m + 1 when every agent has 4 goods. m = 3n forces β = 1.

**L7 for k = 4.** The count "a size-≤ 2 allocation with e empty bundles has 2n − m − 2e alone goods" is pure
counting and carries over. But m can exceed 2n (up to 3n), and then every allocation has a bundle with ≥ 3 goods.
If at most one bundle has more than 2 goods, it has at least m − 2n + 2 goods (n + 2 when m = 3n).

**L8 for k = 4 (proof).** "Holding two of its goods ⟹ safe" fails. An agent holding {c, d} strongly envies a
bundle {a, b, x} with x ∉ R_i, since v(c) + v(d) < v(a) + v(b). The replacement: *an agent holding a set O ⊆ R_i
with v(O) ≥ v(R_i ∖ O) is envy-free*, because every other bundle meets R_i inside R_i ∖ O. For a strictly balanced
agent this holds for every O that misses only one of its goods (the missing good is worth less than the rest), for
O ⊇ {a, b} and O ⊇ {a, c}, and for {a, d} or {b, c} depending on the type. *β = 1 cores are solved by orientation*:
a connected core with β = 1 is one cycle of agents and degree-2 goods, with pendant private goods. Give every agent
its private goods and the next cycle good. Each agent then holds all but one of its goods, so it is envy-free.

**L11 for k = 4.** Delete the private goods. Agents with 2 private goods become degree-2 vertices, and the others
keep degree ≥ 2. So a connected k = 4 core is a subdivision, with pendant private goods, of one of finitely many
multigraphs of minimum degree ≥ 3 and cyclomatic number β. Agent vertices now have degree up to 4.

### K4.OT: additive order types of 3 and 4 goods (`k4/order_types.py`, `results/k4_order_types.log`)

An agent compares only disjoint sets: its own bundle with part of another bundle. And v(S) ≥ v(T) iff
v(S ∖ T) ≥ v(T ∖ S). So its behavior is fixed by the sign vector (sign(v(S) − v(T)) : S, T disjoint, nonempty),
which has 25 entries for 4 goods and 6 for 3. A *type* is a sign vector realized by positive values: a face of
the arrangement of the hyperplanes v(S) = v(T) inside the open orthant. Equivalently, it is a weak order on
subsets that positive additive values realize.

*Every type has a representative in [1, 16]⁴ (proof).* Add the coordinate hyperplanes. The closure of a face F is
a pointed cone generated by extreme rays, which are 1-dimensional faces. Each ray solves 3 independent equations
with coefficients in {−1, 0, 1}, so it has an integer generator made of 3 × 3 minors, with coordinates ≤ 4. With
d = dim F, the sum of d linearly independent extreme rays lies in the open simplicial cone they span. That cone is
open in span F and contained in cl F, hence in F. So this sum is a point of F with coordinates ≤ 16. For 3 goods
the bound is 6. The script checks this in two ways. It enumerates the grid, and it computes all 101 rays and all
sums of ≤ 4 of them. The two give the same 1,519 types, and the grid [1, 20]⁴ adds none.

| goods | weak types (labeled / up to relabeling) | strict | balanced (weak) | **balanced strict** | per ranking (strict / balanced strict) |
|---|---|---|---|---|---|
| 3 | 31 / 8 | 12 | 13 / 4 | **6** | 2 / 1 |
| 4 | 1,519 / 88 | 336 | 1,271 / 72 | **288** | 14 / 12 |

For 3 goods a balanced agent's type is its ranking, which is L5. For 4 goods every ranking a > b > c > d carries
12 balanced strict types. They are listed with their smallest integer representatives (largest value 10) in
`results/k4_order_types.log`. For example, (8, 4, 3, 2) is d < c < b < cd < bd < bc < a < bcd < ad < ⋯, and
(7, 6, 5, 3) is d < c < b < a < cd < ⋯. Any two of the 12 differ on some comparison v(S) vs v(T) of disjoint sets.
In a configuration where the agent holds S and another bundle is T plus a good the agent does not value, one type
is safe and the other is not. So the 12 are behaviorally distinct, and EFX₀ in a k = 4 core is **not ordinal**. A
k = 4 instance is a hypergraph plus one of 288 labels per 4-good agent (6 per 3-good agent), with half as many
choices for an agent with two private goods, because of p + q < s + t.

**K4.TIE, ties reduce to strict types (proof).** Whether agent i is safe in an allocation depends only on v_i, and
it is a conjunction of weak inequalities between subset sums of v_i. So the set of v_i under which i is safe is
closed. Let a tied core profile have values v_i. Every core condition (strict balance, p + q < s + t) is a strict
inequality, so a small generic perturbation v_i′ keeps it and lies in a chamber (strict type) C_i with v_i ∈ cl C_i.
Suppose the strict profile (C_i) has an EFX₀ allocation X. Then X is EFX₀ for every valuation in the product of the
C_i (the condition depends only on the types), hence, by closedness, at v. So it suffices to search strict profiles.

## 3. Small-case search (`k4/search4.py`, `k4/check4.py`)

**Cores.** `search4.py` lists the connected k = 4 cores with nauty's `genbg`: agent degree 3 or 4 (with `--pure`,
all 4), good degree ≥ 1, one graph per isomorphism class, keeping those with at most d − 2 private goods per agent of
degree d. Counts (pure = every agent has 4 goods; mixed = degrees 3 and 4, at least one 4):

| n | all (≥ one 4-good agent) | by number n₄ of 4-good agents | m range | certificate |
|---|---|---|---|---|
| 2 | 5 | n₄ = 2 (pure): 3 | 4–6 | `results/k4_certs_2.json.gz` |
| 3 | 51 | n₄ = 3 (pure): 18 | 4–9 | `results/k4_certs_3.json.gz` |
| 4 | 1,002 | n₄ = 1: 135, 2: 309, 3: 339, 4 (pure): 219 | 4–12 | `results/k4_certs_4_n4_{1,2,3}.json.gz`, `results/k4_certs_4_pure.json.gz` |
| 5 | (≈ 45,600 before the private-good filter) | n₄ = 1: 1,735; n₄ = 2: 5,468 (n₄ = 3, 4 and pure: not searched) | 4–12 | `results/k4_certs_5_n4_1.json.gz`, `results/k4_certs_5_n4_2.json.gz` |

**Method.** Per core, CEGAR over profiles of strict balanced types. The domain has 288 types per 4-good agent (144
if it has two private goods) and 6 per 3-good agent, so a pure n = 4 core has up to 288⁴ ≈ 6.9·10⁹ profiles. A
proposal step picks a profile no allocation found so far covers: first random profiles until 4,096 random samples are
all covered, then a C scanner (`k4/scan.c`) that walks the rest in lexicographic order. The scanner prunes with
bitsets, and skips a subtree when an allocation makes all remaining agents safe for every type. An inner
SAT solver finds an allocation for the proposed profile in the model "at most one bundle with more than 2 goods"
(D2). It takes the best of 8 solutions, diversified by random phases. An agent's covered types are those under which
it is safe, computed from the raw EFX₀ definition with the types' integer representatives. A profile with no D2
allocation would be recorded, and solved without the shape limit. None occurred.

**Certificates and checker.** `results/k4_certs_*.json.gz` list, per core, the allocations. `k4/check4.py` is
independent of the search: its own order-type enumeration from the grid [1, 16]^d, the raw EFX₀ definition, a
plain C coverage loop. It checks
(1) every listed hypergraph is a k = 4 core,
(2) no two are isomorphic, and Σ n! m! / |Aut| equals the number of labeled cores, which comes from a DP (self-tested
against brute force for n ≤ 3, `results/k4_check_selftest.log`), so the list is complete, and
(3) every strict balanced profile of every core is covered.
Negative tests (a deleted allocation, a deleted core) are caught.

**Results (CERTIFIED).** For every strict profile, an EFX₀ allocation with at most one bundle of more than 2
goods exists in:
- every k = 4 core with n = 2 or n = 3 (5 and 51 cores; `results/k4_check_2_3.log`). With ties too, all 1,271
  balanced weak types per 4-good agent and 13 per 3-good agent: n = 2 and n = 3 (`results/k4_certs_2_ties.json.gz`, `results/k4_certs_3_ties.json.gz`,
  `results/k4_check_3_ties.log`), which corroborates K4.TIE directly;
- every k = 4 core with n = 4, all 1,002 of them (`results/k4_check_4_pure.log`, `results/k4_check_4_mixed.log`). The
  pure cores alone have up to 288⁴ ≈ 6.9·10⁹ profiles each; 22,000 allocations cover them all;
- every k = 4 core with n = 5 and exactly one 4-good agent (1,735 cores,
  `results/k4_check_5_n4_1.log`) and with exactly two (5,468 cores, `results/k4_check_5_n4_2.log`).
  Together: 8,261 cores.

No profile anywhere needed a second bundle of more than 2 goods, so the search's fallback models (D3, no limit) never
ran.

By K4.CORE, K4.TIE and L6, these give: **every instance with |R_i| ≤ 4 whose reduction reaches only core components
with at most 4 agents, or with 5 agents of which at most two have 4 goods, has an EFX₀ allocation**. Each
component is a k = 4 core, or a k = 3 core, which TARGET covers. This is conditional on K4.CORE and K4.TIE, whose
written proofs are not yet reviewed.

**EVIDENCE for n = 5 with all agents of degree 4** (random strict profiles, PROMPT.md §5 rule 3):
all 4,674 pure n = 5 cores (m = 4–15), 30 random strict profiles each, 140,220 profiles in all. Every one has an
EFX₀ allocation with at most one bundle of more than 2 goods (`k4/sample5.py`, `results/k4_sample_5_pure.log`).
Random testing misses rare failures: at k = 3 some failed in 1 of 23,000 profiles.

**A bug the checker caught.** An early version of `scan.c` indexed agent rows as base + t·W instead of
(base + t)·W. With more than 64 allocations it read wrong rows and could declare uncovered profiles covered.
`check4.py` rejected the resulting n = 4 certificate (7 cores not covered). Every certificate listed here was
produced after the fix, except n = 2 and 3, which came from an earlier SAT-based proposal step. All of them pass
the checker. `k4/test_scan.py` tests the scanner against brute force with several words per row.

## 4. Structure (toward a k = 4 analogue of conjecture D)

**D2, the same statement as D, held in every certified case.** Every certificate above uses only allocations with at
most one bundle of more than 2 goods. So D2 holds for every k = 4 core with n ≤ 4, and with n = 5 and at most two 4-good agents. No profile needed
two large bundles.

**All bundles ≤ 3 does not suffice; the large bundle can be big (REFUTED / CERTIFIED at n = 3,
`k4/structure.py`, `results/k4_structure_3.log`).** Exhaustive over all strict profiles of the 51 cores with n = 3:

| m | cores | all bundles ≤ 2 (C2) fails | all bundles ≤ 3 (C3) fails | least L (D2 with the large bundle ≤ L goods) vs. counting bound max(3, m − 2n + 2) |
|---|---|---|---|---|
| 4 | 4 | 0 | 0 | 3 = bound (4 cores) |
| 5 | 11 | 9 | 0 | 3 = bound (11) |
| 6 | 18 | 15 | 6 | bound 3: L = 3 (12), **4** (6) |
| 7 | 12 | (m > 2n) | 3 | bound 3: L = 3 (7), 4 (3), **5** (2) |
| 8 | 5 | (m > 2n) | 1 | bound 4: L = 4 (3), 5 (1), **6** (1) |
| 9 | 1 | (m > 2n) | 0 | bound 5: L = 5 |

C2 already fails at n = 2 (two agents with the same 4 goods and type (8, 4, 3, 2): every 2 + 2 split leaves the
holder of the lower pair envious, so the only EFX₀ allocations are {a} | {b, c, d}). Every UNSAT claim in this table
that enters the ledger is confirmed by `k4/verify_small.py`: brute force over all n^m allocations with explicit
integer values and the raw definition, no SAT (`results/k4_verify_small.log`: 51 instances, every claim confirmed). The "fails" counts are confirmed this
way, one instance per failing core. The "holds" counts and the exact values of L come from one implementation
(CEGAR in `structure.py`, no certificate).

**Smallest configurations.**
- *C3 fails* (n = 3, m = 6): agent 0 has goods {0, 2, 4, 5} with values (4, 3, 8, 2) (goods 0 and 2 private).
  Agents 1 and 2 have {1, 4, 5} and {3, 4, 5}, each with values (2, 3, 4) (goods 1 and 3 private). Every EFX₀
  allocation has a bundle of 4 goods. The two shared goods 4 and 5 are the tops of three agents. Agents 1 and 2
  rank them 5 > 4 and have one private good each.
- *The large bundle must be twice the counting bound* (n = 3, m = 8; `cited_n3_m8_L6_bound4` in `k4/small_claims.json`): agents {0, 2, 6, 7},
  {1, 4, 6, 7}, {3, 5, 6, 7} share goods 6 and 7, and each has two private goods. Values: (4, 3, 8, 2), (4, 1, 6, 8),
  (4, 1, 6, 8). Exactly 4 EFX₀ allocations exist, and each is: goods 6 and 7 as singletons for two agents, and all six
  private goods to the third ({0, 1, 2, 3, 4, 5}). All six private goods pool into one bundle of 2n goods
  (brute force; no hand proof extracted). At k = 3 an agent has at most one private good, and in the n ≤ 6 data the
  large bundle collects private goods of agents in case T or B (conjecture S2.K). This is the same phenomenon, but
  here the privates come in pairs.

**Serial dictatorship plus junk (the shape of LB's output) — EVIDENCE that it survives at k = 4 (`k4/sdj.py`,
`results/k4_sdj_sample_2_3.log`, `results/k4_sdj_sample_4_pure.log`).** Model SDJ: for some order of the agents, each agent picks its favourite remaining
good (nothing if none remains), and the unpicked goods are placed freely with at most one bundle of more than 2 goods.
LB and LB's upgrades produce allocations of this shape; LB⁺'s rotation does not. Results: SDJ holds for every strict
profile of every n = 2 core (exhaustive, CEGAR). At n = 3 it held on all 102,000 random profiles (2,000 per core,
EVIDENCE only). The test does detect failures: on the k = 3 core H3 it reproduces the known 14 of 216 profiles
without a size-≤ 2 allocation. At n = 4 it held on all 657,000 random profiles of the 219 pure cores (3,000 per core,
`results/k4_sdj_sample_4_pure.log`, EVIDENCE only).

## 5. Conjecture and recommended route

**Conjecture K4.D (D for k ≤ 4).** Every k = 4 core has an EFX₀ allocation in which at most one bundle has more
than two goods. By K4.CORE and L6 (whose composition of components loses only the shape, not EFX₀), K4.D implies
TARGET₄. For k = 3 cores this is conjecture D, which is proved. Status: CONJECTURE. It is certified for n ≤ 4, and for n = 5 with at most two 4-good agents (8,261 cores). No case searched, random samples included, gave a counterexample to D2.

What the data rule out, so a proof cannot aim for them: all bundles ≤ 3 (fails at n = 3), a large bundle of
bounded size (it needs 2n goods in the n = 3, m = 8 example; at least m − 2n + 2 by counting, and more in 13 of the 51
n = 3 cores), and ordinality (12 behaviorally distinct types per ranking).

**Recommended route: LB₄, construction LB⁺ carried to four goods.**
Serial dictatorship plus junk is the shape of LB, and the SDJ data suggest it survives. LB's soundness proof
(Theorem 1 of `proofs/construction.md`) uses only additivity, the serial-dictatorship invariants (I1), (I2) (valid
for any k), and a_k < b_k + c_k for upgraded agents. It never uses L5. What must change:
1. *Upgrades.* An agent holding its pick Y may take junk goods J ⊆ R_k with v(Y ∪ J) ≥ v(R_k ∖ (Y ∪ J)). It is then
   envy-free (the L8 replacement of §2). At k = 3 this is exactly "b takes c". At k = 4 the agent may need two junk
   goods, which breaks "every non-owner bundle has ≤ 2 goods". So the upgrade rule has to be chosen (for example,
   {pick, one junk} only when that already dominates).
2. *Owner constraint.* An agent i ≠ o holding only its pick is threatened by the large bundle X_o exactly when
   v_i(X_o ∩ R_i) > v_i(Y_i), after removing a good of X_o outside R_i. At k = 3 this is "b_i and c_i both in X_o". At
   k = 4 it is type-dependent: a pair with v(x) + v(y) > v(Y_i), or any triple. Size-≤ 2 bundles are harmless by (I1),
   as at k = 3.
3. *Private pairs.* Agents with two private goods are new. Their privates are junk to everyone else and are the
   natural contents of the large bundle (the n = 3, m = 8 example). The analogue of S2.K should be conjectured and
   tested first.
4. *Theorem A (the bad case) and the rotation* of `proofs/lb_last_step.md` must be redone with type-dependent
   threats in place of the {b_k, c_k} pair.

First steps, in order:
(a) implement LB₄ with rules 1–2 (adaptive order: the R1 step now fires when an agent's favourite remaining good is
worth at least the rest of its remaining goods) and run it on every strict profile of every core with n ≤ 3. This is
288³ profiles per core, so it needs C or a split: Phase 1 depends only on the ranking profile (24³), Phase 2 on the
types. Record the smallest failing configurations;
(b) prove LB₄'s soundness (the Theorem 1 analogue), which should be routine;
(c) state and test the k = 4 analogue of S2.K (what the large bundle contains, and who owns it);
(d) re-derive Theorem A and design the rotation;
(e) computationally, extend the certified range (§3) as a safety net: n = 5 with three 4-good agents
(`k4/search4.py 5 --n4=3`, about 14,500 hypergraphs before filtering, estimated 3 h on 4 CPUs), then four. Pure n = 5 cores have 288⁵ ≈ 2·10¹² profiles each, beyond this method.
They need either symmetry reduction or a structural lemma that shrinks the type set.

Alternatives, in case LB₄ breaks: the local search of `proofs/local_search.md`. Its Lemma 1 (EFX₀ is local and
ordinal in a core) is exactly what fails at k = 4, so it needs the most rework. Or the multigraph route
(`proofs/multigraph_extension.md`), which covers goods with at most two valuers for every k already (Afshinmehr et
al.), and would need goods with 3 or 4 valuers.

## Reproduce

```
python3 k4/order_types.py --write                  # K4.OT, ~2 min (the ray cross-check is pure Python)
python3 k4/search4.py 2 3                          # n = 2, 3 (all cores), seconds; writes k4/k4_certs_{2,3}.json.gz
python3 k4/search4.py 4 --pure                     # n = 4, 219 pure cores: ~6 min on 4 CPUs
python3 k4/search4.py 4 --n4=1                     # likewise --n4=2, --n4=3 (seconds each); n = 5: --n4=1 (1.5 min), --n4=2 (9 min)
python3 k4/search4.py 3 --ties                     # all balanced weak types, seconds
python3 k4/check4.py results/k4_certs_*.json.gz    # independent checker; n = 4 pure ~30 min, the rest minutes
python3 k4/check4.py --selftest                    # labeled-core DP vs brute force
python3 k4/structure.py 3                          # §4 table, seconds
python3 k4/verify_small.py                         # brute-force confirmation of every failure claim in k4/small_claims.json
python3 k4/sdj.py 4 --pure --sample=3000           # SDJ sampling (EVIDENCE), seconds
python3 k4/sample5.py 5 30 --pure                  # pure n = 5 sampling (EVIDENCE), ~3.5 min
(cd k4 && python3 test_scan.py)                    # scanner vs brute force
```
`search4.py` needs nauty's `genbg` and compiles `k4/scan.c` on first use. It checkpoints finished cores in
`k4/checkpoint_*.jsonl` (resume by rerunning; `--fresh` starts over). The search is randomized but seeded, so reruns
give valid, not necessarily identical, certificates.

