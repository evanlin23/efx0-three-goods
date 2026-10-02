# The θ-b case and the non-S1 T3-stage states at f = 1: role swaps seen from an unmoved owner

Workstream `proof/k4-thetab` (PR #85). Ledger rows K4.TB.*. Task: `k4/dl13.md` §6 item 2. Builds on `k4/dl2.md`
§3–§4 (the moves (T1)–(T3); Lemmas 1, 6; refereed, K4.DL2.MOVES), `k4/dl13.md` (the T3 stage, the targets, C1–C3;
PR #75, merged), `k4/hall.md` §1 (Lemma H1, K4.HALL.COVER) and `k4/c4x.md` §1 (𝒫, needs, frozen agents, slots,
deficit). Nothing here changes K4.D or K4.T.

**Context.** The coordinator reports that DL_RT4 (and key-graph DL with single (T3) or (T4) edges) is refuted at n = 5,
f = 3. The data are on cloud branches compute/k4-rt4-n5b and -n5c (`results/k4_rt4/n5*_FAILURES.md`), and the ledger
statuses are the coordinator's to change. The new target relation is R_C = (T1) ∪ (T2) ∪ (T3⁺) ∪ (T4), where (T3⁺) is
the frozen-chain role swap. At f = 1, (T3⁺) = (T3), so this file's question is unchanged. Everything here is at
f = 1 except Lemma G, which holds at every f. The f ≥ 2 targets are left to proof/k4-f2 (§6).

**Summary.**
- **The targets** (§1, EVIDENCE). These are the T3-stage records of PR #75's dumps that C1, C2 and C3 do not certify:
  1,343 records, 1,223 of them at f = 1 (1,199 θ-b, 2 θ-a, 22 without an S1 shape). In 1,219 of the 1,223 the frozen
  good g has exactly two needers, both big-top on g (**setting (H)**). In all 1,223 the dump lists a (T3) repair
  **without a helper** (a *plain swap*) whose new best owner is an agent that did not move.
- **Lemma G** (§2, any f, written proof, not yet refereed): the deficit after a (T3) role swap with at most one helper,
  seen from any free owner o that does not move:

  def(P′) ≤ |C| − (2 − |A|) − (2 − |B′_h|) − S_rest − κ.

  Here A is x's new base, B′_h the helper's (the term is absent without helper), S_rest counts the slots of the other
  free agents, C ⊆ J′ is a set of junk goods whose removal leaves o's bundle safe, and κ = 1 when the swap unfreezes
  z for o. **Corollary G1** is its value form: the least such C is computable from P alone, as a hitting set.
- **Structural existence theorems in (H)** (§3, written proofs, not yet refereed):
  - **Theorem W**: if the lower goods of x lie in J ∪ B_y1 ∪ B_y2, one of them is valued by a needer, and every other
    free agent is *tame* (its threats can be removed within its own slots), then an explicit plain swap gives
    def(P′) ≤ 0.
  - **Corollary N3**: at n = 3 these hypotheses always hold. So **at n = 3, f = 1, with two big-top needers, every
    state with def > 0 has a (T3) move without helper that lowers the deficit**, with no stuckness hypothesis.
  - **Theorem K**: a pair worth more than g to x unfreezes z for the other needer (κ = 1).
- **Coverage** (§4, EVIDENCE): **every one of the 1,223 f = 1 targets satisfies the hypotheses of W, K or G1 with a
  plain swap** (W at all 1,154 at n = 3 and at 15 at n = 4, K at 50, G1 at 4). SCAN_SUMMARY Every bound is asserted
  against the exact deficit, with no violation.
- **At n ≥ 4 a helper can be necessary** (§3.4, REFUTED row K4.TB.X): at a T3-stage state in (H) with n = 4, m = 8,
  x's best lower goods are a third agent's base, no plain swap exists at all, and only (T3) moves with that agent as
  helper lower the deficit (Lemma G certifies one). So no plain-swap statement, and in particular neither W nor K,
  covers the regime at n ≥ 4.
- **Open** (§5): the existence step at n ≥ 4. **Conjecture PS**: at every T3-stage state with f = 1 whose frozen good
  has two or more needers, Lemma G certifies a (T3) move with at most one helper that lowers the deficit. It holds at
  every target and at every such state of the scans (EVIDENCE), but it is not derived from the T3 stage.

## 1. The targets (EVIDENCE)

`k4/thetab_targets.py` (`results/k4_thetab/targets.log`) reads every T1-stuck record of PR #75's dumps
(`results/k4_dl13_stuck/stuck_*.jsonl.gz`, 13,971 records). It keeps the records at the **T3 stage** (no (T1), (T2)
or (T4) move lowers the deficit; `k4/dl13.md` §2.3) that none of C1 (Corollary 9.1), C2 (Corollary 11.1) or C3
(Corollary 8.2) of `k4/dl13.md` §4 certifies. Counts are of records, as in `k4/dl13.md`.

| class | f = 1 | f = 2 |
|---|---|---|
| S1 shape, every S1 triple θ-b | 1,199 | 43 |
| S1 shape, every S1 triple θ-a | 2 | 0 |
| no S1 shape | 22 | 77 |

These are the numbers of `k4/dl13.md` §2.3 and §6 item 2: 1,343 = 1,242 θ-b + 2 θ-a + 99 without an S1 shape.

At f = 1 (frozen agent x on g):
- In **1,219** of the 1,223 the needers of g are exactly two agents, both big-top on g, and x has four goods and is
  not big-top. These are all 1,154 records at n = 3 and 65 at n = 4. The other four are at n = 4: two θ-a records with
  needers 4 + 4 + BT (three needers), one θ-b record with needers 4 + BT, and one with 4 + BT + BT.
- **Repair shapes in the dump** (every improving (T3) move of each record). Every record has a repair without a
  helper whose best owner afterwards is a needer that did not move (all 1,199 θ-b, 2 θ-a, 22 without S1). Repairs
  without a helper owned by x itself (Lemma 8's mechanism) occur at 470 θ-b records.

So the repair to explain at the targets is a **plain swap**: z needs g and takes it, x takes A ⊆ J ∪ B_z, nobody else
moves, and an agent that did not move owns the bundle.

In the θ-b case the S1 repair fails (`k4/dl13.md` Lemma 10). That repair has the S1 owner o take g and x own
X ∪ {c}, but o is big-top on g and X ∪ {c} holds o's three lower goods. The plain swap does something else. Either
the *other* needer takes g and o (or a third agent) owns, or o takes g and the other needer owns. In both cases the
swapped needer is big-top, and holding its top it is threatened by almost nothing.

## 2. The deficit after a role swap

Notation of `k4/dl2.md` §4 and `k4/dl13.md` §1:
- a strict profile of a connected k = 4 core with ω ≥ 1, and P ∈ 𝒫 min-frozen with needed set 𝒩, frozen agents F
  and junk J; frozen agents hold one good each, so ω = |J| − S = m − 2n + |F| is the same for every min-frozen P;
- N_w(B) = {h ∈ R_w ∖ B : v_w(h) > v_w(B)}; θ_w(Z) = max_{h ∈ Z} v_w(Z ∖ h), and Z *threatens* w holding B if
  θ_w(Z) > v_w(B);
- a bundle of a free o is a Z with B_o ⊆ Z ⊆ B_o ∪ J; u_o(Z) counts the agents frozen in P but not once o's needs are
  taken from Z: a frozen w with base {g_w} is counted iff g_w ∉ N_o(Z) ∪ ⋃_{w′ ≠ o} N_{w′};
- Lemma H1: def(P) = ω + 2 − max (|Z| + u_o(Z)) over the free o and the safe bundles Z.

Two facts are used throughout.

**(θ)** For every w, every Z and every B: θ_w(Z) ≤ v_w(Z ∩ R_w). So Z does not threaten w holding B if
v_w(Z ∩ R_w) ≤ v_w(B).

**(BT)** Let z be *big-top* on its top g: |R_z| = 4, and with L_z := R_z ∖ {g} = {b, c, d} in decreasing order,
v_z(g) > v_z(b) + v_z(c). Then every Q ⊆ L_z with |Q| ≤ 2 has v_z(Q) < v_z(g), while v_z(L_z) > v_z(g) by strict
balance. So a set Z ∌ g with |Z ∩ L_z| ≤ 2 does not threaten z holding {g} (by (θ)).

**The role swap.** Let x ∈ F with B_x = {g}, let z be a free agent with g ∈ N_z, and let h be either absent or a free
agent h ≠ z (the *helper*). Put G := J ∪ B_z ∪ B_h (read B_h = ∅ without helper). Let A ⊆ G ∩ R_x with
1 ≤ |A| ≤ 2 and N_x(A) ⊆ 𝒩 (A is *admissible* for x), and, with a helper, B′_h ⊆ (G ∖ A) ∩ R_h with |B′_h| ≤ 2
and N_h(B′_h) ⊆ 𝒩. P′ is P with z on {g}, x on A and h on B′_h; every other agent keeps its base. When B′_h misses a
good of B_h this is the (T3) move of `k4/dl2.md` §3; without helper we call it a **plain swap**. By Lemma 6 of
`k4/dl2.md`, P′ is min-frozen with NA(P′) = 𝒩 and F(P′) = (F ∖ {x}) ∪ {z}, so ω(P′) = ω. Its junk is
J′ := G ∖ (A ∪ B′_h): the bases of P′ are those of P with {g} ∪ B_z ∪ B_h replaced by {g} ∪ A ∪ B′_h.

**Lemma G (the role swap seen from an unmoved owner).** Let P be min-frozen with ω ≥ 1, and let x, g, z, h, A, B′_h,
P′ and J′ be as above. Let o be a free agent of P with o ∉ {z, h}, and let S_rest := Σ (2 − |B_w|) over the free
agents w of P other than o, z and h. Let C ⊆ J′ be such that Y := (B_o ∪ J′) ∖ C threatens no agent w ≠ o holding
its base B′_w in P′. Then

  def(P′) ≤ |C| − (2 − |A|) − (2 − |B′_h|) − S_rest − u′_o(Y),

where the term (2 − |B′_h|) is absent without helper. Moreover z is counted in u′_o(Y), so the bound improves by
κ = 1, as soon as:
- g ∉ N_o(Y);
- v_x(A) > v_x(g);
- with a helper, g ∉ N_h(B′_h);
- no agent w ∉ {o, x, z, h} needs g in P.

*Proof.* o ∉ F(P′) = (F ∖ {x}) ∪ {z}, so o is free in P′ with base B_o. Its bundles in P′ are the sets between B_o
and B_o ∪ J′, and Y is one of them (C ⊆ J′, so B_o ⊆ Y). Y is safe in P′ by hypothesis.

The size of Y comes from the slot count. ω = |J| − S, where S = Σ (2 − |B_w|) over the free agents of P
(`k4/c4x.md` §1). The free agents of P are o, z, h (if any) and the agents counted in S_rest (x is frozen). So
|J| = ω + (2 − |B_o|) + (2 − |B_z|) + (2 − |B_h|) + S_rest. J, B_z and B_h are pairwise disjoint, and A, B′_h are
disjoint subsets of G, so |J′| = |J| + |B_z| + |B_h| − |A| − |B′_h|. Hence
|Y| = |B_o| + |J′| − |C| = ω + 2 + (2 − |A|) + (2 − |B′_h|) + S_rest − |C|.

Lemma H1 in P′ (min-frozen, ω(P′) = ω ≥ 1, o free) gives def(P′) ≤ ω + 2 − |Y| − u′_o(Y), which is the bound.

For the second claim: z ∈ F(P′) holds {g} and is counted iff g ∉ N_o(Y) ∪ ⋃_{w ≠ o} N′_w, the needs in P′. The
agents w ∉ {o, x, z, h} keep their bases, so N′_w = N_w. Further g ∉ N_z({g}), g ∉ N′_h = N_h(B′_h) by hypothesis,
and g ∉ N_x(A) iff v_x(A) ≥ v_x(g), i.e. v_x(A) > v_x(g) (strict profile, g ∉ A). ∎

Lemma G is Lemma H1 at P′ with the slot count made explicit. Its use is the *budget*: with def(P) ≥ 1, the swap lowers
the deficit as soon as some admissible C has |C| ≤ (2 − |A|) + (2 − |B′_h|) + S_rest + κ + def(P) − 1. It lowers it
to at most 0 if |C| ≤ (2 − |A|) + (2 − |B′_h|) + S_rest + κ. A helper adds the term 2 − |B′_h| to the budget, but it
also changes the agents Y must not threaten (h now holds B′_h) and it removes h's slots from S_rest.

**Corollary G1 (value form).** In the setting of Lemma G, for every agent w ≠ o let E_w be the set of minimal subsets
Q ⊆ R_w ∩ (B_o ∪ J′) with v_w(Q) > v_w(B′_w), where B′_w is w's base in P′ (B′_z = {g}, B′_x = A). If C ⊆ J′ meets
every set of ⋃_{w ≠ o} E_w, then Y := (B_o ∪ J′) ∖ C is safe in P′ and Lemma G's bound holds for this C. So, with
c* the least size of such a C,

  def(P′) ≤ c* − (2 − |A|) − (2 − |B′_h|) − S_rest − κ,

with κ = 1 if the four conditions of Lemma G hold for some C of size c*, and κ = 0 otherwise. Everything here is
computed from P and the move.

*Proof.* Y ∩ R_w ⊆ R_w ∩ (B_o ∪ J′). If v_w(Y ∩ R_w) > v_w(B′_w), then Y ∩ R_w contains a minimal such set Q ∈ E_w,
which C meets; but C ∩ Y = ∅. So v_w(Y ∩ R_w) ≤ v_w(B′_w) for every w ≠ o, and by (θ) Y threatens nobody. ∎

`k4/thetab_lib.lemma_g` computes c* exactly, and for κ it uses two sufficient conditions for g ∉ N_o(Y): g ∉ R_o; or
o is big-top on g, L_o ⊆ B_o ∪ J′ and C ⊆ J′ ∖ L_o (then L_o ⊆ Y and v_o(Y) ≥ v_o(L_o) > v_o(g)). In the
scans, **G1** names a plain swap that Corollary G1 certifies with def(P′) ≤ 0, and **G1h** a swap with one helper.

**Fact 0 (f = 1).** Let f = 1, F = {x}, B_x = {g}. Then 𝒩 = {g}, and:
- (a) g is the top of x;
- (b) every needer y of g has g as its top, B_y ≠ ∅, g ∉ B_y, and v_y(h) < v_y(B_y) for every h ∈ R_y ∖ (B_y ∪ {g});
- (c) every free agent w that does not need g has N_w = ∅ and B_w ≠ ∅;
- (d) if g has two needers, u_o ≡ 0 at P for every free o.

*Proof.*
- (a) N_x({g}) ⊆ 𝒩 = {g} and g ∉ N_x({g}), so N_x({g}) = ∅.
- (b) g ∈ N_y(B_y) ⊆ {g}, so v_y(g) > v_y(B_y). Every other good h ∉ B_y is not needed by y, so
  v_y(h) ≤ v_y(B_y), and the inequality is strict (distinct subset sums). So g is y's top. B_y ≠ ∅ because
  N_y(∅) = R_y ⊄ {g}.
- (c) N_w(B_w) ⊆ {g} ∖ {g} = ∅, and B_w ≠ ∅ as in (b).
- (d) x is counted in u_o(Z) only if g ∉ 𝒩₋ₒ, but a needer other than o puts g there. ∎

**Fact 1 (admissible sets of x at f = 1).** Let L_x := R_x ∖ {g} (two or three goods) and let p be its best good. A
set A ⊆ L_x with 1 ≤ |A| ≤ 2 is admissible iff every good of L_x ∖ A is worth less than v_x(A). So the admissible
sets are:
- {p};
- every pair containing p;
- if L_x = {p, q, r}, the pair {q, r} iff v_x(q) + v_x(r) > v_x(p).

Consequently:
- **(s2)** x holding an admissible pair A is threatened by no set Y with Y ∩ (A ∪ {g}) = ∅. Indeed Y ∩ R_x ⊆ L_x ∖ A
  is at most one good, worth less than v_x(A); apply (θ).
- **(s3)** x holding {p} is threatened by no Y ∌ g, p with v_x(Y ∩ L_x) ≤ v_x(p).

*Proof.* By Fact 0(a) g beats every good of L_x, so N_x(A) ⊆ {g} iff no good of L_x ∖ A beats v_x(A). Every other
good of L_x is worth less than p ≤ v_x(A) when p ∈ A, and the singletons other than {p} fail against p. ∎

## 3. Existence in setting (H)

**Setting (H).** f = 1, F = {x}, B_x = {g}, and the needers of g are exactly two agents y1 ≠ y2, both big-top on g (g
is their top by Fact 0(b)). Write:
- L_y := R_y ∖ {g} (three goods) for y ∈ {y1, y2}, and L_x, p as in Fact 1;
- T := the free agents other than y1 and y2 (they do not need g);
- B_T := ⋃_{w ∈ T} B_w and S_T := Σ_{w ∈ T} (2 − |B_w|).

For a plain swap σ(y_i, A), write z := y_i, o := y_{3−i} (the *other needer*) and J′ = (J ∪ B_z) ∖ A. Then
S_rest = S_T. The bases of P′ are {g} (z), A (x), B_o and those of T, and the rest is J′; so
B_o ∪ J′ = M ∖ ({g} ∪ A ∪ B_T).

A free agent w ∈ T is **tame in a pool Q after A** if some H_w ⊆ Q with |H_w| ≤ 2 − |B_w| has
v_w(R_w ∖ ({g} ∪ B_T ∪ A ∪ H_w)) ≤ v_w(B_w). *Tame* means tame in J after ∅. Then, by (θ), no set avoiding g, B_T, A
and H_w threatens w holding B_w.

### 3.1 Theorem W

**Theorem W.** Assume (H) and:
- (W1) L_x ⊆ J ∪ B_y1 ∪ B_y2;
- (W2) some good of L_x is valued by y1 or y2;
- (W3) every w ∈ T is tame.

Then there are i ∈ {1, 2} and an admissible A ⊆ (J ∪ B_{y_i}) ∩ L_x such that the plain swap σ(y_i, A) has
def(P′) ≤ |A| − 2 ≤ 0. In particular it lowers the deficit whenever def(P) > 0. A satisfies A ∩ L_{y_i} ≠ ∅, and
either |A| = 2, or A = {p} with v_x(L_x ∖ {p}) < v_x(p). `k4/thetab_lib.w1_construction` builds A as in the proof.

*Proof.* Let R′ := L_x ∖ {p} (one or two goods). Every chosen A will lie in J ∪ B_z and miss B_o, and meet L_z.

*Case 1: p ∈ B_{y_i}, or p ∈ J ∩ L_{y_i}, for some i.* Take z := y_i, o := y_{3−i}; then p ∈ L_z.
- If some s ∈ R′ is not in B_o, then s ∈ J ∪ B_z by (W1). Take A := {p, s}; it is admissible by Fact 1 and meets
  L_z in p.
- Otherwise R′ ⊆ B_o.
  - If R′ = {q, r} and v_x(q) + v_x(r) > v_x(p), swap the other way: z := y_{3−i}, A := {q, r} = B_z. A is admissible
    (Fact 1), meets L_z ⊇ B_z, and misses the base of y_i.
  - Else A := {p}. Here v_x(R′) < v_x(p): R′ is a single good worth less than p, or q + r < p.

*Case 2: otherwise.* By (W1), p ∈ J ∖ (L_y1 ∪ L_y2). By (W2) some s ∈ R′ lies in L_y1 ∪ L_y2. Choose i with
s ∈ L_{y_i} ∖ B_{y_{3−i}}: i = 1 if s ∈ L_y1 ∖ B_y2; otherwise s ∈ B_y2 ⊆ L_y2, and s ∉ B_y1 (disjoint bases), so
i = 2. Then s ∈ J ∪ B_{y_i} by (W1). Take A := {p, s}; it is admissible and meets L_z in s.

*The bound.* Let H := ⋃_{w ∈ T} H_w ⊆ J, so |H| ≤ S_T, and C := H ∩ J′. Apply Lemma G with o, without helper, and
Y := (B_o ∪ J′) ∖ C, which misses g, A, B_T and H. Safety of Y:
- z: Y ∩ L_z ⊆ L_z ∖ A has at most two goods; apply (BT);
- x: if |A| = 2, (s2); if A = {p}, Y ∩ L_x ⊆ R′ with v_x(R′) < v_x(p), so (s3);
- w ∈ T: Y ∩ R_w ⊆ R_w ∖ ({g} ∪ B_T ∪ H_w); apply (θ) and (W3).

So def(P′) ≤ |C| − (2 − |A|) − S_T ≤ |A| − 2. ∎

**Corollary N3 (three agents).** Let the core have n = 3 agents and f = 1. Let P be min-frozen with frozen agent x on
g, and suppose both other agents need g and are big-top on g. Then some plain swap gives def(P′) ≤ 0. So at every P
with def(P) > 0 some (T3) move without helper lowers the deficit. No stuckness hypothesis is needed.

*Proof.* The agents are x, y1, y2, and y1, y2 need g, so (H) holds with T = ∅, and (W3) is empty.
- (W1): every good other than g lies in J ∪ B_y1 ∪ B_y2, since B_x = {g}.
- (W2): by condition (C3) of a k = 4 core (K4.CORE), x has at most |R_x| − 2 = |L_x| − 1 private goods. So some
  good of L_x is valued by another agent, which is y1 or y2. ∎

This covers all 1,154 θ-b targets at n = 3, which include `dl13-n3m7-theta` (P = ({0, 2}, {1, 4}, {6}),
def(P) = 1). There the construction takes Case 1: p = 4, worth 6 to x = agent 2, lies in B_1, and q = 5 ∈ J lies
outside B_0. The swap is: agent 1 takes 6 and agent 2 takes {4, 5}. Agent 0 then owns {0, 1, 2, 3}, and
def(P′) = 0. The repair that `k4/dl13.md` reports (agent 2 takes {3, 4}, agent 0 owns {0, 1, 2, 5}, def(P′) = −1) is
the instance of Theorem K below.

### 3.2 Theorem K

**Theorem K (the unfreezing swap).** Assume (H), and let z ∈ {y1, y2} with o the other needer. Let A ⊆ (J ∪ B_z) ∩ L_x
be a pair with v_x(A) > v_x(g) (so N_x(A) = ∅), and set J′ := (J ∪ B_z) ∖ A. Suppose:
- (K1) A ∩ L_o = ∅ and L_o ∩ B_T = ∅;
- (K2) some C ⊆ J′ ∖ L_o with |C| ≤ S_T + 1 satisfies L_z ∩ (A ∪ B_T ∪ C) ≠ ∅ and
  v_w(R_w ∖ ({g} ∪ B_T ∪ A ∪ C)) ≤ v_w(B_w) for every w ∈ T.

Then def(σ(z, A)) ≤ 0.

(K2) holds in particular when every w ∈ T is tame in J′ ∖ L_o after A, and either L_z ∩ (A ∪ B_T) ≠ ∅ or some
e ∈ L_z ∖ (L_o ∪ B_T ∪ A) exists. In that case take C := ⋃ H_w ∪ {e}. Such an e lies in J′: it is not g, not in
B_T ∪ A, and not in B_o ⊆ L_o.

*Proof.* Y := (B_o ∪ J′) ∖ C = M ∖ ({g} ∪ A ∪ B_T ∪ C). Safety of Y:
- z: |Y ∩ L_z| ≤ 2 by (K2); apply (BT);
- x: (s2);
- w ∈ T: by (K2) and (θ).

z is counted (κ = 1 in Lemma G):
- v_x(A) > v_x(g);
- the agents of T do not need g (only y1, y2 do);
- L_o ⊆ Y, since L_o misses g, A, B_T (K1) and C ⊆ J′ ∖ L_o. So v_o(Y) ≥ v_o(L_o) > v_o(g) (strict balance), and
  g ∉ N_o(Y).

Lemma G: def(P′) ≤ |C| − 0 − S_T − 1 ≤ 0. ∎

### 3.3 Outside (H)

The four f = 1 targets outside (H) are covered by Corollary G1 with a plain swap. Each has a big-top needer z, and a
third or second needer whose slot pays for the removal that z's edge needs. Example: `hunt_n4_pure_s400k`, core
(m = 11, idx 1), profile 72,38,83,120, P = ({0}, {5}, {10}, {4}). There g = 10 has three needers. The swap:
- the big-top needer 0 takes g;
- x = agent 2 takes {3, 6};
- owner 1 keeps its base.

z's edge L_0 = {0, 2, 8} needs one removal. The needer 3 (base {4}, one slot) pays for it: |C| = 1 = S_rest, so
def(P′) ≤ 0 by Lemma G.

### 3.4 When a helper is needed

Theorems W and K, and every plain swap, need x's new base inside J ∪ B_z. When x's admissible sets all meet the base of
a third agent t ∈ T, no plain swap exists, and the repair must take t as helper. This happens at the T3 stage
(`attempts/k4-thetab-plain-swap-t3-stage.md`, found by the structured hunt `k4/thetab_scan.py hunt 1`): n = 4, m = 8,
- x = agent 0 with goods 0:12, 4:10, 5:9, 6:8; the needers 1 (0:13, 1:7, 2:5, 3:4) and 2 (0:15, 1:8, 2:6, 3:4),
  both big-top with the same goods; agent 3 with goods 1:8, 4:6, 5:7, 7:12;
- P = ({0}, {1}, {2, 3}, {4, 5}), J = {6, 7}, ω = 1, def(P) = 1; P is at the T3 stage and is a target in the sense
  of §1 (no S1 shape; C1, C2, C3 do not apply).

x's admissible sets are {4}, {4, 5}, {4, 6} and {5, 6}, and all of them meet B_3 = {4, 5}, so no plain swap exists. The
(T3) moves that lower the deficit (21 of them) all use agent 3 as helper. Corollary G1 certifies one: agent 1 takes
0, x takes {4}, and agent 3 gives up {4, 5} for its top 7 from the junk. Then J′ = {1, 5, 6}, and the owner is agent 2
(base {2, 3}). The sets of Corollary G1 are {5, 6} (x holding {4}), {1, 2, 3} (agent 1 holding {0}) and {1, 5}
(agent 3 holding {7}). C = {1, 5} meets all three, and the budget is (2 − |A|) + (2 − |B′_3|) + S_rest = 1 + 1 + 0.
So def(P′) ≤ 0, and def(P′) = 0 by both implementations (`attempts/k4_thetab_attempts.py`, case X3).

Here the helper is needed for x's sake, not the owner's: agent 3 holds the goods x needs. Theorems W and K have no
analogue for this case yet.

## 4. Coverage (EVIDENCE)

Every conclusion below is asserted against the exact deficits (`k4/dl13_stuck.Profile`, i.e. Lemma H1 on
`k4/suite/model.py`) wherever the hypotheses hold: Theorem W's def(P′) ≤ |A| − 2, K's def(P′) ≤ 0, and Lemma G's bound
(Corollary G1, least C computed) for every plain swap or swap with one helper and every unmoved free owner examined.
There is no violation anywhere.

**The targets** (`results/k4_thetab/targets.log`):

| f = 1 targets | Theorem W | Theorem K | Corollary G1 (plain swap) | none of these |
|---|---|---|---|---|
| θ-b, n = 3: 1,154 | 1,154 | | | 0 |
| θ-b, n = 4: 45 | 15 | 28 | 2 | 0 |
| θ-a, n = 4: 2 | | | 2 | 0 |
| no S1 shape, n = 4: 22 | | 22 | | 0 |
| **all: 1,223** | **1,169** | **50** | **4** | **0** |

(First applicable statement in the order W, K, G1.) So **every f = 1 target satisfies the hypotheses of Theorem W,
Theorem K or Corollary G1 with a plain swap**, each of which is a condition on P alone, and is repaired by the swap it
names.

**Scans** (`k4/thetab_scan.py`, `results/k4_thetab/scan_*.log`, table by `k4/thetab_table.py`). These cover every
def > 0 state with f = 1 of each profile of the inputs:
- the suite;
- #53's catalogues at 245040b (n = 3 every record; n = 4 every 4th; n = 5 every 10th);
- the hunt catalogues (every 4th);
- random n = 3 profiles of every certified n = 3 core (`k4_certs_3`, 500 per core);
- the structured hunts `hunt` (random cores built around a frozen x and two big-top needers) and `twin` (the two
  needers have the same goods, and x's third lower good is shared with the third agents).

Three kinds of states are classified:
- the states in (H) at every stage (T3 stage; T1-stuck but not at the T3 stage; other);
- the other states with two or more needers at the T3 stage;
- the states with one needer, where only G1 can apply.

Each cell reads: states / W, K or G1 applies (a plain swap) / only G1h applies (a swap with one helper) / some plain
swap lowers the deficit (exact). Every conclusion is asserted, and Corollary N3 is asserted at every n = 3 state in
(H). The last column counts T3-stage states where no (T3) move at all lowers the deficit (a failure of DL_RT4 at
f = 1).

SCAN_TABLE

SCAN_NOTES

## 5. What remains open, and candidates that fail

The existence step at f = 1 is proved where W, K or G1 applies. That includes every n = 3 state with two big-top
needers (Corollary N3), with or without the T3 stage. At n ≥ 4 the theorems need hypotheses, (W1)–(W3) or (K1)–(K2),
about where x's goods lie and about the other free agents. These are **not** consequences of the T3 stage as stated:

- *(H) does not cover every target*: 4 of the 1,223 have three needers or a non-big-top needer (§1). Smallest: n = 4,
  m = 9 (`gap_n4_3_s4000`, core (m = 9, idx 5) of `results/k4_certs_4_n4_3.json.gz`, profile 106,48,94,3).
- *No plain swap need exist at a T3-stage state in (H)*, so W, K and the plain form of G1 can all fail: n = 4, m = 8
  (§3.4).

What the data support is:

**Conjecture PS (role swap at f = 1).** At f = 1, at every T3-stage state with def(P) > 0 whose frozen good has two or
more needers, some (T3) move with at most one helper lowers the deficit, and Corollary G1 certifies one through a free
owner that does not move.

The first half is the T3-stage statement of `k4/dl13.md` §6 item 2 for these states (no f = 1 failure of it is known).
The second half asks that the repair be visible to Lemma G. A proof would have to show that the T3 stage forces the
other free agents, and the agents holding x's lower goods, to fit the budget of Lemma G: the analogue at n ≥ 4 of what
Corollary N3 gets for free at n = 3. At states that are not at the T3 stage plain swaps can fail (§5.1), so the
hypothesis must be used; the f = 0-like structure of the other free agents (Theorem Z′ of `k4/c4min_reduce.md` §2) is
the natural tool.

### 5.1 Failed candidates (`attempts/k4-thetab-*.md`, REFUTED row K4.TB.X)

Each candidate fails at the state given. The state's f, deficit, stage, needers and swaps are computed by two
implementations (`attempts/k4_thetab_attempts.py`: this file's code on PR #75's `Profile`, and main's
`k4/c4x_check.py` with the key, the T1 test, the needers, the plain swaps and the (T3) moves written separately).

| candidate | smallest failing state found | note |
|---|---|---|
| in (H), a plain swap lowers the deficit at **every** state with def > 0 (Corollary N3 at n = 3) | n = 4, m = 9: core (m = 9, idx 5) of `k4_certs_4_pure`, profile 38,20,245,105, P = ({0, 2}, {1, 3}, {5, 6}, {8}) | P is not T1-stuck; a third agent is threatened by the only two junk goods (`attempts/k4-thetab-plain-swap-everywhere.md`) |
| every f = 1 target is in (H) | n = 4, m = 9: core (m = 9, idx 5) of `k4_certs_4_n4_3`, profile 106,48,94,3, P = ({0, 7}, {8}, {4, 6}, {5}) | needers big-top and 4-good; G1 covers it (`attempts/k4-thetab-two-big-top-needers.md`) |
| in (H), at the **T3 stage**, a plain swap lowers the deficit (Conjecture PS in plain form; so also "W or K applies") | n = 4, m = 8: the hunt state of §3.4, P = ({0}, {1}, {2, 3}, {4, 5}) | no plain swap exists; only (T3) moves with a helper repair it, and G1h certifies one (`attempts/k4-thetab-plain-swap-t3-stage.md`) |
| W, K or G1 with a plain swap applies at every **T1-stuck** state in (H) | n = 4, m = 10: core (m = 10, idx 13) of `k4_certs_4_pure`, profile 60,8,93,84, P = ({0, 9}, {1, 5}, {8}, {4, 7}) | not key-optimal (a (T2) move helps); a plain swap still lowers the deficit, owned by x itself, and G1h certifies a swap with a helper (`attempts/k4-thetab-t1-stuck-cover.md`) |

## 6. f ≥ 2 (for proof/k4-f2)

The 43 θ-b and 77 non-S1 targets at f = 2 are left to proof/k4-f2, and there (T3⁺) replaces (T3). Two observations
come for free.
- Lemma G and Corollary G1 hold at every f as stated. Their proofs never use f = 1: the other frozen agents are among
  the agents Y must not threaten, and they have no slots. (A (T3) move is a (T3⁺) move with a chain of length one;
  Lemma G says nothing about longer chains.)
- On the data (`results/k4_thetab/targets.log`, rows "f>=2"):
  - every one of the 120 f = 2 target records has a plain swap that lowers the deficit; by PR #75's dumps, so does
    every one of the 800 T1-stuck records with f ≥ 2;
  - Corollary G1 (`k4/thetab_lib.g_certificates` on the plain swaps; the other frozen agents enter through their edges
    and through κ) certifies such a swap at all 120.

The structural existence statements of §3 are not extended to f ≥ 2 here.

## 7. Reproduce

```
mkdir -p k4/suite/.cache/gapbench
git archive 245040b results/k4_gap | tar -x -C k4/suite/.cache/gapbench      # #53's catalogues (k4/strategy.md §4)
sh k4/thetab_runs.sh                     # results/k4_thetab/: targets.log (§1, §4, §6) and the scans (§4, §5)
sh k4/thetab_runs2.sh                    # random n = 3 profiles, the twin hunts, attempts.log (§5.1)
python3 k4/thetab_table.py results/k4_thetab/scan_*.log                       # the table of §4
python3 k4/thetab_targets.py --show      # the smallest target of each class, printed in full
```

Code: `k4/thetab_lib.py` (setting (H), the swaps, Lemma G's value form `lemma_g` with the least removal set, the
hypotheses of W and K and W's construction, `theorems`), `k4/thetab_targets.py` (§1, §4, §6), `k4/thetab_scan.py`
(§4, §5), `k4/thetab_table.py` (§4), `attempts/k4_thetab_attempts.py` (§5.1, two implementations). They use PR #75's
`k4/dl13_stuck.py` (`Profile`) and `k4/dl13_lemmas.py` (`Ctx`) and `k4/suite/model.py`. Every run uses one process.
