# The θ-b case and the non-S1 T3-stage states at f = 1: the plain swap

Workstream `proof/k4-thetab` (PR #85). Ledger rows K4.TB.*. Task: `k4/dl13.md` §6 item 2. Builds on `k4/dl2.md`
§3–§4 (the moves (T1)–(T3); Lemmas 1, 6; refereed, K4.DL2.MOVES), `k4/dl13.md` (the T3 stage, the targets, C1–C3;
PR #75, merged), `k4/hall.md` §1 (Lemma H1, K4.HALL.COVER) and `k4/c4x.md` §1 (𝒫, needs, frozen agents, slots,
deficit). Nothing here changes K4.D or K4.T.

**Context.** The coordinator reports that DL_RT4 (and key-graph DL with single (T3) or (T4) edges) is refuted at n = 5,
f = 3. The data are on cloud branches compute/k4-rt4-n5b and -n5c (`results/k4_rt4/n5*_FAILURES.md`), and the ledger
statuses are the coordinator's to change. The new target relation is R_C = (T1) ∪ (T2) ∪ (T3⁺) ∪ (T4), where (T3⁺) is
the frozen-chain role swap. At f = 1, (T3⁺) = (T3), so this file's question is unchanged. Everything here is at
f = 1. The f ≥ 2 targets are left to proof/k4-f2 (§6).

**Summary.**
- **The targets** (§1, EVIDENCE). These are the T3-stage records of PR #75's dumps that C1, C2 and C3 do not certify:
  1,343 records, 1,223 of them at f = 1 (1,199 θ-b, 2 θ-a, 22 without an S1 shape). In 1,219 of the 1,223 the frozen
  good g has exactly two needers, both big-top on g (**setting (H)**). In all 1,223 the dump lists a (T3) repair
  **without a helper** whose new best owner is a needer that did not move.
- **The repair is a plain swap** (§2, written proofs, not yet refereed). In a plain swap a big-top needer z takes g, x
  takes one or two goods of J ∪ B_z, and nobody else moves. **Lemma G** gives the deficit after a plain swap through
  any unmoved owner o:
  def(P′) ≤ |C| − (2 − |A|) − S_oz − κ.
  Here C is a set of junk goods whose removal leaves o's bundle safe, S_oz counts the slots of the other free agents,
  and κ = 1 when the swap unfreezes z for o. A big-top z holding its top is threatened only by bundles that contain all
  three of its lower goods. x holding an admissible pair is never threatened by a set avoiding g and that pair. So the
  only real constraints come from the other free agents.
- **Structural existence theorems** (§3, written proofs, not yet refereed):
  - **Theorem W** (in (H)): if the lower goods of x lie in J ∪ B_y1 ∪ B_y2, one of them is valued by a needer, and
    every other free agent is *tame* (its threats can be removed within its own slots), then an explicit plain swap
    gives def(P′) ≤ 0.
  - **Corollary N3**: at n = 3 these hypotheses always hold. So **at n = 3, f = 1, with two big-top needers, every
    state with def > 0 has a (T3) move without helper that lowers the deficit**, with no stuckness hypothesis.
  - **Theorem K**: a pair worth more than g to x unfreezes z for the other needer (κ = 1).
  - **Corollary G1** (the budget form of Lemma G at f = 1): any owner, any number of needers.

  Each of W, K, G1 is a condition on P alone that names the swap.
- **Coverage** (§4, EVIDENCE): **every one of the 1,223 f = 1 targets satisfies the hypotheses of W, K or G1** (W at
  all 1,154 at n = 3 and at 15 at n = 4, K at 50, G1 at 4). Every bound is asserted against the exact deficit, with no
  violation. At the 120 f = 2 targets Lemma G (which holds at every f) certifies a plain swap too (§6).
- **Open** (§5): the existence step at n ≥ 4. The hypotheses of W and K are not consequences of the T3 stage as stated
  (smallest failures in §5). They hold at every target, and Lemma G certifies a plain swap at every T3-stage state of
  the scans (Conjecture PS, EVIDENCE).

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

So the repair to explain is a **plain swap**: z needs g and takes it, x takes A ⊆ J ∪ B_z, nobody else moves, and an
agent that did not move owns the bundle.

In the θ-b case the S1 repair fails (`k4/dl13.md` Lemma 10). That repair has the S1 owner o take g and x own
X ∪ {c}, but o is big-top on g and X ∪ {c} holds o's three lower goods. The plain swap does something else. Either
the *other* needer takes g and o (or a third agent) owns, or o takes g and the other needer owns. In both cases the
swapped needer is big-top, and holding its top it is threatened by almost nothing.

## 2. The deficit after a plain swap

Notation of `k4/dl2.md` §4 and `k4/dl13.md` §1:
- a strict profile of a connected k = 4 core with ω ≥ 1, and P ∈ 𝒫 min-frozen with needed set 𝒩, frozen agents F
  and junk J;
- θ_w(Z) = max_{h ∈ Z} v_w(Z ∖ h), and Z *threatens* w holding B if θ_w(Z) > v_w(B);
- a bundle of a free o is a Z with B_o ⊆ Z ⊆ B_o ∪ J; u_o(Z) counts the frozen agents unfrozen by o's needs from Z;
- Lemma H1: def(P) = ω + 2 − max (|Z| + u_o(Z)) over the free o and the safe bundles Z.

Two facts are used throughout.

**(θ)** For every w, every Z and every B: θ_w(Z) ≤ v_w(Z ∩ R_w). So Z does not threaten w holding B if
v_w(Z ∩ R_w) ≤ v_w(B).

**(BT)** Let z be *big-top* on its top g: |R_z| = 4, and with L_z := R_z ∖ {g} = {b, c, d} in decreasing order,
v_z(g) > v_z(b) + v_z(c). Then every Q ⊆ L_z with |Q| ≤ 2 has v_z(Q) < v_z(g), while v_z(L_z) > v_z(g) by strict
balance. So a set Z ∌ g with |Z ∩ L_z| ≤ 2 does not threaten z holding {g} (by (θ)).

**The plain swap.** Let x ∈ F with B_x = {g}, and let z be a free agent with g ∈ N_z. Let A ⊆ (J ∪ B_z) ∩ R_x with
1 ≤ |A| ≤ 2 and N_x(A) ⊆ 𝒩 (A is *admissible* for x). σ(z, A) is the pre-allocation P′ where z holds {g}, x holds A
and every other agent keeps its base. It is the (T3) move of `k4/dl2.md` §3 without a helper. By Lemma 6 of
`k4/dl2.md` (H = ∅), P′ is min-frozen with NA(P′) = 𝒩, F(P′) = (F ∖ {x}) ∪ {z} and ω(P′) = ω. Its junk is
J′ := (J ∪ B_z) ∖ A.

**Lemma G (the plain swap seen from an unmoved owner).** Let P be min-frozen with ω ≥ 1, and let x, g, z, A, P′ and
J′ be as above. Let o be a free agent of P with o ≠ z. Write S_oz := Σ (2 − |B_w|) over the free agents w of P other
than o and z. Let C ⊆ J′ be such that Y := (B_o ∪ J′) ∖ C threatens no agent w ≠ o holding its base in P′. That is,
x holds A, z holds {g}, and every other agent holds B_w. Then

  def(P′) ≤ |C| − (2 − |A|) − S_oz − u′_o(Y).

Moreover z is counted in u′_o(Y), so the bound improves by κ = 1, as soon as three conditions hold:
- g ∉ N_o(Y);
- v_x(A) > v_x(g);
- no agent w ∉ {o, x, z} needs g.

*Proof.* o ∉ F(P′) = (F ∖ {x}) ∪ {z}, so o is free in P′ with base B_o. Its bundles in P′ are the sets between B_o
and B_o ∪ J′, and Y is one of them (C ⊆ J′, so B_o ⊆ Y). Y is safe in P′ by hypothesis.

The size of Y comes from the slot count. ω = |J| − S, where S = Σ (2 − |B_w|) over the free agents of P
(`k4/c4x.md` §1). The free agents of P are o, z and the agents counted in S_oz (x is frozen). So
|J| = ω + (2 − |B_o|) + (2 − |B_z|) + S_oz. Since A ⊆ J ∪ B_z and J ∩ B_z = ∅, |J′| = |J| + |B_z| − |A|. Hence
|Y| = |B_o| + |J′| − |C| = ω + 2 + (2 − |A|) + S_oz − |C|.

Lemma H1 in P′ (min-frozen, ω ≥ 1, o free) gives def(P′) ≤ ω + 2 − |Y| − u′_o(Y), which is the bound.

For the second claim: z ∈ F(P′) holds {g} and is counted iff g ∉ N_o(Y) ∪ 𝒩′₋ₒ. Here
𝒩′₋ₒ = N_x(A) ∪ N_z({g}) ∪ ⋃_{w ∉ {o,x,z}} N_w, since every other agent keeps its base and needs. Now g ∉ N_z({g}),
and g ∉ N_x(A) iff v_x(A) ≥ v_x(g), i.e. v_x(A) > v_x(g) (strict profile, g ∉ A). ∎

Lemma G is Lemma H1 at P′ with the slot count made explicit. Its use is the *budget*: with def(P) ≥ 1, the swap lowers
the deficit as soon as some admissible C has |C| ≤ (2 − |A|) + S_oz + κ + def(P) − 1. It lowers it to at most 0 if
|C| ≤ (2 − |A|) + S_oz + κ.

The removal set C must protect three kinds of agents.
- **z holding {g}**: if z is big-top on g, by (BT) it suffices that |Y ∩ L_z| ≤ 2. This is automatic when
  A ∩ L_z ≠ ∅, or when some good of L_z lies in another agent's base; otherwise one good of L_z ∩ J′ in C suffices.
- **x holding A**: see Fact 1 below.
- **every other agent w holding B_w**: by (θ), it suffices that v_w(Y ∩ R_w) ≤ v_w(B_w).

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

**Corollary G1 (the budget form at f = 1).** Let f = 1 and let z be a needer of g that is big-top on g. Let A be an
admissible pair for x inside J ∪ B_z, and let o ≠ z be free. Let R be the set of free agents other than o and z, let
B_R be the union of their bases and S_R := Σ_{w ∈ R} (2 − |B_w|) (= S_oz). Suppose some C ⊆ J′ with |C| ≤ S_R
satisfies:
- L_z ∩ (A ∪ B_R ∪ C) ≠ ∅;
- v_w(R_w ∖ ({g} ∪ B_R ∪ A ∪ C)) ≤ v_w(B_w) for every w ∈ R.

Then def(σ(z, A)) ≤ 0.

*Proof.* At f = 1 the bases of P′ are {g} (z), A (x), B_o, and B_R, and the rest is J′. So
Y := (B_o ∪ J′) ∖ C = M ∖ ({g} ∪ A ∪ B_R ∪ C). Safety of Y:
- z: Y misses a good of L_z, so |Y ∩ L_z| ≤ 2; apply (BT);
- x: (s2);
- w ∈ R: Y ∩ R_w = R_w ∖ ({g} ∪ B_R ∪ A ∪ C); apply (θ).

Lemma G: def(P′) ≤ |C| − 0 − S_R ≤ 0. ∎

The removal set C may serve several agents at once. In the simplest case every w ∈ R is **tame in J′ after A**: some
H_w ⊆ J′ with |H_w| ≤ 2 − |B_w| has v_w(R_w ∖ ({g} ∪ B_R ∪ A ∪ H_w)) ≤ v_w(B_w). If moreover A ∩ L_z ≠ ∅, then
C := ⋃ H_w works.

## 3. Existence in setting (H)

**Setting (H).** f = 1, F = {x}, B_x = {g}, and the needers of g are exactly two agents y1 ≠ y2, both big-top on g (g
is their top by Fact 0(b)). Write:
- L_y := R_y ∖ {g} (three goods) for y ∈ {y1, y2}, and L_x, p as in Fact 1;
- T := the free agents other than y1 and y2 (they do not need g);
- B_T := ⋃_{w ∈ T} B_w and S_T := Σ_{w ∈ T} (2 − |B_w|).

For a swap σ(y_i, A), write z := y_i, o := y_{3−i} (the *other needer*) and J′ = (J ∪ B_z) ∖ A. Then S_oz = S_T.

**Theorem W.** Assume (H) and:
- (W1) L_x ⊆ J ∪ B_y1 ∪ B_y2;
- (W2) some good of L_x is valued by y1 or y2;
- (W3) every w ∈ T is **tame**: some H_w ⊆ J with |H_w| ≤ 2 − |B_w| has v_w(R_w ∖ ({g} ∪ B_T ∪ H_w)) ≤ v_w(B_w).

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

*The bound.* Let H := ⋃_{w ∈ T} H_w ⊆ J, so |H| ≤ S_T, and C := H ∩ J′. Lemma G with Y := (B_o ∪ J′) ∖ C, which
misses g, A, B_T and H. Safety of Y:
- z: Y ∩ L_z ⊆ L_z ∖ A has at most two goods; apply (BT);
- x: if |A| = 2, (s2); if A = {p}, Y ∩ L_x ⊆ R′ with v_x(R′) < v_x(p), so (s3);
- w ∈ T: Y ∩ R_w ⊆ R_w ∖ ({g} ∪ B_T ∪ H_w); apply (θ) and (W3).

So def(P′) ≤ |C| − (2 − |A|) − S_T ≤ |A| − 2. ∎

**Corollary N3 (three agents).** Let the core have n = 3 agents, f = 1, and let both needers of the frozen good g be
big-top on g. Then at **every** min-frozen P, some plain swap gives def(P′) ≤ 0. So at every P with def(P) > 0 some
(T3) move without helper lowers the deficit. No stuckness hypothesis is needed.

*Proof.* The agents are x, y1, y2, and both others need g, so (H) holds with T = ∅, and (W3) is empty.
- (W1): every good other than g lies in J ∪ B_y1 ∪ B_y2, since B_x = {g}.
- (W2): by condition (C3) of a k = 4 core (K4.CORE), x has at most |R_x| − 2 = |L_x| − 1 private goods. So some
  good of L_x is valued by another agent, which is y1 or y2. ∎

This covers all 1,154 θ-b targets at n = 3, which include `dl13-n3m7-theta` (P = ({0, 2}, {1, 4}, {6}),
def(P) = 1). There the construction takes Case 1: p = 4, worth 6 to x = agent 2, lies in B_1, and q = 5 ∈ J lies
outside B_0. The swap is: agent 1 takes 6 and agent 2 takes {4, 5}. Agent 0 then owns {0, 1, 2, 3}, and
def(P′) = 0. The repair that `k4/dl13.md` reports (agent 2 takes {3, 4}, agent 0 owns {0, 1, 2, 5}, def(P′) = −1) is
the instance of Theorem K below.

**Theorem K (the unfreezing swap).** Assume (H), and let z ∈ {y1, y2} with o the other needer. Let A ⊆ (J ∪ B_z) ∩ L_x
be a pair with v_x(A) > v_x(g) (so N_x(A) = ∅), and set J′ := (J ∪ B_z) ∖ A. Suppose:
- (K1) A ∩ L_o = ∅ and L_o ∩ B_T = ∅;
- (K2) some C ⊆ J′ ∖ L_o with |C| ≤ S_T + 1 satisfies L_z ∩ (A ∪ B_T ∪ C) ≠ ∅ and
  v_w(R_w ∖ ({g} ∪ B_T ∪ A ∪ C)) ≤ v_w(B_w) for every w ∈ T.

Then def(σ(z, A)) ≤ 0.

(K2) holds in particular when every w ∈ T is tame in J′ ∖ L_o after A (sets H_w as in Corollary G1, inside J′ ∖ L_o)
and either L_z ∩ (A ∪ B_T) ≠ ∅ or some e ∈ L_z ∖ (L_o ∪ B_T ∪ A) exists. In that case take C := ⋃ H_w ∪ {e}. Such
an e lies in J′: it is not g, not in B_T ∪ A, and not in B_o ⊆ L_o.

*Proof.* As in Corollary G1, Y := (B_o ∪ J′) ∖ C = M ∖ ({g} ∪ A ∪ B_T ∪ C). Safety of Y:
- z: |Y ∩ L_z| ≤ 2 by (K2); apply (BT);
- x: (s2);
- w ∈ T: by (K2) and (θ).

z is counted (κ = 1 in Lemma G):
- v_x(A) > v_x(g);
- the agents of T do not need g (only y1, y2 do);
- L_o ⊆ Y, since L_o misses g, A, B_T (K1) and C ⊆ J′ ∖ L_o. So v_o(Y) ≥ v_o(L_o) > v_o(g) (strict balance), and
  g ∉ N_o(Y).

Lemma G: def(P′) ≤ |C| − 0 − S_T − 1 ≤ 0. ∎

**Theorem S (the single-good swap).** Assume (H), and let z ∈ {y1, y2} with o the other needer and p ∈ J ∪ B_z. Put
A := {p}, J′ := (J ∪ B_z) ∖ {p} and W′ := B_o ∪ J′. Suppose every w ∈ T is tame in J′ after A (as after Corollary G1,
with R = T). Suppose also that one good e ∈ J′ meets:
- L_z, if L_z ⊆ W′;
- every subset Q ⊆ (L_x ∖ {p}) ∩ W′ with v_x(Q) > v_x(p).

Then def(σ(z, A)) ≤ 0.

*Proof.* C := H ∪ {e}, so |C| ≤ S_T + 1. Lemma G gives def(P′) ≤ |C| − 1 − S_T ≤ 0. Safety of Y:
- z: |Y ∩ L_z| ≤ 2, by (BT);
- x: Y ∩ L_x contains no such Q, so v_x(Y ∩ L_x) ≤ v_x(p), by (s3);
- T: by (θ). ∎

(Theorem S is not needed for the targets; it is listed because `k4/thetab_scan.py` checks it.)

## 4. Coverage (EVIDENCE)

Every conclusion below is asserted against the exact deficits (`k4/dl13_stuck.Profile`, i.e. Lemma H1 on
`k4/suite/model.py`) wherever the hypotheses hold: Theorem W's def(P′) ≤ |A| − 2, K's, S's and G1's def(P′) ≤ 0, and
Lemma G's bound for every (z, A, o) with the least removal set computed from P. There is no violation anywhere.

**The targets** (`results/k4_thetab/targets.log`):

| f = 1 targets | Theorem W | Theorem K | Corollary G1 | none of these | Lemma G, least C computed |
|---|---|---|---|---|---|
| θ-b, n = 3: 1,154 | 1,154 | | | 0 | 1,154 |
| θ-b, n = 4: 45 | 15 | 28 | 2 | 0 | 45 |
| θ-a, n = 4: 2 | | | 2 | 0 | 2 |
| no S1 shape, n = 4: 22 | | 22 | | 0 | 22 |
| **all: 1,223** | **1,169** | **50** | **4** | **0** | **1,223** |

(First applicable statement in the order W, K, G1.) So **every f = 1 target satisfies the hypotheses of Theorem W,
Theorem K or Corollary G1**, each of which is a condition on P alone, and is repaired by the plain swap it names.

The four targets outside (H) are covered by G1: each has a big-top needer z, and a third or second needer whose slot
pays for the removal that z's edge needs. Example: `hunt_n4_pure_s400k`, core (m = 11, idx 1), profile
72,38,83,120, P = ({0}, {5}, {10}, {4}). There g = 10 has three needers. The swap:
- the big-top needer 0 takes g;
- x = agent 2 takes {3, 6};
- owner 1 keeps its base.

z's edge L_0 = {0, 2, 8} needs one removal. The needer 3 (base {4}, one slot) pays for it: |C| = 1 = S_R, so
def(P′) ≤ 0.

**Scans** (`k4/thetab_scan.py`, `results/k4_thetab/scan_*.log`; inputs as in `k4/dl13.md` §1): every def > 0 state
with f = 1 and at least two needers, at every stage. *Counts to be filled in when the runs of `k4/thetab_runs.sh`
finish.*

## 5. What remains open, and candidates that fail

The existence step at f = 1 is proved where W, K or G1 applies. That includes every n = 3 state with two big-top
needers (Corollary N3), with or without the T3 stage. At n ≥ 4 the theorems need hypotheses, (W1)–(W3) or (K1)–(K3),
about where x's goods lie and about the other free agents. These are **not** consequences of the T3 stage as stated:

- *(H) does not cover every target*: 4 of the 1,223 have three needers or a non-big-top needer (§1). Smallest: n = 4,
  m = 9 (`gap_n4_3_s4000`, core (m = 9, idx 5) of `results/k4_certs_4_n4_3.json.gz`, profile 106,48,94,3).
- *W or K need not apply at a T3-stage (H) state*: smallest in the suite, n = 4, m = 11 (`red-b1-blocked-improvement`;
  Lemma G certifies a swap there with |C| = 1 = κ).

What the data support is:

**Conjecture PS (plain swap at f = 1).** At f = 1, at every T3-stage state whose frozen good has two or more needers,
some plain swap of a big-top needer lowers the deficit, certified by Lemma G with an unmoved owner.

A proof would have to show that the T3 stage forces the other free agents to fit the budget of Lemma G, the analogue
at n ≥ 4 of what Corollary N3 gets for free at n = 3. At states that are not at the T3 stage, plain swaps can fail
(§5.1). So the hypothesis must be used, and the argument is the f = 0-like structure of the other free agents (Theorem
Z′ of `k4/c4min_reduce.md` §2 is the natural tool).

### 5.1 Failed candidates (`attempts/k4-thetab-*.md`, REFUTED row K4.TB.X)

Each candidate fails at the state given. The state's f, deficit, stage, needers and plain swaps are computed by two
implementations (`attempts/k4_thetab_attempts.py`: this file's code on PR #75's `Profile`, and main's
`k4/c4x_check.py` with the key, the T1 test, the needers and the plain swaps written separately).

| candidate | smallest failing state | note |
|---|---|---|
| in (H), a plain swap lowers the deficit at **every** state with def > 0 (Corollary N3 at n = 3) | n = 4, m = 9: core (m = 9, idx 5) of `k4_certs_4_pure`, profile 38,20,245,105, P = ({0, 2}, {1, 3}, {5, 6}, {8}) | P is not T1-stuck; a third agent is threatened by the only two junk goods (`attempts/k4-thetab-plain-swap-everywhere.md`) |
| every f = 1 target is in (H) | n = 4, m = 9: core (m = 9, idx 5) of `k4_certs_4_n4_3`, profile 106,48,94,3, P = ({0, 7}, {8}, {4, 6}, {5}) | needers big-top and 4-good; G1 covers it (`attempts/k4-thetab-two-big-top-needers.md`) |
| W, K or G1 applies at every T3-stage state with two needers | n = 3, m = 6: core (m = 6, idx 8) of `k4_certs_3`, profile 11,11,246, P = ({4}, {1, 3}, {5}) | neither needer big-top; Lemma G still certifies a plain swap (`attempts/k4-thetab-structural-cover.md`) |

## 6. f ≥ 2 (for proof/k4-f2)

The 43 θ-b and 77 non-S1 targets at f = 2 are left to proof/k4-f2, and there (T3⁺) replaces (T3). Two observations
come for free.
- Lemma G holds at every f as stated. Its proof never uses f = 1: the other frozen agents are among the agents Y must
  not threaten, and they have no slots.
- On the data (`results/k4_thetab/targets.log`, rows "f>=2"):
  - every one of the 120 f = 2 target records has a plain swap (a (T3) move without helper) that lowers the deficit;
    by PR #75's dumps, so does every one of the 800 T1-stuck records with f ≥ 2;
  - Lemma G, with the least removal set computed from P (`k4/thetab_lib.swap_bound_any_f`; other frozen agents
    counted only through κ), certifies such a swap at all 120.

The structural existence statements of §3 are not extended to f ≥ 2 here.

## 7. Reproduce

```
mkdir -p k4/suite/.cache/gapbench
git archive 245040b results/k4_gap | tar -x -C k4/suite/.cache/gapbench      # #53's catalogues (k4/strategy.md §4)
sh k4/thetab_runs.sh                     # results/k4_thetab/: targets.log (§1, §4, §6) and the scans (§4, §5)
sh k4/thetab_runs2.sh                    # random n = 3 profiles, the twin hunts, attempts.log (§5.1)
python3 k4/thetab_targets.py --show      # the smallest target of each class, printed in full
```

Code: `k4/thetab_lib.py` (setting (H), the swaps, Lemma G's least removal set `swap_bound`, the hypotheses of W, K, S,
G1 and W's construction), `k4/thetab_targets.py` (§1, §4, §6), `k4/thetab_scan.py` (§4, §5),
`attempts/k4_thetab_attempts.py` (§5.1, two implementations). They use PR #75's `k4/dl13_stuck.py` (`Profile`) and
`k4/dl13_lemmas.py` (`Ctx`) and `k4/suite/model.py`.
