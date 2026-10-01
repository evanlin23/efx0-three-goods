# The one-needer regime at the T3 stage (f = 1)

Workstream `proof/k4-oneneeder`. Ledger rows K4.ON.* (CONJECTURE / EVIDENCE until refereed). Task: `k4/dl13.md` §6
item 3 (on branch `proof/k4-dl13`, PR #75): at a T3-stage state whose frozen good has exactly one needer z, show that
the frozen agent x is big-top and that its lower goods are within reach of one helper, so that Corollary 8.2 of
`k4/dl13.md` §2.1 (the Lemma 7 swap) applies. Builds on `k4/dl2.md` §4 (Lemmas 1, 1′, 2, 3, 6, 7; PROVED rows
K4.DL2.MOVES, K4.DL2.DEF), `k4/dl13.md` §1–§3 (Lemmas 8, 10, Corollary 8.2, Proposition T; refereed in the PR #75
review), `k4/hall.md` §1 (Lemma H1, K4.HALL.COVER) and `k4/c4min_reduce.md` §1–§2 (Lemmas K, T and Theorem Z′,
K4.C4MIN.RED.Z, PROVED). Nothing here changes K4.D or K4.T.

(Since this work started, the coordinator reports DL_RT4 and the key-graph DL with single T3/T4 edges refuted at n = 5,
f = 3, by frozen-chain role swaps; the claims below are about f = 1, where that move is a plain (T3) swap.)

**Status: in progress.** This first version records the setting, two lemmas with written proofs, the swap in the case
where the best owner is the needer itself, and the data. Written proofs here are not yet refereed.

## 1. Setting

Notation of `k4/dl2.md` §4 and `k4/dl13.md` §1. A strict profile of a connected k = 4 core whose fewest frozen agents is
f = 1, with ω = 1 − (2n − m) ≥ 1. P ∈ 𝒫 min-frozen; its frozen agent is x with base {g}; 𝒩 = NA(P) = {g}; the *key* of
P is (x, g) (`k4/c4min_reduce.md` §1; there it is written (g, x)). By Lemma K of `k4/c4min_reduce.md`, g is x's top;
L := R_x ∖ {g} are x's *lower goods*. A *needer* is an agent z with g ∈ N_z; by Lemma T there, every needer has top g.
Every free agent that is not a needer has needs ⊆ 𝒩 = {g} not containing g, i.e. it is *need-free*: N_y(B_y) = ∅.
x is *big-top* if |R_x| = 4 and v_x(g) > v_x(b) + v_x(c) (b > c > d its lower goods); then (Lemma 8(a) of
`k4/c4min_f1.md`, or directly) a set Z ⊆ M ∖ {g} threatens x holding {g} iff L ⊆ Z and Z ≠ L.

def(P) = ω + 2 − V(P), V(P) := max (|Z| + u_o(Z)) over the free o and their safe bundles Z (Lemma H1). At f = 1,
u_o(Z) = 1 iff no agent other than o needs g and v_o(Z) > v_o(g) (`k4/dl13.md` §2.1, the term ι).

**The T3 stage at f = 1.** No (T4) move exists (one frozen agent), and (T1) ∪ (T2) are exactly the moves inside a key
(`k4/dl2.md` §3). So P is at the T3 stage iff def(P) > 0 and def(P) = def*(κ) := min{def(P′) : P′ min-frozen with key
κ = (x, g)}. P is *one-needer* if exactly one agent z needs g; z is free (x does not need its own base).

**An x-alone triple** at P is (o, X, c): o a best owner (Val_P(o) = V(P)), X an optimal bundle of o, c ∈ J ∖ X, such
that X ∪ {c} threatens x holding {g} and no agent w ∉ {o, x} holding B_w (the only blocker of c is x). This is the
strongest form of the frozen obstruction of `k4/dl13.md` §2.3 (row A4 there: a junk good of a best owner blocked by one
frozen agent alone).

## 2. Big-top keys have least deficit at most 1

**Lemma A.** Let κ = (x, g) be a key with x big-top on g (f = 1, ω ≥ 1). Then some min-frozen Q with key κ has
def(Q) ≤ 1, and def(Q) ≤ 0 if ω = 1. Consequently, at a T3-stage state P with key κ: ω ≥ 2, def(P) = 1 and
V(P) = ω + 1.

*Proof.* By Theorem Z′(ii) of `k4/c4min_reduce.md` §2 (configurations at the key exist by Lemma K there, since ω ≥ 1),
some configuration at κ (pairs Q_y ⊆ M ∖ {g} for y ≠ x with Q_y ∩ U_y admissible, pool L₀ with ω goods) has a
free-valid owner o: X := Q_o ∪ L₀ threatens no y ∉ {o, x} holding Q_y. Let Q be the pre-allocation with x on {g} and
B_y := Q_y ∩ U_y for every y ≠ x (U_y = R_y ∖ {g}). Each B_y is admissible for {g}, so by Lemma K Q is min-frozen with
key κ. X is a bundle of o in Q: B_o ⊆ Q_o ⊆ X, and the goods of X ∖ B_o (those of Q_o outside U_o, and the pool) lie in
no base of Q. X threatens no free y ≠ o holding B_y, since v_y(B_y) = v_y(Q_y) (the goods of Q_y ∖ U_y are worthless to
y, as g ∉ Q_y). If X does not threaten x, V(Q) ≥ |X| = ω + 2 and def(Q) ≤ 0; this is the case if ω = 1, since
|X| = 3 = |L| and a threat needs L ⊊ X. Otherwise L ⊆ X; as |B_o| ≤ 2 < |L|, some ℓ ∈ L ∖ B_o exists, and X ∖ {ℓ} is a
bundle of o that threatens nobody (it misses ℓ, and threats are monotone), so V(Q) ≥ ω + 1 and def(Q) ≤ 1 (Lemma H1).
At a T3-stage P with key κ, 0 < def(P) = def*(κ) ≤ def(Q) ≤ 1, and ω ≥ 2 by the case ω = 1. ∎

## 3. Need-free pre-allocations and what they exclude

**Lemma B.** At f ≥ 1 no pre-allocation (pairwise disjoint B_i ⊆ R_i, |B_i| ≤ 2) has every agent need-free.

*Proof.* It would lie in 𝒫 (NA = ∅ makes (V1), (V2) empty) with no frozen agent. ∎

Throughout §3–§4, P is min-frozen with f = 1, x on {g}, and z the only needer of g. A *swap* is the role swap of
`k4/dl13.md` §2.1: z takes {g}, x takes A, and a helper h (or none) takes B′_h, where (as in Corollary 8.2) B′_h is
admissible and g ∉ N_h(B′_h), i.e. B′_h is need-free; G := J ∪ B_z ∪ B_h.

**Corollary B1 (z cannot be bought off).** Let H be a set of free agents other than z with pairwise disjoint need-free
bases B′_h ⊆ J ∪ B_z ∪ ⋃_{h ∈ H} B_h (h ∈ H). Then every Q ⊆ (J ∪ B_z ∪ ⋃_{h ∈ H} B_h) ∖ ⋃_h B′_h with Q ⊆ R_z,
|Q| ≤ 2 has v_z(Q) < v_z(g). Likewise every S ⊆ L in that set with |S| ≤ 2 has v_x(S) < v_x(g).

*Proof.* Otherwise give z the base Q (resp. x the base S and z the base {g}), H their bases B′_h, x the base {g} (resp.
nothing more), and everybody else its base in P. z on Q is need-free because v_z(Q) > v_z(g) and g is z's top; x on S
likewise; z on {g} and x on {g} hold their tops; H is need-free by assumption; the others are free non-needers of P,
hence need-free. The bases are disjoint, inside the relevant sets, of at most two goods: Lemma B. ∎

With H = ∅ this contains Proposition T(d) of `k4/dl13.md`.

**Corollary B2 (when z is threatened after a swap).** In a swap with helper h (or none), a set Z ⊆ G ∖ B′_h threatens
z holding {g} only if z is big-top on g and L_z := R_z ∖ {g} ⊆ Z, so in particular only if B_z ⊆ Z.

*Proof.* θ_z(Z) = v_z(Z ∖ q) for some q ∈ Z; put Q′ := (Z ∖ q) ∩ R_z, so v_z(Q′) > v_z(g) and g ∉ Q′. If some subset of
Q′ with at most two goods were worth more than g to z, Corollary B1 (H = {h} or ∅) would be contradicted. So
|Q′| ≥ 3, i.e. Q′ = L_z (|R_z| = 4), and every pair of L_z is worth less than g: z is big-top on its top g. B_z ⊆ U_z =
L_z. ∎

**Corollary B3 (non-big-top x).** If x is not big-top, no rich pair S ⊆ L (v_x(S) > v_x(g)) lies in J ∪ B_z; and if
(o, X, c) is an x-alone triple, then o ≠ z and every rich pair S ⊆ X ∪ {c} meets B_o.

*Proof.* The first claim is Corollary B1 with H = ∅. Let Y := X ∪ {c}; it threatens x holding {g}, so
v_x(Y ∖ q) > v_x(g) for some q ∈ Y, and (Y ∖ q) ∩ R_x ⊆ L (g ∉ Y). A single lower good is worth less than g, so
(Y ∖ q) ∩ L has two goods, which form a rich pair inside Y, or three (x has four goods), and then {b, c} ⊆ Y is rich
since x is not big-top. If o = z, or if a rich pair S ⊆ Y misses B_o, then S ⊆ J ∪ B_z (Y ⊆ B_o ∪ J), against the
first claim. ∎

## 4. The swap from an x-alone triple

**Proposition C (the needer is the owner).** Let P be at the T3 stage (f = 1), x big-top, z the only needer of g, and
(z, X, c) an x-alone triple with u_z(X) = 0. Then the swap without helper (z takes {g}, x takes A := {b, c_x}, its two
best lower goods) gives def(P′) ≤ 0 < def(P), with x's bundle Z := Y or Y ∖ {ℓ} (Y := X ∪ {c}) — unless R_z = R_x and
ω ≥ 3.

*Proof.* By Lemma A, def(P) = 1 and |X| = V(P) = ω + 1, so |Y| = ω + 2. Y threatens x, so L ⊆ Y ⊆ W_z = J ∪ B_z = G;
A ⊆ L is admissible for x (its needs are {g}). By Lemma 6 P′ is min-frozen with key (z, g), and nobody but z needs g in
P′ (the other agents keep their needs). Y threatens no agent w ∉ {x, z} holding B_w (x-alone).
- If Y does not threaten z holding {g}, Z := Y is a safe bundle of x in P′ containing L, and Corollary 8.2 gives
  def(P′) ≤ ω + 1 − |Y| = −1.
- Otherwise, by Corollary B2 (no helper), z is big-top on g and L_z ⊆ Y. If L_z ≠ L, take ℓ ∈ L_z ∖ L and Z := Y ∖ {ℓ}:
  Z ⊇ L ⊇ A, Z ∩ R_z ⊆ L_z ∖ {ℓ} is worth less than g to z (z big-top), Z ⊆ Y threatens no w ∉ {x, z}, and Corollary
  8.2 gives def(P′) ≤ ω + 1 − (ω + 1) = 0.
- If L_z = L and ω = 2: if L ⊆ X then X = L (X is safe), so v_z(X) > v_z(g) (z big-top) and u_z(X) = 1, excluded;
  so c ∈ L and Z := L is a safe bundle of x in P′ (it is not a proper superset of L_z = L, and L ⊆ Y), with
  |Z| = 3 = ω + 1: def(P′) ≤ 0. ∎

The cases u_z(X) = 1, R_z = R_x with ω ≥ 3, and best owners o ≠ z are treated in §5 (to come).

## 6. Data (EVIDENCE)

`k4/oneneeder.c` (driver `k4/oneneeder_run.py`) enumerates the min-frozen class of every profile with f = 1, computes
every deficit by Lemma H1, the least deficit of every key, and at every one-needer T3-stage state tests: x big-top;
def(P) = 1; an x-alone triple (with o ≠ z, with o = z); u at a best owner; Corollary 8.2 with at most one helper
(asserting its conclusion against the exact deficit of the swapped state, looked up in the class); some improving (T3)
move (exact scan); R_z = R_x.

Its counts agree, profile by profile, with a Python computation on `k4/dl13_stuck.py`'s model (the T1-stuck dumps of
`k4/dl13.md` §1, on branch `proof/k4-dl13`): 2,541 profiles with f = 1, 1,009 one-needer T3-stage states, Corollary
8.2 applicable at all 1,009 (`k4/dl13_lemmas.py`'s C3 test), 0 mismatches.

| input | profiles | f = 1, ω ≥ 1 | T3-stage states | one needer | x big-top | def = 1 | x-alone triple (o ≠ z / o = z) | u at a best owner | Cor. 8.2 (no helper / best-owner helper / other helper) | R_z = R_x |
|---|---|---|---|---|---|---|---|---|---|---|
| `k4/dl13.md` §1 dumps, f = 1 profiles | 2,541 | 2,541 | 10,621 | 1,009 | 1,009 | 1,009 | 1,009 (917 / 375) | 0 | 1,009 (536 / 917 / 90) | 0 |
| n = 3, 20,000 random per core (seed 11) | 1,020,000 | 28,055 | 1,104 | 183 | 183 | 183 | 183 (160 / 80) | 0 | 183 (111 / 160 / 22) | 0 |

At every T3-stage state of both inputs (one needer or not) some (T3) move lowers the deficit.

## 7. Reproduce

```
python3 k4/oneneeder_run.py certs results/k4_certs_3.json.gz --sample=20000 --seed=11 \
  --dump=results/k4_oneneeder/certs3_r20000_s11.jsonl.gz --rep=200
```
