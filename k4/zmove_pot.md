# Theorem ZMOVE by a potential argument

Workstream `proof/k4-zmove-pot` (PR #87). Notation of `k4/c4x.md` §1, `k4/c4min.md` §1, `k4/c4min_reduce.md` §1–§2,
`k4/sx.md` §1–§3 and §6, `k4/dl2.md` §3–§4 and `k4/dl13.md` §2.1. Nothing here changes K4.D or K4.T. Ledger rows
K4.ZMP.* (written proofs: CONJECTURE, "written proof, not yet refereed"; data: EVIDENCE; failed candidates: REFUTED).

**Target (Theorem ZMOVE).** For every strict profile of every connected k = 4 core with f ≥ 1 and ω ≥ 1, and every key
κ with def*(κ) > 0: at some Z′-maximum Q of κ (a configuration at κ maximizing (r′, Λ′)), some single (T3⁺) move from
P_Q with at most one helper (the helper giving up a good of its base) reaches a state P′ with def(P′) ≤ 0, or κ has a
(T4) edge to a key with smaller def*.

**Status. ZMOVE is not proved here.** What is here:
- **The potential (§2, EVIDENCE, K4.ZMP.POT).** On every input tested, the one-move repair exists at *every* state of
  the key that maximizes the number r′ of robust free agents, with or without Λ′, and at every Z′-maximum. It fails at
  states that are only Pareto-maximal, or at which every free agent is only locally optimal (core 4515, f = 2), and at
  arbitrary states (core 4604, f = 1). The stuck states of compute/k4-rc at both cores are exactly states where a move
  inside the key raises r′, and that move is the extra helper of their nearest repair. So the potential is r′, and the
  exchange a proof must exclude is one that makes one more free agent robust; Pareto improvements do not suffice.
- **Written proofs, not yet refereed (§3, K4.ZMP.Z0).** Lemma Z0: Z′-maximality is a property of the state P_Q, every
  arrangement of the junk into slots and pool gives a Z′-maximum ("re-choice of Q"), and at a Z′-maximum every free
  agent is locally optimal. Lemma R0: a robust free agent is never threatened by a bundle missing its base and 𝒩.
- **Written proofs, not yet refereed (§4, K4.ZMP.AR): Theorem AR (f = 1).** At every state P of a key with def(P) ≥ 1 at
  which every free agent is robust and every terminal is locally optimal, one plain (T3) move (no helper) reaches
  def ≤ 0, except in two residual configurations (E) and (R3) with no slot, every terminal θ-b and x's lower goods valued
  by no terminal. Corollary: ZMOVE holds at every f = 1 key that has an all-robust Z′-maximum outside (E), (R3). The
  proof is uniform: one owner swap (Lemma S, `k4/sx.md`'s Lemma A without the forest), one slot (Lemma S′, which makes
  θ-b harmless whenever some free agent holds one good), and, with no slot, the state-level forms of Lemmas C and C′
  without their third-agent hypotheses (H), (H′).
- **Checks (EVIDENCE).** `k4/zmove_pot.py` asserts every case of Theorem AR against exact deficits at every all-robust
  state of the f = 1 data (9,388 states; 0 violations; the residual never occurs), and a second, repo-free implementation
  (`k4/rt4_n5_indep.py`) agrees on every deficit and every one-move verdict it recomputes (9,565 states).
- **Refuted (§6, K4.ZMP.X):** the Pareto / local-optimality form at core 4515; the potential (−t, r′, Λ′) at core 4604;
  "Lemma A or B at some Z′-maximum in some arrangement" at n = 3, m = 7.
- **Open:** the residual (E), (R3) of Theorem AR (never seen); states with a non-robust free agent (26% of the f = 1 keys
  of the data have no all-robust Z′-maximum; §5 extends Lemma S to them and locates what is left, the terminal that
  exposes the non-robust agent, as in Lemmas B, B′ of `k4/sx.md`); f ≥ 2.

## 1. Setting

f ≥ 1, ω ≥ 1, κ = (𝒩, φ) a key with frozen set F and def*(κ) > 0. A *state* of κ is a min-frozen P with key κ. For a
free agent y, U_y := R_y ∖ 𝒩. On states:
- y is *robust* at P if v_y(B_y) ≥ v_y(U_y ∖ B_y); r′(P) is the number of robust free agents;
- Λ′(P) := Σ_{y free} ℓ_y(B_y), with ℓ_y(S) = #{T ⊆ R_y : v_y(T) < v_y(S)} (`k4/sx.md` §2);
- y is *locally optimal* at P if no set S′ ⊆ (B_y ∪ J) ∩ R_y with |S′| ≤ 2 has v_y(S′) > v_y(B_y).

For a configuration Q at κ these are r′ and Λ′ of `k4/sx.md` §2 evaluated at its state P_Q, and Q is a Z′-maximum iff
P_Q maximizes (r′, Λ′) over the states of κ (Lemma Z0).

**zm(P)** holds if some (T3⁺) move from P with at most one helper (giving up a good of its base) reaches a min-frozen P′
with def(P′) ≤ 0. ZMOVE asks for zm(P_Q) at some Z′-maximum Q, or a (T4) edge.

## 2. Which potential: the data (EVIDENCE, K4.ZMP.POT)

For a class 𝒞 of states (defined key by key), the *every-form* "zm(P) for every P ∈ 𝒞, at every key with def* > 0" was
tested; a class that passes is a candidate potential. Classes, relative to the states of one key:
- ALL: every state; U: every free agent locally optimal; PARETO: no state of the key is at least as good for every free
  agent and better for one;
- R: r′-maximal; RU: R and U; RPARETO: r′-maximal and Pareto among those;
- LAM: Λ′-maximal; RLAM: (r′, Λ′)-maximal, i.e. the states of the Z′-maxima;
- TRL: the states of the maxima of (−t, r′, Λ′) over the configurations of the key (#41's Φ with t first; t counts the
  frozen agents threatened by the pool alone).

States without a one-move repair, by `k4/zmove_pot.py` (logs `results/k4_zmove_pot/run_*.log`):

| input | keys with def* > 0 | ALL | U | PARETO | R | RU | RPARETO | LAM | RLAM | TRL |
|---|---|---|---|---|---|---|---|---|---|---|
| PR #80's hunts (n = 4: three 4-good agents 40,000 per core, pure 40,000 and 400,000 per core; n = 5 pure 1,000 per core), compute/k4-cover's f = 1 hunts (seeds 0 and 9) and its two COVER⁺ failures (`run_hunts_n4n5.log`) | 4,477 f = 1, 2 f = 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| compute/k4-rc's core 4604 (n = 5, m = 13, f = 1), all 369 profiles, and core 4515 (n = 5, m = 12, f = 2), all 1,076 profiles (`run_rc.log`) | 369 f = 1, 2,152 f = 2 | 4,673 | 42 | 42 | 0 | 0 | 0 | 0 | 0 | 403 |

The second implementation (main's repo-free `k4/rt4_n5_indep.py`) recomputes every 10th (first row) and every 50th
(second row) profile: every deficit, and zm at every state of every key with def* > 0, agree (7,853 + 1,712 states).
At core 4604 no maximum of (−t, r′, Λ′) has a one-move repair at any of the 369 keys. The Z′-maxima (RLAM) and the
r′-maxima (R) have a one-move repair everywhere. Not yet rerun with the committed tool (scratch runs of this workstream
on compute/k4-cover's libraries, same definitions): every Z′-maximum of every key with def* > 0 of PR #80's f ≥ 2 inputs
and T1-stuck keys (1,522 keys), of compute/k4-cover's f = 2 hunt on the crossed n = 4, m = 10 core (3,871 keys) and of
PR #80's n = 3 hunts (sampled) has a one-move repair, and so does every r′-maximal state of the samples tested.
compute/k4-zmove (3091066) and PR #88 (proof/k4-zmove-hall, for r′ alone) report the same on their data.

**Core 4515: why P_Q avoids the two-helper trap.** In each of the 1,076 profiles the states without a one-move repair
are exactly compute/k4-rc's four stuck states ({4}, {1,8}, {10,11}, B₃, {9}) (B₃ one of {5,6}, {5,7}, {6,7} and a
singleton), 4,304 states. At each of them agent 1 is not robust (v₁({1,8}) < v₁({10,11})), agent 2 holds {10,11} and is
robust, and r′ = 2, while the key reaches r′ = 3. The trade "agent 1 takes {1,10} or {1,11}, agent 2 takes {3}, {3,10}
or {3,11}" is a (T2) move inside the key that keeps agent 2 robust and makes agent 1 robust: it raises r′ but lowers
agent 2's value, so the stuck states with B₃ = {6,7} are Pareto-maximal and locally optimal (the 42 PARETO and U
failures) but not r′-maximal. The two-helper repair of compute/k4-rc (agent 1: {1,8} → {1,10}, agent 2: {10,11} → {3},
agent 3 takes 4, agent 0 takes {0}) is this trade followed by a plain (T3) swap. Every r′-maximal state has made the
trade already, and from it one plain swap suffices (the coordinator's C′⁺ repair, `k4/f2.md` §7.2 on
proof/k4-f2-zmove). At core 4604 (f = 1) the stuck state ({11}, {12}, {3,7}, {4,8}, {5,9}) has agent 1 non-robust on
{12} with the junk good 1 available: the (T1) move to {1,12} raises r′, and it is the growing helper of the nearest
repair (`results/k4_rc/FAILURES.md` §1 on compute/k4-rc).

So a proof by potential has to use exchanges that raise r′ and are not Pareto improvements; Pareto optimality or local
optimality alone is refuted (§6).

## 3. Re-choice of Q, and robust agents (written proofs, not yet refereed; K4.ZMP.Z0)

Throughout, f ≥ 1, ω ≥ 1 and κ = (𝒩, φ) is a key with frozen set F; the free agents are the others. Facts used:
(V) (`k4/dl2.md` §4: P ∈ 𝒫 iff its bases are disjoint subsets of the relevant sets with at most two goods and every
needed good is the whole base of one agent), (M2) (`k4/dl2.md` §4: v_y(B′) ≥ v_y(B) implies N_y(B′) ⊆ N_y(B)), and
minimality of f (a P ∈ 𝒫 with NA(P) ⊆ 𝒩 has NA(P) = 𝒩).

**Lemma Z0 (Z′-maximality is a property of the state; the fillers are free).** Let P be a state of κ that maximizes
(r′, Λ′) over the states of κ, with junk J and S := Σ_{y free} (2 − |B_y|) slots.
- (a) A free agent y with |B_y| = 1 values no good of J.
- (b) A free agent y with |B_y| = 2 has no set S′ ⊆ (B_y ∪ J) ∩ R_y with |S′| ≤ 2 and v_y(S′) > v_y(B_y).
- (c) For every family of pairwise disjoint sets F_y ⊆ J with |F_y| = 2 − |B_y| (y free), the pairs
  Q_y := B_y ∪ F_y and the pool L := J ∖ ⋃ F_y form a configuration at κ with P_Q = P, and every such Q is a
  Z′-maximum. Conversely, the Z′-maxima are exactly the configurations obtained this way from the states that maximize
  (r′, Λ′).

*Proof.* (a), (b). Otherwise let y re-base to B′ := B_y ∪ {u} (u ∈ J ∩ R_y) in (a), B′ := S′ in (b). B′ ⊆ U_y: J misses
𝒩 by (V1) and a free base misses 𝒩 (a free one-good base is not needed, a pair by (V2)). The bases stay disjoint, and
v_y(B′) > v_y(B_y), so N_y(B′) ⊆ N_y(B_y) ⊆ 𝒩 by (M2); the other needs are unchanged. Every good of 𝒩 is still the
one-good base of an agent of F, and B′ misses 𝒩. So the new P′ is in 𝒫 by (V), |F(P′)| = |NA(P′)| ≤ f, hence
NA(P′) = 𝒩 by minimality, and its frozen agents are F with φ: P′ is a state of κ. Λ′ rises strictly (ℓ_y increases
strictly with value), and r′ does not fall: if y was robust, v_y(U_y ∖ B′) = v_y(U_y) − v_y(B′) < v_y(U_y) − v_y(B_y)
≤ v_y(B_y) < v_y(B′). This contradicts maximality.

(c) The F_y exist because |J| = S + ω ≥ S. Q_y ⊆ M ∖ 𝒩, the Q_y are disjoint pairs, and Q_y ∩ U_y = B_y: for
|B_y| = 1 by (a); for |B_y| = 2 there is no filler; for B_y = ∅ we have U_y = ∅, since N_y(∅) = R_y ⊆ 𝒩. B_y is
admissible (N_y(B_y) ⊆ 𝒩, `k4/c4min.md` §1), and |L| = |J| − S = ω. So Q is a configuration at κ with P_Q = P. For any
configuration Q′, Q′_y ∩ R_y = Q′_y ∩ U_y = H′_y (Q′_y misses 𝒩), so r′(Q′) and Λ′(Q′) of `k4/sx.md` §2 equal r′ and Λ′
of the state P_{Q′}, which is a state of κ (`k4/c4min.md` Lemma 1(a) with C = ∅, K4.C4MIN.CFG; `k4/sx.md` Lemma 0). Hence
the maximum of (r′, Λ′) over configurations is at most its maximum over states, and equality holds because a maximizing
state is P_Q for the configurations just built. So a configuration is a Z′-maximum iff its state maximizes (r′, Λ′),
and its pairs are then B_y plus fillers from J. ∎

So "some Z′-maximum Q" in ZMOVE is "some (r′, Λ′)-maximal state P": the conclusion of ZMOVE depends on P_Q only, and
the arrangement of J into fillers and pool (on which Lemma F's forest depends) may be chosen freely afterwards. That is
the "re-choice of Q" of this workstream's brief.

**Lemma R0 (robust agents are inert).** If a free y is robust at P (v_y(B_y) ≥ v_y(U_y ∖ B_y)), then no set Z with
Z ∩ (𝒩 ∪ B_y) = ∅ threatens y holding B_y.

*Proof.* θ_y(Z) ≤ v_y(Z ∩ R_y) ≤ v_y(U_y ∖ B_y) ≤ v_y(B_y). ∎

(At f = 1 this is the first line of the proof of Theorem Z′, K4.C4MIN.RED.Z.) Every owner bundle in a move that keeps
y's base misses 𝒩 and B_y, so a robust free agent that does not move never blocks a repair. At an r′-maximal state the
agents that can block are as few as possible; this is the sense in which r′ is the potential.

## 4. f = 1, every free agent robust: Theorem AR (written proofs, not yet refereed; K4.ZMP.AR)

Setting: f = 1, κ = (g, x), ω ≥ 1, and P a state of κ with def(P) ≥ 1 (for instance any state, when def*(κ) > 0). The
free agents are the agents other than x; J is the junk, S := Σ_{y ≠ x} (2 − |B_y|), and |J| = S + ω (`k4/c4x.md` §1).
U_y := R_y ∖ {g}. Recall (`k4/c4min_f1.md` Lemma 1, K4.C4MIN.F1; `k4/c4min_reduce.md` Lemma T, K4.C4MIN.RED.Z):
- g is x's top, so every good of U_x is worth less than g to x, while v_x(U_x) > v_x(g) (balance); p, q (, r) are the
  goods of U_x in decreasing value for x;
- the *terminals* T are the free agents that need g; T ≠ ∅ (g ∈ NA(P), and x does not need its own base), and g is the
  top of every terminal. For a terminal τ, u₁ > u₂ (> u₃) are the goods of U_τ in decreasing value for τ.

**Hypotheses (H_AR).** (i) Every free agent is robust at P. (ii) Every terminal τ is *locally optimal*: no set
S′ ⊆ (B_τ ∪ J) ∩ R_τ with |S′| ≤ 2 has v_τ(S′) > v_τ(B_τ).

By Lemma Z0 (a), (b), (ii) holds at every (r′, Λ′)-maximal state, i.e. at P_Q for every Z′-maximum Q.

**Definition (θ-b at P).** A terminal τ is *θ-b at P* if |R_τ| = 4, B_τ = {u₁, u₂}, u₃ ∈ J and |J| ≥ 2. Since τ needs g,
v_τ(g) > v_τ(u₁) + v_τ(u₂): τ is big-top on g, and any two goods of U_τ are together worth less than g to τ. (When
S = 0 the junk is the pool, and this is θ-b(τ) of `k4/sx.md` §3.)

**Two facts.**
- **(F1)** For every free o, W_o := B_o ∪ J threatens x holding {g}, so v_x(W_o ∩ U_x) > v_x(g), and W_o ∩ U_x contains
  a set admissible for x. *Proof.* |W_o| = |B_o| + S + ω ≥ ω + 2, since S ≥ 2 − |B_o|. W_o misses g and the other free
  bases, so by Lemma R0 it threatens no free agent other than o. If it did not threaten x, it would be a safe bundle of o
  and Lemma H1 (K4.HALL.COVER) would give def(P) ≤ ω + 2 − |W_o| ≤ 0. The admissible set: the first part of
  `k4/dl13.md` Lemma 9 (K4.DL13.SWAP). The value bound: θ_x(W_o) ≤ v_x(W_o ∩ R_x) and W_o ∩ R_x = W_o ∩ U_x. ∎
- **(F2) The plain swap σ(τ, A).** For τ ∈ T and A ⊆ (J ∪ B_τ) ∩ U_x admissible for x, let P′ be P with τ on {g} and x
  on A. By `k4/dl2.md` Lemma 6 (K4.DL2.MOVES) P′ is a state of the key (g, τ), and P → P′ is a (T3) move without helper.
  Its junk is J′ := (J ∪ B_τ) ∖ A, and its bundles are: for x, the Y with A ⊆ Y ⊆ J ∪ B_τ; for a free o ≠ τ of P, the
  Y with B_o ⊆ Y ⊆ B_o ∪ J′ (`k4/dl13.md` Lemmas 8 and 11, K4.DL13.SWAP). Such a Y is safe in P′ iff it does not threaten
  τ holding {g}, x holding A (if o ≠ x), and the free agents w ∉ {τ, o, x} holding B_w; by Lemma R0 and (i), the last
  never happens. Lemma H1 in P′: def(P′) ≤ ω + 2 − |Y| − u′(Y) for every safe bundle Y.

**Lemma S (state-level owner swap).** Assume (H_AR). If a terminal τ is not θ-b at P, then for every admissible
A ⊆ (J ∪ B_τ) ∩ U_x (one exists by (F1)) the plain swap σ(τ, A) gives def(P′) ≤ 0, with owner x and bundle J ∪ B_τ.

*Proof.* First, θ_τ(J ∪ B_τ) ≤ v_τ(g). Indeed g ∉ J ∪ B_τ, so θ_τ(J ∪ B_τ) ≤ v_τ((J ∪ B_τ) ∩ U_τ). An admissible
base of τ contains u₁ or is {u₂, u₃} (a single good other than u₁ would need u₁ ∉ {g}).
- |R_τ| = 3: u₁ ∈ B_τ, and B_τ ≠ U_τ because v_τ(U_τ) > v_τ(g) (balance) while τ needs g. So B_τ = {u₁}, and (ii)
  gives u₂ ∉ J. The intersection is {u₁}, worth less than g.
- |R_τ| = 4, B_τ = {u₁}: (ii) gives u₂, u₃ ∉ J; the intersection is {u₁}.
- B_τ = {u₁, u₃} or {u₂, u₃}: (ii) gives u₂ ∉ J, resp. u₁ ∉ J; the intersection is B_τ, worth less than g.
- B_τ = {u₁, u₂}: if u₃ ∉ J, the intersection is B_τ. If u₃ ∈ J and |J| = 1, then J ∪ B_τ = U_τ ⊆ R_τ and
  θ_τ(U_τ) = v_τ(u₁) + v_τ(u₂) < v_τ(g). The remaining case is θ-b.

So Y := J ∪ B_τ does not threaten τ holding g; it is a bundle of x in P′ (A ⊆ Y), safe by (F2), and
|Y| = S + ω + |B_τ| ≥ ω + 2. ∎

At a Z′-maximum this is Lemma A of `k4/sx.md` §3 without its forest hypothesis: the swapped terminal need not be a
leaf, because the bundle J ∪ B_τ meets no free agent's base and every free agent is robust.

**Lemma S′ (a slot pays for a θ-b terminal).** Assume (H_AR), every terminal θ-b at P, and S ≥ 1. For τ ∈ T, A as in
Lemma S and any c ∈ U_τ ∖ A, the plain swap σ(τ, A) gives def(P′) ≤ 0, with owner x and bundle (J ∪ B_τ) ∖ {c}.

*Proof.* c exists since |U_τ| = 3 > |A|. Y := (J ∪ B_τ) ∖ {c} ⊇ A, |Y| = S + ω + 1 ≥ ω + 2, and Y ∩ R_τ ⊆ U_τ ∖ {c}
has two goods, worth less than g. (F2). ∎

In configuration terms: c goes into the slot of a free agent with a one-good base, so θ-b fails for τ in that
arrangement (Lemma Z0 (c)) and Lemma A applies.

**The case S = 0.** Assume (H_AR), every terminal θ-b, S = 0. Then every free agent holds a pair, |J| = ω ≥ 2, and the
lower goods of each terminal lie in J ∪ B_τ. Write D := J ∩ U_x.

**Lemma C₀ (one terminal).** If T = {τ}, a plain swap σ(τ, A) gives def(P′) ≤ 0:
- (a) if U_τ ⊄ U_x: any admissible A ⊆ (J ∪ B_τ) ∩ U_x, owner x, bundle Y := (J ∪ B_τ) ∖ {c} with c ∈ U_τ ∖ U_x;
- (b) if U_τ ⊆ U_x: A := {p, q}, owner any free o ≠ τ, bundle Y := B_o ∪ J′.

*Proof.* (a) A ⊆ Y as c ∉ U_x, |Y| = ω + 1, and Y ∩ R_τ ⊆ U_τ ∖ {c} is worth less than g, so Y is safe (F2). In P′ the
only frozen agent is τ, on g. Nobody but x can need g there: the free agents other than x keep their bases, and none of
them needed g (T = {τ}). And v_x(Y) = v_x((J ∪ B_τ) ∩ U_x) > v_x(g) by (F1) for o = τ, so g ∉ N_x(Y). Hence τ is
counted in u′_x(Y) (Lemma H1's u), and def(P′) ≤ ω + 2 − (ω + 1) − 1 = 0.
(b) |U_τ| = 3, so U_x = U_τ ⊆ J ∪ B_τ, and A ⊆ J ∪ B_τ contains p, hence is admissible. There is a free o ≠ τ: with
n = 2 all goods would be g and U_x, so m = 4 and ω = f − (2n − m) = 1 < 2. B_o misses U_x. |Y| = 2 + (ω + 2) − 2 = ω + 2;
Y ∩ R_τ ⊆ U_τ ∖ A = {r} and Y ∩ R_x ⊆ {r}, worth less than g and than v_x(A). (F2). ∎

**Lemma C₁ (a C-pair; `k4/sx.md` Lemma C at the state level).** Let τ ∈ T and A ⊆ (J ∪ B_τ) ∩ U_x be admissible and
*robust for x* (v_x(A) ≥ v_x(U_x ∖ A)), with A ∩ U_τ ≠ ∅ or |A| = 1. Then for every free o ≠ τ the plain swap σ(τ, A)
gives def(P′) ≤ 0, with owner o and bundle Y := B_o ∪ (J′ ∖ C), where C = ∅ if A ∩ U_τ ≠ ∅ and C = {c} for some
c ∈ U_τ otherwise.

*Proof.* |Y| = 2 + (ω + 2) − |A| − |C| ≥ ω + 2. Y misses (A ∪ C) ∩ U_τ ≠ ∅, so Y ∩ R_τ has at most two goods of U_τ,
worth less than g. Y ∩ R_x ⊆ U_x ∖ A, worth at most v_x(A). (F2). ∎

**Lemma C₂ (a C′-pair; `k4/sx.md` Lemma C′ at the state level).** Let T = {τ, τ′} with U_x ∩ U_τ = U_x ∩ U_τ′ = ∅, and
let A ⊆ D be a pair with v_x(A) > v_x(g). Then the plain swap σ(τ, A) gives def(P′) ≤ 0, with owner τ′ and bundle
Y := B_τ′ ∪ (J′ ∖ {w}) for any w ∈ U_τ other than τ′'s third lower good u₃^τ′.

*Proof.* A is admissible (worth more than x's top) and robust (U_x ∖ A is at most one good, worth less than g).
|Y| = 2 + (ω + 2) − 2 − 1 = ω + 1. Y ∩ R_τ ⊆ U_τ ∖ {w}; Y ∩ R_x ⊆ U_x ∖ A, worth less than v_x(A); so Y is safe (F2).
U_τ′ ⊆ Y: B_τ′ ⊆ Y, and u₃^τ′ ∈ J ∖ (A ∪ {w}) (A ⊆ U_x misses U_τ′). Hence v_τ′(Y) ≥ v_τ′(U_τ′) > v_τ′(g) (balance)
and g ∉ N_τ′(Y). In P′ also g ∉ N_x(A), τ holds g, and no other agent needed g in P. So τ is counted in u′_τ′(Y), and
def(P′) ≤ ω + 2 − (ω + 1) − 1 = 0. ∎

**Lemma C₃ (three or more terminals, x's best good alone).** Let |T| ≥ 3, U_x ∩ U_τ = ∅ for every τ ∈ T, p ∈ J and
v_x(D ∖ {p}) ≤ v_x(p). Then for τ ≠ τ′ in T the plain swap σ(τ, {p}) gives def(P′) ≤ 0, with owner τ′ and bundle
Y := B_τ′ ∪ (J′ ∖ {c}), c ∈ U_τ.

*Proof.* {p} is admissible (its only need is g). |Y| = 2 + (ω + 2) − 1 − 1 = ω + 2. B_τ′ and B_τ miss U_x, so
Y ∩ R_x = D ∖ {p}, worth at most v_x(p); Y ∩ R_τ ⊆ U_τ ∖ {c}. (F2). ∎

**Proposition ℛ (what remains when S = 0).** Assume (H_AR), every terminal θ-b at P, S = 0, |T| ≥ 2, and that none of
Lemmas C₁, C₂, C₃ applies. Then U_x ∩ U_τ = ∅ for every τ ∈ T, v_x(D) > v_x(g), |U_x| = 3, and:
- **(E)** if |T| = 2: U_x ⊆ J, x is big-top on g (v_x(p) + v_x(q) < v_x(g)), and v_x(p) < v_x(q) + v_x(r);
- **(R3)** if |T| ≥ 3: either p ∉ J (p lies in the base of a free non-terminal) and D = {q, r} with
  v_x(q) + v_x(r) > v_x(g), or U_x ⊆ J and v_x(q) + v_x(r) > v_x(p).

*Proof.* Let τ ∈ T and S_τ := (J ∪ B_τ) ∩ U_x; v_x(S_τ) > v_x(g) by (F1), so |S_τ| ≥ 2. Suppose s ∈ U_x ∩ U_τ; then
s ∈ S_τ. If |S_τ| = 2, A := S_τ is admissible (worth more than g), robust (U_x ∖ A is at most one good) and meets U_τ.
If |S_τ| = 3, A := {p, s} (or {p, q} if s = p) is admissible (contains p), robust (one good of U_x is left, worth less
than p) and meets U_τ. Lemma C₁ would apply; so U_x ∩ U_τ = ∅, B_τ misses U_x, S_τ = D and v_x(D) > v_x(g).
Lemma C₁ with A = {p} does not apply either, so not (p ∈ D and v_x(p) ≥ v_x(U_x ∖ {p})). If |U_x| = 2, then D = U_x ∋ p
and v_x(p) > v_x(q): impossible. So |U_x| = 3.
|T| = 2: no pair of D beats g (Lemma C₂). As v_x(D) > v_x(g), D = U_x ⊆ J and v_x(p) + v_x(q) < v_x(g); and p ∈ D gives
v_x(p) < v_x(q) + v_x(r).
|T| ≥ 3: Lemma C₃ fails, so p ∉ J or v_x(D ∖ {p}) > v_x(p). In the first case D ⊆ {q, r} has two goods. In the second,
D ∖ {p} ⊆ {q, r} is worth more than p, so it is {q, r}. ∎

**Theorem AR (f = 1).** Let P be a state of κ with def(P) ≥ 1 satisfying (H_AR). Then one plain (T3) move from P (no
helper) reaches a state P′ with def(P′) ≤ 0, unless S = 0, every terminal is θ-b at P, and P is in case (E) or (R3) of
Proposition ℛ.

*Proof.* If some terminal is not θ-b: Lemma S. Otherwise, if S ≥ 1: Lemma S′. Otherwise S = 0: Lemma C₀ when |T| = 1;
when |T| ≥ 2, Lemmas C₁, C₂, C₃ or Proposition ℛ. ∎

**Corollary AR (ZMOVE at f = 1 when a Z′-maximum is all robust).** If some Z′-maximum Q of a key κ with f = 1 and
def*(κ) > 0 has every free agent robust, and P_Q is not in case (E) or (R3), then ZMOVE holds at κ, by a (T3) move without
helper from P_Q.

*Proof.* P_Q satisfies (H_AR)(ii) by Lemma Z0, and def(P_Q) ≥ def*(κ) ≥ 1. ∎

**One more constraint on the residual (written proof).** In the setting of Proposition ℛ (U_x ∩ U_τ = ∅ for all τ ∈ T,
|T| ≥ 2), if some terminal τ has v_τ(u₁) ≥ v_τ(u₂) + v_τ(u₃) and some e ∈ D has v_x(D ∖ {e}) ≤ v_x(g), then
def*(κ) ≤ 0. *Proof.* Re-base τ to {u₁} (a (T1) move: {u₁} is admissible, N_τ({u₁}) = {g}, and the argument of Lemma Z0
(a) gives a state P* of κ). P* has one slot (τ's) and junk J ∪ {u₂}. Take a terminal τ′ ≠ τ as owner with
Y := B_τ′ ∪ ((J ∪ {u₂}) ∖ {e}): |Y| = ω + 2; Y ∩ R_x = D ∖ {e} (B_τ′ and u₂ miss U_x), worth at most v_x(g);
Y ∩ R_τ ⊆ {u₂, u₃}, worth at most v_τ(u₁); the other free agents are robust with unchanged bases (Lemma R0). Lemma H1
(e goes into τ's slot): def(P*) ≤ 0. ∎ In (E), e := p works (x big-top), and in the first form of (R3), e := q works.
So in those residual cases every terminal is *fragile*: v_τ(u₁) < v_τ(u₂) + v_τ(u₃).

## 5. Beyond Theorem AR: where the potential has to act

Theorem AR uses three things only: (F1), which is def(P) ≥ 1; the inertness of robust agents (Lemma R0); and the local
optimality of the terminals. Its first lemma extends verbatim to agents that are not robust, as long as the bundle does
not meet what threatens them:

**Lemma S⁺.** Let f = 1, P a state of κ with def(P) ≥ 1, and τ a locally optimal terminal that is not θ-b at P, such that
W_τ = B_τ ∪ J threatens no free agent other than τ (τ *exposes* nobody, in the sense of `k4/hall.md` §2). Then the plain
swap σ(τ, A) (any admissible A ⊆ W_τ ∩ U_x) gives def(P′) ≤ 0, with owner x and bundle W_τ.

*Proof.* The proof of Lemma S, with the hypothesis in place of Lemma R0 for the agents other than τ and x; (F1) for
o = τ holds because W_τ is safe for every free agent other than τ. ∎

At a state satisfying (U) and (U₂) (in particular at every (r′, Λ′)-maximal state, Lemma Z0), a free agent is exposed
by at most one free agent (`k4/hall.md` Lemma H3, K4.HALL.COVER, whose proof uses only (U) and (U₂)). So when exactly one
free agent y is not robust, Lemma S⁺ applies at every terminal that is neither θ-b nor y's exposer, and Lemma S′
applies (with the same proof) as soon as S ≥ 1 and some θ-b terminal is not y's exposer. What is left there is the
situation of `k4/sx.md` Lemmas B and B′: the terminal that is not θ-b is the agent that exposes the non-robust agent.

On the data, 74% of the f = 1 keys with def* > 0 have a Z′-maximum with every free agent robust (16,506 of 22,358 keys
in a scratch sample of every third profile of the inputs of §2 and PR #80's n = 3 hunts), 26% have exactly one
non-robust free agent at every Z′-maximum, and 3 keys have two. `k4/zmove_pot.py` reports the case of Theorem AR at
every all-robust state.

## 6. What remains, and the candidates that failed

**Open.**
- (E) and (R3) of Proposition ℛ. Neither occurs on the data (no state of any run reaches them; §2 logs, counter
  "AR residual"). Both need four agents with S = 0, three θ-b terminals (R3) or two (E) whose lower goods x does not
  value, and, by the last lemma of §4, every terminal fragile.
- States with a non-robust free agent (§5). The exchange the potential must exclude is a move inside the key that raises
  r′: this is what the stuck states of cores 4604 and 4515 admit (§2), and what Lemma F's rotations do in `k4/sx.md`.
  PR #88 (proof/k4-zmove-hall, Lemma EX, unrefereed) gives one such exchange in written form.
- f ≥ 2. Lemma Z0 and Lemma R0 hold at every f. Theorem AR does not carry over as it stands: at f = 2, 428 states with
  every free agent robust and every free agent locally optimal need a helper (compute/k4-cover's crossed n = 4, m = 10
  core, whose repair is Lemma C⁺ₕ of `k4/f2.md` §5.1 on proof/k4-f2).

**Failed candidates** (each with its smallest failure and a replay by two implementations,
`attempts/k4_zmove_pot_attempts.py`, log `results/k4_zmove_pot/attempts.log`):
- `attempts/k4-zmove-pot-pareto.md`: ZMOVE at every Pareto-maximal state of the key, or at every state at which every
  free agent is locally optimal. Fails at core 4515 (n = 5, m = 12, f = 2): the stuck states are both.
- `attempts/k4-zmove-pot-t-first.md`: the potential (−t, r′, Λ′) over the configurations of the key (#41's Φ with t
  first, restricted to one key): at core 4604 (n = 5, m = 13, f = 1) no maximum has a one-move repair.
- `attempts/k4-zmove-pot-a-or-b.md`: "at some Z′-maximum, in some arrangement of the junk, Lemma A or Lemma B with path
  length 1 applies". Fails at n = 3, m = 7 (two θ-b terminal leaves and no slot): there Lemmas C and C′ are needed. So
  re-choosing the arrangement does not replace C and C′; it replaces them only when a slot exists (Lemma S′).

## 7. Reproduce

One process at a time; times on a shared 4-CPU machine.
```
python3 k4/zmove_pot.py results/k4_sx/hunt/n4_3_r40k.jsonl.gz results/k4_sx/hunt/n4_pure_r40k.jsonl.gz \
  results/k4_sx/hunt/n4_pure_r400k.jsonl.gz results/k4_sx/hunt/n5_pure_r1000_3000.jsonl.gz \
  results/k4_sx/hunt/n5_pure_r1000_4000.jsonl.gz results/k4_zmove_pot/inputs/cover_f1_seed0.jsonl.gz \
  results/k4_zmove_pot/inputs/cover_f1_seed9.jsonl.gz inst:results/k4_zmove_pot/inputs/cover_failures_inst.json \
  --indep=10 > results/k4_zmove_pot/run_hunts_n4n5.log                      # ~6 min
python3 k4/zmove_pot.py inst:results/k4_zmove_pot/inputs/rc4604_inst.json \
  inst:results/k4_zmove_pot/inputs/rc4515_inst.json --indep=50 --tmax=1100 > results/k4_zmove_pot/run_rc.log   # ~6 min
python3 attempts/k4_zmove_pot_attempts.py > results/k4_zmove_pot/attempts.log   # ~1 min
```
Inputs: `results/k4_sx/` is on main (PR #80). `results/k4_zmove_pot/inputs/` holds copies of compute/k4-rc's
`results/k4_rc/rc_fail_all_inst.json` (core 4604) and `rc_fail_4515_all_inst.json` (core 4515), of compute/k4-cover's
`results/k4_cover/hunt/*.jsonl.gz` and of the two instances of its `results/k4_cover/FAILURES.md`.
