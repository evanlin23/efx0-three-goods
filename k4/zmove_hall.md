# Theorem ZMOVE by a Hall argument

Workstream `proof/k4-zmove-hall` (PR #88). Target: Theorem ZMOVE, the uniform repair from Theorem Z′'s state. Nothing
here changes K4.D or K4.T. Written proofs here are CONJECTURE rows until refereed ("written proof in
`k4/zmove_hall.md` §x, not yet refereed"); data rows are EVIDENCE.

**Theorem ZMOVE (target, open).** For every strict profile of every connected k = 4 core with f ≥ 1 and ω ≥ 1, and
every key κ with def*(κ) > 0: at some Z′-maximum Q of κ, some single (T3⁺) move from P_Q with at most one helper
reaches a state P′ with def(P′) ≤ 0, or κ has a (T4) edge to a key with smaller def*. (The helper gives up a good of
its base; (T3⁺) is `lean/EFX/MovesC.lean` `MoveT3plus`, ledger K4.DL2.RC.) ZMOVE implies DLKey((T3⁺) ∪ (T4)) and so
TARGET₄ (`lean/EFX/KeyFrame.lean`, `lean/EFX/MovesC.lean`).

**Status.** ZMOVE is not proved here, and the Hall-type contradiction argument asked for was not completed. What is
here:

- **Data (§1, EVIDENCE; K4.ZMH.E).** ZMOVE holds, in the stronger form *at every Z′-maximum* and *without (T4) edges*, at
  every key with def* > 0 of: every n = 3 profile (255,952 keys: 62,208 with f = 1 and 193,744 with f = 2; the profiles
  are those of compute/k4-cover's exhaustive screen, and the key counts agree with that screen and, at f = 1, with PR
  #80's `k4/red.c`); PR #80's n = 4 and n = 5 hunts (2,672 keys); compute/k4-rc's cores 4604 (f = 1) and 4515 (f = 2);
  compute/k4-cover's two COVER⁺ failures; every 8th f ≥ 2 profile (n ≤ 5) of compute/k4-cover's dumps (20,198 keys,
  f = 2, 3, 4). A second implementation (main's repo-free `k4/rt4_n5_indep.py` for the deficits and the move kinds,
  configurations enumerated directly as pairs) agrees key by key where it was run (§1). compute/k4-zmove reports the
  same every-maximum form on its data. The every-maximum form is CONJECTURE (K4.ZMH.R).
- **How much maximality is needed (§2.3, EVIDENCE).** Every configuration that maximizes r′ alone (Λ′ ignored) has a
  repair, on all data tested. Pool-optimality together with Lemma F⁺'s forest does not suffice: at core 4515 there are
  pool-optimal configurations with acyclic free threats, at def*, without any one-move repair
  (`attempts/k4-zmh-pool-optimal-forest.md`). So a contradiction argument must end in an r′-improving exchange (Lemma EX,
  §2.3), which is what the proof of §3 does at n = 3.
- **The Hall form of the obstruction (§2).** For a fixed move and owner, def(P′) ≤ 0 is a covering condition: a hitting
  set of the owner's threat hypergraph no larger than the slots of the other free agents (Lemma HF: Lemma H1,
  `k4/thetab.md` Corollary G1). In the removal-only deficit every removed good fits every slot, so for one move this
  "Hall condition" is a bare count; the failures of the lemma lists are each one excess blocker (§2.2). Combining them
  over all moves into one Hall violation was not achieved.
- **Proposition S1c₃ (§3; written proof, not yet refereed; K4.ZMH.S1C3).** n = 3: at a Z′-maximum of a non-completable
  f = 1 key whose two free agents are both terminals, x is not big-top. This is the open direction K4.TB.S1C of the
  coordinator's terminal dichotomy (S1, K4.ON.S, is the other one) at n = 3. The proof parks a lower good of x by an
  exchange (Lemma PK) and closes with Lemma EX and the core condition (C3). At n ≥ 4 the same exchanges leave the
  configurations in which every parking is blocked by a third agent (§3.3); open.
- **Refuted (attempts/, K4.ZMH.X):** S1c⁺, the local form "big-top x and two terminals at a Z′-maximum ⇒ def(P_Q) ≤ 0"
  (n = 3, m = 8); ZX, "the unfrozen agent x can always be the new owner" (n = 3, m = 8: two θ-b terminal leaves, where
  only the other leaf can own, Lemma C's shape); ZMOVE from every pool-optimal configuration with acyclic free threats
  (n = 5, m = 12, core 4515). Also, on the data, a helper is needed at some n = 3, f = 1 keys (45 of 3,119 sampled), and
  a frozen agent passing its good on (W ≠ ∅) at some f ≥ 2 keys (§1).

## 0. Setting

Notation of `k4/c4x.md` §1, `k4/hall.md` §1, `k4/dl2.md` §4, `k4/sx.md` §1–§2 and §6, `k4/thetab.md` §2. A strict profile
of a connected k = 4 core, f ≥ 1 the fewest frozen agents, ω = f − (2n − m) ≥ 1. A key κ = (𝒩, φ): the frozen agents F
with their goods. U_y = R_y ∖ 𝒩. A configuration Q at κ: disjoint pairs Q_y ⊆ M ∖ 𝒩 of the free agents with admissible
parts H_y = Q_y ∩ U_y, pool L with ω goods; X_y = Q_y ∪ L; P_Q the state (frozen w on {φ(w)}, free y on H_y). A
Z′-maximum maximizes (r′, Λ′) (robust free agents, then the sum of levels ℓ_y(H_y) over R_y). θ_w(Z) = max_{h ∈ Z}
v_w(Z ∖ h); Z threatens w holding B if θ_w(Z) > v_w(B). Lemma H1: def(P) = ω + 2 − max (|Z| + u_o(Z)) over the free o
and their safe bundles Z (B_o ⊆ Z ⊆ B_o ∪ J).

Only PROVED ledger rows are used: K4.HALL.COVER (Lemma H1), K4.C4MIN.CFG (Lemma 1), K4.C4MIN.RED.Z (Theorem Z′),
K4.C4MIN.F1 (`k4/c4min_f1.md` Lemmas 1–5), K4.SX.KEY (Lemma 0 and Lemma F of `k4/sx.md`), K4.SX.APLUS (Lemma F⁺),
K4.CORE (the core conditions), K4.DL2.MOVES (Lemma 6 of `k4/dl2.md`).

The facts on P_Q used below (`k4/sx.md` §2, §6, K4.SX.KEY, K4.SX.APLUS): Q is pool-optimal; the threats among the free
agents form a forest of out-trees, in-degree ≤ 1, no cycle; its leaves V (the free agents that threaten no free agent)
are nonempty and each threatens a frozen agent; a robust free agent is threatened by nobody; at f = 1 a non-robust
free agent has a kind of `k4/c4min_f1.md` Lemma 3 and is threatened as listed there. Every X_y is a bundle of y in
P_Q with ω + 2 goods (J(P_Q) = L ∪ ⋃_y (Q_y ∖ H_y)); so def*(κ) > 0 forces every X_y to threaten somebody.

## 1. Data (EVIDENCE)

Tools (this workstream): `k4/zmh_lib.py` (𝒫, needs, Lemma H1 deficits, keys, def*, the configurations through the
states: a configuration's P_Q is a state of κ whose free bases are nonempty (empty only when U_y = ∅) and admit
fillers, a matching of the free agents' empty slots to junk goods they do not value; the move classes T3, T3⁺, T4); `k4/zmove_check.py` (ZMOVE per
key and per Z′-maximum); `k4/zmh_xcheck.py` (a second implementation: main's repo-free `k4/rt4_n5_indep.py` for 𝒫, the
raw removal-only deficit and the move kinds, and the configurations enumerated directly as pairs, compared key by key
with `k4/zmh_lib.py`: def*, the set of Z′-maximum states, the number of good moves at each, the verdict);
`k4/zmh_zx.py` (the forms of the repair); `k4/zmh_roles.py` (roles of x, z, helper, owner).

| input | keys with def* > 0 (f = 1 / f ≥ 2) | Z′-maximum states | without a one-move repair | log |
|---|---|---|---|---|
| every n = 3 profile with a non-completable key (compute/k4-cover's screen at f25fb8e, 159,080 profiles) | 62,208 / 193,744 | 278,616 | 0 | `results/k4_zmove_hall/zmove_n3_all.log` |
| PR #80's n = 4 and n = 5 hunts (n4_3_r40k, n4_pure_r40k, n4_pure_r400k, n5_pure) | 2,672 / 0 | 3,317 | 0 | `results/k4_zmove_hall/zmove_hunts_n45.log` |
| compute/k4-cover's dumps of f ≥ 2 profiles (compute/k4-rt4, k4-dl13, k4-rc, k4-portfolio), n ≤ 5, every 8th | 0 / 20,198 (f = 2: 2,717; f = 3: 17,445; f = 4: 36) | 21,896 | 0 | `results/k4_zmove_hall/zmove_dumps_f2_every8.log` |
| compute/k4-rc's cores 4604 (369 profiles, f = 1) and 4515 (1,076 profiles, f = 2), with PR #80's small n = 4 hunts | 2,820 keys in all | 4,168 | 0 | `results/k4_zmove_hall/classes_rc_hunts.log` |
| compute/k4-cover's two COVER⁺ failures (n = 4, m = 7 and m = 10), four f = 3 profiles with a free agent whose goods all lie in 𝒩 | 1 / 20 | 23 | 0 | `results/k4_zmove_hall/zx_forms.log` (first block) |

Second implementation (`k4/zmh_xcheck.py`): `results/k4_zmove_hall/xcheck.log` and `xcheck2.log` (the samples are
listed on the logs' first lines: the hard instances, every 50th n = 3 screen profile, all of PR #80's small n = 4 hunts
and every 4th of the large one, every 8th profile of compute/k4-rc's cores, every 60th f ≥ 2 dump profile with n ≤ 5):
10,029 keys with def* > 0 and 11,202 Z′-maxima, every one with a repair, and 0 mismatches with `k4/zmh_lib.py` in def*,
the set of Z′-maximum states, the number of repairing moves at each, and the verdict. A bug found on the way: a free agent all of whose goods lie in 𝒩 has the empty
admissible part (U_y = ∅); `k4/zmh_lib.py` first treated such keys as having no configuration (f = 3 instances of the
dumps), both implementations were corrected, and the keys hold.

**Forms of the repair** (`k4/zmh_zx.py`, `results/k4_zmove_hall/zx_forms.log`; samples: every 20th profile of the n = 3
screen, PR #80's n = 4 hunts, every 5th profile of compute/k4-rc's cores, every 40th f ≥ 2 profile of the dumps with
n ≤ 5). Keys at which *no* Z′-maximum has a repair of the restricted form:

| form | n = 3 (3,119 keys f = 1; 9,670 f = 2) | n = 4 hunts (2,661, f = 1) | rc cores (504) | dumps (536 f = 2; 3,550 f = 3) |
|---|---|---|---|---|
| ZMOVE | 0 | 0 | 0 | 0 |
| ZMOVE, (T3) only (W = ∅) | 0 | 0 | 0 | 33; 805 |
| ZMOVE, no helper | 45 (f = 1) | 2 | 0 | 0 |
| ZX: x is a best owner after the move | 42 (f = 1) | 0 | 0 | 0 |
| ZX, no helper | 203 (f = 1) | 88 | 0 | 6; 1 |

So the uniform shapes one might hope for each fail somewhere: the owner cannot always be x (two θ-b terminal leaves,
`attempts/k4-zmh-x-owner.md`); a helper is needed already at n = 3; and at f ≥ 2 a frozen agent passing its good on.

## 2. The Hall form of the obstruction, and how much maximality it needs

### 2.1 One move: a covering count

Fix a move P_Q → P′ between min-frozen states and a free agent o′ of P′ (the would-be owner). Put W′ := B′_{o′} ∪ J′
(its largest bundle), s′ := Σ (2 − |B′_w|) over the free w ≠ o′ of P′ (the *slots* of the others), and let H be the
hypergraph of the minimal subsets of W′ that threaten some w ≠ o′ holding B′_w (`k4/thetab.md` Corollary G1, any f).
Since |J′| = ω + s′ + (2 − |B′_{o′}|) (`k4/c4x.md` §1: |J| − S = ω, and o′'s own slots are 2 − |B′_{o′}|), we have
|W′| = ω + 2 + s′, and Lemma H1 in P′ reads:

**Lemma HF (the covering form; a restatement of K4.HALL.COVER).** o′ certifies def(P′) ≤ 0 iff some C ⊆ J′ meets every
edge of H and |C| ≤ s′ + u′_{o′}(W′ ∖ C). In configuration language: each of the s′ slots receives one good of W′
(a "slot good"), the owner keeps the rest, and the goods placed in slots must hit every threat.

*Proof.* |W′ ∖ C| + u′ ≥ ω + 2 iff |C| ≤ s′ + u′, and W′ ∖ C is safe iff C meets every minimal threatening set
(threats are monotone). Lemma H1. ∎

The bipartite graph "removed goods × slots" of Lemma HF is *complete*: in the removal-only deficit a removed good may
go to any slot (`k4/c4x.md` §1). So Hall's condition for placing the removed goods is the bare count, and an
obstruction to one move at one owner is a transversal inequality τ(H) > s′ + u′, not a Hall violation in the matching
sense. A set S of threatened agents "served by fewer than |S| slot goods" arises only when the edges of H of different
agents of S are pairwise disjoint; then τ(H) ≥ |S|.

### 2.2 The failures of the lemma lists in this form

At a Z′-maximum every bundle X_o of ω + 2 goods threatens somebody (def*(κ) > 0), and each lemma of the lists is one
move with one owner and an explicit bundle. In the language of Lemma HF each failure is a single excess blocker:
- **A / A⁺** (owner x on X_o, o takes φ(x)): the only edge left is o's own threat (θ-b, or θ failing at the chain's
  end), or a second frozen agent threatened by X_o; τ(H) = 1, s′ = 0, u′ = 0.
- **B / B⁺** (owner x on X_o, helper o): the (R) leaf with s ∈ L is threatened by X_o holding Q_τ; B′ removes s and adds
  the released y; it fails when y creates an edge at a third agent ((H_B′)) or X″ has no admissible set of x.
- **C, C⁺** (another leaf owns Y = Q_o ∪ (X_τ ∖ P_x)): edges at third agents valuing the goods τ releases ((H)).
- **C′, C′⁺** (owner with ω + 1 goods): one edge paid by u′ = 1, which needs a good passing Fact 3 (no third needer).
- **C⁺ₕ, C′⁺ₕ**: the helper re-bases so that x's admissible set exists; same count.

The common pattern is: *one agent w is threatened by the would-be owner's bundle and no slot good is free to remove the
threat*. A "Hall violation" combining the failures over all x, z, helpers and bases A would be a set S of such blockers
with fewer free slot goods than |S|. To reach a contradiction it must produce a configuration at κ that beats Q.

### 2.3 Which maximality the contradiction must use (EVIDENCE)

`k4/zmh_classes.py` asks, for every state P of every key with def* > 0, whether some (T3⁺) move with at most one helper
from P reaches deficit ≤ 0, and groups the states: all states; configuration states; pool-optimal configurations; those
whose free threats form a forest; configurations maximizing r′ alone; the Z′-maxima.

| input | keys | states without a move: all / pool-optimal / pool-optimal forest / r′-max / Z′-max | log |
|---|---|---|---|
| compute/k4-rc cores 4604 (369 profiles) and 4515 (1,076), PR #80's small n = 4 hunts | 2,820 | 4,673 of 92,439 / 42 of 12,693 / 42 of 12,689 / 0 of 16,171 / 0 of 4,168 | `results/k4_zmove_hall/classes_rc_hunts.log` |
| PR #80's n = 4 hunts (n4_3_r40k, n4_pure_r40k; n4_pure_r400k every 2nd record) | 1,482 | 0 / 0 / 0 / 0 / 0 | `results/k4_zmove_hall/classes_n3_n4.log` |
| every n = 3 profile with a non-completable key, every 10th (compute/k4-cover's screen) | 25,595 | 0 / 0 / 0 / 0 / 0 | `results/k4_zmove_hall/classes_n3_n4.log` |
| compute/k4-cover's f ≥ 2 dumps, n ≤ 5, every 40th | 4,086 | 12 of 14,812 / 0 of 7,530 / 0 of 7,529 / 0 of 10,238 / 0 of 4,421 | `results/k4_zmove_hall/classes_dumps_f2_every40.log` |

So:
- on the n = 3 sample and in PR #80's n = 4 hunts *every* state of a key with def* > 0 has such a move (single-step DL
  with these moves); the states without one are compute/k4-rc's (core 4604, f = 1: P_fail; core 4515, f = 2) and 12
  states of the f ≥ 2 dump sample, none of them r′-maximal;
- pool-optimality and the forest of Lemma F⁺ do not suffice: at core 4515, 42 pool-optimal configurations whose free
  threats form a forest have no move (`attempts/k4-zmh-pool-optimal-forest.md`; there an (R) agent threatened along the
  forest could become robust by an exchange with its threatener, which raises r′);
- maximality of r′ alone suffices on all these data: every configuration maximizing r′ (Λ′ ignored) has a move.

Hence the contradiction of a Hall-type argument has to be an *r′-improving exchange*; Λ′ is never needed on the data.
The exchanges available at an r′-maximum are of this kind:

**Lemma EX (an exchange along a threat edge; any f).** Let Q be a configuration at κ that maximizes r′, o → y a threat
between free agents with y not robust, and Q′_y ⊆ Q_o ∪ Q_y ∪ L a pair on which y is robust with an admissible part.
If o has a pair Q′_o ⊆ (Q_o ∪ Q_y ∪ L) ∖ Q′_y with an admissible part, then o is robust in Q and not robust on Q′_o.

*Proof.* Q with y on Q′_y, o on Q′_o and the pool (Q_o ∪ Q_y ∪ L) ∖ (Q′_y ∪ Q′_o) is a configuration at κ (pairs in
M ∖ 𝒩, admissible parts, ω pool goods). Only o and y change: y gains robustness, so maximality forces o to lose it. ∎

Lemma EX is the step that closes Case (ii) of Proposition S1c₃ (§3), and the step the pool-optimal forest of the
4515 instance misses. A proof of ZMOVE along these lines would show that when every candidate move is blocked (§2.2),
the blockers and their threateners admit an exchange of Lemma EX type with a robust Q′_o; this was not achieved here
beyond n = 3 (§3).

## 3. Proposition S1c at n = 3 (written proof, not yet refereed)

The coordinator's dichotomy (from PR #85's `k4/thetab_xbt.py` on PR #80's dumps): at the Z′-maxima of the
non-completable f = 1 keys, exactly one terminal goes with a big-top x and two or more terminals with an x that is not
big-top. The first direction is Proposition S1 (`k4/oneneeder.md` §5, K4.ON.S, PROVED). The second is open
(K4.TB.S1C). Its proof cannot be local to P_Q: a Z′-maximum of a *completable* key can have a big-top x, two terminals
and def(P_Q) = 1 (`attempts/k4-zmh-s1c-plus.md`, n = 3, m = 8). The proof below uses that *every* configuration of κ
fails, through exchanges that park one lower good of x in a pair.

### 3.1 Facts

Let f = 1, κ = (g, x) with def*(κ) > 0, Q a Z′-maximum at κ. Write U_x = {b, c, d} when x has four goods.

- **(BT)** If x is big-top on g, a set Z ∌ g threatens x holding {g} iff U_x ⊆ Z and Z ≠ U_x. (`k4/oneneeder.md` §1:
  a proper subset of U_x is worth at most b + c < v_x(g); U_x plus one good x does not value is worth b + c + d > v_x(g)
  after that good is removed, by balance; U_x alone has θ = b + c.)
- **(Ω)** If x is big-top, ω ≥ 2, and U_x ⊆ X_o for every leaf o. (Every leaf threatens x, `k4/sx.md` Lemma F(c); by
  (BT) this needs U_x ⊊ X_o, so ω + 2 = |X_o| ≥ 4.) With two leaves o ≠ o′, U_x ⊆ X_o ∩ X_{o′} = L.
- **(F)** A free agent y with a filler (|H_y| = 1) values no good of L: for ℓ ∈ L ∩ R_y = L ∩ U_y the pair H_y ∪ {ℓ}
  ⊆ Q_y ∪ L would be worth more than Q_y, against pool-optimality (K4.C4MIN.RED.Z).
- **(T)** A terminal has top g (`k4/c4min_reduce.md` Lemma T). A terminal that holds two goods it values has four goods:
  a three-good agent with top g holding its two other goods holds more than g, by balance.
- **(θ₂)** (θ is monotone in the valued part.) If Y ∩ R_w ⊆ Z ∩ R_w and |Y| ≤ |Z|, then θ_w(Y) ≤ θ_w(Z). *Proof.* If
  Y ⊄ R_w, θ_w(Y) = v_w(Y ∩ R_w), and some h ∈ Z lies outside Y ∩ R_w (as |Y ∩ R_w| < |Y| ≤ |Z|), so
  θ_w(Y) ≤ v_w(Z ∖ h) ≤ θ_w(Z). If Y ⊆ R_w, then Y ⊆ Z; Y = Z is trivial, and otherwise some h ∈ Z ∖ Y gives
  θ_w(Y) ≤ v_w(Y) ≤ v_w(Z ∖ h). ∎ (This is Fact 2 of `k4/f2.md` §5.)
- **(K)** If some configuration Q* at κ has a free agent o whose bundle X*_o = Q*_o ∪ L* threatens nobody (x holding
  g, every free y ≠ o holding Q*_y), then def*(κ) ≤ 0 (`k4/sx.md` Lemma 0, K4.SX.KEY).

**Lemma PK (parking a pool good at a filler).** Let o be a leaf of Q, y ≠ o a free agent with a filler f (Q_y = H_y ∪
{f}, f ∉ R_y), and ℓ ∈ L. Let Q* be Q with y on H_y ∪ {ℓ} and the pool L* = (L ∖ {ℓ}) ∪ {f}. Then Q* is a configuration
at κ with the same holdings' values, and X*_o = (X_o ∖ {ℓ}) ∪ {f} threatens no free agent w that does not value f.

*Proof.* By (F) y does not value ℓ, so its admissible part stays H_y. For a free w ≠ o that does not value f (y is
one), X*_o ∩ R_w ⊆ X_o ∩ R_w and |X*_o| = |X_o|, so by (θ₂) θ_w(X*_o) ≤ θ_w(X_o) ≤ v_w(Q_w), the last because o is a
leaf. ∎

### 3.2 The proposition

**Proposition S1c₃.** Let n = 3, f = 1, κ = (g, x) with def*(κ) > 0, and Q a Z′-maximum at κ whose two free agents
y₁, y₂ are both terminals. Then x is not big-top.

*Proof.* Suppose x is big-top. By (Ω), ω ≥ 2. The threat forest on {y₁, y₂} has no cycle (`k4/sx.md` Lemma F(b)), so
either no threat edge joins them, or exactly one does.

*Case (i): no edge.* Both are leaves, and U_x ⊆ L by (Ω).
- If some y_i has a filler f, apply Lemma PK with y = y_i, o = y_{3−i} and any ℓ ∈ U_x. The only other free agent is
  y_i itself, which does not value f, so X*_o threatens no free agent; it misses ℓ ∈ U_x, so it does not threaten x
  (BT). By (K), def*(κ) ≤ 0: a contradiction.
- So both hold pairs of goods they value, and both have four goods (T). x has four goods and at most two private ones
  (K4.CORE (C3)); g is valued by the terminals; so some ℓ ∈ U_x is valued by y₁ or y₂, say y₁. Then ℓ ∈ L, and
  R_{y₁} = {g} ∪ U_{y₁} with U_{y₁} = Q_{y₁} ∪ {ℓ} (Q_{y₁} ⊆ U_{y₁}, three goods). Pool-optimality gives
  v(Q_{y₁}) ≥ v(h) + v(ℓ) for each h ∈ Q_{y₁}, so ℓ = u₃ and Q_{y₁} = {u₁, u₂} (u₁ > u₂ > u₃ the goods of U_{y₁}).
  Let Q* be Q with y₁ on {u₁, u₃} and the pool (L ∖ {u₃}) ∪ {u₂}. {u₁, u₃} is admissible (u₂ < u₁ + u₃), so Q* is a
  configuration at κ. X*_{y₂} = (X_{y₂} ∖ {u₃}) ∪ {u₂} misses u₃ ∈ U_x, so it spares x (BT). It meets R_{y₁} in {u₂}
  only (u₁, u₃ are y₁'s, g is x's), and v(u₂) < v(u₁) + v(u₃): it spares y₁. By (K), def*(κ) ≤ 0: a contradiction.

*Case (ii): one edge,* say y₁ threatens y₂. Then V = {y₂}. y₂ is threatened, hence not robust; it values g, so by
`k4/c4min_f1.md` Lemma 3 (K4.C4MIN.F1) it is of kind (Tg): four goods, H_{y₂} = {u₁} with u₁ < u₂ + u₃ (its goods of
U_{y₂} in decreasing order), and Q_{y₁} = {u₂, u₃}. By (Ω), U_x ⊆ X_{y₂} = Q_{y₂} ∪ L; as |Q_{y₂}| = 2 < 3 = |U_x|,
some ℓ ∈ U_x lies in L.
- If y₁ does not value one of u₂, u₃, that good is a filler of y₁. Lemma PK with y = y₁, o = y₂, this ℓ: X*_{y₂}
  spares y₁ (the only other free agent; y₁ does not value its filler) and x (it misses ℓ). By (K): a contradiction.
- So H_{y₁} = {u₂, u₃}, worth less than g to y₁ (a terminal), and y₁ has four goods (T): R_{y₁} = {g, u₂, u₃, w}. Write
  p, q for u₂, u₃ ordered by y₁'s values, v_{y₁}(p) > v_{y₁}(q). w lies outside Q_{y₁} and is not g, so
  w ∈ X_{y₂} = {u₁, f} ∪ L, where f is y₂'s filler.
  - *w ∈ L or w = f.* Let Q′ be Q with y₁ on {p, w}, y₂ on {u₁, q}, and the pool (L ∖ {w}) ∪ {f} (if w ∈ L) or L (if
    w = f). {p, w} is admissible for y₁ (its other lower good q is worth less than p) and robust (v(p) + v(w) > v(q));
    {u₁, q} is admissible and robust for y₂ (it contains u₁, and its remaining good is worth less than u₁). Q′ is a
    configuration at κ in which both free agents are robust, while y₂ is not robust in Q. So r′(Q′) > r′(Q), against
    the maximality of Q.
  - *w = u₁.* Then R_{y₁} = R_{y₂} = {g, u₁, u₂, u₃}. A lower good of x shared with another agent lies in
    U_x ∩ {u₁, u₂, u₃} ⊆ {u₁} (u₂, u₃ ∈ Q_{y₁} are outside X_{y₂} ⊇ U_x). By (C3) one exists, so u₁ ∈ U_x and the
    two other lower goods of x are private. Every good is relevant to some agent (K4.CORE), so
    M = {g, u₁, u₂, u₃} ∪ (two private goods of x), m = 6, and ω = m − 2n + f = 1, against (Ω). ∎

*What the proof uses.* Pool-optimality and the maximality of r′ (Theorem Z′, K4.C4MIN.RED.Z), the forest and the
kinds (K4.SX.KEY, K4.C4MIN.F1), non-completability through (K), and the core condition (C3). Two terminals enter
through (T) (a terminal holding a valued pair has four goods with g among them, which fixes R_{y₁}) and through Lemma 3's
kind (Tg). The data agree: on the n = 3 screen no non-completable key has a Z′-maximum with two terminals and a big-top
x (§3.4).

### 3.3 n ≥ 4: what the same exchanges give

The two exchanges (parking at a filler, Lemma PK; parking at a terminal valuing a pool lower good of x, Case (i)) and
the maximality exchange of Case (ii) are defined at every n. At n ≥ 4 each can be *blocked by a third agent*:
- Lemma PK at (o, y, ℓ) fails only if some free w ∉ {o, y} values y's filler f and is threatened by
  (X_o ∖ {ℓ}) ∪ {f};
- the exchange of Case (i) at a terminal y₁ (its pool lower good ℓ = u₃ parked, u₂ released) fails only if some free
  w ∉ {y₁, y₂} values u₂ and is threatened by (X_{y₂} ∖ {u₃}) ∪ {u₂};
- a lower good of x may be valued only by non-terminals, and with a single leaf the free agents form one threat path of
  length n − 2, so Case (ii)'s threatener need not be a terminal.

So S1c at n ≥ 4 reduces to the configurations in which every parking of a lower good of x is blocked by a third agent
(a *blocking system*), with the free agents on one threat path or U_x ⊆ L. A Hall-type count over the terminals would
have to show that a blocking system cannot cover all parkings while the two terminals compete for g; I did not find
it. S1c at n ≥ 4 stays CONJECTURE (K4.TB.S1C; data: PR #85's 82,098 maxima, and §3.4).

### 3.4 Data (EVIDENCE)

- *The statement.* `k4/zmh_s1c.py` on every f = 1 profile of compute/k4-cover's n = 3 screen (62,208 profiles,
  `results/k4_zmove_hall/s1c3.log`): at the non-completable keys, 22,752 Z′-maximum states have one terminal (x big-top at
  all of them: S1) and 62,120 have two (x big-top at none: S1c₃). The same counts in configurations, from PR #85, are
  40,174 and 82,098. The hypothesis "big-top x and two terminals" occurs at 64 Z′-maximum states of *completable* n = 3
  keys of the screen, all with ω = 1.
- *The steps.* `k4/zmh_s1c3_steps.py` tests each step of the proof as an implication on every pool-optimal
  configuration (not only maxima) of random n = 3 profiles with a big-top x and two terminals
  (`results/k4_zmove_hall/s1c3_steps_rand.log`; 6,000 random profiles per core, 376 configurations): Lemma PK 274 times,
  Case (i)'s exchange 3, Case (ii)'s kind 56 and its exchange 10, with no failure. On the screen these configurations do
  not occur with ω ≥ 2 (`results/k4_zmove_hall/s1c3_steps_screen.log`).
- *The local form fails* (`attempts/k4-zmh-s1c-plus.md`): of 127 Z′-maxima with a big-top x and two terminals in random
  n = 3, 4 profiles, 126 have def(P_Q) ≤ 0 and one has def(P_Q) = 1 at a completable key.

## 4. What remains

- **ZMOVE** (target): open. It holds at every Z′-maximum on all data here (§1) and on compute/k4-zmove's. The smallest
  instances where the proved lemma lists do not apply are compute/k4-cover's n = 4, m = 7 and n = 4, m = 10 keys (f = 2;
  repaired by C⁺ₕ-type moves with one helper); the smallest where the repair must start at the Z′-maximum rather than at
  an arbitrary state of the key are compute/k4-rc's cores 4604 (f = 1, m = 13) and 4515 (f = 2, m = 12; there even some
  pool-optimal configurations with acyclic threats fail, §2.3).
- **The Hall combination** (§2.2–§2.3): a statement saying that when every candidate move is blocked, the blockers and
  their threateners admit an r′-improving exchange (Lemma EX with a robust new pair for the threatener). Not formulated
  in a form that survives the data beyond the S1c₃ setting; the data say it must use r′-maximality, and that Λ′ is
  never needed.
- **Conjecture ZMOVE_r** (K4.ZMH.R): the one-move repair exists at every configuration that maximizes r′ (hence at
  every Z′-maximum). It holds at all r′-maximal configuration states in the runs of §2.3: 98,574 counted over the runs
  (16,171 at compute/k4-rc's cores with the small n = 4 hunts, 2,152 + 9,275 in PR #80's n = 4 hunts, the small ones
  counted twice, 60,738 in every 10th profile of the n = 3 screen, 10,238 in every 40th f ≥ 2 profile of the dumps).
- **S1c at n ≥ 4** (K4.TB.S1C): open; §3.3 reduces it to blocking systems. Smallest open case: n = 4, f = 1.
- ZMOVE at n = 3 is not proved here either (S1c₃ is one structural fact about its keys, not a repair).

## 5. Reproduce

One worker at a time; times on a shared 4-CPU machine. Inputs from other branches:
```
S=k4/suite/.cache/zmh; mkdir -p $S
git show origin/compute/k4-cover:results/k4_cover/screen/n3_all.jsonl.gz > $S/screen_n3_all.jsonl.gz   # f25fb8e
git show origin/compute/k4-cover:results/k4_cover/inputs/dumps_f2.jsonl.gz > $S/dumps_f2.jsonl.gz
git show origin/compute/k4-rc:results/k4_rc/rc_fail_all_inst.json > $S/rc4604.json
git show origin/compute/k4-rc:results/k4_rc/rc_fail_4515_all_inst.json > $S/rc4515.json
H=results/k4_sx/hunt
python3 k4/zmove_check.py $S/screen_n3_all.jsonl.gz                                   # zmove_n3_all.log (~8 min)
python3 k4/zmove_check.py $H/n4_3_r40k.jsonl.gz $H/n4_pure_r40k.jsonl.gz $H/n4_pure_r400k.jsonl.gz \
  $H/n5_pure_r1000_3000.jsonl.gz $H/n5_pure_r1000_4000.jsonl.gz                          # zmove_hunts_n45.log (~2 min)
python3 k4/zmove_check.py $S/dumps_f2.jsonl.gz --maxn=5 --every=8                       # zmove_dumps_f2_every8.log (~7 min)
python3 k4/zmh_classes.py $S/rc4604.json $S/rc4515.json $H/n4_3_r40k.jsonl.gz $H/n4_pure_r40k.jsonl.gz   # §2.3 (~5 min)
python3 k4/zmh_classes.py $S/screen_n3_all.jsonl.gz --every=10                          # classes_n3_n4.log (with the hunts)
python3 k4/zmh_classes.py $S/dumps_f2.jsonl.gz --maxn=5 --every=40                      # classes_dumps_f2_every40.log
python3 k4/zmh_zx.py ...                                                                # zx_forms.log (inputs on its first line)
python3 k4/zmh_s1c.py $S/screen_n3_all.jsonl.gz; python3 k4/zmh_s1c3_steps.py 6000 11   # §3.4
python3 k4/zmh_xcheck.py ...                                                            # xcheck.log (sample on its first line)
python3 attempts/k4_zmh_attempts.py                                                     # the three refutations, both implementations
```
