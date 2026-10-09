# Target ZMOVE by a Hall argument

Workstream `proof/k4-zmove-hall` (PR #88). Target: ZMOVE, the uniform repair from Theorem Z′'s state. Nothing here
changes K4.D or K4.T. Proposition S1c₃ (§3) was refereed in the PR #88 review and found correct (K4.ZMH.S1C3, PROVED);
the other statements are data (EVIDENCE) or conjectures.

**Target ZMOVE (open).** For every strict profile of every connected k = 4 core with f ≥ 1 and ω ≥ 1, and every key κ
with def*(κ) > 0: at some Z′-maximum Q of κ, some single (T3⁺) move from P_Q with at most one helper reaches a state P′
with def(P′) ≤ 0, or κ has a (T4) edge to a key with smaller def*. (The helper gives up a good of its base; (T3⁺) is
`lean/EFX/MovesC.lean` `MoveT3plus`, ledger K4.DL2.RC.) ZMOVE implies DLKey((T3⁺) ∪ (T4)) and so TARGET₄
(`lean/EFX/KeyFrame.lean`, `lean/EFX/MovesC.lean`).

**Status.** ZMOVE is not proved here, and the Hall-type contradiction argument asked for was not completed. What is
here:

- **Data (§1, EVIDENCE; K4.ZMH.E).** ZMOVE holds, in the stronger form *at every Z′-maximum* and *without (T4) edges*, at
  every key with def* > 0 of: every n = 3 profile (255,952 keys: 62,208 with f = 1 and 193,744 with f = 2; the profiles
  are those of compute/k4-cover's exhaustive screen, and the key counts agree with that screen and, at f = 1, with PR
  #80's `k4/red.c`); PR #80's n = 4 and n = 5 hunts (2,672 keys); the 369 / 1,076 DL_RC-failing profiles of
  compute/k4-rc's cores 4604 (f = 1) / 4515 (f = 2) (`results/k4_rc/rc_fail_all_inst.json`,
  `results/k4_rc/rc_fail_4515_all_inst.json`); compute/k4-cover's two COVER⁺ failures; every 8th f ≥ 2 profile (n ≤ 5)
  of compute/k4-cover's dumps (20,198 keys, f = 2, 3, 4). A second implementation (main's repo-free
  `k4/rt4_n5_indep.py` for the deficits and the move kinds, configurations enumerated directly as pairs) agrees key by
  key on samples of these inputs (§1). compute/k4-zmove reports the every-maximum form on its own data (its
  `phase2/n3_all.jsonl.gz` and `dumps_f2_p0.jsonl.gz` at 576da7c, checked by the PR #88 auditor; not read here). The
  every-maximum form is implied by Conjecture ZMOVE_r (K4.ZMH.R), not identical to it.
- **How much maximality is needed (§2.3, EVIDENCE; single implementation, `k4/zmh_lib.py`).** Every configuration that
  maximizes r′ alone (Λ′ ignored) has a repair, on all data tested. Pool-optimality together with Lemma F⁺'s forest does
  not suffice: at core 4515 there are pool-optimal states with acyclic free threats, at def*, without any one-move
  repair (`attempts/k4-zmh-pool-optimal-forest.md`). So a proof of ZMOVE must use more than pool-optimality and the
  forest; on the data r′-maximality suffices (Lemma EX, §2.3, is the exchange it gives). §3's own proof ends mostly in a
  completable configuration (fact (Kc) of §3.1) or in a count, and once in an r′-raising exchange.
- **The Hall form of the obstruction (§2).** For a fixed move and owner, def(P′) ≤ 0 is a covering condition: a hitting
  set of the owner's threat hypergraph no larger than the slots of the other free agents plus u′ (Lemma HF, a
  restatement of Lemma H1). In the removal-only deficit every removed good fits every slot, so for one move this "Hall
  condition" is a bare count; informally, the failures of the lemma lists are each one excess blocker (§2.2).
  Combining them over all moves into one Hall violation was not achieved.
- **Proposition S1c₃ (§3; PROVED, refereed in the PR #88 review; K4.ZMH.S1C3).** n = 3: at a Z′-maximum of a
  non-completable f = 1 key whose two free agents are both terminals, x is not big-top. This is the open direction
  K4.TB.S1C of the coordinator's terminal dichotomy (S1, K4.ON.S, is the other one) at n = 3. The proof parks a lower
  good of x by an exchange (Lemma PK), or uses an r′-raising exchange (Lemma EX), or the core conditions. §3.3 lists the
  steps that are specific to n = 3; S1c at n ≥ 4 is open.
- **Refuted (attempts/, K4.ZMH.X):** S1c⁺, the local form "big-top x and two terminals at a Z′-maximum ⇒ def(P_Q) ≤ 0"
  (n = 3, m = 8); ZX, "the unfrozen agent x can always be the new owner" (n = 3, m = 8: two θ-b terminal leaves, where
  only the other leaf can own, Lemma C's shape); ZMOVE from every pool-optimal state with acyclic free threats (n = 5,
  m = 12, core 4515). Observations on the data (single implementation; no attempts file): a helper is needed at some
  n = 3, f = 1 keys (45 of 3,119 sampled), and a frozen agent passing its good on (W ≠ ∅) at some f ≥ 2 keys (§1).

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
fillers, a matching of the free agents' empty slots to junk goods they do not value; the move classes T3, T3⁺, T4); `k4/zmh_check.py` (ZMOVE per
key and per Z′-maximum); `k4/zmh_xcheck.py` (a second implementation: main's repo-free `k4/rt4_n5_indep.py` for 𝒫, the
raw removal-only deficit and the move kinds, and the configurations enumerated directly as pairs, compared key by key
with `k4/zmh_lib.py`: def*, the set of Z′-maximum states, the number of good moves at each, the verdict);
`k4/zmh_zx.py` (the forms of the repair); `k4/zmh_roles.py` (roles of x, z, helper, owner).

| input | keys with def* > 0 (f = 1 / f ≥ 2) | Z′-maximum states | without a one-move repair | log |
|---|---|---|---|---|
| every n = 3 profile with a non-completable key (compute/k4-cover's screen at f25fb8e, 159,080 profiles) | 62,208 / 193,744 | 278,616 | 0 | `results/k4_zmove_hall/zmove_n3_all.log` |
| PR #80's n = 4 and n = 5 hunts (n4_3_r40k, n4_pure_r40k, n4_pure_r400k, n5_pure) | 2,672 / 0 | 3,317 | 0 | `results/k4_zmove_hall/zmove_hunts_n45.log` |
| compute/k4-cover's dumps of f ≥ 2 profiles (compute/k4-rt4, k4-dl13, k4-rc, k4-portfolio), n ≤ 5, every 8th | 0 / 20,198 (f = 2: 2,717; f = 3: 17,445; f = 4: 36) | 21,896 | 0 | `results/k4_zmove_hall/zmove_dumps_f2_every8.log` |
| the 369 / 1,076 DL_RC-failing profiles of compute/k4-rc's cores 4604 (f = 1) / 4515 (f = 2) (`results/k4_rc/`), with PR #80's small n = 4 hunts | 2,820 keys in all | 4,168 | 0 | `results/k4_zmove_hall/classes_rc_hunts.log` |
| compute/k4-cover's two COVER⁺ failures (n = 4, m = 7 and m = 10), one profile each of cores 4604 and 4515, four f = 3 profiles with a free agent whose goods all lie in 𝒩 (8 profiles: the first 8 records of `results/k4_zmove_hall/hard_inst.json`) | 1 / 20 | 23 | 0 | `results/k4_zmove_hall/zx_forms.log` (first block) |

Second implementation (`k4/zmh_xcheck.py`): `results/k4_zmove_hall/xcheck.log` and `xcheck2.log` (the samples are
listed on the logs' first lines: the hard instances, every 50th n = 3 screen profile, all of PR #80's small n = 4 hunts
and every 4th of the large one, every 8th profile of compute/k4-rc's cores, every 60th f ≥ 2 dump profile with n ≤ 5):
10,029 keys with def* > 0 and 11,202 Z′-maxima counted over the samples (with overlap), every one with a repair, and 0
mismatches with `k4/zmh_lib.py` in def*, the set of Z′-maximum states, the number of repairing moves at each, and the
verdict. For cores 4604 / 4515 the second implementation covers every 8th profile; the rest of those two cores is
single implementation (`k4/zmh_lib.py`). A third implementation (compute/k4-zmove's model.py-based checker) agrees with
`k4/zmh_lib.py` on 7,210 keys (PR #88 review; not rerun here). A bug found on the way: a free agent all of whose goods lie in 𝒩 has the empty
admissible part (U_y = ∅); `k4/zmh_lib.py` first treated such keys as having no configuration (f = 3 instances of the
dumps), both implementations were corrected, and the keys hold.

**Forms of the repair** (single implementation, `k4/zmh_lib.py`; `k4/zmh_zx.py`, `results/k4_zmove_hall/zx_forms.log`;
samples: every 20th profile of the n = 3
screen, PR #80's n = 4 hunts, every 5th profile of compute/k4-rc's cores, every 40th f ≥ 2 profile of the dumps with
n ≤ 5). Keys at which *no* Z′-maximum has a repair of the restricted form:

| form | n = 3 (3,119 keys f = 1; 9,670 f = 2) | n = 4 hunts (2,661, f = 1) | rc cores (504) | dumps (536 f = 2; 3,550 f = 3) |
|---|---|---|---|---|
| ZMOVE | 0 | 0 | 0 | 0 |
| ZMOVE, (T3) only (W = ∅) | 0 | 0 | 0 | 33; 805 |
| ZMOVE, no helper | 45 (f = 1) | 2 | 0 | 0 |
| ZX: x is a best owner after the move | 42 (f = 1) | 0 | 0 | 0 |
| ZX, no helper | 203 (f = 1) | 88 | 0 | 6; 1 |

So the uniform shapes one might hope for each fail somewhere on the data: the owner cannot always be x (two θ-b
terminal leaves, `attempts/k4-zmh-x-owner.md`, replayed by two implementations); and, as observations of this single
implementation only, a helper is needed already at n = 3, and at f ≥ 2 a frozen agent passing its good on
(`zx_forms.log` prints instances: n = 3, m = 7, f = 1 for the helper; n = 4, m = 6, f = 3 for W ≠ ∅).

## 2. The Hall form of the obstruction, and how much maximality it needs

### 2.1 One move: a covering count

Fix a move P_Q → P′ between min-frozen states and a free agent o′ of P′ (the would-be owner). Put W′ := B′_{o′} ∪ J′
(its largest bundle), s′ := Σ (2 − |B′_w|) over the free w ≠ o′ of P′ (the *slots* of the others), and let H be the
hypergraph of the minimal subsets of W′ that threaten some w ≠ o′ holding B′_w (the exact threat hypergraph of
`k4/hall.md` §1, Lemma H1; `k4/thetab.md` Corollary G1 uses the larger families E_w of minimal valued sets).
Since |J′| = ω + s′ + (2 − |B′_{o′}|) (`k4/c4x.md` §1: |J| − S = ω, and o′'s own slots are 2 − |B′_{o′}|), we have
|W′| = ω + 2 + s′, and Lemma H1 in P′ reads:

**Lemma HF (the covering form; a restatement of K4.HALL.COVER).** o′ certifies def(P′) ≤ 0 iff some C ⊆ J′ meets every
edge of H and |C| ≤ s′ + u′_{o′}(W′ ∖ C). In configuration language: each of the s′ slots receives one good of W′
(a "slot good"), u′ further goods may be dropped (paid by the frozen agents the owner's bundle unfreezes), the owner
keeps the rest, and the removed goods must hit every threat.

*Proof.* |W′ ∖ C| + u′ ≥ ω + 2 iff |C| ≤ s′ + u′, and W′ ∖ C is safe iff C meets every minimal threatening set
(threats are monotone). Lemma H1. ∎

The bipartite graph "removed goods × slots" of Lemma HF is *complete*: in the removal-only deficit a removed good may
go to any slot (`k4/c4x.md` §1). So Hall's condition for placing the removed goods is the bare count, and an
obstruction to one move at one owner is the inequality min over the hitting sets C of (|C| − u′(W′ ∖ C)) > s′, not a
Hall violation in the matching sense. A set S of threatened agents "served by fewer than |S| slot goods" arises only when the edges of H of different
agents of S are pairwise disjoint; then τ(H) ≥ |S|.

### 2.2 The failures of the lemma lists in this form (informal)

At a Z′-maximum every bundle X_o of ω + 2 goods threatens somebody (def*(κ) > 0), and each lemma of the lists is one
move with one owner and an explicit bundle. In the language of Lemma HF each failure is a single excess blocker:
- **A / A⁺** (owner x on X_o, o takes φ(x)): the only edge left is o's own threat (θ-b, or θ failing at the chain's
  end), or a second frozen agent threatened by X_o: one blocker more than s′.
- **B / B⁺** (owner x on X_o, helper o): the (R) leaf with s ∈ L is threatened by X_o holding Q_τ; B′ removes s and adds
  the released y; it fails when y creates an edge at a third agent ((H_B′)) or X″ has no admissible set of x.
- **C, C⁺** (another leaf owns Y = Q_o ∪ (X_τ ∖ P_x)): edges at third agents valuing the goods τ releases ((H)).
- **C′, C′⁺** (owner with ω + 1 goods): one edge paid by u′ = 1, which needs a good passing Fact 3 (no third needer).
- **C⁺ₕ, C′⁺ₕ**: the helper re-bases so that x's admissible set exists; same count.

The common pattern is: *one agent w is threatened by the would-be owner's bundle and no slot good is free to remove the
threat*. A "Hall violation" combining the failures over all x, z, helpers and bases A would be a set S of such blockers
with fewer free slot goods than |S|. To reach a contradiction it must produce a configuration at κ that beats Q.

### 2.3 How much of the maximality a proof must use (EVIDENCE)

`k4/zmh_classes.py` asks, for every state P of every key with def* > 0, whether some (T3⁺) move with at most one helper
from P reaches deficit ≤ 0, and groups the states: all states; configuration states; pool-optimal configurations; those
whose free threats form a forest; configurations maximizing r′ alone; the Z′-maxima. Single implementation
(`k4/zmh_lib.py`); the pool-optimal forest refutation is replayed by two (`attempts/k4_zmh_attempts.py`).

| input | keys | states without a move: all / pool-optimal / pool-optimal forest / r′-max / Z′-max | log |
|---|---|---|---|
| compute/k4-rc cores 4604 (369 profiles) and 4515 (1,076), PR #80's small n = 4 hunts | 2,820 | 4,673 of 92,439 / 42 of 12,693 / 42 of 12,689 / 0 of 16,171 / 0 of 4,168 | `results/k4_zmove_hall/classes_rc_hunts.log` |
| PR #80's n = 4 hunts (n4_3_r40k, n4_pure_r40k; n4_pure_r400k every 2nd record) | 1,482 | 0 / 0 / 0 / 0 / 0 | `results/k4_zmove_hall/classes_n3_n4.log` |
| every n = 3 profile with a non-completable key, every 10th (compute/k4-cover's screen) | 25,595 | 0 / 0 / 0 / 0 / 0 | `results/k4_zmove_hall/classes_n3_n4.log` |
| compute/k4-cover's f ≥ 2 dumps, n ≤ 5, every 40th | 4,086 | 12 of 14,812 / 0 of 7,530 / 0 of 7,529 / 0 of 10,238 / 0 of 4,421 | `results/k4_zmove_hall/classes_dumps_f2_every40.log` |

So:
- on the n = 3 sample and in PR #80's n = 4 hunts every state of every key with def* > 0 has such a move; the states without one are compute/k4-rc's (core 4604, f = 1: P_fail; core 4515, f = 2) and 12
  states of the f ≥ 2 dump sample, none of them r′-maximal;
- pool-optimality and the forest of Lemma F⁺ do not suffice: at core 4515, 42 pool-optimal states whose free
  threats form a forest have no move (`attempts/k4-zmh-pool-optimal-forest.md`; there an (R) agent threatened along the
  forest could become robust by an exchange with its threatener, which raises r′);
- maximality of r′ alone suffices on all these data: every configuration maximizing r′ (Λ′ ignored) has a move.

Hence a proof of ZMOVE must use more than pool-optimality and the forest; on the data r′-maximality suffices, and Λ′ is
never needed. The exchange that r′-maximality provides is this one:

**Lemma EX (an exchange along a threat edge; any f).** Let Q be a configuration at κ that maximizes r′, o → y a threat
between free agents with y not robust, and Q′_y ⊆ Q_o ∪ Q_y ∪ L a pair on which y is robust with an admissible part.
If o has a pair Q′_o ⊆ (Q_o ∪ Q_y ∪ L) ∖ Q′_y with an admissible part, then o is robust in Q and not robust on Q′_o.

*Proof.* Q with y on Q′_y, o on Q′_o and the pool (Q_o ∪ Q_y ∪ L) ∖ (Q′_y ∪ Q′_o) is a configuration at κ (pairs in
M ∖ 𝒩, admissible parts, ω pool goods). Only o and y change: y gains robustness, so maximality forces o to lose it. ∎

Lemma EX gives the r′-raising exchange of Case (ii) of Proposition S1c₃ (§3) (the other cases of that proof end in a
completable configuration or in a count), and it is the step the pool-optimal forest of the 4515 instance misses. A proof of ZMOVE along these lines would show that when every candidate move is blocked (§2.2),
the blockers and their threateners admit an exchange of Lemma EX type with a robust Q′_o; this was not achieved here
beyond n = 3 (§3).

## 3. Proposition S1c at n = 3 (PROVED: refereed in the PR #88 review, K4.ZMH.S1C3)

The coordinator's dichotomy (from PR #85's `k4/thetab_xbt.py` on PR #80's dumps): at the Z′-maxima of the
non-completable f = 1 keys, on the data, exactly one terminal goes with a big-top x and two or more terminals with an x
that is not big-top. The first direction is Proposition S1 (`k4/oneneeder.md` §5, K4.ON.S, PROVED). The second is open
(K4.TB.S1C). It cannot be proved by showing def(P_Q) ≤ 0 from the hypotheses at the maximum alone: a Z′-maximum of a
*completable* key can have a big-top x, two terminals and def(P_Q) = 1 (`attempts/k4-zmh-s1c-plus.md`, n = 3, m = 8). The proof below uses that *every* configuration of κ
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
- **(Kc)** If some configuration Q* at κ has a free agent o whose bundle X*_o = Q*_o ∪ L* threatens nobody (x holding
  g, every free y ≠ o holding Q*_y), then def*(κ) ≤ 0 (`k4/sx.md` Lemma 0, K4.SX.KEY). (Named (Kc) to keep it apart
  from Lemma K of `k4/c4min_reduce.md`.)

**Lemma PK (parking a pool good at a filler).** Let o be a leaf of Q, y ≠ o a free agent with a filler e (Q_y = H_y ∪
{e}, e ∉ R_y), and ℓ ∈ L. Let Q* be Q with y on H_y ∪ {ℓ} and the pool L* = (L ∖ {ℓ}) ∪ {e}. Then Q* is a configuration
at κ with the same holdings' values, and no free agent w ≠ o that does not value e is threatened by
X*_o = (X_o ∖ {ℓ}) ∪ {e}.

*Proof.* By (F) y does not value ℓ, so its admissible part stays H_y. For a free w ≠ o that does not value e (y is
one), X*_o ∩ R_w ⊆ X_o ∩ R_w and |X*_o| = |X_o|, so by (θ₂) θ_w(X*_o) ≤ θ_w(X_o) ≤ v_w(Q_w), the last because o is a
leaf. ∎

### 3.2 The proposition

**Proposition S1c₃.** Let n = 3, f = 1, κ = (g, x) with def*(κ) > 0, and Q a Z′-maximum at κ whose two free agents
y₁, y₂ are both terminals. Then x is not big-top.

*Proof.* Suppose x is big-top. By (Ω), ω ≥ 2. The threat forest on {y₁, y₂} has no cycle (`k4/sx.md` Lemma F(b)), so
either no threat edge joins them, or exactly one does.

*Case (i): no edge.* Both are leaves, and U_x ⊆ L by (Ω).
- If some y_i has a filler e, apply Lemma PK with y = y_i, o = y_{3−i} and any ℓ ∈ U_x. The only other free agent is
  y_i itself, which does not value e, so X*_o threatens no free agent; it misses ℓ ∈ U_x, so it does not threaten x
  (BT). By (Kc), def*(κ) ≤ 0: a contradiction.
- So both hold pairs of goods they value. x has four goods and at most two private ones (K4.CORE (C3)), so some lower
  good ℓ ∈ U_x is valued by another agent, y₁ or y₂, say y₁. Then ℓ ∈ L, y₁ has four goods (T), and
  R_{y₁} = {g} ∪ U_{y₁} with U_{y₁} = Q_{y₁} ∪ {ℓ} (Q_{y₁} ⊆ U_{y₁}, three goods). Pool-optimality gives
  v(Q_{y₁}) ≥ v(h) + v(ℓ) for each h ∈ Q_{y₁}, so ℓ = t₃ and Q_{y₁} = {t₁, t₂} (t₁ > t₂ > t₃ the goods of U_{y₁}).
  Let Q* be Q with y₁ on {t₁, t₃} and the pool (L ∖ {t₃}) ∪ {t₂}. {t₁, t₃} is admissible (t₂ < t₁ + t₃), so Q* is a
  configuration at κ. X*_{y₂} = (X_{y₂} ∖ {t₃}) ∪ {t₂} misses t₃ ∈ U_x, so it spares x (BT). It meets R_{y₁} in {t₂}
  only (t₁, t₃ are y₁'s, g is x's), and v(t₂) < v(t₁) + v(t₃): it spares y₁. By (Kc), def*(κ) ≤ 0: a contradiction.

*Case (ii): one edge,* say y₁ threatens y₂. Then V = {y₂}. y₂ is threatened, hence not robust; it values g, so by
`k4/c4min_f1.md` Lemma 3 (K4.C4MIN.F1) it is of kind (Tg): four goods, H_{y₂} = {u₁} with u₁ < u₂ + u₃ (its goods of
U_{y₂} in decreasing order), and Q_{y₁} = {u₂, u₃}. By (Ω), U_x ⊆ X_{y₂} = Q_{y₂} ∪ L; as |Q_{y₂}| = 2 < 3 = |U_x|,
some ℓ ∈ U_x lies in L.
- If y₁ does not value one of u₂, u₃, that good is a filler of y₁. Lemma PK with y = y₁, o = y₂, this ℓ: X*_{y₂}
  spares y₁ (the only other free agent; y₁ does not value its filler) and x (it misses ℓ). By (Kc): a contradiction.
- So H_{y₁} = {u₂, u₃}, worth less than g to y₁ (a terminal), and y₁ has four goods (T): R_{y₁} = {g, u₂, u₃, r}. Write
  p, q for u₂, u₃ ordered by y₁'s values, v_{y₁}(p) > v_{y₁}(q). r lies outside Q_{y₁} and is not g, so
  r ∈ X_{y₂} = {u₁, e} ∪ L, where e is y₂'s filler.
  - *r ∈ L or r = e.* Let Q′ be Q with y₁ on {p, r}, y₂ on {u₁, q}, and the pool (L ∖ {r}) ∪ {e} (if r ∈ L) or L (if
    r = e). {p, r} is admissible for y₁ (its other lower good q is worth less than p) and robust (v(p) + v(r) > v(q));
    {u₁, q} is admissible and robust for y₂ (it contains u₁, and its remaining good is worth less than u₁). Q′ is a
    configuration at κ in which both free agents are robust, while y₂ is not robust in Q. So r′(Q′) > r′(Q), against
    the maximality of Q (Lemma EX of §2.3 with o = y₁, y = y₂).
  - *r = u₁.* Then R_{y₁} = R_{y₂} = {g, u₁, u₂, u₃}. A lower good of x shared with another agent lies in
    U_x ∩ {u₁, u₂, u₃} ⊆ {u₁} (u₂, u₃ ∈ Q_{y₁} are outside X_{y₂} ⊇ U_x). By (C3) one exists, so u₁ ∈ U_x and the
    two other lower goods of x are private. Every good is relevant to some agent (K4.CORE (C5)), so
    M = {g, u₁, u₂, u₃} ∪ (two private goods of x), m = 6, and ω = m − 2n + f = 1, against (Ω). ∎

*What the proof uses.* Pool-optimality and the maximality of r′ (Theorem Z′, K4.C4MIN.RED.Z), the forest and the
kinds (K4.SX.KEY, K4.C4MIN.F1), Lemmas K and T of `k4/c4min_reduce.md` (the keys at f = 1 and the terminals' top),
non-completability through (Kc), and the core conditions (C2) (strict balance, in (BT) and (T)), (C3) and (C5). Two
terminals enter through (T) (a terminal holding a valued pair has four goods with g among them, which fixes R_{y₁}) and
through Lemma 3's kind (Tg). The data agree: on the n = 3 screen no non-completable key has a Z′-maximum with two
terminals and a big-top x (§3.4).

### 3.3 Where the n = 3 argument stops

The steps of the proof that use n = 3 (each fails, or needs a new argument, at n ≥ 4):
- *Third agents.* Lemma PK and the exchange of Case (i) leave the parking bundle safe only for agents that do not value
  the released good (the filler e, resp. t₂); at n = 3 there is no third free agent, at n ≥ 4 one valuing it may be
  threatened.
- *r in a third agent's pair.* In Case (ii) the fourth good r of y₁ lies in X_{y₂} because at n = 3 every good other
  than g lies in Q_{y₁} ∪ Q_{y₂} ∪ L; at n ≥ 4 it may lie in another agent's pair, and the r′-raising exchange is not
  available.
- *r = u₁ and the count m = 6.* Case (ii)'s last case counts all goods of the three agents; at n ≥ 4 the other agents'
  goods break the count.
- *A leaf that is not a terminal.* Case (ii) uses that the leaf y₂ values g, so its kind is (Tg); at n ≥ 4 the leaf may
  be a non-terminal of any kind of `k4/c4min_f1.md` Lemma 3, and the threat path from a terminal may be longer.
- *Three or more terminals.* At n ≥ 4 there may be three or more terminals; on the data this happens at 168 maxima with
  n = 4 (the PR #88 review's count).

S1c at n ≥ 4 stays CONJECTURE (K4.TB.S1C; data: PR #85's maxima, and §3.4). No reduction to a smaller statement is
claimed.

### 3.4 Data (EVIDENCE; single implementation, `k4/zmh_lib.py`)

- *The statement.* `k4/zmh_s1c.py` on every f = 1 profile of compute/k4-cover's n = 3 screen (62,208 profiles,
  `results/k4_zmove_hall/s1c3.log`): at the non-completable keys, 22,752 Z′-maximum states have one terminal (x big-top at
  all of them: S1) and 62,120 have two (x big-top at none: S1c₃). PR #85's n = 3 counts, in configurations, are 39,840
  and 76,408 (its totals 40,174 and 82,098 include n = 4, 5). The hypothesis "big-top x and two terminals" occurs at 64
  Z′-maximum states of *completable* n = 3 keys of the screen; there ω = 1, and none of them has ω ≥ 2
  (`results/k4_zmove_hall/s1c3_steps_screen.log`, where no configuration qualifies).
- *The steps.* `k4/zmh_s1c3_steps.py` tests each step of the proof as an implication on every pool-optimal
  configuration (not only maxima) of random n = 3 profiles with a big-top x and two terminals: 1,500 random profiles
  per core with seed 7 (the first block of `results/k4_zmove_hall/s1c3.log`; 84 configurations) and 6,000 per core with
  seed 11 (`results/k4_zmove_hall/s1c3_steps_rand.log`; 376 configurations: Lemma PK 274 times, Case (i)'s exchange 3,
  Case (ii)'s kind 56 and its exchange 10), with no failure.
- *The local form fails* (`attempts/k4-zmh-s1c-plus.md`): of 127 Z′-maxima with a big-top x and two terminals in
  146,430 random n = 3, 4 profiles (4,418 with f = 1), 126 have def(P_Q) ≤ 0 and one (n = 4, m = 11) has def(P_Q) = 1 at
  a completable key (`results/k4_zmove_hall/s1c_plus_rand.log`); the n = 3, m = 8 witness comes from a smaller run
  (`results/k4_zmove_hall/s1c_plus_rand_seed1.log`).

## 4. What remains

- **ZMOVE** (target): open. It holds at every Z′-maximum on all data here (§1) and, as reported, on compute/k4-zmove's.
  The smallest instances where the helper-free lemmas (A⁺, B⁺, C⁺, C′⁺) do not apply are compute/k4-cover's n = 4,
  m = 7 and n = 4, m = 10 keys (f = 2); Lemmas C⁺ₕ / C′⁺ₕ (K4.F2.CCH) cover them with one helper. The smallest where the
  repair must start at the Z′-maximum rather than at an arbitrary state of the key are compute/k4-rc's cores 4604 (f = 1,
  m = 13) and 4515 (f = 2, m = 12; there even some pool-optimal states with acyclic threats fail, §2.3).
- **The Hall combination** (§2.2–§2.3): a statement saying that when every candidate move is blocked, the blockers and
  their threateners admit an exchange that beats Q. Not formulated in a form that survives the data beyond the S1c₃
  setting; the data say it must use more than pool-optimality and the forest (r′-maximality suffices there), and that
  Λ′ is never needed.
- **Conjecture ZMOVE_r** (K4.ZMH.R): the one-move repair exists at every configuration that maximizes r′ (hence at
  every Z′-maximum). It holds at all r′-maximal configuration states in the runs of §2.3 (single implementation): 98,574
  counted over the runs (16,171 at compute/k4-rc's cores with the small n = 4 hunts, 2,152 + 9,275 in PR #80's n = 4
  hunts, the small ones counted twice, 60,738 in every 10th profile of the n = 3 screen, 10,238 in every 40th f ≥ 2
  profile of the dumps).
- **S1c at n ≥ 4** (K4.TB.S1C): open; §3.3 lists where the n = 3 argument stops. This includes the case of three or
  more terminals (168 maxima at n = 4 on the data). Smallest open case: n = 4, f = 1.
- **S1c₃ and COVER at n = 3.** S1c₃ has no new consequence for K4.SX.COVER at n = 3: Lemma P(iii) of `k4/thetab.md`
  (K4.TB.P) already excludes its exception (E) there. ZMOVE at n = 3 is not proved here either.

## 5. Reproduce

One worker at a time; times on a shared 4-CPU machine. Inputs from other branches, pinned:
```
S=k4/suite/.cache/zmh; mkdir -p $S
git show f25fb8e:results/k4_cover/screen/n3_all.jsonl.gz > $S/screen_n3_all.jsonl.gz      # compute/k4-cover at f25fb8e
git show f25fb8e:results/k4_cover/inputs/dumps_f2.jsonl.gz > $S/dumps_f2.jsonl.gz
R=results/k4_rc; H=results/k4_sx/hunt; Z=results/k4_zmove_hall                              # results/k4_rc/ is on main
python3 k4/zmh_check.py $S/screen_n3_all.jsonl.gz                                          # zmove_n3_all.log (~8 min)
python3 k4/zmh_check.py $H/n4_3_r40k.jsonl.gz $H/n4_pure_r40k.jsonl.gz $H/n4_pure_r400k.jsonl.gz \
  $H/n5_pure_r1000_3000.jsonl.gz $H/n5_pure_r1000_4000.jsonl.gz --out=$Z/zmove_hunts_n45.jsonl.gz   # zmove_hunts_n45.log (~2 min)
python3 k4/zmh_check.py $S/dumps_f2.jsonl.gz --maxn=5 --every=8                            # zmove_dumps_f2_every8.log (~7 min)
python3 k4/zmh_classes.py $R/rc_fail_all_inst.json $R/rc_fail_4515_all_inst.json $H/n4_3_r40k.jsonl.gz \
  $H/n4_pure_r40k.jsonl.gz                                                                    # classes_rc_hunts.log (~5 min)
python3 k4/zmh_classes.py $H/n4_3_r40k.jsonl.gz $H/n4_pure_r40k.jsonl.gz; python3 k4/zmh_classes.py $H/n4_pure_r400k.jsonl.gz --every=2; \
  python3 k4/zmh_classes.py $S/screen_n3_all.jsonl.gz --every=10                              # classes_n3_n4.log
python3 k4/zmh_classes.py $S/dumps_f2.jsonl.gz --maxn=5 --every=40 --show=3                  # classes_dumps_f2_every40.log
python3 k4/zmh_zx.py $Z/hard_inst.json --max=8; python3 k4/zmh_zx.py $S/screen_n3_all.jsonl.gz --every=20; \
  python3 k4/zmh_zx.py $H/n4_3_r40k.jsonl.gz $H/n4_pure_r40k.jsonl.gz $H/n4_pure_r400k.jsonl.gz; \
  python3 k4/zmh_zx.py $R/rc_fail_all_inst.json $R/rc_fail_4515_all_inst.json --every=5; \
  python3 k4/zmh_zx.py $S/dumps_f2.jsonl.gz --maxn=5 --every=40                               # zx_forms.log
python3 k4/zmh_s1c3_steps.py 1500 7; python3 k4/zmh_s1c.py $S/screen_n3_all.jsonl.gz --show=0   # s1c3.log
python3 k4/zmh_s1c3_steps.py 6000 11                                                       # s1c3_steps_rand.log (~8 min)
python3 k4/zmh_s1c3_steps.py $S/screen_n3_all.jsonl.gz                                     # s1c3_steps_screen.log (~5 min)
python3 k4/zmh_s1c.py rand:results/k4_certs_3.json.gz:2500:3 rand:results/k4_certs_4_pure.json.gz:40:4 \
  rand:results/k4_certs_4_n4_3.json.gz:30:5 --show=4                                         # s1c_plus_rand.log (~6 min)
python3 k4/zmh_s1c.py rand:results/k4_certs_3.json.gz:300:1 --show=3                       # s1c_plus_rand_seed1.log
python3 k4/zmh_xcheck.py $Z/hard_inst.json; python3 k4/zmh_xcheck.py $S/screen_n3_all.jsonl.gz --every=500; \
  python3 k4/zmh_xcheck.py $H/n4_3_r40k.jsonl.gz --every=5; python3 k4/zmh_xcheck.py $H/n4_pure_r40k.jsonl.gz --every=20; \
  python3 k4/zmh_xcheck.py $H/n4_pure_r400k.jsonl.gz --every=100; \
  python3 k4/zmh_xcheck.py $R/rc_fail_all_inst.json $R/rc_fail_4515_all_inst.json --every=60; \
  python3 k4/zmh_xcheck.py $S/dumps_f2.jsonl.gz --every=500 --maxn=5                         # xcheck.log
python3 k4/zmh_xcheck.py $S/screen_n3_all.jsonl.gz --every=50; python3 k4/zmh_xcheck.py $H/n4_3_r40k.jsonl.gz $H/n4_pure_r40k.jsonl.gz; \
  python3 k4/zmh_xcheck.py $H/n4_pure_r400k.jsonl.gz --every=4; \
  python3 k4/zmh_xcheck.py $R/rc_fail_all_inst.json $R/rc_fail_4515_all_inst.json --every=8; \
  python3 k4/zmh_xcheck.py $S/dumps_f2.jsonl.gz --every=60 --maxn=5                          # xcheck2.log (~10 min)
python3 attempts/k4_zmh_attempts.py                                                        # attempts_replay.log: the three refutations, both implementations
```
(The xcheck and zx runs that produced the logs read the 4604 / 4515 lists from compute/k4-rc, identical to main's
`results/k4_rc/` files; `zmove_hunts_n45.log` and the zmove logs were produced under the script's earlier name
`k4/zmove_check.py`.)
