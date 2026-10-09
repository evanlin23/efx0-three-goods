# Referee report on `k4/zmove_f1.md` §2–§4 (PR #91)

An independent review of the written proofs of `k4/zmove_f1.md` (Lemma JO, Lemma CNT, Corollary R1, Lemma ABS,
Corollary E; ledger row K4.ZF1.CNT) and a re-run of its evidence (ledger row K4.ZF1.BT4), made by an AI session that did
not write them, on the PR's branch after merging main at d21d3f7 (PR #88 and PR #92 merged). Every step was checked
against the definitions and PROVED lemmas it cites: `k4/c4min.md` §1 (configurations, admissibility, valid owners),
`k4/c4min_reduce.md` §1–§3 (Lemmas K, T, Theorem Z′, Lemmas D and C), `k4/c4min_f1.md` Lemmas 1, 3 and 8, `k4/sx.md`
§1–§3 (Lemma 0, Lemma F, θ-b), `k4/f2.md` §5 Fact 2, `k4/thetab.md` §7 (Lemma P and the exception (E)), and K4.CORE.

**Verdict.** I found no mathematical error in Lemma JO, Lemma CNT, Corollary R1, Lemma ABS or Corollary E. Every step
follows from the cited definitions and PROVED rows. The remarks below are citations and wording, fixed in
`k4/zmove_f1.md` and the ledger in the same commit. This is one review and does not change the row's status (it stays
CONJECTURE; an upgrade to PROVED is left to the owner). In the data section, two statements were not
reproducible as written (the n = 3 hill-climb rate, and an n = 3 observation that holds only on the sample it was
made on); both are corrected in the text, with logs. Every other number matches.

## 1. The written proofs, step by step

**Setting and facts (§0).** Correct, with two citation fixes.
- (Z′): Theorem Z′ (K4.C4MIN.RED.Z). Its proof indeed derives "at most one threatener" from y's own pool-optimality,
  |X| = ω + 2 ≥ 3 and L ≠ ∅, with the kinds of `k4/c4min_f1.md` Lemma 3.
- (BT): `k4/c4min_f1.md` Lemma 8(a) is stated for X = Q_o ∪ L, but its proof uses only g ∉ X, so it holds for every
  Z ∌ g, as used. It needs balance (b + c + d > a), which every core agent has (K4.CORE (C2)).
- (K): `k4/sx.md` Lemma 0 (K4.SX.KEY).
- (θ₂): `k4/f2.md` §5 Fact 2. Its ledger row is K4.F2.CC (PROVED), which K4.ZF1.CNT did not list. *Fixed.*
- "A set worth more than an admissible set is admissible" (used in JO): `k4/c4min.md` §1, one line. It needs the
  set to have one or two goods inside U_w, which holds in every use.

**Lemma JO.** Correct.
- The count: |B ∖ Q_w| = |D|. |B ∩ Φ| goods of D replace the fillers in B, and the other |B ∩ L| go to the pool, so
  the pool keeps ω goods. The two goods of B ∖ Q_w that are fillers belong to different agents: a pair holds at most
  one filler, since its admissible part is nonempty.
- Each y whose filler is replaced keeps H_y, so its new part contains H_y and is admissible. Its value and level do
  not fall, and robustness is monotone in v_y(Q_y), since v_y(U_y ∖ Q_y) = v_y(U_y) − v_y(H_y).
- w: B ⊆ M′, so v_w(B) = v_w(B ∩ U_w) > v_w(H_w). Hence B ∩ U_w is admissible, and Λ′ rises strictly while r′ does not
  fall. This contradicts the Z′-maximality of Q.
- (a) and (b) are the two obvious choices of B. (b) uses strictness (v(z) ≠ v(h)).

**Lemma CNT.** Correct. It is the big-top case of Lemma C of `k4/c4min_reduce.md` §3 (K4.C4MIN.RED.C, PROVED). For a
big-top balanced x, t = [v_x(L ∩ U_x) > v_x(g)] = 1 iff U_x ⊆ L, since a proper subset of U_x is worth at most b + c.
So L_x ⊄ L* is t = 0, and Lemma D(ii) gives |D_x| ≤ 1 < 2 ≤ r′. The text called it "Theorem Z′(i) with Lemma D(ii)", and
the ledger row put Lemma D under K4.C4MIN.RED.Z; Lemma D and Lemma C are in K4.C4MIN.RED.C. *Fixed.* The PR's own proof
is self-contained and also correct:
- the injective threat map gives at least r′ ≥ 2 free-valid owners;
- (BT) puts L_x ∖ L* ≠ ∅ inside the pair of every owner that threatens x, so at most one owner does;
- the remaining owner is valid with C = ∅, since X_o contains H_o and threatens nobody;
- Lemma 0 gives def*(κ) ≤ 0.

**Corollary R1.** Correct.
- A Z′-maximum maximizes r′ over all configurations at κ, so r′(Q) ≤ 1 suffices for "every configuration".
- (a) is CNT applied to Q itself.
- (b) The configuration Q*:
  - JO(a) gives ℓ ∉ R_y, so H*_y = H_y, y's complement U_y ∖ Q*_y is unchanged, and every robust status is kept.
  - Q*_y ∪ L* = Q_y ∪ L.
  - For w ≠ y, Q_w ∪ L* ⊆ Q_w ∪ L ∪ Φ₋w, since the released filler belongs to y ≠ w. So JO gives pool-optimality of
    Q*, Theorem Z′ gives at most one threatener per free agent, ℓ ∉ L*, and CNT applies.
- (c) The kinds (T3), (Tg), (T4) of `k4/c4min_f1.md` Lemma 3 have |H_y| = 1, hence a filler. A non-robust agent that
  values g is of kind (Tg), since a 3-good agent valuing g is robust and (T3), (T4), (D), (R) have g ∉ R_y. So in shape
  (I) every terminal is robust, as the summary says.

**Note before ABS** (robust ⇒ admissible for B ⊆ U_w). Correct, by strictness: {z} ≠ B are distinct nonempty sets.

**Lemma ABS.** Correct.
- Q* (w on B, pool (L ∖ ℓ) ∪ {h}) is a configuration at κ, with r′(Q*) ≥ r′(Q) ≥ 2, w robust, and ℓ ∉ L*.
  Shape (I) includes r′(Q) ≥ 2 by its definition in R1(c).
- X*_w = X_w, and X*_o = (X_o ∖ ℓ) ∪ {h} for o ≠ w. Every bundle meets R_y inside U_y ∖ Q_y.
- y does not value h: (θ₂) shows that y's threateners in Q* are among its threateners in Q.
- y values h and is of kind (D):
  - a single good of {b, c} is worth at most b < a < a + d, so a threat needs {b, c} ⊆ X*_o;
  - two threateners put b, c in X*_{o₁} ∩ X*_{o₂} = L* (the pairs are disjoint);
  - at most one of b, c is h, so the other lies in L, and pool-optimality fails ({a, b} or {a, c} beats {a, d}).
- y values h and is of kind (R):
  - a and s are each worth less than p + q ({p, q} is admissible), so a threat needs both;
  - a ∉ L (pool-optimality, as a + p > p + q), so a = h and s ∈ L ∖ {ℓ};
  - Q** is a configuration: {a, s} contains y's top, and the pool (L ∖ {ℓ, s}) ∪ {p, q} has ω goods;
  - y becomes robust (a + s > p + q, the threat condition), w is robust, and nobody else changes, so r′ rises,
    contradicting maximality.
- So CNT applies to Q*.
- Instance (i): B ∩ U_w = {k} is admissible (k is the top of U_w) and robust by hypothesis.
- Instance (ii): {h₁, ℓ} is robust because U_w ∖ {h₁, ℓ} ⊆ {h₂}. The appeal to JO(b) there is true but not needed.

**Corollary E.** Correct.
- Setting: θ-b terminals are robust (`k4/sx.md` §3: Q_τ = {u₁, u₂}, u₃ ∈ L). With two of them r′(Q) ≥ 2, and R1(c)
  gives shape (I).
- (E1): ABS (i) with k = α_i. τ_i does not value ℓ ∈ L_x, because L_x ∩ U_τᵢ = ∅ and ℓ ≠ g. Steepness
  α ≥ β + γ would be exactly instance (i)'s robustness.
- (E2):
  - w ∉ {τ₁, τ₂}, and w holds two valued goods (shape (I)).
  - U_w ⊆ {h₁, h₂, ℓ} is instance (ii). Otherwise a fourth good z exists, R_w = {h₁, h₂, ℓ, z} and g ∉ R_w.
  - Robustness of {h₁, ℓ} would be ABS. Its negation h₁ + ℓ < h₂ + z forces z > ℓ.
  - z ∈ L_x would make {h₁, z} robust (h₁ + z > h₂ + ℓ), which is ABS again.
  - h₁, h₂ ∉ L_x because L_x ⊆ L. So ℓ is the only lower good of x that w values.
- (E3): K4.CORE (C3) gives x at most two private goods. g is not private (τ₁ values it), so some lower good of x is
  valued by another agent, and by (E) that agent is not a terminal. *Wording made explicit.*
- Minor: §3 states (E) without its last condition v_x(p) < v_x(q) + v_x(r) (`k4/thetab.md` Lemma P (ii)). The results
  hold under the weaker hypothesis, so nothing changes. *Noted in the text.*

**Plan text (§3 "What remains", "The plan for S1c").** Not claimed as proved. The factual sub-claims are right:
- z ∈ L forces v(z) < v(h₂) (JO(b));
- with z in another pair and {h₁, ℓ} admissible, after w → {h₁, ℓ} only the holder of z can threaten w;
- with z ∈ L every owner threatens w (|X*_o| ≥ 4 since ω ≥ 2 in (E));
- a (Tg) terminal's u₂, u₃ lie in other agents' valued parts (JO(a)).

**§1 (stale after the merge).** PR #88 is merged and Proposition S1c₃ is PROVED (K4.ZMH.S1C3). The text called it
"unrefereed". It also listed four places where the n = 3 argument stops, while `k4/zmove_hall.md` §3.3 lists five; the
first one ("third agents" that value the released good) was missing. *Fixed.*

## 2. Evidence: re-runs

All re-runs on the merged branch, 4 CPUs, from the commands in the logs.

| log | re-run | result |
|---|---|---|
| `count_hunts.log` (`k4/zf1_count.py`, 6 dumps) | identical | 2,691 non-completable keys at n ≥ 4 (2,679 + 12), 4,253 Z′-maxima, none big-top; 135 big-top at n = 3 |
| sanity check (`n4_3_r40k`, `n4_pure_r40k`) | `k4/zf1_count.py` on the two files | 299 keys, 565 maxima (553 + 12), as in `k4/sx.md` §4.2 |
| `embed_n4.log` | identical except the time (26 s vs 28 s) | 400 bases, 16,000 f = 1 profiles, 20,679 big-top keys, all completable |
| `embed_n5.log` | identical | 120 bases, 3,480 f = 1 profiles (120 with f ≠ 1), 5,254 big-top keys, all completable |
| `bthunt_n4_s11.log` | identical (the `--dump` path differs; the dump stays empty) | 500 runs: 498 end with big-top f = 1 keys, all completable; 2 end at profiles without one (score ∞) |
| `eshape_n4_z4.log` | identical except the time (751 s vs 742 s) | 248,832 profiles; (0, x) not a key 11,520; a key and completable 237,312 |

Totals in the PR description: 19,480 structured extensions = 16,000 + 3,480 ✓. The `k4/thetab.md` §7.1 table agrees
with `count_hunts.log` (n = 5 hunts + compute/k4-rc + T1-stuck: 1,297 = 11 + 45 + 1,241 keys).

**Not reproduced as written.**
- *"The same search at n = 3 finds one in 60 runs."* With the committed `k4/zf1_bthunt.py` on `k4_certs_3` (18 cores
  with ω ≥ 2), 60 runs find a non-completable big-top key in 2 to 9 runs depending on the seed (seeds 1–12,
  `bthunt_n3_seeds.log`), and 600 runs (seed 1) find 39 (`bthunt_n3_s1.log`). The first session's run was not logged.
  The search is less weak at n = 3 than stated, which slightly strengthens the n = 4 null result. *Text corrected.*
- *"At every non-completable key whose x is not big-top both free agents are big-top on g"* (n = 3, every 20th profile
  of `n3_all_30`, `n3_all_40`, not logged). This holds on that sample: 1,247 keys (`indep_n3_every20.log`). It fails on
  the rest of the n = 3 data (`indep_n3_all.log`, all of PR #80's `n3_all_*` dumps, i.e. every strict n = 3 profile
  with a non-completable key). Of the 47,328 keys with x not big-top:
  - 34,080 have both free agents big-top on g;
  - 7,296 have one;
  - 5,952 have none.

  Smallest instance: core 17 of `k4_certs_3`, m = 6, sets [[0,1,4,5],[2,3,4,5],[2,3,4,5]], values
  [[2,7,6,10],[2,4,5,8],[2,4,5,8]]. Its key (5, agent 0) is non-completable, and no agent is big-top.

  The companion statement does hold on all the n = 3 data: at each of the 14,880 non-completable keys with x big-top,
  exactly one free agent values g. Neither statement is a lemma of the PR, so no attempts file is needed. *Text
  corrected.*

## 3. Independent check (second implementation)

`k4/zf1_indep.py`, written for this review from `k4/c4x.md` §1. It does not use configurations, Lemma K or Lemma 0, and
it imports nothing from the repository.
- It enumerates the valid pre-allocations with one frozen agent: NA = {g}, the frozen agent on {g}, the other bases
  avoiding g with needs inside {g}.
- It decides f = 0 by need-free disjoint bases.
- It decides def*(κ) ≤ 0 by the removal-only deficit itself: every free owner, every C ⊆ J up to the available slots,
  the threat test on every other agent holding its base, and the slots recomputed with the owner's needs from its
  bundle (the unfreezing clause).
- It builds its own list of strict balanced 4-good types (288, the count of `k4/SCOUT.md`) and the (E)-shaped domain:
  12 big-top types each for x, τ₁, τ₂, and 144 types with (C4) for w.

| input | result | log |
|---|---|---|
| (E)-shaped n = 4 core, every profile of the domain (248,832) | f = 1 at 248,736, f ≥ 2 at 96. (0, x) is not a key at 11,520 (11,424 + 96, as the PR's tool) and is a completable key at 237,312 (as the PR's tool). Every f = 1 key of every profile is completable, including those of the other two big-top agents: (0, τ₁) at 245,376 profiles, (0, τ₂) at 239,616 | `indep_eshape_n4_z4.log` (200 s, 3 processes) |
| the six dumps of `count_hunts.log` | 1,222 / 2,679 / 12 non-completable keys at n = 3 / 4 / 5; big-top only at n = 3 (135). Identical to `k4/zf1_lib.py` | `indep_count_hunts.log` |
| n = 3, all of PR #80's `n3_all_*` dumps, and every 20th profile of `n3_all_30`, `n3_all_40` | §2 above | `indep_n3_all.log`, `indep_n3_every20.log` |

So the key claim of K4.ZF1.BT4 on these inputs (no non-completable f = 1 key with a big-top frozen agent at n ≥ 4) is
now confirmed by two implementations that compute completability by different routes (configurations vs.
pre-allocations and deficits). The 19,480 extension profiles and the 500 hill-climbs were not dumped, so they remain
single implementation.

## 4. Consistency with PR #87 on (E)

Read on `origin/proof/k4-zmove-pot` at 19fe9c1 (`k4/zmove_pot.md` §4, Proposition ℛ and the last lemma of §4).

#87's (E) is state-level. Its hypotheses:
- every free agent robust, every terminal locally optimal (H_AR);
- every terminal θ-b at P, S = 0, |T| = 2;
- U_x ∩ U_τ = ∅ for both terminals, U_x ⊆ J;
- x big-top, and v_x(p) < v_x(q) + v_x(r).

At P_Q of an all-robust Z′-maximum this is Lemma P's (E) with all free agents robust, so it is a special case of the (E)
treated here. The two PRs agree:
- **Terminals fragile / non-steep.** #87 proves that in (E) every terminal is *fragile*, v(u₁) < v(u₂) + v(u₃), by
  re-basing a steep terminal to {u₁} (a (T1) move) and an owner count. This PR's (E1) proves the same inequality,
  v(α) < v(β) + v(γ), by Lemma ABS (i) and CNT at the configuration level. The arguments differ and the conclusions
  coincide.
- **Four agents.** #87 notes that (E) needs four agents. This PR's (E3) gives the reason: a third agent values a lower
  good of x.
- **The third agents.** #87 says nothing about them. This PR's (E2) restricts them to the shape {h₁, h₂, ℓ, z} with
  h₁ + ℓ < h₂ + z. In #87's all-robust setting w is robust, so v(h₁) + v(h₂) ≥ v(ℓ) + v(z) as well. This is compatible.
- **The data.** Both report that (E) never occurs on their data.

No disagreement. One difference in scope: this PR's (E) allows non-robust third agents (kinds (D), (R)), and #87's
does not. So at a Z′-maximum, where #87's Corollary AR uses its Theorem AR, (E1)–(E3) apply to #87's residual (E). At
other states of #87's Theorem AR they do not. If #87 is revised after 19fe9c1, this comparison should be re-read.

## 5. What remains open

Unchanged by this review:
- S1c at n ≥ 4 (K4.TB.S1C);
- the exception (E) itself;
- shape (II) of Corollary R1;
- Conjecture BT4;
- K4.SX.COVER and ZMOVE at f = 1.

Reproduce (from the repository root):
```
python3 k4/zf1_indep.py --eshape --procs=3                                   # indep_eshape_n4_z4.log (~3 min)
python3 k4/zf1_indep.py results/k4_sx/hunt/n4_3_r40k.jsonl.gz results/k4_sx/hunt/n4_pure_r40k.jsonl.gz \
  results/k4_sx/hunt/n4_pure_r400k.jsonl.gz results/k4_sx/hunt/n5_pure_r1000_3000.jsonl.gz \
  results/k4_sx/hunt/n5_pure_r1000_4000.jsonl.gz results/k4_sx/t3stage/profiles_f1.jsonl.gz   # indep_count_hunts.log (~15 s)
python3 k4/zf1_indep.py --n3 results/k4_sx/hunt/n3_all_0.jsonl.gz results/k4_sx/hunt/n3_all_10.jsonl.gz results/k4_sx/hunt/n3_all_20.jsonl.gz \
  results/k4_sx/hunt/n3_all_30.jsonl.gz results/k4_sx/hunt/n3_all_40.jsonl.gz results/k4_sx/hunt/n3_all_50.jsonl.gz   # indep_n3_all.log (~1 min)
python3 k4/zf1_indep.py --n3 --every=20 results/k4_sx/hunt/n3_all_30.jsonl.gz results/k4_sx/hunt/n3_all_40.jsonl.gz  # indep_n3_every20.log
python3 k4/zf1_bthunt.py results/k4_certs_3.json.gz --runs=600 --steps=200 --seed=1       # bthunt_n3_s1.log (~1 min)
for s in 1 2 3 4 5 6 7 8 9 10 11 12; do python3 k4/zf1_bthunt.py results/k4_certs_3.json.gz --runs=60 --steps=200 --seed=$s | grep -v '^NC big-top'; done   # bthunt_n3_seeds.log
```
