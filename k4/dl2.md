# DL₂ and its successors: the shapes of the deficit repairs

Workstream `proof/k4-dl2-k1` (PR #69). Ledger rows K4.DL2.* (and K4.STRAT.DL2, now REFUTED). Builds on
`k4/strategy.md` §3 (Conjecture DL₂ and its plan), `k4/c4x.md` §1 (the space 𝒫 and the removal-only deficit),
`k4/hall.md` (Lemma H1 and the exposure lemmas H3, H6, H7), `k4/c4min.md`, `k4/c4min_reduce.md`, `k4/c4min_f1.md`,
`k4/gap.md` and the suite `k4/suite/`. Nothing here changes K4.D or K4.T.

**Summary.**
- **DL₂ is false** (§1, ledger K4.DL2.X3, K4.STRAT.DL2 REFUTED): on a connected k = 4 core with n = 3, m = 7, a
  min-frozen P with def(P) = 1 has no min-frozen P′ with a smaller deficit within two agents' base changes. The nearest
  one is a *role swap* (the frozen agent gives its good to an agent that needs it) plus a third agent that gives up a
  good. 89 of the 74,256 profiles of #53's n = 3 catalogue have such a state (311 states).
- **The repairs, classified** (§2, EVIDENCE row K4.DL2.CLASS): on 52,166 states with def > 0 (the suite and #53's
  catalogues), the nearest repairs are one-agent changes in 76%, two-agent changes in 24% and three-agent changes in
  0.6% (all at n = 3); one-agent repairs are almost always *releases* (an agent gives up a good that an owner's safe
  bundle absorbs); two-agent repairs are role swaps with an agent that needs the frozen good (91%) or *trades* between
  two free agents; every three-agent repair is a role swap plus one more agent's change.
- **The successor targets** (§3): DL_R for a structured neighbourhood relation R. Since PR #68
  (`EFX.C4min.target4_of_defLocal`, K4.STRAT.DL2.LEAN), DL_R implies TARGET₄ for every R. The relation **R_T** ((T1) a
  re-base keeping the needed set; (T2) a rotation among free agents; (T3) a role swap with a needer and at most one
  helper that gives up a good; CONJECTURE K4.DL2.T, evidence K4.DL2.TE) survives every state tested. But R_T is local
  only in the frozen agents: (T1) and (T2) are exactly the moves that keep the key (needed set, frozen agents and their
  goods), so at f = 0 DL_T is C₄ᵐⁱⁿ's removal-only conclusion, which Theorem Z proves. **The open content is f ≥ 1**,
  and there the sharper **DL₁₃** (re-bases and role swaps only, no rotations; CONJECTURE K4.DL2.T13, evidence
  K4.DL2.T13E) survives all 96,605 f ≥ 1 states of the runs and all 29,072 f = 1 states at distance 3 of the
  exhaustive n = 3 enumeration of compute/k4-dl2. Other relations (no rotations, or restricted helpers) fail
  (K4.DL2.RX), mostly at f = 0, where they do not bear on DL_T or DL₁₃.
- **The moves, in writing** (§4; written proofs refereed in the PR #69 review; PROVED rows K4.DL2.MOVES, K4.DL2.DEF):
  the moves of R_T stay in the min-frozen class and keep its needed set (Lemmas 1, 1′, 6); a one-agent move lowers the
  deficit exactly through an owner's bundle growing (Lemma 2, extension) or the moving agent becoming a better owner
  (Lemma 3, owner re-base); releases and unblocking pool improvements are the two structural instances (Corollaries 4,
  5); Lemma 7 is the unfreezing mechanism of the three-agent traps. As a consistency check on the repairs found by
  enumeration, a lemma accounts for some minimal repair at 97.8% of the def > 0 states (§5). Why a repair *exists* is
  not proved.

## 1. DL₂ fails at n = 3

`attempts/k4-dl2-three-agents.md` has the instance, the hand computation of every deficit used, and its replay with
two implementations (`attempts/k4_dl2_attempts.py`). In short: agents 0 (0:2, 1:4, 2:3, 3:8; big-top),
1 (2:2, 4:6, 5:10, 6:7) and 2 (3:8, 4:3, 5:4, 6:2; big-top); f = 1, ω = 2. At the key where agent 0 is frozen on 3 every
min-frozen P has deficit 1. At the other key (agent 2 frozen on 3) the P with deficit −1 are exactly those where agent 1
does not hold good 2, which agent 0's bundle needs. So from P₀ = ({3}, {2,5}, {4,6}) the nearest improvement swaps the
roles of agents 0 and 2 **and** makes agent 1 give up good 2: three agents.

The ledger row K4.STRAT.DL2E (DL₂ on data) did not run #53's n = 3 catalogue; on it, 89 profiles have k* = 3. No state of
the n = 4 and n = 5 samples and hunts run here needs three agents (§3), so the n = 3 traps are the only ones known.

## 2. The classification (`k4/dl2_classify.py`, `results/k4_dl2_classify/`)

For every strict profile in the inputs, every min-frozen P ∈ 𝒫 with def(P) > 0 is a *state*. For each state the
classifier records:
- **the obstruction**: the best owners (free agents attaining def(P) in Lemma H1), an optimal owner bundle X and the
  removed junk C = J ∖ X, and for each agent exposed w.r.t. a best owner o (W_o = B_o ∪ J threatens it) its class:
  - free agents: Lemma H3's shapes e1, e2, e3; otherwise fU / fU2 (the agent violates (U) / (U₂) of Lemma H2, i.e. P is
    not Pareto-maximal there) or fO;
  - frozen agents: Lemma H7's classes G, G1, L (with #53's plain G test and chain-end test); otherwise O; suffix 2
    when the frozen agent is exposed w.r.t. two or more free agents (the double threat of Lemma D).

  The *signature* of P is the set of classes at the best owner with the fewest exposures.
- **the minimal repairs**: every min-frozen P′ with def(P′) < def(P) at the least distance k (number of agents whose
  base changes), with a *kind*:
  - k = 1: `release` (the changed agent y gives up a good that an optimal bundle of a best owner o′ ≠ y of P′ holds),
    `unblock` (some best owner o′ ≠ y of P′, no released good used), `owner` (only y is a best owner of P′),
    `need-transfer` (the needed set changes);
  - k = 2: `role-swap` (a frozen agent x unfreezes and a free agent z takes x's good and freezes; `/needer` if z
    needed it, `/J` or `/T` if x's new base is junk only or takes a good of z), `two-free` (a trade: two free agents,
    needed set unchanged);
  - k = 3: the status changes of the three agents.

Inputs (all strict profiles of each record; the catalogues are #53's at 245040b, `k4/strategy.md` §4):

| input | records | states | k = 1 | k = 2 | k = 3 |
|---|---|---|---|---|---|
| suite (cores with ω ≥ 1, n ≤ 6) | 147 | 359 | 296 | 63 | 0 |
| n = 2 catalogue, every record | 1,296 | 0 | | | |
| n = 3 catalogue, every record | 74,256 | 47,080 | 34,732 | 12,037 | 311 |
| n = 4 catalogues, every 10th record (one, two, three 4-good agents, pure) | 18,404 | 3,553 | 3,347 | 206 | 0 |
| n = 5 catalogues, every 20th record | 5,793 | 982 | 970 | 12 | 0 |
| hard hunt (n = 4) | 117 | 192 | 121 | 71 | 0 |
| **total** | | **52,166** | **39,466** | **12,389** | **311** |

The non-core suite instance `lil-noncore-n3` (20 states, one with k = 3) is counted apart. Full tables:
`results/k4_dl2_classify/table.md` (made by `k4/dl2_classify_table.py`).

### 2.1 Obstruction × k

| obstruction group (signature) | k = 1 | k = 2 | k = 3 |
|---|---|---|---|
| H7 only, a frozen agent threatened by two owners (G2, L2, O2 …) | 22,022 | 7,902 | 0 |
| a free exposed agent violating (U)/(U₂) (fU, fU2, with others) | 9,742 | 1,492 | 150 |
| H7 only, single threats (G, G1, L) | 4,970 | 1,128 | 161 |
| other frozen exposure (O) | 1,949 | 1,428 | 0 |
| H3 only: e1 | 602 | 47 | 0 |
| H3 only: e2 | 170 | 361 | 0 |
| H3 + H7 mixed | 11 | 30 | 0 |
| H3 only: e3 | 0 | 1 | 0 |

At the Pareto-maximal states (where Lemmas H3 and H7 describe every exposure; 3,962 states): double threat
2,368 / 203 / 0, single H7 threats 821 / 315 / **80**, e2 only 100 / 75 / 0 (k = 1 / 2 / 3). So:
- **no obstruction class forces k = 1**; every class with more than a few states has two-agent cells;
- the **three-agent cells** are single local frozen threats (L, 161 states; 80 of them Pareto-maximal) and free agents
  violating (U₂) (150), all at n = 3, f = 1, with a big-top frozen agent;
- the **"other" classes** (fO never occurs; frozen O 3,377 states) are not covered by H3/H7 because those lemmas need
  Pareto-maximality; they are repaired like the rest (nearest repair: release 1,690, owner re-base 259, role swap
  1,428).

### 2.2 Repair kinds

| kind of the nearest repair | states |
|---|---|
| one agent: release | 36,892 |
| one agent: unblock | 1,386 |
| one agent: owner re-base | 1,188 |
| one agent: need transfer | 0 |
| two agents: role swap with a needer (x takes junk only / takes a good of z) | 10,716 / 550 |
| two agents: trade between two free agents | 1,123 |
| three agents: role swap + a third agent | 311 |

(For two-agent states the row is the first kind in the order listed; 6,822 states have both kinds of role swap with a
needer, 1,159 a role swap and a trade.) Every role swap in a minimal repair uses an agent that *needs* the frozen good,
except at 12 states that also have a swap with a needer. In every three-agent repair (4,779 moves at the 311 states) the
unfrozen agent x is a best owner afterwards.

### 2.3 How far the one-agent lemmas reach

At every state the classifier (`k4/dl2_classify.py lemma_checks`) evaluates the hypotheses of Lemmas 2, 3 and
Corollaries 4, 5 for every free agent's admissible re-bases, and asserts the gain conclusion def(P′) ≤ def(P) − gain
against the exact deficits whenever the hypotheses hold with a positive gain (§6 lists exactly what is asserted). No
assertion fails on any input, and no lemma applies with a positive gain at a state with k > 1.

| k = 1 states | Corollary 4, structural form (i′) | Corollary 4 (release) | Corollary 5 (unblocking) | Corollary 4 or 5 | Lemma 2 at a best owner | Lemma 2 at another owner | Lemma 3 (owner re-base) | Lemma 2 or 3 |
|---|---|---|---|---|---|---|---|---|
| all inputs: 39,466 | 23,719 (60.1%) | 26,324 (66.7%) | 2,354 (6.0%) | 27,937 (70.8%) | 37,821 (95.8%) | 1,060 (2.7%) | 4,139 (10.5%) | 39,465 (100.0%) |
| Pareto-maximal: 3,289 | 2,580 (78.4%) | 2,606 (79.2%) | 0 | | 3,044 (92.6%) | 0 | 365 (11.1%) | 3,289 (100%) |

(Lemma 2 is applied to X ∖ B′ for each optimal bundle X of each free agent; "another owner" means a free agent that is
not a best owner of P, so its gain must exceed Val*(P) − Val_P(o).) So the one-agent repairs are understood: every one
but one (`gap_n4_pure_s4000`, core (m = 11, idx 5) of `k4_certs_4_pure`, profile 83,6,64,235, where the bound of
Lemma 2 loses the unfreezing term e) is an extension of an owner's bundle (Lemma 2) or an owner re-base (Lemma 3), and
71% satisfy the structural hypotheses of a release or an unblocking (Corollaries 4, 5). What is **not** understood is why a one-agent repair exists when it does;
no obstruction class guarantees one.

For the states with k ≥ 2, Lemma 2* (a best owner of P that does not move extends its bundle) and Lemma 7 (the unfrozen
agent as owner unfreezes its needer) are evaluated at every minimal repair P′ (`k4/dl2_classify.py multi_checks`,
`table.md` section C′). A state counts for Lemma 2* when its gain is positive. It counts for Lemma 7 when, at some
minimal repair, a safe bundle Z of the unfrozen agent x with v_x(Z) > v_x(g) has |Z| + u′_x(Z) > Val*(P): this is
Lemma H1 in P′ with every agent counted in u′_x(Z), of which Lemma 7 guarantees z, not Lemma 7's own bound
def(P′) ≤ ω + 1 − |Z|. The PR #69 referee recounted with Lemma 7's own bound (|Z| + 1 > Val*(P)) and got the same states
(9,726 at k = 2, 311 at k = 3).

| | states | Lemma 2* | Lemma 7 | either | neither |
|---|---|---|---|---|---|
| k = 2 | 12,389 | 10,682 (86.2%) | 9,726 (78.5%) | 11,250 (90.8%) | 1,139: the 1,123 states whose only minimal repairs are trades, and 16 role-swap states |
| k = 3 | 311 | 0 | 311 (100%) | 311 (100%) | 0 |

So the two-agent role swaps are mostly explained by an owner that keeps its role and absorbs what the swap frees, or by
the unfrozen agent unfreezing its needer; trades, where the new owner is one of the two trading agents, are not
explained by any lemma here.

## 3. Structured relations R (`k4/dl2_relations.py`, `results/k4_dl2_relations/`)

DL_R: every min-frozen P with def(P) > 0 has a min-frozen P′ with R(P, P′) and def(P′) < def(P). By K4.STRAT.DL2.LEAN
(PR #68), DL_R ⟹ TARGET₄ for every R, so R may be any relation whose moves a proof can handle. `k4/dl2_relations.py`
enumerates, for each state, **every** min-frozen P′ with a smaller deficit (not only the nearest), describes the move
P → P′ by its shape (which agents change, which unfreeze or freeze, whether the frozen good goes to an agent that
needed it, what the other changed agents do), and evaluates each relation.

The moves (P, P′ both min-frozen; "needed set unchanged" means NA(P′) = NA(P)):
- **re-base**: exactly one agent's base changes (it is free, Lemma 1);
- **trade**: exactly two agents' bases change, both free in P and in P′, needed set unchanged (Lemma 1′);
- **rotation**: any number of agents' bases change, all free in P and in P′, needed set unchanged (Lemma 1′; a trade is
  a rotation of two agents);
- **role swap with a needer**: a frozen agent x with base {g} unfreezes, a free agent z with g ∈ N_z(B_z) takes {g}
  and freezes, needed set unchanged (Lemma 6); *helpers*: further changed agents, free in P and P′.

| relation (code name) | moves | fails on |
|---|---|---|
| R2 | at most two agents change (DL₂) | n = 3, f = 1 (`dl2-n3m7`) |
| RB | re-base, or a plain role swap with a needer | n = 2, f = 0 (`induct-g-r1`); also f = 1 (`dl2-n3m6-take`, n = 3, m = 6) |
| RB2 | RB or a trade | n = 3, f = 1 (the states of R2) |
| RS1 / RS1+2 | re-base, (trade,) or a role swap with any number of helpers each giving up one good and taking nothing | n = 2, f = 0, and f = 1 / n = 3, f = 1 |
| RSR+2 | re-base, trade, or a role swap with helpers that only give up goods (any number) | n = 3, f = 1 |
| RC | re-base, trade, or a chain of frozen goods ending at a free agent (LB⁺'s rotation shape) with releasing helpers | n = 3, f = 1 |
| RSY, RSYa, RSYg | re-base, or a role swap with at most one (RSYa: any number of) helper(s); **no trades** | n = 2, f = 0 only (`induct-g-r1`) |
| RSYz+2, RSYgz+2 | re-base, trade, or a role swap with at most one helper that takes goods only from its own base and B_z (RSYgz+2: and gives up a good) | n = 3, f = 1 (`dl2-n3m8-junk`) |
| RSY+2, RSYg+2, R_T2 (RT) | re-base, trade, or a role swap with at most one helper (RSYg+2: giving up a good; R_T2: also re-bases keeping the needed set, trades passing a good) | n = 3, f = 0 only (`dl2-rot-n3m7` of compute/k4-dl2, PR #70): a three-agent rotation is needed |
| **R_13** (R13) | (T1) re-base keeping the needed set; (T3) role swap with a needer and at most one helper giving up a good; **no rotations** | f = 0 only (`induct-g-r1`, `dl2-rot-n3m7`); **none at f ≥ 1** |
| **R_T** (RTr) | (T1); (T2) **rotation**; (T3) | **none** |

Of these, only R_T2 and R_13 are sub-relations of R_T; the others are not narrower than R_T but different (they allow
re-bases that change the needed set, or helpers that keep their whole base), restricted in rotations or in the helpers.
The failures, each confirmed by two implementations (`k4/dl2_relations.py` on `k4/suite/model.py`, and main's
`k4/c4x_check.py` with separately written membership tests in `attempts/k4_dl2_attempts.py`; at each failing state both
implementations also find an R_T move, and at the f ≥ 1 ones an R_13 move):
- **at f = 0, free agents must be able to rotate** (RSY, RSYa, RSYg, R_13: no trades; RSY+2, R_T2: trades of two agents
  only): `induct-g-r1` (#43), n = 2, m = 5, f = 0: no agent is frozen, so there is no role swap, and every improvement
  exchanges goods 2 and 3 between the two agents (Theorem Z's rotation of a 2-cycle). The parallel workstream
  compute/k4-dl2 (PR #70, `attempts/k4-dl2-rotation.md` on its branch) found `dl2-rot-n3m7` (core (m = 7, idx 11) of
  `results/k4_certs_3.json.gz`, n = 3, m = 7, f = 0): a P with deficit 1 whose every improvement rotates goods around
  the 3-cycle of exposures (e2, e3, e3); it refutes every relation here whose free moves have at most two agents.
  These are f = 0 failures, which do not bear on DL_T or DL₁₃ (below);
- **plain or single-release role swaps are not enough, also at f = 1** (RB, RS1; no trades): `dl2-n3m6-take`
  (#53's n = 3 catalogue, core (m = 6, idx 13), profile 4,17,236; n = 3, m = 6, f = 1): every improvement is a trade of
  two free agents or a role swap whose helper gives up a good and takes the needer's old good; over all runs RB fails
  at 1,433 and RS1 at 1,215 states with f ≥ 1 (R_13 holds at each);
- **two agents are not enough** (R2, RB2): `dl2-n3m7` of §1;
- **releasing helpers are not enough** (RS1+2, RSR+2, RC): `dl2-n3m7-trade` (n = 3, m = 7, f = 1), where the helper must
  also take a good of the needer's old base;
- **the helper needs junk** (RSYz+2, RSYgz+2): `dl2-n3m8-junk` (n = 3, m = 8, f = 1), where the helper gives up the
  unfrozen agent's good and takes a junk good.

`attempts/k4-dl2-relations.md` (REFUTED row K4.DL2.RX) has the instances and what every improving move of each does.

**Conjecture DL_T (K4.DL2.T).** For every strict profile of every connected k = 4 core with ω ≥ 1, every min-frozen
P ∈ 𝒫 with def(P) > 0 (+∞ included) has a min-frozen P′ ∈ 𝒫 with def(P′) < def(P) that arises from P by one of the
following moves, the needed set NA staying the same:
- **(T1) re-base**: one free agent y replaces its base by another base B′_y ⊆ (B_y ∪ J) ∩ R_y;
- **(T2) rotation**: a set Y of agents free in P (|Y| ≥ 2) takes new bases B′_y ⊆ (J ∪ ⋃_{w ∈ Y} B_w) ∩ R_y,
  pairwise disjoint, everybody else unchanged; so goods of the old bases may drop into the junk and junk may enter
  bases, as in Lemma 1′ (code `RTr`: every changed agent is free in P and in P′, NA unchanged);
- **(T3) role swap with at most one helper**: a frozen agent x with base {g} and a free agent z with g ∈ N_z(B_z):
  z takes {g}, x takes a new base, and at most one further free agent h (the *helper*) replaces its base by one that
  misses at least one good of B_h. (The new bases then lie in the goods the move frees, J ∪ B_z ∪ B_h, since the other
  bases do not move.)

By Lemmas 1′ and 6 every such move stays in the min-frozen class as soon as the new bases are disjoint, inside the
relevant sets, of at most two goods, and need only goods of NA. DL_T implies TARGET₄ (K4.STRAT.DL2.LEAN).

*Note (2026-10-01, compute/k4-rt4-n5):* DL_RT4 (DL_T with (T4) added: frozen agents permute their goods; K4.DL2.RT4E)
and its key-graph form (`k4/dl13.md` §2.3) are refuted at n = 5 (K4.DL2.RT4, K4.DL13.KEY); see
`attempts/k4-rt4-n5-chain.md`.

**R_T is local only in the frozen agents, and DL_T holds at f = 0.** The *key* of a min-frozen P is its needed set
with the frozen agents and their goods (𝒩, φ) (`k4/c4min.md` §1). A min-frozen P′ ≠ P has the same key as P iff only
agents free in both change and NA is unchanged, i.e. iff P → P′ is a (T1) or (T2) move. So R_T(P, P′) holds iff P′ has
P's key or arises by a (T3) role swap: the only non-local part of R_T is the role swap. At f = 0 every min-frozen P has
the empty key, every min-frozen P′ ≠ P is an R_T-neighbour, and DL_T on such a profile is DL for the full relation,
which is equivalent to C₄ᵐⁱⁿ's removal-only conclusion there (K4.STRAT.DL2.LEAN); that holds by Theorem Z
(K4.C4MIN.Z, `EFX.C4min.theoremZ_RO`). **So DL_T holds at f = 0, and its open content is exactly f ≥ 1.** The f = 0
failures of the other relations (`induct-g-r1`, `dl2-rot-n3m7`, the f = 0 rotation traps) only show that those
relations are too narrow where Theorem Z already answers the question.

**The sharper target.** At f ≥ 1, rotations are never needed on the data: the relation R_13 := (T1) ∪ (T3) (code
`R13`; proposed by the PR #69 referee, whose own check found no failure at 4,789 catalogue and 982 random n = 3 states
with f ≥ 1) fails only at f = 0 states.

**Conjecture DL₁₃ (K4.DL2.T13).** For every strict profile of every connected k = 4 core whose fewest frozen agents is
f ≥ 1, with ω ≥ 1, every min-frozen P ∈ 𝒫 with def(P) > 0 (+∞ included) has a min-frozen P′ with def(P′) < def(P)
that arises from P by a (T1) or a (T3) move.

DL₁₃ implies DL_T at f ≥ 1 (R_13 ⊆ R_T), and with Theorem Z at f = 0 it implies TARGET₄: for the relation R* := "(T1)
or (T3) when the profile has f ≥ 1, any pair of min-frozen pre-allocations when f = 0", DL_{R*} holds at f = 0 by
Theorem Z (as above) and at f ≥ 1 by DL₁₃, and `EFX.C4min.target4_of_defLocal` turns DL_{R*} into TARGET₄. (This
combination is machine-checked: `lean/EFX/DL13.lean`, `EFX.C4min.target4_of_DL13`, row K4.DL2.T13.LEAN.)

*Evidence* (EVIDENCE rows K4.DL2.TE for DL_T, K4.DL2.T13E for DL₁₃). The runs (`results/k4_dl2_relations/`, table
below): the suite; #53's catalogues (n = 2, 3 every record; n = 4 every 10th; n = 5 every 20th), its hard hunt and its
hunt catalogues (every record); and, f = 0 profiles included, **every** strict profile of every n = 2 core
(`results/k4_certs_2.json.gz`), 400 random profiles of each n = 3 core and 20 of each n = 4 core (seeded, with
replacement). Together 272,858 def > 0 states, 176,253 with f = 0 and 96,605 with f ≥ 1, in 490,947 profiles
summed over the runs (not distinct profiles: the n = 2 catalogue's 1,296 profiles lie inside the run on every n = 2
profile, and random draws repeat). R_T fails at none of them; R_13 at none of the f ≥ 1 states. All n = 2 states have
f = 0 (171,432), as do 2,632 of the 2,862 random n = 3 states; #53's catalogues and hunts have f ≥ 1 only.
Exhaustive at n = 2 (where f = 0, so Theorem Z already gives DL_T); at n = 3 only for the states at distance 3 (below).

The survivals are computed by one implementation (`k4/dl2_relations.py`); a second one (main's `k4/c4x_check.py` with
separately written membership tests, `k4/dl2_relations_xcheck.py`) agrees on deficits, nearest distances and DL_R for
R_T, R_13, R_T2, R2, RB2 and RSY+2 on 16,359 profiles with n ≤ 4 (7,210 def > 0 states: the suite's cores with
n ≤ 4, every 10th record of #53's n = 3 catalogue, its hard hunt, every 40th record of two n = 4 catalogues, 200 random
profiles of each n = 2 core and 100 of each n = 3 core; `results/k4_dl2_relations/xcheck.log`), and every failure above
is replayed by both (`attempts/k4_dl2_attempts.py`). On every profile of every n = 2 core the C tool of compute/k4-dl2
(`results/k4_dl2/n3.log` on that branch) finds the same 171,432 def > 0 states, 158,616 at distance 1 and 12,816 at
distance 2.

*Exhaustive n = 3, three-agent states.* compute/k4-dl2 enumerated every strict profile of every n = 3 core with its C
tool and dumped every P at distance 3 with all its improvements (`results/k4_dl2/trapped_n3.jsonl.gz` on that branch at
baf3b9f: 87,056 states of 52,928 profiles, out of 36,739,800 def > 0 states; 57,984 of the 87,056 have f = 0, 29,072
have f = 1). At n = 3 these improvements are all the min-frozen P′ with a smaller deficit. `k4/dl2_relations_trapped.py`
tests the relations on them with the membership tests of `k4/dl2_relations_xcheck.py`
(`results/k4_dl2_relations/trapped_n3_compute.log`): R2 and RB2 fail at all 87,056 (they are at distance 3), RSY+2,
R_T2 and R_13 at the 57,984 with f = 0, **R_T at none, and R_13 at none of the 29,072 with f = 1**. Recomputing every
20th of the 52,928 profiles with `k4/dl2_relations.py` gives the same states at distance 3 and the same verdicts for
every relation (2,647 profiles, no mismatch). So DL_T and DL₁₃ hold at every n = 3 state whose nearest repair needs
three agents (on compute's enumeration); the states at distance 1 and 2 of the exhaustive n = 3 run are not tested
here. Reproduce: `mkdir -p k4/suite/.cache/compute_k4_dl2`,
`git show baf3b9f:results/k4_dl2/trapped_n3.jsonl.gz > k4/suite/.cache/compute_k4_dl2/trapped_n3.jsonl.gz`, then the
command on the log's first line.

Failures of DL_R as states, with the f ≥ 1 states among them in brackets; 0 = DL_R holds at every state of the input.
Per-input rows, profile counts and every relation: `results/k4_dl2_relations/table.md`.

| inputs | def > 0 states (f = 0 / f ≥ 1) | R2 | RB | RB2 | RS1+2, RSR+2, RC | RSY, RSYa, RSYg | RSYz+2, RSYgz+2 | RSY+2, RSYg+2, R_T2 | **R_13** | **R_T** |
|---|---|---|---|---|---|---|---|---|---|---|
| suite (cores, n ≤ 6) | 359 (197 / 162) | 0 | 7 (2) | 0 | 0 | 5 (0) | 0 | 0 | 5 (0) | 0 |
| n = 2: every profile of every core; catalogue | 171,432 (171,432 / 0) | 0 | 12,816 (0) | 0 | 0 | 12,816 (0) | 0 | 0 | 12,816 (0) | 0 |
| n = 3: catalogue; 400 random profiles per core | 49,942 (2,632 / 47,310) | 314 (311) | 1,459 (1,428) | 314 (311) | 155 (152) | 31 (0) | 16 (13) | 3 (0) | 31 (0) | 0 |
| n = 4: catalogues, hard hunt, hunts; 20 random per core | 44,489 (1,992 / 42,497) | 0 | 3 (3) | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| n = 5: catalogues, hunts | 6,636 (0 / 6,636) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| **total of the runs** | **272,858** (176,253 / 96,605) | 314 (311) | 14,285 (1,433) | 314 (311) | 155 (152) | 12,852 (0) | 16 (13) | 3 (0) | 12,852 (0) | 0 |
| n = 3 exhaustive, distance 3 (dump) | 87,056 (57,984 / 29,072) | 87,056 (29,072) | · | 87,056 (29,072) | · | · | · | 57,984 (0) | 57,984 (0) | **0** |

(Relations grouped in one column fail at the same states. "·": not evaluated on the dump.) The R_T2 failures at n = 3
are two random profiles of the same kind as `dl2-rot-n3m7`: f = 0, nearest repair three agents, all free, a three-agent
rotation. Every state where some relation fails is dumped to `results/k4_dl2_relations/*.jsonl.gz`.

*What a proof of DL₁₃ needs.* A case analysis at f ≥ 1 on the obstruction (§2.1) showing that when no (T1) move lowers
the deficit, a (T3) move does. §4 handles the (T1) side exactly (Lemmas 2, 3). For (T3) validity is proved (Lemma 6);
its effect on the deficit is again Lemma H1 applied to P′. For the three-agent cells the data and Lemma 7 give the
mechanism: the frozen agent x is big-top, the swap frees it, and x becomes the owner of a bundle that holds its three
lower goods, which unfreezes the needer z; the helper is the agent holding one of those goods. The swap has the shape
of Lemma F1's path move of length 0 (`k4/c4min_f1.md` §2: x becomes free, a terminal takes g), and big-top frozen agents
are exactly where F1's potential Ψ = (r, Λ) stalls (every path move from a big-top x ties in Ψ, `k4/c4min_f1.md` §3; no
potential starting with (r, Λ) works, K4.C4MIN.F1BT). The deficit counts the unfreezing, which Ψ does not see; that is
an observation, not a proof that it always suffices.

## 4. The moves, in writing

Written proofs, **refereed in the PR #69 review** (ledger rows K4.DL2.MOVES, K4.DL2.DEF: PROVED; the referee read
every lemma line by line and tested each with independent code, 0 violations). They use only the definitions of
`k4/c4x.md` §1 and Lemma H1 of `k4/hall.md` §1 (ledger K4.HALL.COVER, PROVED). What this workstream's code checks is
listed in §6: the gain conclusions of Lemmas 2, 2*, 3, 7 and Corollaries 4, 5 and the validity part of Lemma 1(c) at
the states of §2, and Lemmas 1′, 6, 7 on random instances. Lemma 1(a), (b), the equality in Lemma 3 and
(i′) ⟹ (i) of Corollary 4 are not checked by that code; the PR #69 referee checked them.

**Setting.** A strict profile of an instance in which every agent has three or four relevant goods and is strictly
balanced: the setting of Lemma H1; every k = 4 core is one. (Balance enters only through Lemma H1; the random checks of
§6 use such instances that are not cores.) 𝒫, bases B_i, junk J, needs N_i(B) = {g ∈ R_i ∖ B : v_i(g) > v_i(B)},
N_i := N_i(B_i), NA = ⋃ N_i, frozen agents F, slots and ω are those of `k4/c4x.md` §1. Recall:
- (V) P ∈ 𝒫 iff its bases are disjoint subsets of the agents' relevant sets with at most two goods each and every
  needed good is the whole base of one agent ((V1) and (V2), `k4/c4x.md` §1). Hence |F| = |NA|, and
  ω = |J| − S = |F| − (2n − m).
- f is the fewest frozen agents over 𝒫; P is *min-frozen* if |F(P)| = f. All min-frozen P have the same ω; we assume
  ω ≥ 1.
- An agent's needs avoid its own base. A free agent's base contains no needed good (a free one-good base is not
  needed by definition, a pair by (V2)). Values are nonnegative, so every good of a base is worth at most the base.

For Z ⊆ M nonempty and an agent x, θ_x(Z) := max_{h ∈ Z} v_x(Z ∖ h); Z *threatens* x holding B if θ_x(Z) > v_x(B).
By convention ∅ threatens nobody (empty bundles occur when B_o = ∅ and nothing is added).
θ_x is monotone: Z ⊆ Z′ implies θ_x(Z) ≤ θ_x(Z′). If Z ⊄ R_x then θ_x(Z) = v_x(Z ∩ R_x) (remove a good x does not
value); always θ_x(Z) ≤ v_x(Z ∩ R_x).

For a free agent o of P and any set Z ⊆ M, Z is *safe for o* (in P) if it threatens no agent x ≠ o holding B_x.
W_o := B_o ∪ J. A *bundle* of o is a Z with B_o ⊆ Z ⊆ W_o; a safe bundle is a bundle that is safe for o. For any
Z ⊆ M, u_o(Z) is the number of x ∈ F with B_x ∩ (N_o(Z) ∪ 𝒩₋ₒ) = ∅, where 𝒩₋ₒ := ⋃_{i ≠ o} N_i and
N_o(Z) := {g ∈ R_o ∖ Z : v_o(g) > v_o(Z)} (such an x is *counted* in u_o(Z)): the frozen agents that the owner's needs
from Z unfreeze. Val_P(o) := max{|Z| + u_o(Z) : Z a safe bundle of o} (Z = B_o is
safe: each of its goods is unneeded, hence worth at most v_x(B_x) to every x), and Val*(P) := max_o Val_P(o) over the
free o; a *best owner* attains it, an *optimal* bundle of o attains Val_P(o).

**Lemma H1** (`k4/hall.md` §1, K4.HALL.COVER). If P is min-frozen, ω ≥ 1 and P has a free agent, then
def(P) = ω + 2 − Val*(P).

Two monotonicity facts are used repeatedly. (M1) If Z ⊆ Z′, then N_o(Z′) ⊆ N_o(Z): a good of R_o ∖ Z′ worth more than
v_o(Z′) ≥ v_o(Z) lies in R_o ∖ Z. (M2) If v_y(B′) ≥ v_y(B) for two sets B, B′, then N_y(B′) ⊆ N_y(B): a g ∈ N_y(B′) has
v(g) > v(B′) ≥ v(B), so g is not in B (each good of B is worth at most v(B)), hence g ∈ N_y(B).

### 4.1 Re-bases and trades

**Lemma 1 (re-bases of free agents).** Let P ∈ 𝒫 be min-frozen with needed set 𝒩 := NA(P), and let P′ ∈ 𝒫 be
min-frozen and differ from P exactly in the base of one agent y. Then
- (a) y is free in P and in P′, and B′_y ⊆ (B_y ∪ J) ∩ R_y;
- (b) NA(P′) = 𝒩 iff N_y(B′_y) ⊆ 𝒩; then F(P′) = F(P). Otherwise (a *need transfer*) some agent whose base is
  unchanged changes its frozen status.

Conversely, (c) if y is free in P and B′ ⊆ (B_y ∪ J) ∩ R_y has |B′| ≤ 2, B′ ≠ B_y and N_y(B′) ⊆ 𝒩 (*B′ is
admissible for 𝒩*), then replacing B_y by B′ gives a min-frozen P′ ∈ 𝒫 with NA(P′) = 𝒩, F(P′) = F(P),
J(P′) = (J ∖ B′) ∪ (B_y ∖ B′) and the same ω; every other agent keeps its base, needs and value v_i(B_i).

*Proof.* (a) Suppose y ∈ F, B_y = {g}. g is needed by some z ≠ y, whose base and needs are unchanged, so g ∈ NA(P′),
and by (V) g is the whole base of an agent of P′. The agents other than y keep bases disjoint from {g}, so
B′_y = {g} = B_y, a contradiction. So y is free in P. B′_y ⊆ R_y, and it misses the other agents' (unchanged) bases,
i.e. B′_y ⊆ B_y ∪ J. If B′_y = {h} were needed in P′, then h ∈ N_i for some i ≠ y (an agent never needs its own base),
whose needs are those of P, so h ∈ 𝒩; but h ∈ B_y ∪ J and 𝒩 misses both (y is free; (V1)). So y is free in P′.
(b) NA(P′) = 𝒩₋ᵧ ∪ N_y(B′_y) with 𝒩₋ᵧ ⊆ 𝒩 and |NA(P′)| = |F(P′)| = f = |𝒩|. So NA(P′) = 𝒩 iff N_y(B′_y) ⊆ 𝒩. In that
case F(P′) consists of the agents whose base is a single good of 𝒩: the same agents as in P, since y is free in both.
Otherwise NA(P′) ≠ 𝒩, the frozen sets differ, and y is free in both, so another agent's status changes.
(c) NA(P′) = 𝒩₋ᵧ ∪ N_y(B′) ⊆ 𝒩. Every good of 𝒩 is the whole base of a frozen agent of P, which is not y and keeps its
base. So every needed good of P′ is a one-good base of P′; the bases are disjoint (B′ ⊆ B_y ∪ J), inside the relevant
sets and of at most two goods; by (V), P′ ∈ 𝒫. |F(P′)| = |NA(P′)| ≤ |𝒩| = f, and ≥ f by minimality, so NA(P′) = 𝒩, and
F(P′) = F(P) as in (b). The formula for J(P′) is the bookkeeping of the move, and ω(P′) = |F(P′)| − (2n − m) = ω. ∎

**Lemma 1′ (several free agents; trades).** Let P be min-frozen with needed set 𝒩, Y a set of agents free in P, and
B′_y (y ∈ Y) pairwise disjoint sets with B′_y ⊆ (J ∪ ⋃_{w ∈ Y} B_w) ∩ R_y, |B′_y| ≤ 2 and N_y(B′_y) ⊆ 𝒩. Then P′ (each
y ∈ Y holding B′_y, everybody else unchanged) is min-frozen with NA(P′) = 𝒩, F(P′) = F(P) and the same ω.

*Proof.* As Lemma 1(c): NA(P′) = ⋃_{i ∉ Y} N_i ∪ ⋃_{y ∈ Y} N_y(B′_y) ⊆ 𝒩; every good of 𝒩 is the base of a frozen
agent of P, which is not in Y and keeps its base; the new bases miss the unchanged ones and 𝒩 (they lie in J and in
free agents' bases); so P′ ∈ 𝒫 by (V), |F(P′)| ≤ f, hence = f, NA(P′) = 𝒩, and the frozen agents are those of P. ∎

A *trade* is the case |Y| = 2.

**Lemma 2 (extension).** Let P be min-frozen with ω ≥ 1, y free, B′ admissible for 𝒩 (Lemma 1(c)) and P′ the
result. Let o ≠ y be free, X a bundle of o in P with X ∩ B′ = ∅, and Y ⊇ X a bundle of o in P′
(B_o ⊆ Y ⊆ B_o ∪ J(P′)) that is safe in P′. Let e be the number of agents counted in u_o(X) whose good lies in
N_y(B′). Then

  def(P′) ≤ ω + 2 − |Y| − u_o(X) + e,

and e = 0 if v_y(B′) ≥ v_y(B_y). In particular, if X is optimal for a best owner o of P, then
def(P′) ≤ def(P) − (|Y ∖ X| − e); and for any free o ≠ y and any bundle X with X ∩ B′ = ∅, def(P′) < def(P) as soon as
|Y| + u_o(X) − e > Val*(P). (When B′ meets an optimal bundle X, apply the lemma to the bundle X ∖ B′.)

*Proof.* By Lemma 1(c), P′ is min-frozen with the same F, 𝒩 and ω, and o is free in P′ with base B_o. X ⊆ B_o ∪ J and
X ∩ B′ = ∅ give X ⊆ B_o ∪ (J ∖ B′) ⊆ B_o ∪ J(P′), so supersets Y of X are bundles of o in P′ when they lie in
B_o ∪ J(P′). Lemma H1 in P′ gives def(P′) ≤ ω + 2 − |Y| − u′_o(Y), where u′ is computed in P′:
u′_o(Y) = #{x ∈ F : B_x ∩ (N_o(Y) ∪ 𝒩′₋ₒ) = ∅} with 𝒩′₋ₒ = ⋃_{i ∉ {o, y}} N_i ∪ N_y(B′). Let x be counted in u_o(X) with
its good outside N_y(B′). Then B_x misses N_o(Y) ⊆ N_o(X) (Y ⊇ X), misses N_i for i ∉ {o, y}, and misses N_y(B′); so x
is counted in u′_o(Y). Hence u′_o(Y) ≥ u_o(X) − e. If v_y(B′) ≥ v_y(B_y), then N_y(B′) ⊆ N_y(B_y) ⊆ 𝒩₋ₒ, which no
counted agent's good meets, so e = 0. The last claim is the bound together with def(P) = ω + 2 − Val*(P) (Lemma H1);
the one before it uses in addition |X| + u_o(X) = Val*(P) for an optimal X of a best owner. ∎

**Lemma 2* (extension through any move).** Let P, P′ ∈ 𝒫 be min-frozen with NA(P′) = NA(P) =: 𝒩 and ω ≥ 1, let Ch be
the set of agents whose base changes, and o ∉ Ch an agent free in P. Let X be a bundle of o in P that misses every new
base B′_i (i ∈ Ch), and Y ⊇ X a bundle of o in P′ that is safe in P′. Let e* be the number of agents counted in u_o(X)
that lie in Ch or whose good lies in N_i(B′_i) for some i ∈ Ch. Then

  def(P′) ≤ ω + 2 − |Y| − u_o(X) + e*,

and def(P′) ≤ def(P) − (|Y ∖ X| − e*) when X is optimal for a best owner o of P. Lemma 2 is the case Ch = {y}; the
lemma applies as well to trades (Lemma 1′) and role swaps (Lemma 6), whose moves keep the needed set.

*Proof.* o keeps its base, and its base is a single good of 𝒩 = NA(P′) iff it is one of NA(P); so o is free in P′, and
an agent outside Ch is frozen in P′ iff it is frozen in P. ω(P′) = |NA(P′)| − (2n − m) = ω. A good of J that lies in no
new base lies in no base of P′ (the other bases did not move), so X ⊆ B_o ∪ J(P′) and Y is a bundle of o in P′. Lemma H1
in P′: def(P′) ≤ ω + 2 − |Y| − u′_o(Y). Let x be counted in u_o(X), x ∉ Ch, with its good outside every N_i(B′_i),
i ∈ Ch. Then x is frozen in P′ with the same base; its good misses N_o(Y) ⊆ N_o(X) (M1), misses N_i for i ∉ Ch ∪ {o}
(unchanged needs; x is counted in u_o(X)), and misses N_i(B′_i) for i ∈ Ch. So x is counted in u′_o(Y), and
u′_o(Y) ≥ u_o(X) − e*. The last claim follows from def(P) = ω + 2 − |X| − u_o(X). ∎

**Lemma 3 (owner re-base).** Let P be min-frozen with ω ≥ 1, y free, B′ admissible for 𝒩 and P′ the result. Then
Val_{P′}(y) = max{|Z| + u_y(Z) : B′ ⊆ Z ⊆ W_y, Z safe for y in P}, with W_y = B_y ∪ J and u_y computed in P (Z need
not contain B_y; "safe for y" is defined for every set). So def(P′) < def(P) as soon as some Z with B′ ⊆ Z ⊆ W_y,
safe for y in P, has |Z| + u_y(Z) > Val*(P).

*Proof.* W′_y = B′ ∪ J(P′) = B′ ∪ (J ∖ B′) ∪ (B_y ∖ B′) = W_y. Safety of a bundle of y concerns the agents x ≠ y, whose
bases are the same in P and P′. u′_y(Z) involves N_y(Z), which depends on Z only, 𝒩′₋ᵧ = 𝒩₋ᵧ and F(P′) = F(P); so
u′_y(Z) = u_y(Z). The bundles of y in P′ are the Z with B′ ⊆ Z ⊆ W_y. Lemma H1 in P′. ∎

So the owner's bundle never depends on how the owner splits W_y into base and junk, except through the constraint
Z ⊇ base: an owner re-base helps exactly when the old base blocks every large safe bundle (as in the unhittable
exposures e1, e3 of Lemma H3, where B_o itself is the threat).

**Corollary 4 (release).** Let P be min-frozen with ω ≥ 1 and def(P) > 0, o a best owner with an optimal bundle X,
and y ≠ o a free agent holding a pair B_y = {p, q} with N_y({p}) ⊆ 𝒩 (y stays admissible holding p alone). Suppose
- (i) X ∪ {q} threatens no agent z ∉ {o, y} holding B_z;
- (ii) v_y(X ∩ R_y) + v_y(q) ≤ v_y(p);
- (iii) no agent counted in u_o(X) has its good in N_y({p}).

Then the release of q (B′_y = {p}) gives a min-frozen P′ with def(P′) ≤ def(P) − 1. Hypothesis (i) holds when
(i′) no agent outside {o, y} values q and X ⊄ R_z for every z ∉ {o, y}.

*Proof.* B′ = {p} is admissible for 𝒩 and misses X (p ∈ B_y, X ⊆ B_o ∪ J). Y := X ∪ {q} is a bundle of o in P′, since
q ∈ J(P′) and q ∉ X. It is safe in P′: agents z ∉ {o, y} keep their bases, (i); y holds {p} and
θ_y(Y) ≤ v_y(Y ∩ R_y) = v_y(X ∩ R_y) + v_y(q) ≤ v_y(p) by (ii). e = 0 by (iii). Lemma 2 with |Y ∖ X| = 1.
For (i′): let z ∉ {o, y}; then q ∉ R_z and X ⊄ R_z, so θ_z(X ∪ {q}) = v_z(X ∩ R_z) = θ_z(X) ≤ v_z(B_z), as X is safe
in P. ∎

**Corollary 5 (unblocking).** Let P be min-frozen with ω ≥ 1 and def(P) > 0, o a best owner with an optimal bundle
X, C := J ∖ X, and y ≠ o free. Let B′ ⊆ (B_y ∪ C) ∩ R_y, |B′| ≤ 2, B′ ≠ B_y, with v_y(B′) ≥ v_y(B_y). Suppose some
c ∈ C ∖ B′ is such that X ∪ {c} threatens no agent z ∉ {o, y} holding B_z, and θ_y(X ∪ {c}) ≤ v_y(B′). Then P′ (y
holding B′) is min-frozen with def(P′) ≤ def(P) − 1.

*Proof.* N_y(B′) ⊆ N_y(B_y) ⊆ 𝒩 by (M2), so B′ is admissible; B′ ⊆ B_y ∪ C misses X. Y := X ∪ {c} is a bundle of
o in P′ (c ∈ J ∖ B′ ⊆ J(P′)), safe in P′ by the hypotheses, and e = 0 since v_y(B′) ≥ v_y(B_y). Lemma 2. ∎

A typical instance is a free agent x exposed w.r.t. o that violates (U) or (U₂) of Lemma H2 with an improvement made
of removed junk: "a threatened free agent switching to a better base".

### 4.2 Role swaps

**Lemma 6 (role swap).** Let P be min-frozen with needed set 𝒩, x ∈ F with B_x = {g}, z free with g ∈ R_z, and H a
(possibly empty) set of further free agents (*helpers*). Let G := J ∪ B_z ∪ ⋃_{h ∈ H} B_h (the goods the move may
use). Let P′ be P with B′_z = {g}, B′_x = A and B′_h (h ∈ H), where A ⊆ G ∩ R_x, B′_h ⊆ G ∩ R_h, each of at most two
goods, pairwise disjoint. If N_x(A) ⊆ 𝒩, N_z({g}) ⊆ 𝒩 and N_h(B′_h) ⊆ 𝒩 for every h ∈ H, then P′ is min-frozen,
NA(P′) = 𝒩 (so g is still needed) and F(P′) = (F ∖ {x}) ∪ {z}. If z needs g in P (g ∈ N_z), the condition
N_z({g}) ⊆ 𝒩 holds automatically.

*Proof.* NA(P′) is the union of the unchanged agents' needs, N_x(A), N_z({g}) and the N_h(B′_h), all inside 𝒩. Every
good of 𝒩 ∖ {g} is the base of a frozen agent of P other than x, unchanged in P′ (z and the helpers are free in P, so
their bases miss 𝒩); g is z's base. So every needed good of P′ is a one-good base. The new bases lie in G, which misses
𝒩 and the unchanged bases; they are disjoint, inside the relevant sets and of at most two goods; so P′ ∈ 𝒫 by (V). Then
|F(P′)| = |NA(P′)| ≤ |𝒩| = f, so equality by minimality: NA(P′) = 𝒩 ∋ g, and the frozen agents of P′ are those whose base
is a single good of 𝒩: F ∖ {x} (A and the B′_h lie in G, which misses 𝒩) plus z. If g ∈ N_z, then v_z(g) > v_z(B_z),
and every good of R_z ∖ {g} worth more than g is worth more than B_z, so it is not in B_z and lies in N_z ⊆ 𝒩; so
N_z({g}) ⊆ 𝒩. ∎

Lemma 6 makes the (T3) moves of §3 well defined: a role swap with a needer stays in the min-frozen class as soon as
the unfrozen agent's new base and the helper's are admissible for 𝒩 (for x, in practice, its best one or two goods
outside 𝒩 among the freed goods G).

**Lemma 7 (the unfrozen agent as owner).** Let P′ ∈ 𝒫 be min-frozen with ω ≥ 1, x free in P′, and z ∈ F(P′) with base
{g}, g ∈ R_x, such that no agent other than x needs g in P′. If Z is a safe bundle of x in P′ with v_x(Z) > v_x(g),
then z is counted in u′_x(Z), and def(P′) ≤ ω + 1 − |Z|. If x has four goods and g is its top with
v_x(g) > v_x(b) + v_x(c) (x is *big-top*: b, c its second and third goods), then v_x(Z) > v_x(g) forces
R_x ∖ {g} ⊆ Z; so every good of R_x ∖ {g} must lie in x's base or in J(P′).

*Proof.* g ∉ Z (g is z's base, and Z ⊆ B′_x ∪ J(P′) misses the other bases), and v_x(Z) > v_x(g), so g ∉ N_x(Z); by
hypothesis g ∉ N′_i for i ≠ x. So z's base misses N_x(Z) ∪ 𝒩′₋ₓ, i.e. z is counted, u′_x(Z) ≥ 1, and Lemma H1 gives
def(P′) ≤ ω + 2 − |Z| − 1. For the big-top case: Z ∩ R_x ⊆ R_x ∖ {g} = {b, c, d}, and every proper subset of {b, c, d}
is worth at most v(b) + v(c) < v(g) (a pair; a single good is worth less than its pair), so v_x(Z) > v_x(g) needs all
three. ∎

This is the mechanism of every three-agent trap found (§1, §3): the frozen agent x is big-top (all 311 states), the
role swap makes it free, and it lowers the deficit by becoming the owner of a bundle that holds its three lower goods
and so unfreezes z (Lemma 7). One of those goods sits in a third agent's base, which must give it up: that agent is
the helper. On the data, in 4,767 of the 4,779 improving moves at the 311 trap states, x is a best owner afterwards with
an optimal bundle containing R_x ∖ {g} that counts z, and the helper gives up one of x's lower goods; in the other 12
the helper (which also holds a lower good of x) keeps it, and x's bundle gains otherwise.

## 5. Coverage: what the lemmas reach, and what remains

On the 52,166 def > 0 states of §2 (cores; the suite and #53's catalogues):

A state is *certified* when some minimal repair of it satisfies the hypotheses of one of the lemmas of §4 with a
positive gain, so that the lemma shows the repair lowers the deficit; the hypotheses are checked on the state, the
conclusion is asserted against the exact deficit (`results/k4_dl2_classify/table.md`, sections C and C′; for Lemma 7
see §2.3: H1 with every counted agent, the same states with Lemma 7's own bound). This is a **consistency check on the
repairs found by enumeration**: it says that, at those states, a lemma accounts for why the found repair lowers the
deficit. It does not explain why a repair exists.

| states | share | moves stay in the min-frozen class | certified (the repair lowers the deficit by a lemma) | not certified |
|---|---|---|---|---|
| k = 1: 39,466 | 75.7% | Lemma 1 | 39,465 (100.0%) (Lemma 2 or 3); structural hypotheses (Corollary 4 or 5): 27,937 (70.8%) | 1 (`gap_n4_pure_s4000`, core (m = 11, idx 5), §2.3) |
| k = 2: 12,389 | 23.7% | Lemma 1′ (trades), Lemma 6 (role swaps) | 11,250 (90.8%) (Lemma 2* or Lemma 7) | 1,139: 1,123 trade-only states, 16 role-swap states |
| k = 3: 311 | 0.6% | Lemma 6 | 311 (100%) (Lemma 7) | 0 |

So the lemmas certify a repair at 51,026 (97.8%) of the 52,166 def > 0 states; the rest are 1,140 (2.2%): the 1,123
states whose only minimal repairs are trades, 16 role-swap states and the one k = 1 state. What is not proved anywhere
is that a repair *exists*: the certificates are checked on each state, not derived from the obstruction.

Of the 52,166 states, 197 have f = 0 (suite instances; there DL_T holds by Theorem Z, §3) and 51,969 have f ≥ 1.
What a proof of DL₁₃ (hence of DL_T, which holds at f = 0) still needs:
- **existence**: a reason why, at every def > 0 state with f ≥ 1, some (T1) or (T3) move lowers the deficit. No
  obstruction class guarantees a one-agent repair (§2.1), so the case analysis must be on finer structure;
- **the deficit side of (T3)**: a lemma that a role swap (with its helper) lowers the deficit under structural
  hypotheses, extending Lemma 7 (which gives the unfreezing, not the safety of the new owner's bundle). Trades need no
  lemma for DL₁₃: of the 1,123 states whose nearest repairs are all trades, 1,118 have f = 1, and R_13 holds there
  through a farther (T1) or (T3) move; the other 5 have f = 0;
- **Lean**: the relation "(T1) or (T3) when f ≥ 1, any pair when f = 0" together with Theorem Z, so that
  DL₁₃ ⟹ TARGET₄ is machine-checked (§3);
- **more data**: DL₁₃ at the exhaustive n = 3 states at distance 1 and 2 (the distance-3 ones are done, §3, on the
  parallel compute/k4-dl2 workstream's dump), n ≥ 6, more n = 5.

## 6. Checks of the lemmas

Exactly what this workstream's code asserts (no assertion fails anywhere):
- At every state of §2 (`k4/dl2_classify.py`, `lemma_checks`): Lemma 1(c), only its validity part (every re-base
  admissible for 𝒩 gives a min-frozen P′); Lemma 2 (at every free owner o and optimal bundle X, with X ∖ B′), Lemma 3
  and Corollaries 4, 5: the conclusion def(P′) ≤ def(P) − gain whenever the hypotheses hold with a positive gain.
  At the minimal repairs of the states with k ≥ 2 (`multi_checks`): Lemma 2*'s gain conclusion, and Lemma 7's
  conclusions (z is counted, def(P′) ≤ ω + 1 − |Z|) for every bundle it applies to.
- On random strict instances with 3- and 4-good strictly balanced agents that need not be cores (n ≤ 4, m ≤ 10), and
  on #53's n = 3 catalogue (`k4/dl2_lemma_random.py`; `results/k4_dl2_classify/lemma_random.log`,
  `results/k4_dl2_classify/lemma_catalog_n3.log`): the same at every state, plus Lemma 1′ (every trade it allows gives
  a min-frozen P′ with the same needed and frozen sets), Lemma 6 (the same for every role swap with at most one helper
  it allows, frozen set F − x + z) and Lemma 7 (at every min-frozen P, every safe bundle it applies to). No
  violation. Random: 3,000 instances (1,855 with ω ≥ 1), 5,635 def > 0 states, 5,656,122 trades and role swaps
  checked, Lemma 7 at 50 bundles; catalogue: 3,000 records (every 24th), 1,757 states, 841,830 moves, Lemma 7 at 26,216
  bundles.
- Not checked by this code: Lemma 1(a), (b), the equality (not only the gain) in Lemma 3, and (i′) ⟹ (i) in
  Corollary 4. The PR #69 referee checked these with independent code (0 violations).

## 7. Reproduce

```
git archive 245040b k4 results/k4_gap results/k4_certs_2.json.gz results/k4_certs_3.json.gz \
  results/k4_certs_4_n4_1.json.gz results/k4_certs_4_n4_2.json.gz results/k4_certs_4_n4_3.json.gz \
  results/k4_certs_4_pure.json.gz | tar -x -C k4/suite/.cache/gapbench        # #53's catalogues (k4/strategy.md §4)
sh k4/dl2_classify_runs.sh             # classification + table (results/k4_dl2_classify/; ~15 min on 2 CPUs)
sh k4/dl2_relations_runs.sh    # DL_R on the suite, the catalogues and the hunts (results/k4_dl2_relations/)
sh k4/dl2_relations_runs2.sh   # DL_R on whole certificate files: every n = 2 profile, random n = 3, 4 profiles
python3 k4/dl2_relations_table.py results/k4_dl2_relations/*.log > results/k4_dl2_relations/table.md
sh k4/dl2_xcheck_runs.sh       # second implementation on samples (results/k4_dl2_relations/xcheck.log)
mkdir -p k4/suite/.cache/compute_k4_dl2      # baf3b9f is on origin/compute/k4-dl2 (fetch that branch first)
git show baf3b9f:results/k4_dl2/trapped_n3.jsonl.gz > k4/suite/.cache/compute_k4_dl2/trapped_n3.jsonl.gz
python3 k4/dl2_relations_trapped.py k4/suite/.cache/compute_k4_dl2/trapped_n3.jsonl.gz --model=20   # exhaustive n = 3, distance 3
python3 k4/dl2_lemma_random.py 3000 --seed=7 --nmax=4 --mmax=10       # results/k4_dl2_classify/lemma_random.log
python3 k4/dl2_lemma_random.py 3000 --catalog=k4/suite/.cache/gapbench/results/k4_gap/gap_n3.json.gz --every=24
python3 attempts/k4_dl2_attempts.py     # every failure of §1 and §3 with two implementations (results/k4_dl2_relations/attempts.log)
python3 k4/dl2_classify.py one '{"sets": [[0,1,2,3],[2,4,5,6],[3,4,5,6]], "vals": [[2,4,3,8],[2,6,10,7],[8,3,4,2]], "m": 7}'
```
