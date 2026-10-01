# DL₂ and its successor: the shapes of the deficit repairs

Workstream `proof/k4-dl2-k1` (PR #69). Ledger rows K4.DL2.* (and K4.STRAT.DL2, now REFUTED). Builds on
`k4/strategy.md` §3 (Conjecture DL₂ and its plan), `k4/c4x.md` §1 (the space 𝒫 and the removal-only deficit),
`k4/hall.md` (Lemma H1 and the exposure lemmas H3, H6, H7), `k4/c4min.md`, `k4/c4min_reduce.md`, `k4/c4min_f1.md`,
`k4/gap.md` and the suite `k4/suite/`. Nothing here changes K4.D or K4.T.

**Summary.**
- **DL₂ is false** (§1, ledger K4.DL2.X3, K4.STRAT.DL2 REFUTED): on a connected k = 4 core with n = 3, m = 7, a
  min-frozen P with def(P) = 1 has no min-frozen P′ with a smaller deficit within two agents' base changes. The nearest
  one is a *role swap* (the frozen agent gives its good to an agent that needs it) plus a third agent that gives up a
  good. 89 of the 74,256 profiles of #53's n = 3 catalogue have such a state (311 states).
- **The repairs, classified** (§2, EVIDENCE): on 52,166 states with def > 0 (the suite and #53's catalogues), the
  nearest repairs are one-agent changes in 76%, two-agent changes in 24% and three-agent changes in 0.6% (all at n = 3);
  one-agent repairs are almost always *releases* (an agent gives up a good that an owner's safe bundle absorbs);
  two-agent repairs are role swaps with an agent that needs the frozen good (91%) or *trades* between two free agents;
  every three-agent repair is a role swap plus one more agent's change.
- **The successor target** (§3): DL_R for a structured neighbourhood relation R. Since PR #68
  (`EFX.C4min.target4_of_defLocal`, K4.STRAT.DL2.LEAN), DL_R implies TARGET₄ for every R. The relation **R_T** (one
  re-base; a trade of two free agents; or a role swap with a needer and at most one helper that gives up a good)
  survives every state tested; every narrower relation tested fails, smallest failures at n = 2 and n = 3
  (§3, `attempts/k4-dl2-relations.md`).
- **The moves, in writing** (§4; written proofs, not refereed, CONJECTURE rows): the moves of R_T stay in the
  min-frozen class and keep its needed set (Lemmas 1 and 6); a one-agent move lowers the deficit exactly through an
  owner's bundle growing (Lemma 2, extension) or the moving agent becoming a better owner (Lemma 3, owner re-base);
  releases and unblocking pool improvements are the two structural instances (Corollaries 4, 5). On the data,
  Lemmas 2 and 3 cover every one-agent repair (§2.3).

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
`results/k4_dl2_classify/table.md` (made by `k4/dl2_table.py`).

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

Each lemma of §4 is checked at every state: whenever its hypotheses hold, its conclusion is asserted against the exact
deficits (`k4/dl2_classify.py lemma_checks`; no assertion fails on any input), and no lemma ever applies at a state with
k > 1.

| | k = 1 states | Corollary 4 (release), structural form (i′) | Corollary 4 | Corollary 5 (unblocking) | Lemma 2 at a best owner | Lemma 2 at another owner | Lemma 3 (owner re-base) | Lemma 2 or 3 |
|---|---|---|---|---|---|---|---|---|
| all inputs | 39,466 | 23,719 (60.1%) | 26,324 (66.7%) | 2,354 (6.0%) | see `table.md` | | 4,139 (10.5%) | see `table.md` |
| Pareto-maximal states | 3,289 | 2,580 (78.4%) | 2,606 (79.2%) | 0 | | | 365 (11.1%) | 3,289 (100%) |

(The Lemma 2 columns are those of the final run, `results/k4_dl2_classify/table.md`, which uses the form of Lemma 2
with X ∖ B′ in place of X.) So the one-agent repairs are understood: every one is an extension of an owner's bundle
(Lemma 2) or an owner re-base (Lemma 3), and two thirds are releases satisfying the hypotheses of Corollary 4. What is
**not** understood is why a one-agent repair exists when it does; no obstruction class guarantees one.

## 3. Structured relations R (`k4/dl2_relations.py`, `results/k4_dl2_relations/`)

DL_R: every min-frozen P with def(P) > 0 has a min-frozen P′ with R(P, P′) and def(P′) < def(P). By K4.STRAT.DL2.LEAN
(PR #68), DL_R ⟹ TARGET₄ for every R, so R may be any relation whose moves a proof can handle. `k4/dl2_relations.py`
enumerates, for each state, **every** min-frozen P′ with a smaller deficit (not only the nearest), describes the move
P → P′ by its shape (which agents change, which unfreeze or freeze, whether the frozen good goes to an agent that
needed it, what the other changed agents do), and evaluates each relation.

The moves (P, P′ both min-frozen; "needed set unchanged" means NA(P′) = NA(P)):
- **re-base**: exactly one agent's base changes (it is free, Lemma 1);
- **trade**: exactly two agents' bases change, both free in P and in P′, needed set unchanged (Lemma 1′);
- **role swap with a needer**: a frozen agent x with base {g} unfreezes, a free agent z with g ∈ N_z(B_z) takes {g}
  and freezes, needed set unchanged (Lemma 6); *helpers*: further changed agents, free in P and P′.

| relation | moves | fails on |
|---|---|---|
| R2 | at most two agents change (DL₂) | n = 3 (311 states) |
| RB | re-base, or a plain role swap with a needer | n = 2, f = 0 (`induct-g-r1`); n = 3 |
| RB2 | RB or a trade | n = 3 (the 311 states of R2) |
| RS1 / RS1+2 | re-base, (trade,) or a role swap with any number of helpers each giving up one good and taking nothing | n = 2, n = 3 / n = 3 |
| RSR+2 | re-base, trade, or a role swap with helpers that only give up goods (any number) | n = 3 |
| RC | re-base, trade, or a chain of frozen goods ending at a free agent (LB⁺'s rotation shape) with releasing helpers | n = 3 |
| RSY, RSYa, RSYg | re-base, or a role swap with at most one (RSYa: any number of) helper(s); **no trades** | n = 2, f = 0 (`induct-g-r1`) |
| RSYz+2, RSYgz+2 | re-base, trade, or a role swap with at most one helper that takes goods only from its own base and B_z (and gives up a good) | n = 3 (13 states) |
| RSY+2 | re-base, trade, or a role swap with at most one helper re-basing in any way | none |
| RSYg+2 | RSY+2, the helper giving up at least one good of its base | none |
| **R_T** | RSYg+2 with re-bases that keep the needed set and trades in which a good passes between the two agents | **none** |

The failures, each confirmed by two implementations (`k4/dl2_relations.py` on `k4/suite/model.py`, and main's
`k4/c4x_check.py` with separately written membership tests in `attempts/k4_dl2_attempts.py`; at each failing state both
implementations also find an R_T move):
- **trades are needed** (RB, RS1, RSY, RSYa, RSYg): `induct-g-r1` (#43), n = 2, m = 5, f = 0: no agent is frozen, so
  there is no role swap, and every improvement exchanges goods 2 and 3 between the two agents (Theorem Z's rotation of
  a 2-cycle);
- **two agents are not enough** (R2, RB2): `dl2-n3m7` of §1;
- **releasing helpers are not enough** (RS1+2, RSR+2, RC): `dl2-n3m7-trade` (n = 3, m = 7), where the helper must also
  take a good of the needer's old base;
- **the helper needs junk** (RSYz+2, RSYgz+2): `dl2-n3m8-junk` (n = 3, m = 8), where the helper gives up the unfrozen
  agent's good and takes a junk good.

`attempts/k4-dl2-relations.md` has the instances and what every improving move of each does.

**Conjecture DL_T (K4.DL2.T).** For every strict profile of every connected k = 4 core with ω ≥ 1, every min-frozen
P ∈ 𝒫 with def(P) > 0 (+∞ included) has a min-frozen P′ ∈ 𝒫 with def(P′) < def(P) that arises from P by one of the
following moves, the needed set NA staying the same:
- **(T1) re-base**: one free agent y replaces its base by another base inside B_y ∪ J;
- **(T2) trade**: two free agents y, y′ replace their bases by bases inside B_y ∪ B_{y′} ∪ J, and some good of one of
  the two old bases ends in the other agent's new base;
- **(T3) role swap with at most one helper**: a frozen agent x with base {g} and a free agent z with g ∈ N_z(B_z):
  z takes {g}, x takes a new base, and at most one further free agent h (the *helper*) replaces its base by one that
  misses at least one good of B_h. (The new bases then lie in the goods the move frees, J ∪ B_z ∪ B_h, since the other
  bases do not move.)

By Lemmas 1′ and 6 every such move stays in the min-frozen class as soon as the new bases are disjoint, inside the
relevant sets, of at most two goods, and need only goods of NA. DL_T implies TARGET₄ (K4.STRAT.DL2.LEAN).

*Evidence* (EVIDENCE row K4.DL2.TE; single implementation for the survivals): every state of §2's inputs and of #53's
hunt catalogues (`results/k4_dl2_relations/`; table below). Not exhaustive at any n ≥ 3.

RESULTS_TABLE_PLACEHOLDER

*What a proof of DL_T needs.* A case analysis on the obstruction (§2.1) showing that when no (T1) move lowers the
deficit, a (T2) or (T3) move does. §4 handles the (T1) side exactly (Lemmas 2, 3). For (T2) and (T3) validity is proved
(Lemmas 1′, 6); their effect on the deficit is again Lemma H1 applied to P′. For the three-agent cells the data and
Lemma 7 give the mechanism: the frozen agent x is big-top, the swap frees it, and x becomes the owner of a bundle that
holds its three lower goods, which unfreezes the needer z; the helper is the agent holding one of those goods. The
swap has the shape of Lemma F1's path move of length 0 (`k4/c4min_f1.md` §2: x becomes free, a terminal takes g), and big-top frozen
agents are exactly where F1's potential Ψ = (r, Λ) stalls (every path move from a big-top x ties in Ψ, `k4/c4min_f1.md`
§3; no potential starting with (r, Λ) works, K4.C4MIN.F1BT). The deficit counts the unfreezing, which Ψ does not see;
that is an observation, not a proof that it always suffices.

## 4. The moves, in writing

Written proofs, **not refereed** (ledger rows K4.DL2.MOVES, K4.DL2.ONE: CONJECTURE until an independent referee
checks them). They use only the definitions of `k4/c4x.md` §1 and Lemma H1 of `k4/hall.md` §1 (ledger K4.HALL.COVER,
PROVED). Every statement is checked at every def > 0 state of the data (§2): `k4/dl2_classify.py` evaluates the
hypotheses and, whenever they hold, asserts the conclusion against the exact deficits.

**Setting.** A strict profile of an instance in which every agent has three or four relevant goods and is strictly
balanced: the setting of Lemma H1; every k = 4 core is one. (Balance enters only through Lemma H1; the random checks of
§5 use such instances that are not cores.) 𝒫, bases B_i, junk J, needs N_i(B) = {g ∈ R_i ∖ B : v_i(g) > v_i(B)},
N_i := N_i(B_i), NA = ⋃ N_i, frozen agents F, slots and ω are those of `k4/c4x.md` §1. Recall:
- (V) P ∈ 𝒫 iff its bases are disjoint subsets of the agents' relevant sets with at most two goods each and every
  needed good is the whole base of one agent ((V1) and (V2), `k4/c4x.md` §1). Hence |F| = |NA|, and
  ω = |J| − S = |F| − (2n − m).
- f is the fewest frozen agents over 𝒫; P is *min-frozen* if |F(P)| = f. All min-frozen P have the same ω; we assume
  ω ≥ 1.
- An agent's needs avoid its own base. A free agent's base contains no needed good (a free one-good base is not
  needed by definition, a pair by (V2)). Values are nonnegative, so every good of a base is worth at most the base.

For Z ⊆ M nonempty and an agent x, θ_x(Z) := max_{h ∈ Z} v_x(Z ∖ h); Z *threatens* x holding B if θ_x(Z) > v_x(B).
θ_x is monotone: Z ⊆ Z′ implies θ_x(Z) ≤ θ_x(Z′). If Z ⊄ R_x then θ_x(Z) = v_x(Z ∩ R_x) (remove a good x does not
value); always θ_x(Z) ≤ v_x(Z ∩ R_x).

For a free agent o of P, W_o := B_o ∪ J. A *bundle* of o is a Z with B_o ⊆ Z ⊆ W_o; it is *safe* (in P) if it
threatens no agent x ≠ o holding B_x. u_o(Z) is the number of x ∈ F with B_x ∩ (N_o(Z) ∪ 𝒩₋ₒ) = ∅, where
𝒩₋ₒ := ⋃_{i ≠ o} N_i and N_o(Z) := {g ∈ R_o ∖ Z : v_o(g) > v_o(Z)} (such an x is *counted* in u_o(Z)): the frozen
agents that the owner's needs from Z unfreeze. Val_P(o) := max{|Z| + u_o(Z) : Z a safe bundle of o} (Z = B_o is
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
counted agent's good meets, so e = 0. The last two claims follow from def(P) = ω + 2 − Val*(P) (Lemma H1) and
|X| + u_o(X) ≤ Val*(P), with equality for an optimal X of a best owner. ∎

**Lemma 3 (owner re-base).** Let P be min-frozen with ω ≥ 1, y free, B′ admissible for 𝒩 and P′ the result. Then
Val_{P′}(y) = max{|Z| + u_y(Z) : B′ ⊆ Z ⊆ W_y, Z safe in P}, with W_y = B_y ∪ J and u_y computed in P. So
def(P′) < def(P) as soon as some Z with B′ ⊆ Z ⊆ W_y, safe in P, has |Z| + u_y(Z) > Val*(P).

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

| states | share | what is proved about them (written, not refereed) | what is only data |
|---|---|---|---|
| k = 1: 39,466 | 75.7% | the move stays in the class (Lemma 1); it lowers the deficit by Lemma 2 or Lemma 3 at COV_L23 of them (an exact sufficient criterion, checked to hold); structural hypotheses (Corollaries 4, 5) at COV_C45 | that a one-agent repair exists at all |
| k = 2: 12,389 | 23.7% | the move stays in the class (Lemma 1′ for trades, Lemma 6 for role swaps) | that it lowers the deficit (no structural lemma) |
| k = 3: 311 | 0.6% | the move stays in the class (Lemma 6); the mechanism (Lemma 7: the unfrozen big-top agent, as owner of its three lower goods, unfreezes its needer) | that it always works; it does in 4,767 of the 4,779 improving moves |

So the lemmas *certify* a repair (hypotheses checked on the state, conclusion proved) at COV_CERT of all def > 0
states, all of them one-agent states; no lemma certifies a two- or three-agent repair. What a proof of DL_T still needs:
- **existence**: a reason why some (T1), (T2) or (T3) move lowers the deficit at every def > 0 state. No obstruction
  class guarantees a one-agent repair (§2.1), so the case analysis must be on finer structure;
- **the deficit side of (T2) and (T3)**: a lemma that a role swap (with its helper) lowers the deficit under structural
  hypotheses, extending Lemma 7 (which gives the unfreezing, not the safety of the new owner's bundle); and the same
  for trades, which on the data are needed only when no agent is frozen (§3);
- **more data**: exhaustive n ≤ 3 (the parallel `compute/k4-dl2` workstream), n ≥ 6, more n = 5;
- **a referee** for §4.

## 6. Checks of the lemmas

- At every state of §2 (`k4/dl2_classify.py`, `lemma_checks`): Lemma 1(c) (every allowed re-base is a min-frozen P with
  the same needed set), Lemmas 2, 3 and Corollaries 4, 5 (conclusion asserted whenever the hypotheses hold); no lemma
  applies at a state with k > 1. No assertion fails.
- On random strict instances with 3- and 4-good strictly balanced agents that need not be cores (n ≤ 4, m ≤ 10), and
  on #53's n = 3 catalogue (`k4/dl2_lemma_random.py`; `results/k4_dl2_classify/lemma_random.log`,
  `results/k4_dl2_classify/lemma_catalog_n3.log`): the same, plus Lemma 1′ (every trade it allows), Lemma 6 (every role
  swap with at most one helper it allows) and Lemma 7 (every safe bundle it applies to). No violation.

## 7. Reproduce

```
git archive 245040b k4 results/k4_gap results/k4_certs_2.json.gz results/k4_certs_3.json.gz \
  results/k4_certs_4_n4_1.json.gz results/k4_certs_4_n4_2.json.gz results/k4_certs_4_n4_3.json.gz \
  results/k4_certs_4_pure.json.gz | tar -x -C k4/suite/.cache/gapbench        # #53's catalogues (k4/strategy.md §4)
sh k4/dl2_runs.sh              # classification + table (results/k4_dl2_classify/; ~15 min on 2 CPUs)
sh k4/dl2_relations_runs.sh    # DL_R on the suite, the catalogues and the hunts (results/k4_dl2_relations/)
sh k4/dl2_relations_runs2.sh   # DL_R on whole certificate files: every n = 2 profile, random n = 3, 4 profiles
python3 k4/dl2_relations_table.py results/k4_dl2_relations/*.log > results/k4_dl2_relations/table.md
python3 k4/dl2_lemma_random.py 3000 --seed=7 --nmax=4 --mmax=10       # results/k4_dl2_classify/lemma_random.log
python3 k4/dl2_lemma_random.py 3000 --catalog=k4/suite/.cache/gapbench/results/k4_gap/gap_n3.json.gz --every=24
python3 attempts/k4_dl2_attempts.py     # every failure of §1 and §3 with two implementations
python3 k4/dl2_classify.py one '{"sets": [[0,1,2,3],[2,4,5,6],[3,4,5,6]], "vals": [[2,4,3,8],[2,6,10,7],[8,3,4,2]], "m": 7}'
```
