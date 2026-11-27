# One chain suffices at k = 3 (OC₁ at k = 3), and lifting it to k = 4

Workstream `proof/k4-k3-oc1` (PR #96). Code: `k4/k3oc1/`; logs: `results/k4_k3oc1/` (`*.log` summaries, `*.hard.gz`
the hard starts, one per line, readable by every analysis script). Notation: `paper/k3-simple` (Draft and Exchange, DE)
and `proofs/lb_last_step.md` (LB⁺); Conjecture OC₁ is `k4/sdc.md` §29. Everything called evidence is evidence only
(PROMPT.md §5 rule 3).

## Status (end of burst 5)

**Burst 5: the joint statement with kgen-n3** (OC₁ at maximum-matching starts, DE's core case; §11–§12).
- **Proved.**
  - The reduction to perfect starts (Lemmas MAX₃, RED₃; §11).
  - At perfect starts: Theorems R1C and B\* (§3).
  - Lemma 4: shared pairs die together.
  - Lemma 5: the release count. A trade with q pair-takers gives ω′ = ω − r, where r is the number of released
    goods; no owner is needed iff r ≥ ω, or r ≥ ω − 1 using k's slot.
  - Lemma 6: in a hard state every terminal has a frozen exposed agent.
  - Lemma 7: the pointer walk. If no single rotation is valid, the walk closes into a cycle with q ≥ 2 pair arrows
    (§12.1).
  - kgen-n3's Lemma G5 (Rule E rotations keep the want graph acyclic), checked.
- **Conjectured, holding on all data.**
  - **T′_k**: some rotation from an exposed agent k of a terminal t into t completes, with no owner or owner k.
    Exhaustive on every hard perfect draft with n ≤ 6 (338,916 at n = 6); no failure on 4,759 sampled n = 7 drafts.
  - **T-E∃**: some valid Rule E (earliest-wanter) rotation completes, with owner nobody, the chain's end e, or k,
    plus k's slot.
  - **The crossed configuration.** Where no single rotation is valid (64 two-terminal gap drafts at n = 6), a ring
    with two pair arrows completes.
- **Refuted.**
  - kgen-n3's T1′ (one terminal, no owner): fails on 360 one-terminal gap drafts at n = 6.
  - "Two terminals never land in the gap": 10,304 drafts at n = 6.
  - The every-k forms (kgen-n3's T1-E; T-E): fail at n = 7 on a gap draft of an m = 12 core
    (`attempts/k4-k3oc1-every-k.md`, independent replay). The choice of k matters: the failing rotations release
    nothing, while least-ω′ rotations reach ω′ ≤ 0.
- **Next.**
  - Prove T-E∃ with k chosen to maximize releases (least ω′), via Lemma 5 and B\*'s count with |T′|. The release
    lemma is shared with kgen-n3's T1-k.
  - Larger samples running: n = 7, n = 8 cores, and DE's general core case at n = 5, which is the class the
    reduction produces.

**Bursts 1–4:**

- **Headline.** OC₁ as tested in `k4/sdc.md` §29 is false at k = 3. On an n = 5 instance outside the ledger's cores
  the picks need two chains of `k4/sdc/de_free.py` (§9, `attempts/k4-k3oc1-oc1-counterexample.md`). On cores, OC₁
  holds on every test, in the strong form OT below.
  - It is repaired by one chain if a chain may pass an empty-handed agent, and by the free completion.
  - Proved here: OC₁ for R1-compatible orders (Theorem R1C), and LB⁺'s rotation for every order (Theorem B\*).
  - The first k = 3 fact that fails at k = 4 is (DE-a): only top-holders gain from junk (nsw-local-n3m5).
- **OC₁ at maximum-matching starts holds at k = 3 on all data (§10).** This covers every core with n ≤ 5, every
  n = 6, m ≥ 10 core, and DE's general core case with n ≤ 5, every profile and order. One DE trade always suffices.
  The k = 4 counterexamples of `k4/sdc.md` §31 need a b-holder with a junk danger pair, which is (DE-a) and is
  impossible at k = 3.
- **Proved.**
  - Lemma 1 (§2): soundness of the simple completion. LB⁺'s Lemma 1 with one slot per terminal, plus an empty-handed owner left with two goods.
  - Lemma 2 (§2): ω = (m − 2n) + e + ν, where e counts the agents holding nothing and ν the needed goods; no DE trade raises ω.
  - Lemma 3 (§2): self-service. Exposed terminals serve themselves, provided no exposed pair lies inside the owner's base (automatic for terminal owners; referee fix); every satisfied state completes.
  - Refereed (`k4/referee/k3_oc1.md` on `claude/k4-referee`): Lemmas 1 and 2, Theorems R1C and B\* correct; Lemma 3 correct with the fix above.
  - **Theorem B\* (§3): LB⁺'s rotation for every order.** If a terminal has deficit one and an exposed frozen agent whose removal lowers the hitting number, one DE trade completes. It covers 8,075 of 14,138 exact-hard drafts (n ≤ 6 logs), with no failure on the 11,501 rotations checked.
  - **Theorem R1C (§3): OC₁ at k = 3, in DE's core case (every agent values exactly three strictly balanced goods; dead goods allowed), for every order whose draft is R1-compatible**, i.e. whose need order has an R1-priority linear extension (this includes every R1-priority order). The proof is LB⁺ with every slot of size one. The rotation is one DE trade, and the completion has one absorber.
- **Conjectured.** **OT (§4), for the ledger's cores.** At k = 3, from the draft of every order, a one-absorber
  completion exists, or one DE trade gives one (**OT₁**). Indeed it exists after every DE trade of least ω (**OT-ω**). No counterexample is known
  to either form. Both imply OC₁ at k = 3.
  - On the ledger's cores two stronger forms hold on all data: every least-ω trade passes even Lemma 1, and every
    max-score trade completes.
  - In DE's general core case (dead goods, several private goods) both stronger forms are refuted at n = 6
    (`attempts/k4-k3oc1-selection-rules.md`). OT₁ itself fails there at n = 5, and so does "every least-ω trade" (§9).
  - Max score with Lemma 1 already fails on cores with n = 6, m = 9: a pair holder must absorb a junk good.
  - Exhaustive tests: every connected core with 3 ≤ n ≤ 5 (339 hypergraphs), every ranking profile, every order: 273,724,272 starts. Both rules were rechecked on every hard draft (`oc1_fast2_*.log`). Also n = 4 with one dead good.
  - Exhaustive in DE's general core case with n ≤ 4 (`oc1_general.py`): every hypergraph class (16 for n = 3, 93 for n = 4: any private goods, disconnected allowed), 0, 1 or 2 dead goods, every profile and order. OT₁ and OT-ω hold (`oc1_general_4_dead*.log`).
  - n = 6, m ≤ 9 cores, every profile, first 355 of 2,856 cores (`oc1_fast2_small6_partial.log`): every least-ω trade passes Lemma 1, and every max-score trade completes.
  - Exhaustive at n = 6, m ∈ {10, 11}: all 236 connected cores, every profile, and the drafts of all 720 orders, enumerated as distinct drafts (`oc1_fast.py`, `oc1_fast_certs6_*.log`): 11,010,816 profiles, 37,318,272 distinct drafts, 888,292 hard. No failure of either rule; here even the max-score trade passes Lemma 1.
  - Sampled tests: n = 6 cores with m ≤ 9 (6 million starts), random instances with n ≤ 10, and the binary-tree family of `paper/k3-simple` Appendix C up to n = 45 (draft deficits up to 7, owner still needed after the trade).
  - OC₁ itself was also checked directly, with general chains and the exhaustive one-absorber completion, for every core with n ≤ 4 and with n = 5, m = 9.
  - On all data no max-score or least-ω trade is a length-zero DE chain (a free x dropping its top for its pair, which is not a §29 chain; `k0check.py`). So these trades are improving chains, and OT's data are OC₁ data.
- **Refuted: OC₁ as tested in `k4/sdc.md` §29 fails at k = 3** (`attempts/k4-k3oc1-oc1-counterexample.md`, with an
  independent replay).
  - **The instance:** n = 5, m = 9; agents 0, 1 value {0, 1, 2}, and agents 2, 3, 4 value a shared top plus two
    private goods. From the order (2, 3, 4, 0, 1) the picks need two chains of `k4/sdc/de_free.py` (chains stop at
    an empty-handed agent).
  - **Scope:** this hypergraph class is the only failure in DE's general core case at n = 5 (`oc1_general.py`; 288
    drafts).
  - **What survives:** the instance is not a core (R2 peels it). It is repaired by one chain if a chain may pass
    through an agent holding nothing (the literal §29 wording), and by one de_free chain under the free completion
    (Conjecture OC).
  - **So OT₁ and OT-ω are restricted to the ledger's cores**, where they hold on all data, or to DE trades
    glued at empty-handed agents.
- **Refuted proof routes** (§5):
  - "every Pareto-maximal trade works";
  - "every inclusion-maximal trade works";
  - "a failing trade merges with a later trade into one better trade". On n = 5 the repairing trade can be disjoint from the failing one.
  - the reverse-lexicographic rule;
  - a naive induction on the last agent.
  - ω is the quantity that works. The score sum works only on the ledger's cores. Both fail over §29's general chains even at k = 3, so a proof must use DE's narrow trades.
- **Open.** A proof of OT, or of OC₁, for drafts covered by neither R1C nor B\*. Those drafts have least deficit 2, or exposed agents that share junk goods (§3, end). The gap is precise (§6): exposed fresh agents whose need chains meet at one terminal through "cross needs" (R1 violations), and one trade must repair several of them at once (DE's worked example needs two pair arrows).
- **Lifting to k = 4 (§7, `attempts/k4-k3oc1-de-trades.md`).**
  - Lemma 1's soundness, Lemma 2's monotonicity and Lemma 3 lift; for Lemma 3, take the exposed terminal's best junk good.
  - The **first k = 3 fact that fails** is (DE-a): only an agent giving up its top gains from junk. At k = 4 a b-holder gains from {c, d} when c + d > b. On nsw-local-n3m5 (n = 3, m = 5) every repairing chain needs this.
  - The second is (DE-b), the trade keeping validity. On T3 (n = 3, m = 6) every repairing chain leaves a wanted good in a two-good bundle, and the completion compensates the wanter with junk.
  - **Repair:** chains with t ≥ 1 in which any agent may take junk, plus compensable validity. One such chain repairs every hard start of the special, screen and suite sets (n ≤ 5, every order) and of 2,300 random core profiles with n ≤ 4.
  - The k = 3 selection rule does not lift: max score works on 162 of 194 screen picks. It already fails at k = 3 outside DE's narrow trades.
- **Next.**
  - A proof of OT for one terminal: |T| = 1 covers all hard starts at n = 4 and 54% at n = 5, and its max-score trade has Theorem B's shape (§5).
  - A release lemma for the open case (§8): the best trade lifts every needer of an exposed agent's top above it.
  - For k = 4: a completion count with both kinds of one-good slots, terminal slots and compensation slots (§7).

## 1. Setting and the computation

Core case of DE: every agent values exactly three goods a > b > c, strictly balanced (a < b + c); goods valued by
nobody (*dead goods*) are allowed. All comparisons of subset sums of one agent's goods are fixed by its ranking
(0 < c < b < a < b+c < a+c < a+b < a+b+c, `paper/k3-simple` Lemma L5), so the values 4, 3, 2 lose nothing. Every test below is
therefore exact for every strictly balanced profile with the given rankings.

- *Draft* of an order π: serial dictatorship (`paper/k3-simple` Lemma draft). A valid DE state with no pair holders;
  conversely every valid state with no pair holders and an acyclic want graph is the draft of every linear extension
  of its want order.
- *One-absorber completion* (OC₁'s completion): a complete EFX₀ allocation keeping every base in which at most one
  agent receives two or more unallocated goods. `k3lib.completion` tests it by exhaustive search.
- *Improving chain*: `k4/sdc.md` §29 (`k3lib.chains`, same moves as `k4/sdc/de_free.py`). *DE trades*: DE's chains and
  rings (`de_moves.py`); each is an improving chain in §29's sense (a ring is the chain whose x₀ takes the end's base).

**Exhaustive OC₁ at k = 3** (`oc1_k3.py`, general chains, exhaustive completion): every connected core with n ≤ 4
(`results/certs_small_m.json.gz`) and with n = 5, m = 9 (`results/certs_5_6.json.gz`), every profile, every order:
no start needs more than one chain (`oc1_small4.log`: 1,244,160 starts, 17,696 need one chain; `oc1_certs5.log`:
13,996,800 starts, 114,596 need one).

**One DE trade suffices** (`oc1_lb.py`, completion test `lbtest.lb2`, exact on DE states and cross-checked against the
exhaustive test on 371,000 states, `xcheck_lb2_*.log`; and with the simple test `lb_simple` of Lemma 1, which needs no
upgrades):

| data (every profile, every order) | starts | hard (exact) | hard (simple) | one DE trade fails | max-score trade fails |
|---|---|---|---|---|---|
| n = 3 cores | 9,072 | 232 | 304 | 0 | 0 |
| n = 4 cores | 1,244,160 | 17,696 | 19,608 | 0 | 0 |
| n = 4 cores, one dead good | 1,244,160 | | 39,208 | 0 | 0 |
| n = 5, m = 9 cores (15) | 13,996,800 | 114,596 | 147,196 | 0 | 0 |
| n = 5, m ≤ 8 cores (277) | 258,474,240 | 1,587,988 | 1,641,364 | 0 | 0 |
| n = 6 cores, 30 random profiles each (236) | 5,097,600 | | 21,261 | 0 | 0 |
| n = 6, m ∈ {10, 11}, every profile (236); counted in distinct drafts | 37,318,272 drafts | | 888,292 drafts | 0 | 0 |
| n = 6, m ≤ 9 cores, 3 random profiles each (2,856) | 6,168,960 | | 13,782 | 0 | 0 |
| random 3-uniform instances, n = 6–10 | 200,000 | | 362 | 0 | 0 |
| Appendix C trees (k, d) = (2,1), (2,2), (3,2), (4,2) | n = 6, 14, 21, 28 | | 4 | 0 | 0 |

("Hard": the picks fail the test. Columns 5–6 count hard starts. The last column uses the simple test. On the n = 6,
m ≤ 9 cores with every profile, the max-score trade fails the simple test on 912 drafts but never the exact test,
while the least-ω trade never fails the simple test (§4–§5).)

## 2. Lemmas on DE states

A *DE state* gives each agent nothing, one of its goods, or its pair {b, c}; U is the set of pair holders, J the
unallocated goods (junk). It is *valid* if every good some agent wants (ranks above its holding; pair holders want
nothing) is held alone (`paper/k3-simple` Definition valid). The *terminals* T are the agents outside U whose holding
nobody wants (DE's free agents); the others outside U are *frozen*. For an owner o (a terminal or a pair holder) the
*exposed* agents E_o are the agents x ∉ U, x ≠ o, holding exactly a_x with b_x, c_x ∈ J ∪ base(o), and
π_x = {b_x, c_x} ∩ J (LB⁺'s E_o). h(o) is the least size of a set of junk goods meeting every π_x.

**Lemma 1 (simple completion; soundness).** A valid DE state has a one-absorber completion if
- (a) |J| ≤ |T| (every junk good to a different terminal; no owner), or
- (b) some owner o has no x ∈ E_o with {b_x, c_x} ⊆ base(o), and h(o) ≤ |T| − [o ∈ T] (a hitting set goes to the
  other terminals, one good each, and o takes the rest), or
- (c) some terminal o holds nothing and |J| ≤ |T| + 1 (o ends with at most two goods).

*Proof.* Every completion here gives the terminals other than the owner at most one junk good each, the frozen agents
and the pair holders other than the owner nothing. That is LB⁺'s completion with caps at most LB⁺'s, so LB⁺'s
Theorem 1′ applies to (a) and (b), with Lemma 1's argument for (b) (`proofs/lb_last_step.md` §2). Theorem 1′'s proof
also shows that a bundle of at most two goods threatens nobody in a valid state. In (c) every bundle has at most two
goods. ∎

The exact test `lb2` adds three things. On the ledger's cores the least-ω trade never needs them (§4). The max-score
trade and the general core case do (§5):
- upgrades (a b-holder takes its junk c, as in LB's Phase 2), chosen as a set, since the maximal set is not always
  best: an upgrade uses the agent's one junk good;
- a slot for every pair holder that already holds its pair, for a junk good that puts no exposed pair inside its
  bundle;
- an empty-handed owner with two goods, which is (c).

**Lemma 2 (ω).** In a DE state, ω := |J| − |T| = (m − 2n) + e + ν, where e is the number of agents holding nothing and
ν the number of wanted goods. A DE trade never raises e or ν, so it never raises ω.

*Proof.* Counting goods gives m = 2|U| + (n − |U| − e) + |J|, and counting agents gives n = |U| + ν + |T|, since every
wanted good is the single good of exactly one frozen agent. Subtracting gives the identity. A trade gives goods only
to agents that had one or nothing, so e does not grow. By Lemma stay of `paper/k3-simple`, a good wanted after a ring
or chain was wanted before, by the same agent. ∎

So (a) says e + ν ≤ 2n − m: the agents holding nothing and the wanted goods fit in the slack of L7.

**Lemma 3 (self-service).** Let o be an owner such that no x ∈ E_o has {b_x, c_x} ⊆ base(o). This is automatic when
o is a terminal, since base(o) has at most one good. If every exposed agent of o is a terminal, (b) holds for o. More
generally, (b) holds when h(E_o ∩ F) ≤ |T ∖ E_o| − [o ∈ T]. In particular every *satisfied* state (every agent holds
its top or its pair) passes Lemma 1.

*Proof.* By the hypothesis, π_x ≠ ∅ for every x ∈ E_o. An exposed terminal x takes a good of π_x in its own slot.
So H can be one good per exposed terminal plus a hitting set of the frozen exposed agents, placed in the other
terminals: |H| ≤ |E_o ∩ T| + h(E_o ∩ F) ≤ |T| − [o ∈ T]. In a satisfied state every agent outside U is a terminal, so
a terminal owner works; if T = ∅, every pair holder has E_o = ∅. ∎

*Correction* (referee, `k4/referee/k3_oc1.md` §3 on `claude/k4-referee`). An earlier version stated Lemma 3 without
the hypothesis on base(o), and that form is false for a pair-holder owner. Smallest case: two agents with the same
ranking a > b > c and one dead good d; x holds {a}, o holds {b, c}, J = {d}. Then x is an exposed terminal, but o is
no owner, since X_o = {b, c, d} gives x the value b + c > a. The state still completes by (a). No later claim used
the defect: the owners of §6 and Theorem B\* are terminals, or hold a pair that no exposed agent shares (B\* (iii)).

## 3. Theorem R1C: OC₁ for R1-compatible orders (proved)

The *need order* of a draft puts every agent after the holders of the goods it ranks above its pick. Every linear
extension of it gives the same picks: an agent finds the goods it prefers taken, its pick free, and every free good
it values ranked below its pick, since junk is (LB⁺ (I2)) and so are later agents' picks. Call the draft
*R1-compatible* if some linear extension respects R1 priority: whenever an unprocessed agent has lost a good, the
next agent is such an agent. Then the draft is the Phase 1 output of an LB⁺ run (`proofs/lb_last_step.md` §1, insertion choices
included).

**Scope.** Theorem R1C, like the rest of this note unless said otherwise, is about DE's core case. Every agent values
exactly three goods a > b > c with a < b + c, and dead goods are allowed. Agents with fewer goods, and top-heavy
agents, are outside it. Wherever R1C is cited, read "OC₁ at k = 3, in DE's core case, for every R1-compatible order".

**Theorem R1C.** If the draft of π is R1-compatible, then after LB's upgrades either it has a one-absorber completion
or it has one after a single DE trade (LB⁺'s rotation: a DE chain, or a ring with one pair arrow, from k* to r).

*Proof.* Run LB⁺ with every cap equal to one (terminals with no pick included). Lemma 1 of
`proofs/lb_last_step.md` holds for any caps not above LB's. Theorem A's count uses only that each terminal τ(x) has
cap ≥ 1 and that S − cap(r) is the number of slots outside r. Theorem B's count (g) uses only cap′ ≥ 1 for the same
terminals. With unit caps the output gives every agent but the owner at most one junk good (an upgraded agent's c is
its one good), so it is a one-absorber completion. LB⁺'s rotation moves every agent of a need chain up one step and gives k* its pair
from J ∪ {Y_r}: a DE chain when {b_k, c_k} ⊆ J, a ring with the pair arrow r → k* otherwise. ∎

Check (`lbplus_unit.py` on every hard start of the logs above): the R1-compatible ones (4,608) end in "no owner" after
upgrades (1,046), owner r (434), or Theorem B's rotation, which completes from every chain (3,128). The other 13,961 hard
starts are not R1-compatible (`r1compat.py`).

**Theorem B\* (LB⁺'s rotation for every order; proved).** Take any order and its draft after LB's maximal upgrades,
so (UT) holds. Write h(·) for least hitting sets and π_x = {b_x, c_x} ∩ J. Let t be a terminal with h(E_t) = |T|,
deficit one for owner t, and let k ∈ E_t satisfy:
- (i) k is frozen;
- (ii) a need chain k = x₀, x₁, …, x_s = t exists (s ≥ 1);
- (iii) no other agent of E_t has the pair {b_k, c_k};
- (iv) the sets {b_x, c_x} ∖ {b_k, c_k}, for x ∈ E_t ∖ {k}, have a hitting set of at most |T| − 1 goods.

Rotate along the chain: each x_i (i ≥ 1) takes Y_{x_{i−1}}, k takes b_k and c_k, and t's pick (if any) is released.
The result has a one-absorber completion: with no owner if |J′| ≤ |T′|, with owner k otherwise. It is Lemma 1 applied
to the upgraded state, and each upgraded agent's c is its one junk good. The rotation is one DE trade from the draft
itself: a DE chain if {b_k, c_k} ⊆ J, a ring with the one pair arrow t → k otherwise. Its agents are not upgraded, and
{b_k, c_k} contains no upgraded agent's c, since that c is not in W.

*Proof.* `proofs/lb_last_step.md` §5 with r replaced by t. Blocks are never used.
- *(a)–(c): the result P′ is a valid pre-allocation.* These steps use only that {b_k, c_k} ⊆ W := J ∪ {Y_t}
  (k ∈ E_t), that the chain is a need chain, and that Y_t is wanted by nobody (t is a terminal).
- *(d′): every terminal other than t keeps its slot.* It is off the chain, since x₀, …, x_{s−1} are frozen. Its pick
  is not in NA ⊇ NA′.
- *(e): E′_k ⊆ E_t ∖ {k}.*
  - An off-chain agent with its pair inside J′ ∪ {b_k, c_k} = W is in E_t.
  - A middle agent's old pick is held by its successor, so it is not in W.
  - t itself is excluded exactly as r is there: by (I1) if t held c_t or nothing, and by (UT) if it held b_t. Neither
    uses blocks.
- *(f): no x ∈ E′_k has {b_x, c_x} = {b_k, c_k}.* This is (iii).
- *(g): owner k works.* For x ∈ E′_k, π′_x = {b_x, c_x} ∖ {b_k, c_k}, because {b_x, c_x} ⊆ W and J′ = W ∖ {b_k, c_k}.
  By (iv) these sets have a hitting set H′ with |H′| ≤ |T| − 1 ≤ |T′| (by (d′)) = |T′| − cap′(k). Lemma 1 applies to
  owner k when |J′| > |T′|. ∎

LB⁺'s Theorem B is the case of t = r with LB⁺'s bad case, where (iv) follows from Theorem A's distinct terminals.
`thm_bstar.py` (`thm_bstar.log`) runs on the exact-hard drafts of the n ≤ 6 logs: B\* applies to 8,075 of 14,138,
and all 11,501 of its rotations complete under the exact test.

The other 6,063 drafts are of two kinds.
- 1,864 have least deficit 2 for every terminal owner.
- In the rest, every deficit-one owner fails (iv): one rotation leaves the hitting number unchanged (3,228), because
  exposed agents share junk goods. For an owner other than k those shared goods are dead, since they sit in k's
  pair. But owner k keeps them, and Theorem B\*'s count uses owner k.

So the open cases need an owner other than the rotated agent, or a rotation through several terminals (DE's worked
example).

## 4. The candidate theorem OT for every order

**Score**: an agent scores 4, 3, 2, 1, 0 for its pair, a, b, c, nothing (DE's score). By the counts of Lemma 2, the
total score is 3n + |U| − Σ_i |N_i|, where N_i is the set of goods agent i wants.

**Theorem candidate OT.** From the draft of every order there is a one-absorber completion, or there is one after a
single DE trade (OT₁), and in fact after every DE trade of least ω (OT-ω).
- On the ledger's cores (every core with n ≤ 5, every n = 6, m ≥ 10 core, every profile and order), two stronger
  forms hold on all data:
  - every least-ω trade passes Lemma 1;
  - every max-score trade has a one-absorber completion.
- Outside the cores both stronger forms fail (`attempts/k4-k3oc1-selection-rules.md`):
  - no max-score trade repairs on an n = 6, m = 10 instance with an agent holding two private goods;
  - a least-ω trade fails Lemma 1 when there are two dead goods.

- The same holds with "the least ω after the trade" (equivalently the least e + ν), with "most terminals afterwards",
  and with "the largest sum of squared score gains" (`rules2.py` on the hard starts of n = 4, 5 and the n = 6 sample:
  17,751 of 17,751 each).
- The max-score result always has an acyclic want graph (`maxprops.py`, 17,224 of 17,224), and Lemma 1 holds there
  with no owner in most cases (ω ≤ 0: 9,784 of 10,688 at n = 5; `after.py`).
- Shapes of the repairing trades at n = 5 (`structure.py`): chains, rings with one pair arrow, and rings with two
  pair arrows. DE's worked example (n = 6) has no trade but rings with two pair arrows. On the trees of Appendix C the
  max-score ring passes through all k roots.
- What a proof must use (`deficit.py`, `r1compat.py`):
  - At hard drafts the least deficit h(o) − (|T| − 1) over terminal owners is 1 or 2 at n = 5.
  - |T| = 1 on every hard draft at n = 4 and on 4,120 of 7,656 hard drafts at n = 5, m = 9.

## 5. Proof routes that fail (data in the logs named)

- *Pareto-maximal trades.* "Every DE trade whose score vector no other trade dominates repairs" fails on 416 of
  10,688 hard n = 5 starts, even without the degenerate chains in which a free x drops its top. Example
  (`pareto_rule.py`):
  - agents 0: 1 > 0 > 6, 1: 2 > 0 > 7, 2: 3 > 4 > 8, 3: 1 > 5 > 2, 4: 3 > 5 > 4; picks (1, 2, 3, –, 5); junk {0, 4, 6, 7, 8}.
  - The chain (1, 3) gives agent 3 its third good, keeps agent 4's good wanted, and fails.
  - The chains (0, 3) and (2, 4, 3) score more and repair.
  - Inclusion-maximal trades fail on the same starts.
- *Merging.* "If a trade's result fails, some trade from the result composes with it into one DE trade from the draft"
  holds at n = 4 (240 of 240) but fails at n = 5 (`merge.py`). In the example above the repairing trade (2, 4, 3) is
  disjoint from the failing one. So the extremal argument cannot be a plain splice: it must compare the score sum (or ω)
  of disjoint trades.
- *Max score with Lemma 1* (`oc1_fast.py` on the n = 6, m ≤ 9 cores; `maxfail_post.py`).
  - **The example.** Agents 0: 0 > 1 > 6, 1: 3 > 1 > 7, 2: 4 > 2 > 8, 3: 0 > 4 > 5, 4: 3 > 5 > 2, 5: 3 > 4 > 5,
    m = 9. The draft (0, 3, 4, –, 5, –) is hard.
  - **What fails.** The max-score trade, the DE chain (1, 5), leaves the junk {2, 6, 8} with only one terminal, the
    empty-handed agent 3.
  - **What works.** The exact test completes it: pair holder 1 takes good 2, which puts no exposed pair in its
    bundle, and agent 3 owns {6, 8}. The least-ω trade (0, 3) passes Lemma 1 itself.
  - **On all such drafts:** every max-score trade passes the exact test, and every least-ω trade passes Lemma 1
    (912 of 912 on the first 225 of the 2,856 cores with n = 6, m ≤ 9, every profile; `maxfail_post_small6_partial.log`,
    `oc1_fast_small6_partial.*`). A rerun checking both rules on every hard draft is in progress.
- *Lexicographic rules.* Maximizing the score vector read from the last agent backwards fails on 293 of 17,751 hard
  starts; from the first agent, 884 (`rules2.py`).
- *Naive induction on the last agent* (`induct_last.py`). If I − ℓ's draft passes Lemma 1, the repairing trade of I
  always passes through ℓ (7,092 of 7,092 at n = 5). But if I − ℓ's draft is hard, its repairing trades repair I's
  draft on only 1,304 of 3,596 n = 5 starts (0 of 2,512 at n = 4). So adding ℓ changes the trade, not just extends
  the completion.
- *One terminal* (|T| = 1, `k3_oc1.md` §4). The max-score trade always starts at an agent exposed for ℓ and passes
  through ℓ: LB⁺'s Theorem B shape. After it, Lemma 1 holds with no owner in 4,316 of 4,904 n = 5 cases, and with an
  owner in the other 588.
- *DE's own finishing test* instead of Lemma 1 fails: 16 n = 3 and 556 n = 4 starts have no DE trade after which DE can
  finish (`oc1_de.py`). DE's test asks for a blocker's good to be moved even when the finisher ends with only two goods.

## 6. The gap

Theorem R1C covers the drafts in which needs stay inside LB⁺'s blocks. In general, define blocks by the *fresh* agents
(all three goods free at their turn; they take their tops). Exposed agents for the last agent are still fresh, hence
still leaders (LB⁺ (A3) holds for every order). What fails is (B2): an agent can want a good picked in an earlier block
(a *cross need*, exactly an R1 violation). Then the need chains of several exposed leaders can end at the same terminal,
and Theorem A's count of distinct terminals τ(x) breaks for more than one leader.

LB⁺'s bad case has one leader without a terminal of its own, repaired by one rotation. Here several can lack one. The
data say a single DE trade still repairs. It rotates some exposed agents into their pairs and gives their needers goods
they rank above the other exposed agents' tops, which releases those agents (they become terminals that serve
themselves, Lemma 3). In DE's worked example one ring with two pair arrows does both.

A proof of OT must therefore show that the best trade (largest score, or least ω) realizes all these releases at
once.

## 7. Lifting to k = 4

The k = 3 facts used, and their k = 4 replacements (agents value up to four goods a > b > c > d; `k4/k3oc1/lift4.py`
on the k = 4 data, every order, n ≤ 5):

| k = 3 fact | used in | k = 4 replacement | holds at k = 4? |
|---|---|---|---|
| a bundle of ≤ 2 unwanted goods threatens nobody (Theorem 1′) | Lemma 1 | same, with "wanted" = valued above one's own base | yes (`k4/sdc.md` §30 (F2′)) |
| the owner's bundle threatens only top-holders, through their pair {b, c} | Lemma 1, exposure | danger sets: subsets of R_i ∖ B_i of up to three goods worth more than B_i; b-holders are threatened by {c, d} | the notion lifts; the sets are bigger |
| an exposed terminal serves itself with one good of its pair | Lemma 3 | an exposed terminal takes its best junk good: then the rest of R_x in the owner's bundle is two goods below a and that good | yes |
| a trade never raises the set of wanted goods (Lemma stay) | Lemma 2 | same: values only rise along an improving chain | yes |
| blockers of a terminal o all share y_o, so one pair arrow out of o kills every one of them for every other owner | §6 | a blocker can have several danger sets, some inside J | no: one move need not kill a blocker |
| **(DE-a)** only an agent giving up its top gains from junk (a b-holder ranks every junk good below b, and only c is below b) | DE trades, OT | b-holders gain from {c, d} when c + d > b | **no: first failure, nsw-local-n3m5** |
| **(DE-b)** the repairing trade keeps every wanted good alone | DE trades, Lemma 1 after the trade | compensable validity: a wanted good may sit in a bundle if its wanters are compensated by junk | **no: T3**; the compensable form holds on all data |
| max-score / least-ω DE trade repairs | OT | max rank-score chain in the repaired class | no (162 of 194 screen picks; also false at k = 3 outside DE trades) |

Counts (hard starts = starts whose picks have no one-absorber completion; not repaired by one chain of the class):

| class of chains | special (69 hard) | screen (662) | suite (797) | 2,000 random n ≤ 3 core profiles (345) | 300 random n = 4 core profiles (195) |
|---|---|---|---|---|---|
| every improving chain (OC₁) | 0 | 0 | 0 | | |
| (DE-a) and (DE-b) | 1 | 66 | 45 | 15 | 2 |
| (DE-a) and compensable validity | 0 | 57 | 36 | 15 | |
| t ≥ 1, any agent may take junk, compensable validity | 0 | 0 | 0 | 0 | 0 |

So the repaired structure for k = 4 is a single improving chain in which every agent gives its base to the next one
and may add junk, followed by a one-absorber completion in which an agent whose wanted good sits in a bundle of two or
more goods is compensated by one junk good. At k = 3 these compensations are exactly LB's upgrades, and the data say OT
never needs them after a DE trade. The k = 4 completion problem therefore has two kinds of one-good slots: the
terminals' slots, and the compensation slots of agents that want a good in a two-good bundle. A k = 4 proof must count
both kinds. This is the "service count" that `k4/sdc.md` §30 names as the missing ingredient.

## 8. The open case: what the repairing trade does there

Outside R1C and B\* (`thm_bstar.py`; the n = 5 and sampled n = 6 logs), the drafts with least deficit 2 have one
terminal in all but one case. The max-score trade there is a DE chain (1,201 cases) or a ring with one pair arrow
(190), and afterwards the junk fits the terminals' slots (no owner), once LB's upgrades are made. A typical case:
- **The draft.** Agents 0: 0 > 1 > 6, 1: 0 > 2 > 7, 2: 3 > 4 > 8, 3: 1 > 5 > 2, 4: 3 > 5 > 4. Order (1, 0, 2, 3, 4)
  gives the picks (1, 0, 3, 5, 4) and junk {2, 6, 7, 8}. The only terminal is agent 4, which holds its third good 4.
- **The exposure.** Agents 1 (pair {2, 7} in the junk) and 2 (pair {4, 8}, with 4 agent 4's pick) are exposed for
  agent 4, so h = 2 against no slot: deficit 2.
- **The chain (1, 0, 3, 4).**
  - Agent 1 takes {2, 7}.
  - Agents 0 and 3 each receive their top: 0 from agent 1, and 1 from agent 0.
  - Agent 4 receives its b = 5, and its old pick 4, its c, becomes junk.
  - LB's upgrade gives agent 4 its pair {5, 4}, so agent 4 wants nothing, and agent 2, frozen only by agent 4, is
    released.
- **The result.** Junk {6, 8} against three terminals.

The trade works by *releasing*: every needer of an exposed agent's top is moved above it, here by giving it its top or
its pair. One rotation of a single exposed agent (B\*) only removes that agent. A proof of OT has to show that the
best single trade releases enough of the others. The binary trees of Appendix C (deficit up to 7 at n = 30) show how
many releases one ring can be forced to make.

## 9. OC₁ in DE's general core case: a counterexample, and the rescue

The ledger's cores are peeled (PROMPT.md L2–L3), and OC₁ holds on every one tested. DE's general core case allows any
number of private goods and dead goods.
- At n ≤ 4 (`oc1_general.py`: all 16 and 93 hypergraph classes, 0–2 dead goods, every profile and order), OT₁ and OT-ω
  hold.
- At n = 5 with no dead goods, or with one (all 652 classes, every profile and order; `oc1_general_5_dead*`):
  - One class fails OT₁ (shown below). Glued chains repair all 288 of its hard drafts.
  - With one dead good, one more class fails "every least-ω trade", though some least-ω trade repairs
    (`attempts/k4-k3oc1-selection-rules.md` example 4).
  - The class that fails OT₁ is the instance of `attempts/k4-k3oc1-oc1-counterexample.md`:

| agent | 0 | 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|
| goods a > b > c | 0 > 1 > 2 | 0 > 1 > 2 | 0 > 3 > 4 | 1 > 5 > 6 | 2 > 7 > 8 |

From the order (2, 3, 4, 0, 1) the picks (–, –, 0, 1, 2) leave the six private goods of agents 2, 3, 4 as junk and two
empty-handed terminals. Each chain repairs one of agents 2, 3, 4. The other two each need an absorber. Two chains
work.
- With the free completion (several absorbers), one chain works.
- With a chain allowed to pass through an empty-handed agent (agent 1 above passes on its empty base, so agent 4
  takes only junk), one chain works. This is two DE chains glued at an empty-handed agent.

**The family behind it** (`glue_family.py`, `glue_family.log`). q agents each hold a top t_j with a private pair, and
p ≥ 2 empty-handed agents value only tops; the picks are hard whenever q ≥ p.
- Plain chains fail when the empty-handed agents want the same tops: (p, q) = (2, 3) with identical sets, and
  (3, 4) with cyclic sets.
- They work when some empty-handed agent can be given its top while releasing others.
- A glued chain repaired every member tested, up to (p, q) = (3, 6).

For TARGET₄ the right statement is about cores, where peeling has removed such agents. OC₁ as literally written in
§29 ("every instance") needs either the core restriction or the glued chains. The k = 4 data of §29 are cores or near
it, so this never showed there. Note the role of the absorber count: the obstruction is two independent groups of
exposed private pairs, each needing its own absorber.

## 10. OC₁ at maximum-matching starts (OC₁^max) at k = 3: one move everywhere tested

Requested by the coordinator after OC₁^max was refuted at k = 4, n = 4 (`k4/sdc.md` §31 on `claude/kind-lamport-y8fdme`).
`oc1_max.py` keeps the drafts whose picks match ν agents, ν the maximum matching size. It tests the one-absorber
completion with `lb2` (exact on DE states), then one DE trade, then one improving move of §29 under the official rule
(a chain never passes an empty-handed agent; exact completion). It also tests every least-ω DE trade. Logs:
`results/k4_k3oc1/oc1_max_*.log`.

| data (every profile, every order) | maximum-matching drafts (perfect + not perfect) | hard | one DE trade fails | a least-ω DE trade fails | more than one move |
|---|---|---|---|---|---|
| cores n = 3 | 2,922 + 0 | 128 | 0 | 0 | 0 |
| cores n = 4 | 132,520 + 14,112 | 3,196 | 0 | 0 | 0 |
| cores n = 5, m = 9 | 266,508 + 0 | 4,272 | 0 | 0 | 0 |
| cores n = 5, m ≤ 8 | 7,707,562 + 833,664 | 101,380 | 0 | 0 | 0 |
| cores n = 6, m ∈ {10, 11} | 35,353,596 + 0 | 338,916 | 0 | 0 | 0 |
| DE's general core case n ≤ 4 (all 16 + 93 classes), 0–2 dead goods | | 25,516 | 0 | 0 | 0 |
| DE's general core case n = 5 (all 652 classes), 0–1 dead goods | | 451,512 | 0 | 0 | 0 |

So at k = 3 no maximum-matching start tested needs more than one move. In fact one DE trade always suffices, and
every least-ω DE trade does. Every hard maximum-matching draft is a perfect start (every agent picks). Both k = 3
failures of §9 and of `attempts/k4-k3oc1-selection-rules.md` (example 4) have picks matching ν − 2 agents. This is
the signature §31 reports for the k = 4 every-order counterexamples.

**Where k = 4 differs.** In both k = 4 counterexamples to OC₁^max, the two dangerous agents that share a junk danger
pair include a b-holder:
- instance 1: agent 3 holds its top with danger pair {3, 4}, and agent 2 holds its b with the same danger pair;
- instance 2: agents 1 and 2 both hold their b, with danger pair {1, 3}.

At k = 3 a b-holder has no junk danger set: its only good below b is c. Two top-holders sharing a junk pair at k = 3
are killed together by one DE chain, since the pair then sits in a pair holder's bundle (§6). So the k = 4 mechanism
is exactly the first k = 3 fact that fails at k = 4, **(DE-a)** of §7: at k = 4 a b-holder can be endangered by, and
gain from, {c, d} when c + d > b.

## 11. Reduction of maximum-matching starts to perfect starts (k = 3, DE's language)

Joint work with the kgen-n3 session, at the coordinator's request; this section is the reduction, and the case
analysis of perfect starts is kgen-n3's part. Setting: DE's core case (every agent values exactly three goods
a > b > c, strictly balanced; dead goods allowed), an order π whose draft Y is a *maximum-matching start*: its picks
match ν agents, the maximum matching size of the bipartite graph agents–relevant goods.

**Notation.**
- U is the set of pickless agents.
- An *alternating path* from u ∈ U is u, g₁, a₁, g₂, a₂, … with g_i ∈ R_{a_{i−1}} (a₀ = u) and g_i = Y_{a_i}.
- S is the set of agents on such paths (other than U), and T the rest. J is the junk.

**Lemma MAX₃ (`k4/sdc.md` §31, Hall session).** No agent of U ∪ S values a junk good. Hence:
- (i) every good that an agent of U ∪ S values is the pick of an agent of S;
- (ii) at the draft no agent of S is exposed for any owner (Lemma 1), since an exposed agent has a good of its pair in J;
- (iii) S is closed: the holder of a good valued by an agent of U ∪ S is in S.

*Proof.* An agent u ∈ U values no junk good, since at u's turn every junk good was free. If a ∈ S valued g ∈ J,
take an alternating path u, g₁, a₁, …, g_s, a_s = a. Then (u ← g₁, a₁ ← g₂, …, a ← g) is an augmenting path, so the
matching is not maximum. (i) follows because a valued good is not junk, so it is a pick, of some agent b, and b is
reachable. (ii) and (iii) follow from (i). ∎

**Lemma RED₃ (`k4/sdc.md` §31, coordinator; checked here in DE's terms).** Let I′ have the agents T ∪ U and the goods
{Y_t : t ∈ T} ∪ J, with values restricted. The agents of U become *null agents*, valuing nothing, by (i).
1. Y′ = (Y_t)_{t∈T}, with nothing for U, is the draft of π restricted to I′. At t's turn, Y_t is still free and still
   t's favourite among the goods of I′ that are free.
2. Every move of I′ (an improving chain of §29) is a move of I: the values agree on I′'s goods.
3. Every one-absorber EFX₀ completion X′ of I′, at Y′ or after a move, extends to one of I, by giving each s ∈ S
   the singleton {Y_s}:
   - a singleton is never envied;
   - agents of U ∪ S value nothing in the bundles of T ∪ U, by (i);
   - a T agent compares bundles of T ∪ U with the same values in I and in I′;
   - the absorber count is unchanged.

So OC₁ at Y follows from OC₁ at the perfect start Y′ of I′: every agent of I′ that values a good holds a pick.

**The class after the reduction.** A T agent that values a pick of S keeps only its other goods in I′. So I′ is an
instance in which every agent values at most three goods, strictly balanced when it values three, plus null agents.
DE's machinery covers it with two changes.
- *Agents with one or two goods are never exposed.* In Theorem 1′'s case analysis, an agent with R_i = {a, b} that
  holds a sees at most b in another bundle; one that holds b, or nothing, sees nothing, since its wanted goods are
  held alone. So Lemma 1 and Theorem 1′ hold verbatim, with exposure only for three-good top-holders.
- *Null agents are terminals.* They hold nothing, want nothing, are never threatened, and as owners they fall under
  Lemma 1 (b) with E_o = N₀ (the top-holders whose pairs are junk), or (c).

So the statement the case analysis has to prove is:

> **(P) Perfect starts.** In every instance where each agent values at most three goods (strictly balanced when
> three), null agents allowed, at the draft of every order in which every non-null agent picks, a one-absorber
> completion exists, or one improving move gives one.

(P) with no small and no null agents is the perfect-start part of OT₁, which holds on all data (§10).

**Non-perfect hard maximum-matching starts exist** (`max_gadget.py`). In the data of §10 every hard
maximum-matching draft was perfect, but that is a small-n effect. Take any hard perfect draft I₀ and add:
- three agents s₁, s₂, s₃ valuing a new cycle g₁, g₂, g₃ (rankings rotated), placed last in the order;
- a pickless agent u valuing {g₁, g₂, g₃}.

The picks remain a maximum matching, and S = {s₁, s₂, s₃} values no junk. Of 3,000 hard perfect n = 5 drafts, 384
stay hard with the gadget (n = 9), and the null agent u's extra slot does not suffice there. One DE trade repairs
every one of the 384.

**(P) tested on its whole class** (`perfect_small.py`; agents valuing one, two or three goods, all hypergraph classes,
every ranking, every order's draft, brute-force one-absorber completion, every improving move under the official
rule). Null agents are left out, since a null agent can always receive nothing, so instances without them are the
hardest case.

| n | classes | dead goods | perfect drafts | hard | one move fails |
|---|---|---|---|---|---|
| 3 | 97 | 0 | 8,732 | 294 | 0 |
| 3 | 97 | 1 | 8,732 | 510 | 0 |
| 4 | 738 | 0 | 434,113 | 8,064 | 0 |
| 4 | 738 | 1 | 434,113 | 11,840 | 0 |

(The n = 5 run, 6,911 classes, was stopped unfinished to free CPU for the gap scan of §12.)

**Toward (b): how the least-ω trade repairs one-terminal perfect drafts** (`mechanism.py`). Take the 2,847 hard
perfect drafts with T = {ℓ} after LB's upgrades and |E_ℓ| ≥ 2 (n ≤ 6 logs). After the least-ω trade, Lemma 1's
no-owner case always holds after upgrades: the junk fits the terminals' slots.

Since e = 0 at a perfect start, ω = m − 2n + ν, and ν = n − 1 with one terminal. So the trade must make |J| − 1 wanted
goods unwanted. The other exposed agents end up as follows:
- *killed:* a good of their pair now sits in the new pair holder's bundle;
- *released:* all their wanters were lifted above their top;
- *left exposed:* 374 of the drafts, where the released agents supply the slots.

A proof of (b) for one terminal is therefore a counting statement: some single trade releases at least |J| − 1
wanted goods, counting the releases from LB's upgrades of the chain's end.

A natural rule for the one-terminal case, "rotate so that ℓ ends with its top", is not enough (`top_to_l.py`,
`top_to_l.log`; 6,121 one-terminal hard perfect drafts):
- no such rotation exists on 1,173 of them;
- where one exists, every one repairs on 4,947 drafts, and none does on 1.

So the release count must be run over all rotations, as ω does, not through a fixed target for ℓ.

**Status of the joint statement.**
- The reduction (Lemmas MAX₃, RED₃) is written and proved.
- (P) holds on its whole class for n ≤ 4, and on DE's core case wherever §10 tested it.
- (P) itself, OC₁ at perfect starts for every n, is open. It is the content of the case analysis (kgen-n3) and of the
  release count (b).

## 12. The gap of R1C ∪ B\* at perfect starts (joint with kgen-n3)

The split with kgen-n3 (`claude/kgen-n3`, PR #97) gives kgen-n3 the one-terminal gap (its Theorem T1); this session
was to show that two or more terminals never land in the gap. **That claim is false at n = 6.**
`gap_scan.py` lists every hard perfect draft (exact test) that neither Theorem R1C (R1-compatible) nor Theorem B\*
covers. Lists: `results/k4_k3oc1/gap_*.gap.gz`, one GAP line per draft, giving the instance, an order, the picks,
|T| after LB's upgrades, and |E_t| per terminal.

| cores, every profile and order | hard perfect | covered by R1C | by B\* (not R1C) | gap, \|T\| = 1 | gap, \|T\| = 2 |
|---|---|---|---|---|---|
| n = 4 | 3,196 | 1,612 | 544 | 1,040 | 0 |
| n = 5, m = 9 | 4,272 | 584 | 1,944 | 1,744 | 0 |
| n = 5, m ≤ 8 | 101,380 | 45,740 | 31,872 | 23,768 | 0 |
| n = 6, m ∈ {10, 11} | 338,916 | 44,820 | 187,664 | 96,128 | **10,304** |

**One-terminal gap (kgen-n3's part).** With T = {t}, B\* applies iff |E_t| = 1. This is kgen-n3's observation: (iv)
asks for a hitting set of size 0. At n = 6, |E_t| is 2 (77,568) or 3 (18,560). kgen-n3's first candidate rule, the
rotation into t that gives t its best reachable good, fails in its every-form on an n = 6, m = 10 core:
- **The instance.** Agents 0: 0>1>7, 1: 0>2>8, 2: 4>3>9, 3: 0>6>5, 4: 2>3>1, 5: 4>5>6. Order (3,1,5,2,4,0), T = {0},
  and E_0 = {3, 5} with the same junk pair {5, 6}.
- **The failing chain.** (3, 0) gives agent 0 its top, but no one-absorber completion exists (exhaustive search).
- **The repairing chains.** (3,1,4,0) and (5,2,4,0) give agent 0 its b, and they pass through agent 4, which then
  releases agents 1 and 2.

**Two-terminal gap.** |E_t| per terminal: (3,3) 3,456; (3,4) 2,880; (2,4) 1,856; (2,3) 768; (4,4) 704; (4,3) 576;
(2,2) 64. An example:
- **The instance.** Agents 0: 0>1>8, 1: 2>0>9, 2: 2>3>1, 3: 4>5>3, 4: 4>6>7, 5: 5>6>7. Order (0,1,4,5,3,2) gives the
  picks (0,2,1,3,4,5) and junk {6,7,8,9}. The terminals are 0, holding its top, and 2, holding its c.
- **The exposures.**
  - E_0 = {1, 4, 5}, with π = {9}, {6,7}, {6,7}; h = 2 = |T|.
  - E_2 = {0, 4, 5}, with π = {8}, {6,7}, {6,7}; h = 2.
- **Why B\* fails.**
  - For t = 0: agent 1's only need chain ends at the other terminal 2, and agents 4 and 5 share their pair, against
    (iii).
  - For t = 2: agents 4 and 5 share their pair again, and agent 0 is a terminal.
- **The repairs.**
  - The DE chain (4, 3, 2) has ω′ = −1 and needs no owner. Agent 4 takes {6, 7}, which kills agent 5 too, since the
    pair is now in agent 4's bundle. Agent 3 receives its top and is released, and agent 2 rises to its b.
  - The chain (5, 3, 2) and the ring (0, 1, 2), which has two pair arrows, also repair.

**Lemma 4 (shared pairs die together; proved).** If a DE trade gives k its pair {b_k, c_k}, then afterwards no agent
x with {b_x, c_x} ∩ {b_k, c_k} ≠ ∅ is exposed for any owner o ≠ k.

*Proof.* Exposure needs {b_x, c_x} ⊆ J′ ∪ base(o). But a good of {b_x, c_x} lies in k's bundle, which is neither junk
nor o's base. ∎

So B\*'s condition (iii) is needed only because B\* uses owner k. Both gaps need the same extension of B\*. Use an
owner other than k, or none, so that agents sharing k's pair die by Lemma 4. Then credit the agents the chain
releases: chain agents that receive their top, and t lifted above the goods it froze. The draft-level counting of B\*
does not see releases; that is where a proof must go.

**The two-terminal gap in detail** (`t2gap.py`, `tprime.py`; all 10,304 two-terminal gap drafts at n = 6).
- *Why B\* fails.* Mostly because an exposed blocker of t has its only need chains ending at the other terminal
  ("no chain to t"), or because removing one exposed agent leaves the hitting number at |T| (condition (iv)).
  Shared pairs (condition (iii)) occur in a minority. Exposed agents whose pairs lie in J can be rotated into
  either terminal, so "no chain to t" hits only blockers.
- *What repairs.* On every one of them, some rotation into a terminal repairs: a DE trade from an exposed agent of
  a terminal t into t, as in B\*.
  - On 9,504 of them some such rotation, followed by LB's upgrades, leaves |J′| ≤ |T′|, so no owner is needed. Every
    least-ω′ rotation into a terminal does this.
  - On the other 800 the completion after the rotation needs the exact test: a pair holder's slot, or an owner.

**Conjecture T′ (one move into a terminal).** At every hard perfect draft of a ledger core, some rotation from an
exposed agent k of a terminal t into t has a one-absorber completion. **Strong form T′_k:** with no owner, or with
owner k (B\*'s owner). (An earlier version also claimed the no-owner form for |T| = 1 and |E_t| ≥ 2, kgen-n3's T1′;
that is false, see below.)
- T′ holds on all data, with no failure (`tprime_*.log`):
  - every hard perfect draft of every core with n ≤ 5;
  - all 338,916 hard perfect drafts of the n = 6, m ∈ {10, 11} cores, every profile and order: 198,840 with
    |T| = 1 and 140,076 with |T| = 2.

  B\* is its deficit-one case with owner k.
- *Rings with two pair arrows are needed.* `tprime.py` counts as rotations every DE ring through t, including rings
  with more than one pair arrow. At n = 6, 64 two-terminal gap drafts have no rotation with a single pair arrow at
  all: the crossed configuration below. On every other draft one pair arrow suffices (Theorems R1C and B\* outside
  the gap, Conjecture T-E inside it).
- The no-owner form fails on 21,416 of the n = 6 drafts (14,484 with |T| = 1, 6,932 with |T| = 2), and also on these:
  - n = 4: 20 drafts, all with |T| = 1 and covered by B\*;
  - n = 5, m = 9: 132 with |T| = 1 and 96 with |T| = 2, covered by B\*;
  - the 800 two-terminal gap drafts above;
  - **360 of the 96,128 one-terminal gap drafts at n = 6** (`tprime_gap6_T1_*.log`, list `tprime_gap6_T1.fail.gz`).
    So kgen-n3's T1′ in its no-owner form is false.
- **The T1′ counterexample** (n = 6, m = 10 core). Agents 0: 1>0>7, 1: 0>2>8, 2: 1>3>9, 3: 0>5>4, 4: 6>2>4,
  5: 3>6>5. Order (0,1,2,4,5,3) gives the picks (1,0,3,4,6,5) and junk {2,7,8,9}; T = {3} (agent 3 holds its c,
  and nobody wants it), E_3 = {1, 4}.
  - Both rotations into 3, the chain (1, 3) and the ring (3, 4, 5), leave |J′| = 3 > |T′| = 2, even after upgrades.
  - Both complete with owner k (exhaustive search): after the chain, ({1}, {2,7,8}, {3}, {0,4}, {6}, {5,9}), with
    agent 1 the owner; after the ring, ({1}, {0}, {3}, {5,7}, {2,4,9}, {6,8}), with agent 4 the owner.
- **T′_k on the no-owner failures of the gap** (`owner_k.py`, `owner_k.log`): on all 1,160 of them (360 with
  |T| = 1, 800 with |T| = 2), some rotation completes with owner nobody or k, under the exact test with the owner
  restricted (`lbtest.lb2_owners`).
- **T′_k on every hard perfect draft** (`tprime_k.py`, `tprime_k_*.log`; the drafts needing owner k are in
  `tprime_k_needk.gz`). No failure on any of the following:
  - n = 4: 3,196 drafts, 20 of which need owner k;
  - n = 5: 105,652 drafts, 932 of which need owner k;
  - n = 6, m ∈ {10, 11}: all 338,916 drafts. With |T| = 1, 184,356 need no owner and 14,484 need owner k; with
    |T| = 2, 133,144 need no owner and 6,932 need owner k.

  Rotations here include rings with two pair arrows, and k is the agent that follows t on the ring.

### 12.1 Every earliest-wanter rotation completes (Conjecture T-E)

kgen-n3's **Rule E** (`kgen/n3.md` §15.6 on `claude/kgen-n3`): fix σ, here the order itself (a topological order of
the draft's need DAG). From a frozen agent x, the next receiver s(x) is the σ-earliest agent that wants Y_x. Since
wanters come later in σ, iterating s from x ends at a terminal end(x). A *valid Rule E rotation* is a frozen exposed
agent k with {b_k, c_k} ⊆ J ∪ {Y_e}, e = end(k) (so k ∈ E_e), rotated along its Rule E chain into e. kgen-n3's
Lemma G5 (checked here) says such a rotation keeps the want graph acyclic.

**The completion LE.** After the rotation and LB's maximal upgrades, give every terminal other than the owner at most
one junk good, and also k (*k's slot*): k may take a junk good g if {b_k, c_k, g} contains no pair of another
top-holder. The owner takes the rest. LE is Lemma 1 plus k's slot. It is sound by Theorem 1′'s case analysis. In a
valid state, a bundle of three goods threatens only a top-holder whose pair lies inside it, and k's bundle contains
no such pair.

**Conjecture T-E** (as first stated; **its every-k form is false at n = 7**, see below). At every hard perfect
draft in the gap of R1C ∪ B\*, every valid Rule E rotation has a completion LE with owner (N) nobody, (E) e, or
(K) k. If there is no valid Rule E rotation, some DE ring with several pair arrows completes.

**Conjecture T-E∃ (what survives).** At every hard perfect draft of a ledger core, *some* valid Rule E rotation has
a completion LE with owner nobody, e or k; or there is no valid Rule E rotation, and some DE ring with several pair
arrows completes.

Data (`t2k_e.py`; `te_gap_*.log`, `te_gap_fail_owners.log`): every gap draft with n ≤ 6, all rotations.

| gap drafts | valid rotations | LE with owner N or E | needs K (passes simple Lemma 1 with owner k) | no valid rotation |
|---|---|---|---|---|
| n = 4, \|T\| = 1: 1,040 | 2,080 | 2,080 | 0 | 0 |
| n = 5, m = 9, \|T\| = 1: 1,744 | 3,904 | 3,904 | 0 | 0 |
| n = 5, m ≤ 8, \|T\| = 1: 23,768 | 49,040 | 49,040 | 0 | 0 |
| n = 6, \|T\| = 1: 96,128 | 210,816 | 210,688 | 128 | 0 |
| n = 6, \|T\| = 2: 10,304 | 27,008 | 27,008 | 0 | 64 drafts |

- **No failure.** Every valid rotation completes, with no choice of k at all.
- **Owner e is LB⁺'s owner r.** It fails only on 128 one-terminal rotations at n = 6.
  - Example: agents 0: 0>1>7, 1: 2>0>8, 2: 3>4>9, 3: 5>0>1, 4: 2>3>6, 5: 6>5>4; m = 10; order (0,1,2,4,5,3);
    picks (0,2,3,1,6,5); T = {3}, E_3 = {0, 2}; k = 0, chain (0, 3).
  - Owner 3 fails because agent 1's pair {0, 8} becomes exposed once agent 3 holds a_k = 0.
  - Owner k sees no new exposure, E′_k ⊆ E_t ∖ {k} (B\* (e); kgen-n3's G3), and passes B\*'s count.
- **k's slot is needed.** Without it, N or E fails for some rotation on 4,476 one-terminal and 64 two-terminal
  drafts at n = 6.
- **Choice rules** (`t2k_rules.py`, `t2k_rules.log`), for the weaker test "simple Lemma 1, owner none or k". On the
  two-terminal gap at n = 6, "some k" holds on all 10,240 drafts that have a valid rotation; "every k" fails on
  4,224; the σ-first k fails on 2,752 and the σ-last k on 512; every least-ω′ k fails on 64. Under LE with owner e,
  every k works.
- **For every k, any owner** (`t2k_every.py`): all 27,008 two-terminal rotations complete. Length-zero rotations, an
  exposed terminal dropping its top, are not improving chains and do fail (1,856 of 4,160).

**Outside the gap, owners N, E and K do not suffice** (`te_rules.py source:certs:5`). On 16 two-terminal drafts
at n = 5, m = 9, all covered by R1C or B\*, some rotation completes only with the *other* terminal as owner.
- **The instance.** Agents 0: 1>0>5, 1: 0>2>6, 2: 1>3>7, 3: 2>4>8, 4: 0>3>4; m = 9. Order (2,3,4,0,1) gives the picks
  (5,6,1,2,0); T = {0, 1}, and k = 4 has its pair {3, 4} in J.
- **The failing rotation.** The Rule E chain (4, 0) gives agent 0 its b, which agent 1 wants, so e = 0 is frozen.
  Owner k fails: agents 2 and 3 are exposed with π′ = {7} and {8}, but T′ = {1}.
- **The completion.** Owner 1, the other terminal, takes all the junk: ({0}, {5,6,7,8}, {1}, {2}, {3,4}), verified
  by exhaustive search.
- **Any owner** (`te_any.py`): every valid Rule E rotation completes on every hard perfect draft with n = 4 (3,196)
  and n = 5, m = 9 (4,272).

**The every-k form fails at n = 7** (`attempts/k4-k3oc1-every-k.md`, independent replay
`attempts/k4_k3oc1_every_k.py`). A gap draft of an n = 7, m = 12 core has one terminal and four exposed agents.
The rotation of one of them, along its only chain (k, t), has no one-absorber completion with any owner, while the
other three rotations complete. This kills kgen-n3's T1-E and the every-k form of T-E. Random sample
(`te_sample.py`, `te_sample7_*.log`): 4,759 hard perfect drafts of the n = 7 cores (3,103 m = 11 cores × 40
profiles, 541 m = 12 cores × 200), every order.
- T′_k and T-E∃ have no failure.
- "Every rotation, any owner" fails on 8 drafts: 3 in the gap, all with |T| = 1, and 5 covered by B\*, with |T| = 2.
- "Every least-ω′ rotation, N/E/K" fails on 1 draft, covered by B\*.

**More samples** (`te_sample.py`; logs `te_sample7_11b_*`, `te_sample7_11c_*`, `te_sample7_12c`, `te_sample8_14`,
`te_sample_gen5_*`; classifications `te_sample*_classify.log`).
- **Data.**
  - n = 7 cores: two more batches, 4,460 and 8,141 hard perfect drafts.
  - n = 8, m = 14 cores: 1,232 cores × 100 profiles, 1,181 hard drafts (240 with |T| = 1, 787 with |T| = 2, 154 with
    |T| = 3).
  - DE's general core case n = 5 (652 classes, 0 or 1 dead good): 8,326 hard drafts, including 21 with |T| = 3.
- **T′_k and T-E∃ hold on all of them, with no failure.**
- The every-k form fails again, in the gap as well: at n = 7, on one- and two-terminal gap drafts.
- **A second crossed configuration**, at n = 7 (m = 11): a two-terminal gap draft with no valid single rotation.
  Agents 0: 0>7>5, 1: 1>8>5, 2: 3>9>6, 3: 4>6>10, 4: 1>0>6, 5: 3>4>2, 6: 2>5>6; order 0, …, 6.
- **kgen-n3's rule T1-P.** Rotate every k with {b_k, c_k} ⊆ J if some exists, else every k. On the 8,141-draft
  n = 7 batch:
  - it holds on all 5,487 one-terminal drafts;
  - on two terminals it fails on 82 drafts with owners N/E/K and on 12 with any owner, all covered by B\* (none in
    the gap).

**Statement (P)'s class** (§11: agents valuing one, two or three goods; the class the reduction RED₃ produces).
- **The exact test extends.** `lbtest` and `de_moves` now accept agents with one or two goods: they are never
  exposed, never threatened and never upgraded (§11). `mixed_check.py` compares `lb2` with the exhaustive
  one-absorber completion on every hypergraph class, every ranking and every perfect draft, and on the state after
  every DE trade from it. They agree everywhere: n = 3 (97 classes) and n = 4 (738 classes), with 0 or 1 dead good
  (`mixed_check_*.log`). The hard counts 294, 510, 8,064 and 11,840 match `perfect_small.py`.
- **T′_k is exhaustive on the whole class at n = 4** (`tprime_k_mixed_4_*.log`): 8,064 hard drafts with no dead good
  and 11,840 with one, no failure. Owner k is needed on 512 and 1,762 of them.
- **Sample at n = 5** (6,911 classes; 30 profiles each with no dead good, 15 with one; `te_sample_mixed5_*.log`):
  3,354 hard drafts. T′_k and T-E∃ have no failure; rule P fails on 2 two-terminal drafts. The exhaustive n = 5 run
  is in progress.

**The crossed configuration** (64 two-terminal gap drafts at n = 6, one hypergraph; `t2k_gap6_T2.log`,
`t2k_crossed64.log`).
- **The instance.** Agents 0: 2>0>6, 1: 3>0>7, 2: 4>1>8, 3: 5>1>9, 4: 4>5>0, 5: 2>3>1; order 0, …, 5; picks
  (2,3,4,5,0,1); J = {6,7,8,9}.
- **Terminals and exposures.** T = {4, 5}: each holds its c, and nobody wants it. E_4 = {0, 1}, whose pairs are
  {0,6} and {0,7}, both containing Y_4 = 0. E_5 = {2, 3}, with pairs {1,8} and {1,9}.
- **Why no single rotation works.** The tops of 0 and 1 are wanted only by 5, and those of 2 and 3 only by 4. So
  every chain from E_4 ends at 5, and every chain from E_5 ends at 4.
- **The only DE trades** are the 4 rings t₁ → k₁ → t₂ → k₂ → t₁ with two pair arrows. All complete, and the result
  is satisfied, e.g. the ring 4 → 0 → 5 → 2 → 4.

**Lemma 5 (release count; proved).** Let P be a perfect DE state (every agent holds a good or a pair). Let P′ be the
result of a DE trade with q pair-takers, followed by u upgrades: a chain counts its start, and a ring counts its pair
arrows. Then |J′| = |J| − q − u, |T′| = |T| − q − u + r and ω′ = ω − r, where r = ν − ν′ is the number of *released*
goods (wanted in P, not wanted in P′). So the no-owner test (a) holds after the trade iff r ≥ ω, and with k's slot,
when k's slot is usable, iff r ≥ ω − 1.

*Proof.* A chain's start takes two junk goods and its end releases one. Every other pair-taker takes one junk good,
and so does every upgrade. No agent ends with nothing, so e′ = e = 0, and Lemma 2 gives ω′ − ω = ν′ − ν (upgrades
leave ν unchanged, since an upgraded b is wanted by nobody, by (UT)). Then |T′| = |J′| − ω′. ∎

**Lemma 6 (hard states; proved).** In a hard DE state, every terminal t has a frozen exposed agent: E_t ∩ F ≠ ∅.

*Proof.* If E_t ∩ F = ∅, Lemma 3's general form holds for owner t: h(E_t ∩ F) = 0 ≤ |T ∖ E_t| − 1, since t ∈ T ∖ E_t.
Then Lemma 1 (b) completes. ∎

**Lemma 7 (the pointer walk; proved).** At a hard perfect draft, call a frozen exposed agent k *direct* if
{b_k, c_k} ⊆ J or end(k) = t, where k ∈ E_t. A direct k is a valid Rule E rotation. Suppose no frozen exposed agent
is direct. For each terminal t choose k_t ∈ E_t ∩ F (Lemma 6). Then f(t) := end(k_t) defines a map T → T with no
fixed point, and every cycle t₁, …, t_q of f (q ≥ 2) gives a cycle
t₁ → k_{t₁} ⇝ t₂ → k_{t₂} ⇝ … ⇝ t₁ of DE arrows with q pair arrows, whose Rule E segments are pairwise disjoint. It is a DE ring when the junk partners
j_i = {b_{k_{t_i}}, c_{k_{t_i}}} ∖ {Y_{t_i}} are distinct.

*Proof.* Since k_t is not direct, {b_k, c_k} ⊄ J. Since k ∈ E_t, {b_k, c_k} = {Y_t, j} with j ∈ J. The arrow
t → k_t is a pair arrow (t is free; k_t is a blocker of t with leftover j). Also end(k_t) ≠ t, so f has no fixed
point, and f has a cycle with q ≥ 2. Rule E is deterministic (s(x) depends only on x), so two Rule E chains that
share an agent end at the same terminal. On a cycle of f the images f(t_i) = t_{i+1} are distinct, so the segments
from k_{t_i} are pairwise disjoint and contain no t_j (their interior agents are frozen). ∎

In the crossed configuration this walk produces exactly the repairing rings. What remains of T-E is the count after
the rotation, Lemma 5's r against ω for (N), and B\*'s hitting count with |T′| for (E) and (K). That is the release
lemma shared with kgen-n3's T1.
