# One chain suffices at k = 3 (OC₁ at k = 3), and lifting it to k = 4

Workstream `proof/k4-k3-oc1` (PR #96). Code: `k4/k3oc1/`; logs: `results/k4_k3oc1/` (`*.log` summaries, `*.hard.gz`
the hard starts, one per line, readable by every analysis script). Notation: `paper/k3-simple` (Draft and Exchange, DE)
and `proofs/lb_last_step.md` (LB⁺); Conjecture OC₁ is `k4/sdc.md` §29. Everything called evidence is evidence only
(PROMPT.md §5 rule 3).

## Status (end of burst 2)

- **Proved.**
  - Lemma 1 (§2): soundness of the simple completion. LB⁺'s Lemma 1 with one slot per terminal, plus an empty-handed owner left with two goods.
  - Lemma 2 (§2): ω = (m − 2n) + e + ν, where e counts the agents holding nothing and ν the needed goods; no DE trade raises ω.
  - Lemma 3 (§2): self-service. Exposed terminals serve themselves; every satisfied state completes.
  - **Theorem R1C (§3): OC₁ at k = 3 for every order whose draft is R1-compatible**, i.e. whose need order has an R1-priority linear extension (this includes every R1-priority order). The proof is LB⁺ with every slot of size one. The rotation is one DE trade, and the completion has one absorber.
- **Conjectured (no counterexample in any test).** **Theorem candidate OT (§4).** At k = 3, from the draft of every order, the simple completion exists, or it exists after every DE trade (chain or ring) of largest total score. The same holds after every trade of least ω. OT implies OC₁ at k = 3.
  - Exhaustive tests: every connected core with 3 ≤ n ≤ 5 (339 hypergraphs), every ranking profile, every order: 273,724,272 starts. Also n = 4 with one dead good.
  - Exhaustive at n = 6, m ∈ {10, 11}: all 236 connected cores, every profile, and the drafts of all 720 orders, enumerated as distinct drafts (`oc1_fast.py`, `oc1_fast_certs6_*.log`): 11,010,816 profiles, 37,318,272 distinct drafts, 888,292 hard, no failure.
  - Sampled tests: n = 6 cores with m ≤ 9 (6 million starts), random instances with n ≤ 10, and the binary-tree family of `paper/k3-simple` Appendix C up to n = 45 (draft deficits up to 7, owner still needed after the trade).
  - OC₁ itself was also checked directly, with general chains and the exhaustive one-absorber completion, for every core with n ≤ 4 and with n = 5, m = 9.
  - On all data no max-score trade is a length-zero DE chain (a free x dropping its top for its pair, which is not a §29 chain; `k0check.py`). So the max-score trade is always an improving chain, and OT's data are OC₁ data.
- **Refuted proof routes** (§5):
  - "every Pareto-maximal trade works";
  - "every inclusion-maximal trade works";
  - "a failing trade merges with a later trade into one better trade". On n = 5 the repairing trade can be disjoint from the failing one.
  - the reverse-lexicographic rule.
  - The score sum and ω are the quantities that work.
- **Open.** A proof of OT, or of OC₁, for drafts that are not R1-compatible. These are most hard drafts: 13,961 of 18,569. The gap is precise (§6): exposed fresh agents whose need chains meet at one terminal through "cross needs" (R1 violations), and one trade must repair several of them at once (DE's worked example needs two pair arrows).
- **Lifting to k = 4 (§7, `attempts/k4-k3oc1-de-trades.md`).**
  - Lemma 1's soundness, Lemma 2's monotonicity and Lemma 3 lift; for Lemma 3, take the exposed terminal's best junk good.
  - The **first k = 3 fact that fails** is (DE-a): only an agent giving up its top gains from junk. At k = 4 a b-holder gains from {c, d} when c + d > b. On nsw-local-n3m5 (n = 3, m = 5) every repairing chain needs this.
  - The second is (DE-b), the trade keeping validity. On T3 (n = 3, m = 6) every repairing chain leaves a wanted good in a two-good bundle, and the completion compensates the wanter with junk.
  - **Repair:** chains with t ≥ 1 in which any agent may take junk, plus compensable validity. One such chain repairs every hard start of the special, screen and suite sets (n ≤ 5, every order).
  - The k = 3 selection rule does not lift: max score works on 162 of 194 screen picks. It already fails at k = 3 outside DE's narrow trades.
- **Next.** A proof of OT for one terminal (|T| = 1 covers all hard starts at n = 4 and 54% at n = 5), and the group-killing structure of §6 as a counting lemma.

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

("Hard": the picks fail the test. Columns 5–6 count hard starts.)

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

The exact test `lb2` adds three things, and the data need none of them for OT:
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

**Lemma 3 (self-service).** If every exposed agent of an owner o is a terminal, (b) holds for o; more generally (b)
holds when h(E_o ∩ F) ≤ |T ∖ E_o| − [o ∈ T]. In particular every *satisfied* state (every agent holds its top or its
pair) passes Lemma 1.

*Proof.* An exposed terminal x takes a good of π_x in its own slot; so H can be one good per exposed terminal plus a
hitting set of the frozen exposed agents, placed in the other terminals. In a satisfied state every agent outside U
is a terminal. ∎

## 3. Theorem R1C: OC₁ for R1-compatible orders (proved)

The *need order* of a draft puts every agent after the holders of the goods it ranks above its pick. Every linear
extension of it gives the same picks: an agent finds the goods it prefers taken, its pick free, and every free good
it values ranked below its pick, since junk is (LB⁺ (I2)) and so are later agents' picks. Call the draft
*R1-compatible* if some linear extension respects R1 priority: whenever an unprocessed agent has lost a good, the
next agent is such an agent. Then the draft is the Phase 1 output of an LB⁺ run (`proofs/lb_last_step.md` §1, insertion choices
included).

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

## 4. The candidate theorem OT for every order

**Score**: an agent scores 4, 3, 2, 1, 0 for its pair, a, b, c, nothing (DE's score). By the counts of Lemma 2, the
total score is 3n + |U| − Σ_i |N_i|, where N_i is the set of goods agent i wants.

**Theorem candidate OT.** From the draft of every order: Lemma 1 applies, or it applies after every DE trade of the
largest total score.

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
- *Lexicographic rules.* Maximizing the score vector read from the last agent backwards fails on 293 of 17,751 hard
  starts; from the first agent, 884 (`rules2.py`).
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

| class of chains | special (69 hard) | screen (662) | suite (797) |
|---|---|---|---|
| every improving chain (OC₁) | 0 | 0 | 0 |
| (DE-a) and (DE-b) | 1 | 66 | 45 |
| (DE-a) and compensable validity | 0 | 57 | 36 |
| t ≥ 1, any agent may take junk, compensable validity | 0 | 0 | 0 |

So the repaired structure for k = 4 is a single improving chain in which every agent gives its base to the next one
and may add junk, followed by a one-absorber completion in which an agent whose wanted good sits in a bundle of two or
more goods is compensated by one junk good. At k = 3 these compensations are exactly LB's upgrades, and the data say OT
never needs them after a DE trade. The k = 4 completion problem therefore has two kinds of one-good slots: the
terminals' slots, and the compensation slots of agents that want a good in a two-good bundle. A k = 4 proof must count
both kinds. This is the "service count" that `k4/sdc.md` §30 names as the missing ingredient.
