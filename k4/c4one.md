# Conjecture C₄¹: at most one 4-good agent

Workstream `proof/k4-c4one` (ledger row K4.C4.1, open item 18). Builds on `k4/c4.md` (PR #33, under review): notation,
Lemma E, Theorems A₄, B₄, B₄ʷ, A₄ᵀ, A₄⁺ and the conventions of its §1.1. Throughout, q is the unique 4-good agent.

## Status

- **C₄¹ as stated in `k4/c4.md` §6.2 is false** (§2). With at most one 4-good agent, one rotation is not enough at
  n = 5. It fails over every insertion sequence searched, even with index insertion, under every convention. The
  smallest case is n = 5, m = 9 (`attempts/k4-c4one-one-rotation.md`). **Two rotations suffice** on every certified
  core with one 4-good agent and n ≤ 5, for every insertion sequence (Conjecture C₄¹², evidence).
- **Route 2 fails as posed** (§4). The claim was: whenever no owner is valid, some rotation raises "slots minus forced
  goods". It fails first at n = 3 with two 4-good agents, and at n = 5 with one. Wherever two rotations are needed, the
  first one cannot raise it (`attempts/k4-c4one-potential.md`).
- **New: Theorem A₄⁺ holds for every owner** (§5, written proof, not yet reviewed). Any non-frozen owner with a base of
  at most one good, or an upgraded owner, is valid when the goods its exposed agents need kept out fit into the other
  slots. It is checked on the runs `lb4.c` makes with n ≤ 4 (≤ 2 four-good agents): 0 violations. It raises the share of
  runs proved from 94.5% to 97.6% (n = 4, one 4-good agent).
- **The insertion sequence is the lever** (§6). Take the theorems of `k4/c4.md` together with A₄⁺ for every owner.
  Then every strict profile of every certified core with one 4-good agent and n ≤ 5 has an insertion sequence whose
  run they prove.
  - It can even be taken among the sequences that minimize ω (**Conjecture C₄¹τ**).
  - It can also be taken as index order with the single insertion step that started q's block changed.
  - No fixed rule tested (index order, q first, q as late as possible, the lexicographically first least-ω sequence)
    achieves this.
  - A deterministic rule works: minimize (ω, q frozen, −pos(q)).
  - Behind it is a local **Exchange Lemma X**, which holds on every run tested (the runs `lb4.c` makes). When a run is
    not covered, changing one insertion step covers it or lowers that key.
  - **Lemma X plus the theorems imply C₄¹∃.** So on the data, C₄¹∃ reduces to Lemma X, which is open.
  - The stronger **Lemma X′** also holds on the data: from every uncovered run, one changed insertion step gives a
    covered run directly, with no key needed.
  - **n = 6:** on all 26,866 certified n = 6 cores with one 4-good agent (PR #26), for every strict profile, the
    index-order run is covered or one changed insertion step makes it covered. There are 0 exceptions in 5.47·10¹⁰
    profiles (`results/k4_c4one_n6.log`).
  - **A first proved piece: Lemma Ω** (§6, written proof, not yet reviewed). Take a need chain from a block's 3-good
    leader ℓ to a free agent x that holds its second good. Inserting x first in the block, then the chain backwards,
    realizes the rotation along the chain, and ℓ then upgrades. So ω drops by at least 1, under five side conditions.
    - This proves the (Tc) cases of Lemma X that satisfy those conditions: 80–100% of them at n ≤ 5.
    - The proof is for runs with P-steps in any order.
- **The existence form C₄¹∃** (§1) is open. It is what TARGET₄ needs for these instances.

## 1. Statements

**C₄¹∃ (existence form).** Consider every strict profile of every k = 4 core in which at most one agent has four
relevant goods. It has a valid pre-allocation with a completion that satisfies (OC₄), in which frozen agents hold
exactly their bases and only the owner's bundle has more than two goods.
- This is PR #35's `EFX.LB4R.TheoremC4exists` restricted to such cores.
- With Theorem 1′₄ (K4.LB4.S), K4.CORE (whose peeling never adds a 4-good agent) and K4.TIE, it gives **TARGET₄ for
  every instance in which at most one agent values four goods**.

**C₄¹ (LB₄ʳ form, `k4/c4.md` §6.2; false).** Take every run of Phase 1 on such a core, after envy-free upgrades. Then
either some free agent is a valid owner with its needs from its base, or one rotation gives a valid pre-allocation that
needs no owner or has a valid owner. The rotation may use any frozen k, any need chain, and any
O ⊆ R_k ∩ (J ∪ B_{x_t}).

**C₄¹² (evidence).** The same with "at most two nested rotations" in place of "one rotation". The owner's needs come
from its bundle, and chains may end at any non-frozen agent (`lb4.c -u2 -o0 -r2 -w1 -c1`).

## 2. One rotation is not enough; two suffice on the data (`attempts/k4-c4one-one-rotation.md`)

The runs below cover the 1,735 certified cores with n = 5 and one 4-good agent (`results/k4_certs_5_n4_1.json.gz`),
every strict profile and every insertion sequence (`results/k4_c4one_n5_lb4.log`):

| search (`lb4.c`) | failing (run, profile) pairs | cores |
|---|---|---|
| C₄¹'s own: `-i1 -u2 -o0 -r1 -w0 -c0` | 140 | 5 (m = 8, 9, 10) |
| owner's needs from its bundle (a rotated one-good base gets a slot, as in PR #35): `-w1` | 8 | 2 (m = 8, 9) |
| all three policies, chains to upgraded agents: `-i1 -u3 -o0 -r1 -w1 -c1` (on the 5 cores) | 6 | 2 |
| the same with index insertion, `-i0` | 4 | 1 (m = 9) |
| **two rotations, `-i1 -u2 -o0 -r2 -w1 -c1`** | **0** (of 5.78·10⁹) | 0 |

The m = 9 index-order failure is confirmed by the independent tracer (`k4/c4tools/c4trace.py`).
- It fails under each upgrade policy and under all four owner/slot conventions.
- The tracer finds two nested rotations that work.
- Brute force confirms K4.D on that profile.

The mechanism is two agents to protect and only one slot, both for owner r and for owner q (see the attempt file).

At n ≤ 4, one rotation suffices on every run `lb4.c` makes (`results/k4_c4_variants.log`). The gadget chain H_t
(`k4/c4.md` §7) needs many rotations, but its gadgets have three 4-good agents each, and a single 4-good agent cannot
be repeated along a chain. Whether two rotations always suffice with one 4-good agent is open. The certified n = 6
cores with one 4-good agent (PR #26, not merged) were not run here: every insertion sequence at n = 6 is out of reach.
Only index order with one changed step was run there (§6).

## 3. The runs the theorems of `k4/c4.md` leave open, by case (`results/k4_c4one_classes.log`)

`k4/c4check.c -X -Y` (driver `k4/c4one_run.py`) takes every run with ω ≥ 1 that §2–§4c of `k4/c4.md` do not prove.
As everywhere in this file, the runs are those `lb4.c` makes: LB's P-step key, smallest-index upgrades, every
insertion sequence.
It classifies each one and tests these repairs:
- owner r;
- another owner;
- owner q;
- rotating q along a need chain to any end t, q taking all its goods in J ∪ B_t, then owner q;
- owner t;
- `lb4.c`'s single-rotation search.

The cases:
- **(G2):** LB⁺'s bad case with r = q exposed after the rotation.
- **q frozen and exposed**, with no need chain to r, or with (i)/(ii) of B₄ʷ failing.
- **q free and exposed**, with (Tc) or (Tb) of A₄ᵀ.

"q first" means the first insertion step picks q.

- **n ≤ 4:** every unproved run has a repair among these (as §6.2 of `k4/c4.md` says).
  - With q first, (G2), (Tc) and failures of B₄ʷ's (i)/(ii) do not occur.
  - (Tb) is always repaired by owner q (10,044 runs).
  - The rest is "q frozen, no chain to r". There, rotating q, owner t or owner r cover all but 1,104 runs, which are
    repaired by another owner or another rotation.
- **n = 5:** the 140 failures of §2 are all in case (Tb) with q not first, where no repair works.
  - With q first, owner q still repairs every (Tb) run (390,432).
  - With q first, every run has a repair.

## 4. Route 2: a rotation that raises the count (`attempts/k4-c4one-potential.md`)

Route 2 tries to show one local step: whenever no owner is valid, some rotation along a need chain strictly raises
the count. Repeated rotations would then reach a valid owner. Two counts were tried (`k4/c4tools/c4pot.py`):
- **Φ:** the best A₄⁺ slack over owners (§5). Φ ≥ 0 gives a valid owner.
- **The owner-free count:** Proposition H's "slots minus forced goods".

Both are integers, and Φ ≥ 0 already gives a valid owner. So on every state where one rotation is not enough but two
are, the first rotation cannot raise Φ past −1. That happens:
- at n = 3, m = 6 with two 4-good agents;
- at the n = 5 counterexample of §2.

In both examples every valid rotation leaves Φ at −1 or lowers it. An exhaustive scan (`k4/c4tools/c4potscan.py`,
`results/k4_c4one_potential.log`) looks at every no-owner state after Phase 1:
- **one 4-good agent, n ≤ 4:** some rotation always raises Φ, and one rotation always suffices there;
- **all cores with n = 3:** the step fails in 2,184 of 606,042 states, every one with two or more 4-good agents.

The owner-free count fails to rise far more often, already at n = 2.

A potential for route 2 would have to reward preparing moves. In the example, agent 4 is rotated to a single good,
which freezes everyone else but frees a chain for the second rotation. Proposition H's per-gadget count does not do
that.

## 5. Theorem A₄⁺ for every owner

Let P be the state after any run of Phase 1 and envy-free upgrades, with ω ≥ 1. Let o be an owner that is either:
- not frozen, with |B_o| ≤ 1 (a pick, or nothing); or
- upgraded, with an envy-free base of two goods and no needs.

Put W_o := B_o ∪ J. Let E_o be the set of agents x ≠ o, x ∉ U, threatened by W_o with their base.
- For x ∈ E_o that is free and holds a pick, with at most one good of R_x in B_o, let dem(x) = 1.
- For the other x ∈ E_o, let dem(x) = ρ_o(x). This is the least size of a set D ⊆ R_x ∩ J such that x is not
  threatened by W_o ∖ D with its base (∞ if there is none).

**Theorem A₄⁺(o).** If Σ_{x ∈ E_o} dem(x) ≤ S − cap(o), then o is a valid owner (with its needs from its base).

*Proof.* The proof of Theorem A₄⁺ (`k4/c4.md` §4c) goes through with W_o in place of W. Three things need checking.

*W_o ∩ NA = ∅.* J avoids NA by (V1). B_o avoids NA because o is not frozen, or, for o ∈ U, by (V2). Hence:
- the goods of R_x ∩ W_o lie below Y_x, since goods above Y_x are in N_x ⊆ NA;
- an agent without a pick has R_x ⊆ NA, so it is not threatened;
- every x ∈ E_o holds a pick.

*A free x with dem(x) = 1 is protected by its own slot.* The proof of `k4/lb4.md` Lemma 2₄ is per agent. It uses two
facts: X_o ∩ R_x holds at most one good that is not junk, which is |B_o ∩ R_x| ≤ 1 here; and later placements only
shrink X_o. So the lemma applies to x even when |B_o| = 2.

*Completion.* This is as in Theorem A₄⁺.
- Fill the slots of the agents with dem = 1 first, each with its ≻-best junk good.
- Place the chosen sets D_x in the remaining slots of T ∖ {o}, then fill the rest with junk.
- Let X_o = B_o ∪ (J ∖ C), with |C| = S − cap(o) < |J|.

Then Theorem 1′₄ applies: only X_o has more than two goods, and frozen agents hold their bases. For o ∈ U the owner's
needs are empty. ∎

**Checked** (`k4/c4check.c -X`; every owner o ≠ r for which the count holds is run through the exact owner test;
`results/k4_c4one_check_ext.log`): 0 violations, on the runs `lb4.c` makes (every insertion sequence) of every strict
profile of every core with n ≤ 3 or
n = 4 with at most two 4-good agents. Share of runs with ω ≥ 1 that are proved:

| cores | with `k4/c4.md` | with A₄⁺(o) too |
|---|---|---|
| n = 3 | 78.2% | 84.7% |
| n = 4, one 4-good agent | 94.5% | 97.6% |
| n = 4, two 4-good agents | 89.4% | 95.3% |

## 6. Choosing the insertion sequence (`k4/c4one_tau_runs.sh` → `results/k4_c4one_tau.log`)

In this section a run counts as a success when the theorems prove it:
- with `-P`: those of `k4/c4.md` (A₄, B₄, B₄ʷ, A₄ᵀ, A₄⁺ for r);
- with `-P2`: those plus A₄⁺(o) for every owner (§5).

Runs with ω ≤ 0 need no owner and always count as a success. `k4/c4check.c -X -P` restricts the insertion sequences
by a rule. The table counts the profiles on which no allowed insertion sequence gives a proved run, over the certified
cores with one 4-good agent (`k4/c4one_tau.py`):

| criterion | insertion sequences allowed | n = 2 | n = 3 | n = 4 | n = 5 |
|---|---|---|---|---|---|
| `k4/c4.md` | all (`-i2`) | 0 | 24 | 0 | 0 |
| `k4/c4.md` | q first, the rest searched | 0 | 260 | 10,786 | 229,492 |
| + A₄⁺(o) | **all** | **0** | **0** | **0** | **0** |
| + A₄⁺(o) | **those minimizing ω after envy-free upgrades** (`-i14`) | **0** | **0** | **0** | **0** |
| + A₄⁺(o) | index order, or index order with one insertion step changed (`-i6`) | 0 | 0 | 0 | 0 |
| + A₄⁺(o) | index order, or index order with the step that started q's block changed (`-i10`) | 0 | 0 | 0 | 0 |
| + A₄⁺(o) | the first sequence minimizing ω (lexicographic order, `-i12`) | 0 | 136 | 1,000 | 3,202 |
| + A₄⁺(o) | **the first sequence minimizing key(τ) = (ω, q frozen, −pos(q))** (`-i17`) | **0** | **0** | **0** | **0** |
| `k4/c4.md` | the same (`-P -i17`) | 0 | 44 | 509 | 4,518 |
| + A₄⁺(o) | the first sequence minimizing (ω, q frozen) only (`-i15`) | 0 | 0 | 0 | 4 |
| + A₄⁺(o) | index order, else q inserted at the step that started its block (`-i11`) | 0 | 212 | 5,624 | 145,832 |
| + A₄⁺(o) | q first, the rest searched | 0 | 212 | 6,840 | 120,260 |
| + A₄⁺(o) | q as late as possible, the rest searched | 348 | 272 | 80 | 0 |
| + A₄⁺(o) | index order | 0 | 916 | 12,388 | 287,418 |
| + A₄⁺(o) | q first, then index order | 0 | 212 | 6,920 | 183,016 |
| + A₄⁺(o) | q as late as possible, then index order | 348 | 2,308 | 22,498 | 367,828 |

The table has three findings:
- **One change of insertion step suffices.** When the index-order run is not covered, changing the single insertion
  step that started q's block covers it. The new agent there is q in only 45%, 38% and 23% of the cases (n = 3, 4, 5;
  `-i10 -E`, `results/k4_c4one_exchange.log`). The new run often has ω ≤ 0, so it needs no owner.
- **Minimizing ω suffices.** Some insertion sequence that minimizes ω = |NA| − σ after envy-free upgrades is always
  covered. The lexicographically first such sequence is not always covered.
- **A deterministic rule works.** Minimize key(τ) = (ω after envy-free upgrades; q frozen (1) or not (0); −pos(q),
  that is q processed as late as possible), then take the lexicographically first. The resulting run is always
  covered (`-i17`). An upgraded q counts as not frozen: it holds an envy-free pair and is never exposed. Without
  A₄⁺(o) the same rule leaves 44, 509 and 4,518 profiles (n = 3, 4, 5).

The last finding comes from a local statement that holds on every run tested:

**Exchange Lemma X (conjecture).** Let q be the unique 4-good agent. For an insertion sequence τ, let P(τ) be the state
after Phase 1(τ) (LB's P-step key) and envy-free upgrades, and compare key(τ) lexicographically. Suppose the run for τ
is not covered, that is:
- ω(P(τ)) ≥ 1;
- none of A₄ (outside LB⁺'s bad case), B₄ (in the bad case, r not exposed after the rotation), B₄ʷ, A₄ᵀ or A₄⁺(o) for
  any owner o applies.

Then some τ′ has a covered run or key(τ′) < key(τ). Here τ′ agrees with τ before one insertion step, takes another
agent there, and follows index order after it.

*Evidence* (`-i19`, `results/k4_c4one_tau.log`): it holds for every insertion sequence of every strict profile of
every certified core with one 4-good agent and n ≤ 5, with 0 exceptions in 5.78·10⁹ (run, profile) pairs at n = 5.
Restricted to the step that started q's block (`-i18`), it fails for 288 pairs in one core, where q leads its own
block. With only the theorems of `k4/c4.md` (no A₄⁺(o), `-P -i19`) it fails for 24 pairs, all in one core with n = 3.

**Corollary.** Lemma X and the theorems (K4.C4.AB, K4.C4.AO) imply C₄¹∃, and so TARGET₄ for every instance in which
at most one agent values four goods. *Proof.* Start from any τ and apply Lemma X while the run is not covered. The key
strictly decreases, and it takes finitely many values, so this stops at a covered run. That run has one of three
outcomes:
- it needs no owner (ω ≤ 0);
- it has a valid owner (A₄, A₄ᵀ, A₄⁺(o));
- one rotation gives one (B₄, B₄ʷ).

In each case there is a valid pre-allocation with a completion satisfying (OC₄), which is C₄¹∃'s witness
(Theorem 1′₄). ∎

**Exchange Lemma X′ (stronger; conjecture).** If the run for τ is not covered, some τ′ has a covered run. Here τ′
agrees with τ before one insertion step, takes another agent there, and follows index order after it.
- X′ needs no key. Together with the theorems it gives C₄¹∃ directly: start from index order, or from any τ, and
  change one insertion step.
- *Evidence* (`-i20`): 0 exceptions on every insertion sequence of every strict profile of every certified core with
  one 4-good agent and n ≤ 5.
- Without A₄⁺(o) (`-P -i20`) it fails for 72 pairs, all in one core with n = 3.
- *n = 6, from index order* (`-i6`, `results/k4_c4one_n6.log`): on each of the 26,866 certified n = 6 cores with one
  4-good agent, every strict profile has its index-order run covered, or covered after one changed insertion step.
  That is 0 exceptions in 5.47·10¹⁰ profiles (713 s on 4 CPUs).
  - The cores come from `results/k4_certs_6_n4_1.json.gz` of PR #26 (not merged); the log records its SHA-256 prefix.
  - This tests X′ from index order only. Every insertion sequence at n = 6 is out of reach here.
- The working change is always at or before the insertion step that started q's block (`-E`, searching from the first
  step on). At n = 5, of the 1,696,106 uncovered runs, 321,544 are covered by a change at an earlier step, and the
  other 1,374,562 by a change at that step. No run needs a later step.

**Where the change is, by case** (`k4/c4one_exchange.py`; `k4/c4one_exchange_runs.sh` → `results/k4_c4one_exchange.log`).
The runs are the uncovered runs of every insertion sequence (n = 3, 4, 5), split by the classes of §3. Changes are tried
step by step from the first one, and agents in index order, so the counts describe the first change that works.
- **Only the step that started q's block** (`-Z1`) covers every uncovered run at n ≤ 4. At n = 5 it covers all but
  432 runs, all in the class "q frozen, with (i) or (ii) of B₄ʷ failing"; those need an earlier step.
- **Only q inserted at that step** (`-Z3`):
  - (Tc): covers every run, n ≤ 5.
  - (Tb): covers every run at n ≤ 4, and all but 8 at n = 5.
  - G2: covers all but 24, 44 and 956 runs (n = 3, 4, 5).
  - q frozen: often fails. For example, at n = 5 with no need chain from q to r, 294,628 of 682,232 runs stay
    uncovered. There the working agent is usually the old r or another agent of q's block.
- **ω does not always drop.** Where inserting q covers a run of (Tc) or (Tb), ω drops in every case at n ≤ 4. At n = 5
  it drops in all but 678 of 409,416. So these moves are not always steps down in key(τ), and Lemma X′, not X, is
  the form they support.

**A rotation realized by Phase 1** (`k4/c4tools/c4realize.py` → `results/k4_c4one_realize.log`). In (Tc), inserting q at
the start of its block does what a rotation does, with fresh blocks.
- The new picks are those of the old run rotated along a need chain ℓ_q = x₀ → x₁ → … → x_s = q. Each x_i (i ≥ 1)
  takes Y_{x_{i−1}}, the old leader ℓ_q ends on a good it ranks lower, and every other agent keeps its pick.
- This holds in every (Tc) case at n ≤ 4 (7,364 cases, chains of length 1 and 2). At n = 5 it holds in 195,296 of
  203,592 cases (96%, chains of length up to 3), although inserting q covers all of them. The counts are of distinct
  cases as `k4/c4check.c` prints them, not weighted by profiles.
- In (Tb) it holds in 3,352 of 3,592 cases at n ≤ 4 (in the rest q already held its top, so it has no need chain),
  and in 54,292 of 74,120 at n = 5. In G2 it holds in 70% of the cases at n ≤ 4 and 71% at n = 5.
- Why this matters: the new state is the output of a run of Phase 1. So every theorem of `k4/c4.md` applies to it, with
  its own r, blocks and exposed agents. By contrast, LB₄ʳ's rotation along ℓ_q → q keeps the old run's blocks, and the
  theorems of `k4/c4.md` treat only rotations that end at r.

This suggests a proof of X′ for q free, in two parts:
- **(a) Realization.** State when inserting the end of a need chain at the start of its block reproduces the rotation
  along the chain. This is a statement about Phase 1 alone.
- **(b) Coverage.** Show that the rotated state is covered.

What (a) must handle, for a chain ℓ → q of length 1 (so Y_q = b_q, and ℓ took a_q):
- *What goes through.* q takes a_q first. ℓ has lost a_q, so it is processed in the new block and takes b_ℓ, which is
  available (b_ℓ ∈ W).
  - No agent ranks b_q above its pick, since q is free. No agent ranks b_ℓ above its pick, since b_ℓ ∈ W and
    W ∩ NA = ∅.
  - So every other agent of the old block, processed in the old order, finds the same favourite good, as long as the
    same agents have lost a good (see D2).
- *Where it can break:*
  - (D1) An agent z of a later block with b_ℓ ∈ R_z loses b_ℓ and is pulled into the new block. z then takes its top,
    which differs from its old pick unless that pick was its top.
  - (D2) An agent of the old block whose only lost good was b_q is no longer pulled into the new block.
  - (D3) With longer chains, the chain agents must be processed in reverse order, and LB's P-step key must allow
    this.

  None of these breaks the realization in the (Tc) cases at n ≤ 4. At n = 5 they break it in 4% of the (Tc) cases,
  and there the new run is still covered. The smallest example, through (D1), is in
  `attempts/k4-c4one-realization.md`; there ω does not drop.

Why ω drops in the simplest case (a sketch, not a proof). Take a chain of length 1 in which the realization holds with
none of (D1)–(D3), and b_ℓ, c_ℓ ∈ J.
- After the change, q holds a_q and has no needs, and ℓ holds b_ℓ and needs only a_ℓ = a_q. The other picks are
  unchanged, and b_q is junk.
- ℓ is a 3-good core agent, so b_ℓ + c_ℓ > a_ℓ and {b_ℓ, c_ℓ} is an envy-free pair. So ℓ upgrades, unless another
  upgrade takes c_ℓ first.
- Then J′ = (J ∖ {b_ℓ, c_ℓ}) ∪ {b_q}. ℓ had no slot (it was frozen) and still has none (it is upgraded), and q keeps its
  slot unless another agent needs a_q.
- So ω′ = |J′| − S′ ≤ ω − 1 before any further upgrade. Further envy-free upgrades never raise ω: each one moves a junk
  good into a base and removes one slot, and it can only unfreeze agents.

A proof must also compare the two upgrade fixpoints, and handle c_ℓ = Y_r and the cases where another agent needs
a_q. Lemma Ω below does this, for runs of Phase 1 in the sense of `k4/c4.md` §1 (P-steps in any order), and for
chains of any length. Its case s = 1 is called Ω₁.

**Lemma Ω (a move that lowers ω; written proof, not yet reviewed).** Let P be the state after a run ρ of Phase 1 and
envy-free upgrades in any order. Let β be a block of ρ with leader ℓ, and x ≠ ℓ an agent of β, such that:
- **(H1)** ℓ has three goods, and b_ℓ, c_ℓ ∈ J.
- **(H2)** x ∉ U, x's pick is b_x, and no agent ranks b_x above its pick (x is free already after Phase 1). There is
  a need chain ℓ = x₀ → x₁ → … → x_s = x in P (each x_{i+1} ∉ U needs Y_{x_i}) with Y_{x_{s−1}} = a_x.
- **(H2c)** For 0 < i < s, every good that x_i ranks above Y_{x_{i−1}} is the pick of some x_k with i < k < s − 1.
  In particular it is not a_x. For s = 1 there is nothing to check; for s = 2 it says that ℓ's pick is x₁'s top.
- **(H3)** In P, no agent other than x needs a_x.
- **(H4)** Every agent of β off the chain had, at its turn, lost a good other than b_x, or has b_ℓ among its goods.
- **(H5)** No agent processed after β has b_ℓ among its goods, except possibly the leader of the block right after β.

Then some run ρ′ of Phase 1, equal to ρ before β, followed by envy-free upgrades, reaches a state P′ with
ω(P′) ≤ ω(P) − 1. In ρ′ each x_i (1 ≤ i ≤ s) takes Y_{x_{i−1}}, ℓ takes b_ℓ, and every other agent keeps its pick. So
ρ′ realizes the rotation along the chain.

*Proof.* Since ℓ leads β, its pick is its top a_ℓ.

*Two facts.*
- (F) No agent ranks b_ℓ above its pick. This is (I2), because b_ℓ ∈ J ⊆ J₀. By (H2), no agent ranks b_x above its
  pick either.
- (B1) At the start of each block after β, every unprocessed agent has all its goods. So no agent processed after β
  has a good that an agent of β picked in ρ.

*Step 1: the run ρ′.* Process the agents before β as ρ does. Then:
- *Insert x.* Every unprocessed agent has all its goods (B1 at β's start), so this is an insertion step. x takes its
  top a_x.
- *Process x_{s−1}, …, x₁ in this order.* Each x_i has lost Y_{x_i}, which x_{i+1} has just taken, so this is a
  P-step.
  - The goods that x_i ranks above Y_{x_{i−1}} are, by (H2c), picks of chain agents x_k with k > i. In ρ′ each of these
    has already been taken, by x_{k+1}.
  - Y_{x_{i−1}} itself is still there.
  - So x_i takes Y_{x_{i−1}}.
- *Process ℓ.* It has lost a_ℓ = Y_{x₀}, which x₁ has taken. Its b_ℓ is still there: b_ℓ ∈ J₀, so no agent of ρ picked
  it. So ℓ takes b_ℓ.
- *Process the agents p of β off the chain, in ρ's order.* Each is a P-step by (H4): the goods taken before p in ρ′
  include all those taken before p in ρ except b_x.
  - By (I1) and (B2), every good that p ranks above its ρ-pick Y_p was taken in ρ before p's turn, by an agent of β.
  - In ρ′ these goods are all taken too: the chain's picks Y_{x₀}, …, Y_{x_{s−1}} by x₁, …, x_s, and the others by the
    same agents. The one exception would be b_x, which by (H2) p does not rank above Y_p.
  - Y_p is still available. It is not a chain pick, and it is not b_ℓ.
  - So p takes Y_p.
- *Now consider the unprocessed agents.* By (B1), only b_ℓ can be missing among their goods. By (H5), only the leader z
  of the next block γ can have lost it. If z has, process γ's agents next, in ρ's order.
  - z has lost b_ℓ, so this is a P-step. Its other goods are all there, since γ comes right after β. So z takes its top,
    which is its pick in ρ (b_ℓ is junk, so it is not z's pick).
  - Each later agent of γ lost the same goods as in ρ, and it takes the same pick.
- *Process every remaining block as in ρ, with the same leaders.* At each block start no unprocessed agent has lost a
  good: b_ℓ is not among their goods (H5), and neither is any other good picked in β (B1). So each such block runs as
  in ρ.

*Step 2: upgrades.* Compare the states after Phase 1, P₀ (of ρ) and P₀′ (of ρ′). They differ only on the chain:
- x needs nothing, instead of {a_x};
- x_i (0 < i < s) needs the goods above Y_{x_{i−1}}, a subset of its old needs;
- ℓ needs {a_ℓ}, which x₁ needed in P₀.

So NA₀′ ⊆ NA₀, and J₀′ = (J₀ ∖ {b_ℓ}) ∪ {b_x}.
- Replay ρ's upgrades in the same order. Each step stays valid:
  - the upgraded agent is off the chain, since x ∉ U, and x₀, …, x_{s−1} are frozen in P and hence throughout;
  - NA only shrinks relative to ρ's;
  - the good taken is junk and is not b_ℓ, since b_ℓ ∈ J.
  - Afterwards NA ⊆ NA(P), and J = (J(P) ∖ {b_ℓ}) ∪ {b_x}.
- Upgrade ℓ with c_ℓ:
  - b_ℓ ∉ NA, by (V1) in P;
  - ℓ needs a_ℓ;
  - c_ℓ is junk;
  - a_ℓ < b_ℓ + c_ℓ, since ℓ is a 3-good core agent.
  - Call the result P″.

*Counting.*
- |J(P″)| = |J(P)| − 1.
- a_x ∉ NA(P″):
  - agents off the chain need what they needed in P, and by (H3) that excludes a_x;
  - by (H2c), no x_i (0 < i < s) ranks a_x above its new pick;
  - ℓ is upgraded.
  - So x, which holds a_x, is free with one slot, as it was in P.
- ℓ has no slot in P (frozen) and none in P″ (upgraded).
- x₁, …, x_{s−1} have no slot in P (frozen) and at least none in P″.
- Every other agent keeps its base, and is frozen in P″ only if it was in P, since NA(P″) ⊆ NA(P).
- So S(P″) ≥ S(P) and ω(P″) ≤ ω(P) − 1.

*Further upgrades.* Upgrade to a fixpoint P′. Each envy-free upgrade moves a junk good into the base of a free agent
with one slot, so it leaves |J| − S unchanged. It then can only unfreeze agents. So ω(P′) ≤ ω(P″). ∎

*Checked* (`k4/c4tools/c4omega1.py` → `results/k4_c4one_omega1.log`). Take the (Tc) runs that the theorems leave open
(every insertion sequence, n ≤ 5), with x = q. The hypotheses hold in:

| n | (Tc) cases | (H1)–(H5) hold | by chain length 1 / 2 / 3 |
|---|---|---|---|
| 3 | 388 | 388 | 388 / 0 / 0 |
| 4 | 6,976 | 6,052 | 3,396 / 2,656 / 0 |
| 5 | 203,592 | 162,624 (80%) | 96,860 / 44,892 / 20,872 |

- In every one of these cases the script builds ρ′ order by order and checks that it is a run of Phase 1 with the
  stated picks. It then replays the upgrades and finds ω′ ≤ ω − 1.
- Where the hypotheses fail at n = 5:
  - (H5) in 38,674 cases: an agent of a later block, other than the next leader, has b_ℓ;
  - (H2c) in 1,864;
  - (H2) in 430, where some agent ranked b_q above its Phase 1 pick.

*What it gives.* Lemma Ω does not use that q has four goods, or case (Tc). It says that at a run and upgrade fixpoint
minimizing ω, no chain satisfies (H1)–(H5).
- For Lemma X on these (Tc) runs it gives the key decrease directly, and so proves those cases of Lemma X.
- The caveat: ρ′ is a run of Phase 1 in the general sense (P-steps in any order). Lemma X's evidence (`-i19`) covers
  only the runs `lb4.c` makes (LB's key). So an induction on the key that uses Ω needs Lemma X for general runs, which
  has not been tested. #33's theorems hold for general runs, so the covered case is fine.
- (H5) is the main gap. A later agent z with b_ℓ is pulled into β's block and takes its top. If z led its block in ρ,
  that whole block can move too, provided no block in between has z's block's picks. This is the obstacle (D1) above.

So on the data, C₄¹∃ reduces to one local lemma about Phase 1 runs.
- It does not mention rotations beyond single ones, and it does not rely on LB₄ʳ's search.
- The key is a potential over insertion sequences, not over rotations. This is where route 2 (§4) failed: rotations
  need preparing moves, while insertion sequences do not.
- Next step: close (H5) in Lemma Ω, then treat the q-frozen classes, where the working agent is usually not q.

## 7. Reproduce

```
python3 attempts/k4_c4one_attempts.py                                     # §2 and §4 counterexamples (~20 s)
python3 k4/lb4_run.py results/k4_certs_5_n4_1.json.gz -i1 -u2 -o0 -r2 -w1 -c1   # §2, two rotations (~4 min)
python3 k4/c4one_run.py results/k4_certs_2.json.gz results/k4_certs_3.json.gz results/k4_certs_4_n4_1.json.gz results/k4_certs_5_n4_1.json.gz   # §3
python3 k4/c4tools/c4potscan.py results/k4_certs_2.json.gz results/k4_certs_3.json.gz results/k4_certs_4_n4_1.json.gz   # §4 (~25 min)
python3 k4/c4check_run.py results/k4_certs_2.json.gz results/k4_certs_3.json.gz results/k4_certs_4_n4_1.json.gz results/k4_certs_4_n4_2.json.gz   # §5
bash k4/c4one_tau_runs.sh                                                 # §6, every row (~1 h)
python3 k4/c4one_tau.py "-X -P2 -u2 -i20 -o0 -r1 -w0 -c0 -f3" results/k4_certs_5_n4_1.json.gz   # Lemma X', n = 5 (~5 min)
git show origin/compute/k4-frontier:results/k4_certs_6_n4_1.json.gz > /tmp/k4_certs_6_n4_1.json.gz  # PR #26's n = 6 cores
python3 k4/c4one_tau.py "-X -P2 -u2 -i6 -o0 -r1 -w0 -c0 -f3" /tmp/k4_certs_6_n4_1.json.gz          # X' from index order, n = 6 (~12 min)
bash k4/c4one_exchange_runs.sh                                            # §6, where the change is, by case (~10 min)
python3 k4/c4tools/c4realize.py results/k4_certs_3.json.gz results/k4_certs_4_n4_1.json.gz results/k4_certs_5_n4_1.json.gz   # §6, realized rotations
python3 k4/c4tools/c4omega1.py results/k4_certs_3.json.gz results/k4_certs_4_n4_1.json.gz results/k4_certs_5_n4_1.json.gz   # §6, Lemma Ω (~2 min)
```
In `k4/c4check.c`, `-P2` counts a run as a success when the theorems (with A₄⁺(o)) prove it, and the insertion modes
used above are these:
- `-i2`: search every sequence.
- `-i6`: index order, or index order with one step changed.
- `-i14`: every least-ω sequence.
- `-i17`: the key rule.
- `-i19`, `-i20`: Lemmas X and X′, starting from every sequence.

`-E` (with `-E3`) counts which step and which agent the successful change uses. `-E4` (with `-Y`) adds the class of
the uncovered run and whether ω drops. `-Z1`, `-Z3` restrict the changes tried to the step that started q's block,
and to inserting q there. `-K<class>` prints the uncovered runs of a class with the change that covers them.
