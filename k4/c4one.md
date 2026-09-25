# Conjecture C₄¹: at most one 4-good agent

Workstream `proof/k4-c4one` (ledger row K4.C4.1, open item 18). Builds on `k4/c4.md` (PR #33, under review): notation,
Lemma E, Theorems A₄, B₄, B₄ʷ, A₄ᵀ, A₄⁺ and the conventions of its §1.1. Throughout, q is the unique 4-good agent.

## Status

- **C₄¹ as stated in `k4/c4.md` §6.2 is false** (§2). With at most one 4-good agent, one rotation is not enough at
  n = 5. This holds for every run, and even for index insertion, under every convention. The smallest case is n = 5,
  m = 9 (`attempts/k4-c4one-one-rotation.md`). **Two rotations suffice** on every certified core with one 4-good agent
  and n ≤ 5, for every insertion sequence (Conjecture C₄¹², evidence).
- **Route 2 fails as posed** (§4). The claim was: whenever no owner is valid, some rotation raises "slots minus forced
  goods". It fails first at n = 3 with two 4-good agents, and at n = 5 with one. Wherever two rotations are needed, the
  first one cannot raise it (`attempts/k4-c4one-potential.md`).
- **New: Theorem A₄⁺ holds for every owner** (§5, written proof, not yet reviewed). Any non-frozen owner with a base of
  at most one good, or an upgraded owner, is valid when the goods its exposed agents need kept out fit into the other
  slots. It is checked on every run with n ≤ 4 (≤ 2 four-good agents): 0 violations. It raises the share of runs
  proved from 94.5% to 97.6% (n = 4, one 4-good agent).
- **The insertion sequence is the lever** (§6). Take the theorems of `k4/c4.md` together with A₄⁺ for every owner.
  Then every strict profile of every certified core with one 4-good agent and n ≤ 5 has an insertion sequence whose
  run they prove. No fixed rule tested (index order, q first, q as late as possible) achieves this. So C₄¹∃ reduces,
  on the data, to an exchange argument on τ; that argument is open.
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

At n ≤ 4, one rotation suffices on every run (`results/k4_c4_variants.log`). The gadget chain H_t (`k4/c4.md` §7)
needs many rotations, but its gadgets have three 4-good agents each, and a single 4-good agent cannot be repeated along
a chain. Whether two rotations always suffice with one 4-good agent is open. The certified n = 6 cores with one 4-good
agent (PR #26, not merged) were not run: every insertion sequence at n = 6 is out of reach here.

## 3. The runs the theorems of `k4/c4.md` leave open, by case (`results/k4_c4one_classes.log`)

`k4/c4check.c -X -Y` (driver `k4/c4one_run.py`) takes every run with ω ≥ 1 that §2–§4c of `k4/c4.md` do not prove.
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
`results/k4_c4one_check_ext.log`): 0 violations, on every run of every strict profile of every core with n ≤ 3 or
n = 4 with at most two 4-good agents. Share of runs with ω ≥ 1 that are proved:

| cores | with `k4/c4.md` | with A₄⁺(o) too |
|---|---|---|
| n = 3 | 78.2% | 84.7% |
| n = 4, one 4-good agent | 94.5% | 97.6% |
| n = 4, two 4-good agents | 89.4% | 95.3% |

## 6. Choosing the insertion sequence (`k4/c4one_tau.py`, `results/k4_c4one_tau.log`)

In this section a run counts as a success when the theorems prove it:
- with `-P`: those of `k4/c4.md` (A₄, B₄, B₄ʷ, A₄ᵀ, A₄⁺ for r);
- with `-P2`: those plus A₄⁺(o) for every owner.

`k4/c4check.c -X -P` then searches the insertion sequences with `-i2`, or fixes them with `-i0` (index order), `-Q`
(q first) and `-Q2` (q never inserted while another agent is available). The table counts the profiles on which no
allowed insertion sequence gives a proved run, over the certified cores with one 4-good agent:

| criterion | insertion sequences | n = 2 | n = 3 | n = 4 | n = 5 |
|---|---|---|---|---|---|
| `k4/c4.md` | all | 0 | 24 | 0 | 0 |
| `k4/c4.md` | q first, the rest searched | 0 | 260 | 10,786 | 229,492 |
| + A₄⁺(o) | **all** | **0** | **0** | **0** | **0** |
| + A₄⁺(o) | q first, the rest searched | 0 | 212 | 6,840 | 120,260 |
| + A₄⁺(o) | q as late as possible, the rest searched | 348 | 272 | 80 | 0 |
| + A₄⁺(o) | index order | 0 | 916 | 12,388 | 287,418 |
| + A₄⁺(o) | q first, then index order | 0 | 212 | 6,920 | 183,016 |
| + A₄⁺(o) | q as late as possible, then index order | 348 | 2,308 | 22,498 | 367,828 |

So on the data, every profile with one 4-good agent has an insertion sequence where r, or another owner, is valid by a
theorem already proved here or in `k4/c4.md`, or where LB⁺'s rotation (B₄) or the rotation of q (B₄ʷ) works. A proof
of C₄¹∃ along this line needs a rule or an exchange argument: when the run for τ is not covered, some other τ′ is.
None of the fixed rules does it: each misses profiles that another rule, or a search over the remaining insertion
steps, covers, so the choice has to depend on the profile.

## 7. Reproduce

```
python3 attempts/k4_c4one_attempts.py                                     # §2 and §4 counterexamples (~20 s)
python3 k4/lb4_run.py results/k4_certs_5_n4_1.json.gz -i1 -u2 -o0 -r2 -w1 -c1   # §2, two rotations (~4 min)
python3 k4/c4one_run.py results/k4_certs_2.json.gz results/k4_certs_3.json.gz results/k4_certs_4_n4_1.json.gz results/k4_certs_5_n4_1.json.gz   # §3
python3 k4/c4tools/c4potscan.py results/k4_certs_2.json.gz results/k4_certs_3.json.gz results/k4_certs_4_n4_1.json.gz   # §4 (~25 min)
python3 k4/c4check_run.py results/k4_certs_2.json.gz results/k4_certs_3.json.gz results/k4_certs_4_n4_1.json.gz results/k4_certs_4_n4_2.json.gz   # §5
python3 k4/c4one_tau.py "-X -P2 -u2 -i2 -o0 -r1 -w0 -c0 -f3" results/k4_certs_5_n4_1.json.gz                  # §6, one row
```
