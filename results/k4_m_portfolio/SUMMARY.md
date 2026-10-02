# Lemma M portfolio: summary (compute/k4-m-portfolio)

For the provers of Lemma M (row K4.RF.M, `k4/rulef.md` §4, §6). **Everything here is EVIDENCE** (PROMPT.md §5
rule 3): random and adversarial search, and exhaustive enumeration of finite classes. No ledger status changes. Full
tables: `TABLE.md`. Every dead candidate has a `FAILURES_<cand>.md` with its smallest failure, confirmed by the second
implementation.

## Headlines

1. **Lemma M held everywhere**: on ≈1.83·10⁹ strict profiles (exhaustive and sampled) and in every hunt.
2. **M_bt1 is false** (and with it M_bt and "the big-top agent with the fewest private goods"). At n = 4, m = 8 with
   three 4-good agents (core 202 of `k4_certs_4_n4_3`), the only big-top agent q is in neither K0 nor K1.
   `sets=[[0,3,4,6],[1,3,6,7],[2,5,6,7],[4,5,7]] vals=[[3,10,2,6],[2,8,4,5],[2,8,5,4],[2,4,3]]`.
   The second implementation shows LB₄ʳ(τ_q) needs **two** rotations under all three policies; this is exact, so not
   only the counting classes fail. Exhaustively, on seven n4_3 cores, M_bt1 fails on 32 profiles. rulef.md §5.2
   states the opposite. That statement was read off leaf representatives: `rulef.c -A42` stops comparing big-top
   status at the first big-top agent, so a leaf can mix one-big-top and three-big-top profiles
   (`FAILURES_M_bt1.md`, Notes).
3. **Strongest surviving strengthening** (which agent): **sh:W ∧ btsh:W**. In words: *if some agent shares its top
   good with another agent, some such agent is in K0 ∪ K1; otherwise, if some agent is big-top, some big-top agent is
   in K0 ∪ K1.* It implies M_nobt. It is tight: on 11,522 profiles the agent it names is the only first agent in
   K0 ∪ K1.
4. **No certificate stronger than K0 ∪ K1 survives** (how): M1 ∨ M2 dies at n = 2, and "K0 or Lemma KR" dies at n = 4.
   "K0 or KR or a rotation to ω′ ≤ 0" also dies at n = 4, m = 11. There the only certificates rotate k to a base worth
   *less* than its pick, and then need a nonempty kept set.
5. **Best exchange partner: x3cE**. If a's envy-free run is in neither class, *some end of a need chain starting at an
   exposed frozen agent of that run* is in K0 ∪ K1. Over 31,581 (profile, a) pairs it is never undefined and never
   fails. The other partners fail: r on H_t and the suite, the leader of r's block on H_t, and the exposed frozen
   4-good agent at n = 3. A hunt also broke x1N.

## What was run

- **First implementation** `k4/lemmam_portfolio.c`. It `#include`s `k4/rulef.c` unchanged; the file has sha256
  `5721abf3bc9e25b101412aeb6b602db24d80e1991beee9a367a01cf9ccfc424e` and is not modified on this branch. So the
  classes K0 and K1 are rulef.c's own code: Lemma K with Remark 4's kept-out sets (`-Y1`), and the two upgrade policies
  of rule RK. On every leaf of the exhaustive enumeration it evaluates every first agent: 120 candidates (12 allowed
  sets × 10 predicates), 12 exchange-partner variants, (G2) and C40. It also checks the proved lemmas against the
  classes. Big-top status is compared for every agent, so leaves split on it. The driver is
  `k4/lemmam_portfolio.py`; it is checkpointed and resumable. The data runs used source sha `ae819de59cd381bd`.
  The final source differs only in the hunt's candidate numbering (see Hunts).
- **Second implementation** `k4/lemmam_xcheck.py`. It runs on PR #33's independent model `k4/c4_verify_H/lb4r.py`, a
  transcription of `lean/EFX/LB4R.lean`, with Lemma K from `k4/rulef_model.py`. M1, Lemma KR, the ω′ ≤ 0 rotations
  and the partners are written again there from the text of `k4/rulef.md`, without rulef.c code.
- **Data** (`TABLE.md`, `*.log`, `*.json`):
  - Every strict profile of every certified core with n = 2 (189,216) and n = 3 (299,837,376).
  - Every strict profile of every n = 4 core with one 4-good agent (7,247,232) and with two (724,847,616).
  - Every strict profile of the seven n = 4 three-4-good cores that appear in rulef's failure lines (788,299,776).
  - Random profiles of every n = 4 core: 50 and 2,000 per core (2,054,100).
  - Random profiles of every n = 5 core: 20 and 200 per core (6,948,480).
  - H_t for t = 1..5 with 3 relabelings each, and the 152 k = 4 cores of the suite.
- **Hunts** (`k4/lemmam_hunt.py`, `hunt*.log`/`.json`). Annealing walks of one core's profile against one candidate:
  the score is the number of allowed agents satisfying the predicate, then the number of first agents in K0 ∪ K1.
  Walks start from random profiles and from seed profiles. The seeds are the tight and failure profiles of
  `results/k4_rulef/`, H_1 and H_2 with relabelings, and the failure profiles of the dead candidates at n ≥ 4.
  - Hunt 1: 8 candidates × 391 cores/seeds, 50k steps each. It found the M_bt1 failure.
  - Hunt 2: aborted. Candidates with index ≥ 100 collided with the partner-variant offset, so two of its labels hunted
    partners x1N and x3cE instead. It found an x1N failure (`hunt2_aborted.txt`). The offset is now 1000.
  - Hunt 3: HUNT3_PLACEHOLDER

## Lemma M itself

Lemma M never failed. Profiles with exactly one first agent in K0 ∪ K1: 11,520 at n = 3, all on the core
`[[0,1,4,5],[2,3,4,5],[2,3,4,5]]`, and 2 suite cores. The hunts reached such profiles only from n = 3 seeds. On the
n ≥ 4 cores the tightest walks against Lemma M ended with two working first agents (score 130).
Profiles with no agent in K0 but some in K1:

| dataset | profiles |
|---|---|
| n = 3 | 263,336 |
| n = 4, one 4-good agent | 820 |
| n = 4, two 4-good agents | 207,600 |
| seven n4_3 cores | 3,296 |
| n = 4 samples | 18 + 757 |
| n = 5 samples | 33 + 382 |
| suite | 7 |

These equal the K1 counts of rule RK in `k4/rulef.md` §5.1 with `-Y1`.

## Which first agent works

| candidate | statement | applicable profiles | failures | "only" (its agent is the only working one) |
|---|---|---|---|---|
| **sh:W** | some agent shares its top ⇒ some such agent in K0 ∪ K1 | 1,037,069,996 | **0** | 11,522 |
| **btsh:W** | some agent big-top or sharing its top ⇒ some such agent works | 1,336,602,229 | **0** | 11,522 |
| **M_nobt** (nobt:W) | no big-top, some shared top ⇒ some shared-top agent works | 652,433,060 | **0** | 9,216 |
| **bt2:W** | two or more big-top agents ⇒ some big-top agent works | 101,215,503 | **0** | 0 |
| M_bt1 (bt1:W) | exactly one big-top q ⇒ q works | – | **dies** n = 4, m = 8 | – |
| M_bt (bt:W) | some big-top ⇒ some big-top agent works | – | **dies** n = 4, m = 8 | – |
| btp:W | the big-top agents with the fewest private goods | – | **dies** n = 4, m = 8 | – |
| shp:W | (no big-top) the shared-top agents with the fewest private goods | – | **dies** n = 4, m = 7 | – |
| M_gap, M_gapn | the argmax of a − (b + c), raw or normalized | – | **die** n = 3, m = 6 | – |

When no agent is big-top and none shares its top (nobt0, 492,821,741 profiles), some agent is in K0, and even
satisfies M1, on every profile.

**Recommended static statement**: let A be the agents sharing their top good with another agent, if any; otherwise
the big-top agents. Then some agent of A is in K0 ∪ K1 (= sh:W ∧ btsh:W). On the M_bt1 counterexample the working
agents 1 and 2 share their tops.

## How it is certified: everything stronger than K0 ∪ K1 dies

| candidate | statement | smallest failure |
|---|---|---|
| M_K0 (control) | some agent in K0 | n = 3, m = 5 (263,336 n = 3 profiles) |
| M_kappa | some agent with M1 (\|σ_F\| ≤ κ₀) | n = 2, m = 5 |
| M_def1 | some agent with M2 = Lemma KR, o = r, δ ≤ 1 form | n = 2, m = 4 |
| M_12 | M1 or M2 | n = 2, m = 5 |
| M_K0KR | K0, or Lemma KR's full bound with o = r | n = 4, m = 6 (samples) |
| M_K0KRo | K0, or KR for any owner | n = 4, m = 6 |
| K0\|KRa\|Rw | ... or a rotation into r reaching ω′ ≤ 0 | n = 4, m = 11 |
| K0\|KRo\|Rwo | ... any owner, any chain end | n = 4, m = 11 |

- On the n = 4, m = 6 failure every first agent is K1-only, and every certifying rotation reaches ω′ ≤ 0 (no owner
  needed). Lemma KR's count does not see that route.
- On the n = 4, m = 11 failure, `sets=[[0,2,6,10],[1,5,9,10],[3,6,7,8],[4,7,8,9]]`
  `vals=[[5,4,6,8],[3,5,6,7],[4,8,2,3],[2,4,3,8]]`, the certifying rotation gives k the base O = {good 0}. That base
  is worth less than k's pick, outside KR's hypothesis v_k(O) > v_k(Y_k). The new owner k then needs the kept set
  K = {2}.
- Combining the two dimensions dies too: every set × {K0|KRa, K0|KRo, K0|KRa|Rw, K0|KRo|Rwo} dies by n = 4 (TABLE.md).

K1 agents that are not in K0, counted over (profile, first agent):

| dataset | K1 not K0 | with a KR rotation (o = r) | neither KR (any owner) nor an ω′ ≤ 0 rotation |
|---|---|---|---|
| n = 3 | 22,183,446 | 18,438,210 | 1,117,176 |
| n = 4, two 4-good agents | 34,772,542 | 32,546,436 | 73,870 |
| H_t | 29 | 0 | 15 |

## The best exchange partner

For every (profile, first agent a) with a in neither K0 nor K1, the partner a′ is read off a's run, all datasets
together:

| variant | pairs | undefined | **none works** | where none works |
|---|---|---|---|---|
| **x3cE**: an end of a need chain from an exposed frozen agent (envy-free run) | 31,581 | 0 | **0** | – |
| x3E: the same, from an exposed frozen 4-good agent | 31,581 | 2,917 | 0 | – |
| x3bE: from r's block leader (exposed, frozen) | 31,581 | 11,555 | 0 | – |
| x3cN: x3c in the need-shrinking run | 31,581 | 13,725 | 0 | – |
| x1E: the exposed frozen 4-good agent | 31,581 | 20,023 | 11,522 | n = 3, suite |
| x1N | 31,581 | 31,545 | 0 | hunt 2: n = 4, m = 8 |
| x2: the leader of r's block | 31,581 | 31,557 | 24 | H_t, suite (outside them it is a itself) |
| x4E: r itself | 31,581 | 0 | 26 | H_t (n = 13), suite |
| x4N: r of the need-shrinking run | 31,581 | 0 | 23,070 | n = 3, H_t, suite |

- "All ends work" fails for x3cE: 24 pairs, all on H_t and the suite.
- XHUNT_PLACEHOLDER

## (G2) and C40

Counts are over (profile, first agent):

| dataset | bad case, no exposed 4-good agent (envy-free run) | (G2) | (G2) and still in K0 ∪ K1 |
|---|---|---|---|
| n = 3 | 230,196 | 136,704 | 136,544 |
| n = 4, two 4-good agents | 22,504,892 | 9,183,060 | 9,183,060 |
| seven n4_3 cores | 19,357,548 | 10,535,892 | 10,535,892 |

In (G2) the agent is in neither class only on 160 n = 3 pairs and 1 suite pair.

**C40 ⊆ K0 ∪ K1 is never violated** (≈5.4·10⁹ C40 pairs). Step 1 of §6 (C40) gives nothing on the profiles where no
first agent satisfies C40; there Lemma M needs Step 3:

| dataset | profiles with no C40 agent |
|---|---|
| n = 3 | 105,469,290 (35%) |
| n = 4, two 4-good agents | 35,202,605 (4.9%) |
| seven n4_3 cores | 105,739,694 (13%) |
| H_t | 20 of 20 |
| suite | 57 of 152 |

## Checks of the proved lemmas

There were 0 violations on every (profile, first agent) of every dataset, for each of:
- Lemma S: M1 ⇒ K0.
- Lemma KR: KR ⇒ K0 ∪ K1, for o = r and for every owner.
- C40 ⊆ K0 ∪ K1.
- A rotation to ω′ ≤ 0 ⇒ K1.

## Second implementation

- **Random profiles**: field-by-field agreement on 2,000 random profiles (700 n = 3, 700 n = 4, 600 n = 5). The
  fields are K0, K0 ∪ K1, M1, KRa, KRb and big-top. There were 0 disagreements (`xcheck_sample_n*.log`).
- **Hard profiles** (the failure profiles of every dataset): 982 profiles, 3,912 first agents. There were 45
  disagreements, all in Rw/Rwo (C false, Python true). Every one checked is the slot convention of rulef.md §2
  Remark 5. rulef.c's state code gives the marked rotated agent k (one-good base) no slot place; Lean's `Output`
  gives it one. So C's Rw is the stricter, still sound, version, consistent with rulef.c's K1. The rerun with that
  convention in Python: XCHECK_CONV_PLACEHOLDER.
- **Failures**: every smallest failure of every dead candidate is CONFIRMED by the second implementation
  (`FAILURES_*.md`, FAILCOUNT_PLACEHOLDER). This includes M_bt1, where LB₄ʳ is solved exactly.

## Open, and next

- **Lemma M** and **sh:W ∧ btsh:W** are unrefuted. A prover can aim at: *a first agent that shares its top (else a
  big-top agent) is in K0 ∪ K1*.
- **Route (a) of §6 is false as stated.** "With exactly one big-top agent q, τ_q satisfies M1 or KR" fails, because
  q can need two rotations.
- **For M2**, K1 must allow rotations outside Lemma KR's shape: a base O worth less than the pick, kept sets K ≠ ∅ at
  the rotated state, and ω′ ≤ 0 without owner. Lemma KR alone covers 83% (n = 3) to 94% (n = 4) of the K1-only agents.
- **For the exchange argument (M1–M3)**, x3cE is the partner to try.
- **Not done**: exhaustive n = 4 with three 4-good agents (339 cores; about 2 h of 4 CPUs at this harness's speed;
  only the 7 cores above were run), and n = 4 with four 4-good agents exhaustively.
