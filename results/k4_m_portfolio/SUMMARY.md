# Lemma M portfolio: summary (compute/k4-m-portfolio)

Workstream `compute/k4-m-portfolio`, for the provers of Lemma M (row K4.RF.M, `k4/rulef.md` §4, §6). **Everything here is
EVIDENCE** (PROMPT.md §5 rule 3): random and adversarial search, and exhaustive enumeration of finite classes. No
ledger status changes. The full tables are in `TABLE.md`; every dead candidate has a `FAILURES_<cand>.md` with its
smallest failure, confirmed by the second implementation.

## What was run

- **First implementation** `k4/lemmam_portfolio.c`: `#include`s `k4/rulef.c` unchanged (sha256
  `5721abf3bc9e25b101412aeb6b602db24d80e1991beee9a367a01cf9ccfc424e`, the file is not modified on this branch), so
  the classes K0 and K1 are rulef.c's own code (Lemma K with Remark 4's kept-out sets, `-Y1`; policies need-shrinking
  and envy-free, as rule RK). On every leaf of the exhaustive enumeration (or every sampled profile) it evaluates every
  first agent and 100 candidates (10 allowed sets × 10 predicates), 12 exchange-partner variants, (G2) and C40, and
  checks the proved lemmas against the classes. Driver `k4/lemmam_portfolio.py` (checkpointed, resumable).
- **Second implementation** `k4/lemmam_xcheck.py`: PR #33's independent model `k4/c4_verify_H/lb4r.py` (a
  transcription of `lean/EFX/LB4R.lean`) with Lemma K of `k4/rulef_model.py`; M1, Lemma KR, the ω′ ≤ 0 rotations
  and the partners are written again there from the text of `k4/rulef.md`, without code from rulef.c.
- **Data** (≈1.04·10⁹ strict profiles in all): every strict profile of every certified core with n ≤ 3
  (299,837,376 at n = 3) and with n = 4 and one or two 4-good agents (7,247,232 and 724,847,616); random profiles of
  every n = 4 core (50 and 2,000 per core: 50,100 and 2,004,000) and of every n = 5 core (20 and 200 per core:
  631,680 and 6,316,800); H_t for t = 1..5 with 3 relabelings each; the 152 k = 4 cores of the suite.
- **Hunt** (Phase 3, `k4/lemmam_hunt.py`): HUNT_PLACEHOLDER

## Lemma M itself

**Lemma M holds on every profile of every dataset and was never broken by the hunts.** On all data the profiles with
exactly one first agent in K0 ∪ K1 are 11,520 at n = 3 (all on the core `[[0,1,4,5],[2,3,4,5],[2,3,4,5]]`) and 2
suite cores; the profiles where no first agent is in K0 but some is in K1 are 263,336 (n = 3), 820 and 207,600 (n = 4
with one, two 4-good agents), 18 + 757 (n = 4 samples), 33 + 382 (n = 5 samples), 7 (suite); these match rule RK's
K1 counts of `k4/rulef.md` §5.1 with `-Y1`.

## The strongest surviving strengthening

Two kinds of strengthening were tested: *which* first agent works (a static set A of agents), and *how* it is
certified (a predicate stronger than K0 ∪ K1).

**Which agent: survives.** With W = K0 ∪ K1:
- **btp:W** — *if some agent is big-top, some big-top agent with the fewest private goods is in K0 ∪ K1*. It implies
  M_bt (some big-top agent works) and M_bt1 (exactly one big-top agent q ⇒ q works), and bt2:W (two or more). No
  failure on any dataset or hunt. Applicable on BTP_APP profiles. Slack: on 2,304 n = 3 profiles and 2 suite cores the
  big-top agent it names is the *only* first agent in K0 ∪ K1 (so it cannot be weakened to "some agent" there).
- **M_nobt = nobt:W** — *if no agent is big-top, some agent that shares its top good with another agent is in K0 ∪
  K1*. No failure. Slack: on 9,216 n = 3 profiles the shared-top agent is the only working first agent. Its
  refinement "the shared-top agent with the fewest private goods" (**shp:W**) **dies** at n = 4, m = 7 (4 profiles of
  the exhaustive class with two 4-good agents — the failure rulef.md §5.2 reports for `-Q3`/`-Q4`).
- In the vacuous case (no big-top agent, no shared top: nobt0) Lemma M held everywhere, with at least two working
  agents on every such profile.

So the static part of a proof can be: **A := the big-top agents with the fewest private goods if some agent is
big-top, else the agents sharing their top; some agent of A is in K0 ∪ K1.** It survives about 4.5·10⁸ applicable
profiles (exhaustive up to n = 4 with two 4-good agents) and the hunts, and it is tight (the only working agent) on
11,520 n = 3 profiles.

**How it is certified: everything stronger than K0 ∪ K1 dies.**
- **M_kappa** (some agent with M1, |σ_F| ≤ κ₀) dies at n = 2, m = 5; **M_def1** (M2: Lemma KR's "in particular" form
  with o = r) at n = 2, m = 4; **M_12** (M1 or M2) at n = 2, m = 5; so the M1/M2 split of §6 Step 3 is not enough
  even at n = 2 (there some agent is in K0 through another owner or a kept set K ≠ ∅).
- **M_K0KR** (some agent in K0 or with Lemma KR's full bound, o = r) held on all exhaustive classes but **dies** in
  the samples (n = 4, m = 6, and n = 5, m = 8): there every first agent is K1-only and every certifying rotation
  reaches ω′ ≤ 0 (no owner needed), which Lemma KR's count does not see. Adding that route (**K0|KRa|Rw**, and
  **K0|KRo|Rwo** with any owner and any chain end) it still **dies**, on one profile with n = 4, m = 11
  (`sets=[[0,2,6,10],[1,5,9,10],[3,6,7,8],[4,7,8,9]] vals=[[5,4,6,8],[3,5,6,7],[4,8,2,3],[2,4,3,8]]`): every first
  agent is K1-only, and the rotation that certifies it gives k a base O = {g₀} worth **less** than its pick (outside
  Lemma KR's hypothesis v_k(O) > v_k(Y_k)) and then needs owner k with a **nonempty kept set K = {2}**. A K1 statement
  a prover can use must allow such "downgrading" rotations and kept sets.
- Combining both dimensions also dies: bt1:K0|KRo|Rwo (the unique big-top agent in K0 or with KR or an ω′-rotation)
  dies at n = 3 (22,704 profiles); nobt:K0|KRo|Rwo and bt2:K0|KRo|Rwo die in the n = 4 sample.
- **M_gap** / **M_gapn** (the agent maximizing a − (b + c), raw or normalized) die at n = 3, m = 6.

How K1 agents are certified (agents in K1 but not K0, counted over (profile, first agent)): at n = 3 22,183,446, of
which 18,438,210 have a Lemma KR rotation with o = r, and 1,117,176 have neither a KR rotation for any owner nor an
ω′ ≤ 0 rotation; at n = 4 with two 4-good agents 34,772,542, 32,546,436 and 73,870. So KR is the main route, but not
the only one.

## The best exchange partner

For every (profile, first agent a) with a in neither K0 nor K1, the partner a′ read off a's run:

| variant | pairs | undefined | **none works** | where it fails |
|---|---|---|---|---|
| x3c, envy-free: an end of a need chain from an exposed frozen agent | 26,317 | 0 | **0** | never |
| x3, envy-free: an end of a need chain from an exposed frozen 4-good agent | 26,317 | 803 | 0 | undefined when no exposed frozen 4-good agent |
| x1, envy-free: the exposed frozen 4-good agent | 26,317 | 14,742 | 11,522 | n = 3, m = 6 |
| x2: the leader of r's block | 26,317 | 26,291 + … | 24 | always a itself at n ≤ 4; fails on H_t and the suite |
| x4: r itself | 26,317 | 0 | 26 (E), 23,070 (N) | H_t (n = 13), suite; need-shrinking at n = 3 |

**Best exchange partner: x3cE** — *if a's envy-free run is in neither class, some end of a need chain starting at an
exposed (w.r.t. r) frozen agent of that run is in K0 ∪ K1*. It is defined on every pair and works on every pair of
every dataset (25,240 at n = 3, 1,008 at n = 4 with two 4-good agents, 6 in the samples, 22 on H_t, 21 on the suite)
PARTNER_HUNT. "All ends work" fails (H_t: 14 of 22 pairs have a non-working end). On H_t the partner it finds is in
gadget 1, as Proposition H″ needs. The need-shrinking version x3cN is undefined on 13,720 n = 3 pairs.

## (G2) and C40

Over (profile, first agent): LB⁺'s bad case with no exposed 4-good agent (envy-free run) 230,196 at n = 3 and
22,504,892 at n = 4 with two 4-good agents; **(G2)** (r has four goods and is exposed after the rotation along every
chain k* → r) 136,704 and 9,183,060; in (G2) the agent is still in K0 ∪ K1 except on **160** n = 3 pairs (and 1 suite
pair). **C40 ⊆ K0 ∪ K1 is never violated** (2.5·10⁹ C40 pairs at n = 4 alone). Step 1 of §6 (C40) gives nothing on
the profiles where no first agent satisfies C40: 105,469,290 at n = 3 (35%), 35,202,605 at n = 4 with two 4-good
agents (4.9%), all 20 H_t profiles and 57 of 152 suite cores — there Lemma M needs Step 3.

## Checks of the proved lemmas (0 violations everywhere)

Lemma S (M1 ⇒ K0), Lemma KR (KR ⇒ K0 ∪ K1, for o = r and for every owner), C40 ⊆ K0 ∪ K1, and "a rotation to ω′ ≤ 0
⇒ K1" hold on every (profile, first agent) of every dataset.

## Second implementation

- Field-by-field agreement (K0, K0 ∪ K1, M1, KRa, KRb, KRo, Rw, Rwo, big-top) on 2,000 random profiles (700 n = 3,
  700 n = 4, 600 n = 5): **0 disagreements** (`xcheck_sample_n*.log`).
- On the hard profiles (the failure profiles of every dataset): XCHECK_HARD
- Every smallest failure of every dead candidate is CONFIRMED by the second implementation (`FAILURES_*.md`).

## What remains open, and what to try next

- Lemma M, and its static strengthening "btp if some big-top agent, else a shared-top agent", are unrefuted.
- No certificate stronger than K0 ∪ K1 survives: a proof of M2 must use rotations beyond Lemma KR's shape (O worth
  less than the pick, kept sets K ≠ ∅ at the rotated state, owners other than k).
- The exchange argument has a candidate partner that never fails: x3cE.
