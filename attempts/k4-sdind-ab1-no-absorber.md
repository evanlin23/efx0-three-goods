# Attempt: Conjecture AB₁ with "no absorber needed" (any unfrozen agent can be the first one inserted)

Workstream `proof/k4-sd-induct` (`k4/sd_induct.md` §3, §7). Refuted in its original form; kept for the record. The
refined form, which only covers agents that really absorb, is still under test.

**Statement refuted.** "If an unfrozen agent o is the absorber of some one-absorber completion of Y, *or no
completion needs an absorber*, then some order producing Y with π_n = o admits a reverse-SD insertion path with at
most one junk move per step." The prefix-robust form (Conjecture PR) falls with it, since a PR completion gives such
a path.

**Result.** `k4/sdind/e16_ab1_climb.py` (adversarial climb, random k = 4 cores with n = 4; 400 rounds of 150 steps,
seed 3; `results/k4_sdind/e16_ab1_climb_n4_original.log`) reaches 3 counterexamples. In all three:
- every one-absorber completion of the picks gives each agent at most one junk good, so no absorber is needed;
- for some unfrozen o, every order with o last fails at the first insertion, where a frozen agent must be protected
  from o's full bundle with two moves at once;
- other last agents work.

Earlier, 17,403 random and curated cases had passed (`e7_absorber*.log`).

**Smallest failing configuration** (n = 4, m = 7; agent: goods (values)):
- agent 0: {0, 2, 3, 6} (6, 4, 8, 5);
- agent 1: {1, 4, 5, 6} (8, 3, 4, 6);
- agent 2: {3, 4, 5, 6} (10, 6, 7, 2);
- agent 3: {4, 5, 6} (2, 4, 3).

The picks are (3, 1, 4, 5) and the junk is {0, 2, 6}. The completions are {0 → 1, 2 → 3, 6 → 2} and
{0 → 3, 2 → 1, 6 → 2}, so no absorber is needed. Agent 2 is unfrozen. Agent 3 is frozen: agent 2 wants its pick 5
(7 > 6).

With agent 2 inserted first (o = 2), it holds all of {0, 2, 6}. Both final completions give 6 to agent 2: it is
agent 2's compensation for wanting agent 3's pick.
- *Agent 3 inserted second* (orders (0, 1, 3, 2) and (1, 0, 3, 2)). Agent 3 is threatened by {4, 0, 2, 6}: its
  goods 4 and 6 are worth 2 + 3 > 4. The only completion of {2, 3} gives both 0 and 2 to agent 3, which is two
  moves at once.
- *Agent 0 inserted second* (orders (1, 3, 0, 2) and (3, 1, 0, 2)). The sub-instance {2, 0} has no one-absorber
  completion at all: agent 2 wants agent 0's pick 3.
- *Agent 1 inserted second* (orders (0, 3, 1, 2) and (3, 0, 1, 2)). The only one-move continuation is "agent 1 takes
  6". It leads to a dead end, because 6 has to be back with agent 2 at the end.

The order (0, 3, 2, 1), with agent 1 last, works.

**What survives.**
- *Refined AB₁*: o ranges only over agents holding two or more junk goods in some completion, and when no completion
  needs an absorber, *some* unfrozen o works. Under test (`e16_ab1_climb_n*_refined*.log`).
- `e18_mono.py`: on the 15,786 cases (Y, o) of the curated and random data, the monotone form held. Those data
  contain no such instance.

Reproduce (independent brute force): `python3 attempts/k4_sdind_attempts.py ab1`.
