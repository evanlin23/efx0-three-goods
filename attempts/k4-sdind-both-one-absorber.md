# Attempt: Lemma BOTH for one-absorber completions (delete an unwanted top-holder)

Workstream `proof/k4-sd-induct` (`k4/sd_induct.md` §5). Failed for one-absorber completions; kept for the record.
The same statement for free completions (any number of agents absorbing) is not refuted (§5 of the note).

**Idea.** Let u hold its top a = Y_u, with nobody wanting a (v_i(a) ≤ v_i(Y_i) for every i ≠ u), as when a is a
private top. By Lemma F of the note, u can only be threatened by the absorber's bundle. Since nobody wants a, u can
also take a junk good without threatening anyone. So the hope was a black-box induction step:
- if the picks of I − u − a have a one-absorber completion, so do the picks of I;
- the repair: u takes one junk good from the absorber; if the absorber becomes threatened by a two-good bundle
  {Y_j, g_j}, j hands g_j to the absorber.

**Result** (`k4/sdind/e11_both.py`, `results/k4_sdind/e11_both.log`).
- The repair works from every completion on the screen and suite sets (888 and 1,526 completions).
- On 1,500 random n = 4 core profiles (seed 92) there is one start where the sub-instance extends and I does not:
  r1179.

**Smallest failing configuration** (r1179, n = 4, m = 9; agent: goods (values)):
- agent 0: {0, 3, 6, 7} (8, 1, 6, 4);
- agent 1: {1, 4, 6, 7} (4, 8, 3, 2);
- agent 2: {2, 5, 8} (4, 2, 3);
- agent 3: {3, 4, 5, 8} (5, 8, 6, 4).

Order (0, 2, 3, 1) gives picks (0, 1, 2, 4) and junk {3, 5, 6, 7, 8}. Agent 0 holds its private top 0. Without agent 0
there are 8 one-absorber completions. In every one of them agent 1 absorbs both 6 and 7:
- agent 1 wants agent 3's pick 4 (8 > 4), and is compensated only by 6 and 7 (4 + 3 + 2 ≥ 8);
- 6 and 7 are agent 0's danger set (6 + 4 > 8).

With agent 0, no one-absorber completion exists. There are 36 free completions, and each has at least two agents
with two or more junk goods. For example: agent 0 takes {3, 6}, agent 1 takes {5, 7}, agent 2 takes {8}.

**Why.** The absorber is a compensated wanter: its junk keeps it from strongly envying a two-good bundle. The new
agent's danger goods are exactly that compensation. One absorber cannot hold both the new agent's danger set and
the wanter's compensation. Two absorbers can.

Reproduce (independent brute force): `python3 attempts/k4_sdind_attempts.py both1`.
