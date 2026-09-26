# Insertion order from a first/second-choice matching (k4/adaptive.md §5)

**Idea** (the coordinator's candidate, from the literature report `proofs/pq_bounded.md` §2.5). Sgouritsa–Sotiriou
(arXiv 2502.09777, §3, Lemma 3.7) start from a maximum-weight matching in which each agent takes its first or second
choice (weights 1 and 0), which leaves few envied agents. As an insertion rule for LB₄ʳ (`k4/adaptive.c`; the matching
has the largest size and, among those, the most first choices; `k4/adaptive_matching_check.py` checks that against
brute force; among several optimal matchings it returns the one its successive-shortest-path computation ends with,
Bellman–Ford over the edges with the agents in index order and each agent's first-choice edge before its second, which
is deterministic but not a tie-break by index):
- `-A17`: insert the agents matched to their first choice first, then those matched to their second, then the
  unmatched (index order inside each class);
- `-A18`: the agents matched to their second choice first;
- `-A25`: the matching recomputed at every insertion step on the unprocessed agents and the remaining goods.

**Where it breaks.** With at most one rotation each fails at n = 3 (with two, LB₄ʳ succeeds): `-A17` and `-A25` on
11,520 profiles, `-A18` on 8,120; and needs two rotations on 216 profiles with n = 4 and two 4-good agents and 28,256 with three
(`results/k4_adaptive_matching.log`, which also has `-A18`, `-A25`, n = 5 samples, #30's profiles, hill-climbing and
H_1–H_3). On H_t in #33's labeling the matching gives ℓ its first choice g_1 (every x_{j,i} its a except one per
gadget, which takes its b so that y_j gets an a), and ℓ has the least index, so `-A17` and `-A25` insert ℓ first:
that is index order, which by Proposition H (`k4/c4.md` §7) needs ⌈2t/3⌉ rotations, so these rules fail on H_5 with
three (recomputing the matching, `-A25`, does not change the first step). `-A18` does the opposite: the x_{j,1}, matched
to their second choice, come first, so an agent of gadget 1 is processed before ℓ and, by Proposition H′
(`k4/adaptive.md` §3), LB₄ʳ needs no rotation, on every relabeling (the optimal matching is unique on H_t, so it does
not depend on the labels). So on H_t the matching can pick a good or a bad first agent, depending only on which class goes first; on
small cores both orders fail.

**Ties.** The counts above use `adaptive.c`'s matching. `k4/adaptive_matching_ties.py` enumerates every optimal
matching by brute force and runs PR #33's model on each insertion sequence the rule can produce: at n = 3, 16 of the 96
failing leaves of `-A17` and `-A25` (weight 640 of 11,520) and 88 of the 200 of `-A18` (weight 6,280 of 8,120) fail
under every optimal matching (on each leaf's representative; `results/k4_adaptive_matching_ties.log`). The profiles
P1 and P3 below are tie-dependent: each has two optimal matchings, and the other one gives a sequence needing at most
one rotation. T is not.

**Smallest failing configurations** (n = 3, m = 6; `-A18` fails at n = 3 on 8,120 profiles).
- `-A17`, `-A25` (P1): the profile of `attempts/k4-adaptive-greedy-omega.md`, agents {0, 1, 4, 5}, {2, 3, 4, 5},
  {2, 3, 4, 5} with values (1, 4, 6, 8), (2, 3, 4, 8), (2, 7, 8, 4). The largest matchings match all three agents with
  one first choice; `adaptive.c` gives agent 0 its first choice 5 (agents 1, 2 their second choices 4 and 3), so agent 0
  is inserted first, and that run needs two rotations under every policy; the other optimal matching gives agent 1 its
  first choice, and agent 1 first needs one (rule F).
- `-A18` (P3): the profile of `-A9` in `attempts/k4-adaptive-local-features.md`, agents {0, 1, 2, 5}, {1, 3, 4, 5},
  {2, 3, 4, 5} with values (1, 4, 8, 6), (1, 4, 6, 8), (8, 2, 3, 4): with `adaptive.c`'s matching, agent 1 (matched to
  its second choice) is inserted first and needs two rotations; under the other optimal matching agent 0 is, and needs
  one; agent 2 first needs none.
- All three under every optimal matching (T): agents {0, 1, 4, 5}, {2, 3, 4, 5}, {2, 3, 4, 5} with values (1, 4, 6, 8),
  (3, 5, 7, 6), (2, 3, 4, 8). The two optimal matchings match two agents to their first choice and leave one unmatched
  (classes (first, first, unmatched) and (unmatched, first, first)); every sequence the three rules can produce inserts
  agent 0 or agent 1 first, and both need two rotations (PR #33's model); rule F inserts agent 2 first and needs one.

Brute force: K4.D holds on all three.

Reproduce: `python3 attempts/k4_adaptive_attempts.py` (rules 17, 25 and 18 on these profiles, with `k4/adaptive.c` and in
PR #33's independent model `k4/c4_verify_H/lb4r.py`; `results/k4_adaptive_attempts.log`) and
`python3 k4/adaptive_matching_ties.py` (every optimal matching; `results/k4_adaptive_matching_ties.log`).
