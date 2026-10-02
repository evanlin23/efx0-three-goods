# A leader rule that makes the rotation unnecessary

Workstream `proof/k3-simplify` (`proofs/k3_simple.md` §3.6, §4). Earlier rules for construction LB:
`attempts/construction_rules.md`.

**Idea.** K3ALG rotates only when its candidate absorber r fails. Lemma T (`proofs/k3_simple.md` §3.6, proved) says
that this needs **every** leader to be exposed for r. It also needs every block to have exactly one free agent. So a
rule for choosing leaders that guarantees a single non-exposed leader would remove the rotation.

A leader x whose b and c are both tops of other unprocessed agents can never be exposed. Both goods will be picked,
and at most one of them by r. Rule `tops2` prefers such leaders. Such an agent does not always exist.

**Rules tested** (no rotation; count the profiles where r is not a valid owner):
- `index` (K3ALG's choice);
- `tops2` (b and c both tops of other unprocessed agents);
- `topscore` (the most of b, c among other agents' tops);
- `untop` (a top that no other unprocessed agent values, so the leader is never frozen);
- `combo` (`tops2`, else `untop`);
- `valued2` (b and c both valued by other unprocessed agents);
- `rev` (the largest index).

| rule | n = 3 (1,512 profiles) | n = 4 (57,024) | n = 5 (92,100 sampled) |
|---|---|---|---|
| index | 14 | 636 | 538 |
| tops2 | 14 | 404 | 352 |
| topscore | 2 | 48 | 18 |
| untop | 14 | 636 | 541 |
| combo | 14 | 404 | 355 |
| valued2 | 0 | 42 | 93 |
| rev | 0 | 14 | 11 |

Lemma T held on every bad case: all 650 at n ≤ 4 and all 538 in the n = 5 sample.

**Smallest failing configurations.**
- `index`, `tops2`, `untop`, `combo` at n = 3, m = 5: rankings (2, 0, 3), (1, 2, 4), (1, 2, 0).
  - No agent qualifies for `tops2` or `untop`, so agent 0 leads and takes 2.
  - Agent 1 takes 1 and agent 2 takes 0, leaving {3, 4}.
  - Agent 2 needs 1 and 2 alone, so it is the only free agent. Agent 0 is exposed (b = 0 is r's good, c = 3 is
    left over), and no free agent other than r remains for its protecting good.
  - Making agent 1 the leader instead gives {0, 3}, {1}, {2, 4} with no rotation.
- `topscore` at n = 3, m = 5: rankings (2, 0, 3), (2, 1, 4), (2, 1, 0).
- `valued2` at n = 4, m = 6: rankings (1, 4, 5), (1, 0, 2), (3, 0, 4), (3, 4, 2).
- `rev` at n = 4, m = 6: rankings (1, 4, 5), (1, 0, 2), (0, 4, 3), (4, 2, 3).

LB's lookahead (`src/construct.py`) never rotated on any core with n ≤ 8, but that is unproved.

Reproduce:
- `python3 k3/simplify/exp_leaders.py 4` (every profile with n ≤ 4)
- `python3 k3/simplify/exp_leaders.py 5 300 5`

**Lookahead and Lemma T's condition** (`k3/simplify/exp_norotation.py`, log
`results/k3_simplify/no_rotation_leader_rules.log`). With K3S's absorber r, counts on every profile of every core with
n ≤ 5 (2,445,840 profiles):
- index: 33,104;
- construction LB's lookahead (`lb`: the smallest |NA| after the leader's block): 30;
- `P` (a leader satisfying Lemma T's provable condition, else index): 16,437;
- `P`, else `lb`: 24.

Every ranking profile with n = 3 on 5–7 goods: `lb` fails on 12, 36 and 72 profiles. The smallest `lb` failures:
- n = 3, m = 5, core (2, 0, 3), (1, 4, 2), (1, 2, 0);
- n = 3, m = 5, rankings (0, 1, 2), (2, 3, 4), (0, 2, 3) (not a core).

Construction LB never failed on cores, but it chooses its owner by a search over all non-frozen owners and uses
another R1 order. With the absorber fixed to r, the lookahead is not enough.

Choosing only the first leader does avoid the rotation in every case tested, but by a search (Conjecture FL,
`proofs/k3_simple.md` §7). Static choices of the first leader fail (`results/k3_simplify/first_leader_static_rules.log`):
- the failed run's r works on 1,643 of 1,648 profiles at n ≤ 4;
- "b and c valued by the most agents" works on 1,618 of 1,648.

**Redoing the last block with a named leader** (`k3/simplify/exp_last_leader_rules.py`, log
`results/k3_simplify/last_leader_static_rules.log`). When K3S would rotate, redo the draft with the last insertion
step's leader replaced by an agent of the failed run. Neither choice always works:
- x₁, the agent that needed k*'s top, works on 32,865 of 33,104 core profiles with n ≤ 5. Smallest failure: core
  (2, 0, 3), (2, 1, 4), (2, 1, 0), m = 5.
- r works on 33,062 of 33,104. Smallest failure: core (0, 1, 2), (0, 3, 4), (4, 1, 3), (4, 3, 2), m = 5.

Some last leader always worked (Conjecture LL), but only by trying each one.
