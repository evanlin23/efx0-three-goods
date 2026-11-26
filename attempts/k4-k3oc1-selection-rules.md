# Which DE trade? The largest-score rule fails outside the cores, and so does "least ω with Lemma 1"

Workstream `proof/k4-k3-oc1` (`k4/k3_oc1.md` §4–§5). Setting: k = 3, DE's core case. Every agent values exactly
three goods, strictly balanced; dead goods (valued by nobody) and several private goods per agent are allowed. This is
the generality of `paper/k3-simple` and of OC₁. The ledger's *cores* (PROMPT.md §3: peeled, at most one private good
per agent, connected) are a special case.

**The idea tried.** A canonical choice of the single repairing DE trade:
- *max score*: every (or some) DE trade of largest total score (DE's score: 4 for the pair, 3, 2, 1, 0 for a, b, c,
  nothing) leads to a one-absorber completion;
- *least ω*: every DE trade of least ω = |J| − |T| leads to one, even to the simple completion of Lemma 1.

On the ledger's cores they survive every test (`k4/k3_oc1.md` §1, §4). These include every core with n ≤ 5 and every
profile and order; every n = 6, m ∈ {10, 11} core and every profile; and the n = 6, m ≤ 9 cores (run in progress).
There "every least-ω trade passes Lemma 1" and "every max-score trade has a one-absorber completion" have no
counterexample.

**Counterexamples outside the cores** were found by a mutation search started from the hardest n = 6 drafts
(`k4/k3oc1/mutate.py`). Agents are listed as a > b > c; values 4, 3, 2 (any strictly balanced values give the same
result).

1. **No max-score trade repairs** (n = 6, m = 10, no dead good):
   - agents (0, 6, 9), (5, 7, 1), (4, 8, 2), (0, 3, 1), (4, 5, 3), (4, 5, 3); order 0, 1, …, 5;
   - picks (0, 5, 4, 3, –, –), junk {1, 2, 6, 7, 8, 9}.
   - The two max-score trades (score 15) are the chains (2, 4) and (2, 5); neither has a one-absorber completion
     afterwards (exhaustive search).
   - The least-ω trades, chains (0, 3, 4) and (0, 3, 5), both pass Lemma 1.
   - Agent 0 has two private goods (6, 9), and agents 4, 5 are identical; LB's rule R2 would peel agent 0.
2. **A max-score trade fails** (n = 6, m = 9, good 7 dead):
   - agents (0, 2, 6), (3, 8, 1), (4, 1, 8), (3, 0, 5), (4, 5, 2), (4, 3, 5); order 0, 1, 2, 4, 3, 5.
   - Of the two max-score trades, (1, 3) repairs and (2, 5) does not.
   - Both least-ω trades repair.
3. **A least-ω trade fails Lemma 1** (n = 6, m = 11, goods 9, 10 dead):
   - agents (0, 1, 6), (4, 7, 2), (3, 8, 6), (0, 3, 5), (4, 3, 5), (0, 5, 4); order 0, …, 5.
   - All 8 DE trades have ω = 4, and all repair under the exhaustive one-absorber test.
   - Only (1, 4) and (1, 5) pass Lemma 1. The others need a pair holder to take one junk good.

Replay (exhaustive completion; the DE trades of `k4/k3oc1/de_moves.py`): `python3 attempts/k4_k3oc1_rules.py`.

**What survives** (every test, cores and mutation search alike):
- **OT₁**: one DE trade repairs.
- **OT-ω**: every least-ω DE trade repairs, with the one-absorber completion.

The score sum is the wrong measure: in example 1 the max-score chains serve agent 2 well but leave three junk goods
against too few terminals, while the least-ω chains release more agents. ω = (m − 2n) + e + ν counts what the
completion needs (Lemma 2 of `k4/k3_oc1.md`).
