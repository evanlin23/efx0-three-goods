# Lifting "one Draft and Exchange trade" from k = 3 to k = 4 fails twice: junk for b-holders, and validity

Workstream `proof/k4-k3-oc1` (`k4/k3_oc1.md` §7). At k = 3 every repair found is a single Draft and Exchange trade
(candidate OT and Theorem R1C). A DE trade has two properties.
- **(DE-a)** Only an agent that gives up its top takes junk. This is the pair arrow and the chain start. Every other
  receiver gets exactly its predecessor's good.
- **(DE-b)** The state stays *valid*: every good some agent values above its holding is held alone
  (`paper/k3-simple`, Lemmas ring and chain). Lemma 1's completion then gives frozen agents no junk.

**The idea tried.** The k = 4 *DE-type chain*: an improving chain of `k4/sdc.md` §29 with t ≥ 1, satisfying (DE-a)
and (DE-b) (`k4/k3oc1/lift4.py`, `de_type`). Is one DE-type chain enough, from every order?

**Result** (every order, n ≤ 5; `results/k4_k3oc1/lift4_*.log`).

| class of chains | special: hard starts not repaired | screen | suite |
|---|---|---|---|
| all improving chains (OC₁) | 0 | 0 | 0 |
| DE-type: (DE-a) and (DE-b) | 1 (T3) | 66 | 45 |
| (DE-a) and compensable validity (DE-b*) | 0 | 57 | 36 |
| t ≥ 1, any agent may take junk, (DE-b*) | 0 | 0 | 0 |

(DE-b*): a wanted good may sit in a bundle of two or more goods if each of its wanters has a junk good that makes up
the difference (`lift4.valid_star`). The counts are starts (orders) whose picks have no one-absorber completion and
are not repaired by one chain of the class; the special, screen and suite sets have 69, 662 and 797 such hard starts.

**First failure, (DE-a): nsw-local-n3m5** (n = 3, m = 5, screen set). The smallest instance; it also fails with (DE-b*).
- Agent 0 values goods 0, 1, 3, 4 at 8, 4, 5, 6.
- Agent 1 values goods 0, 2, 3, 4 at 10, 3, 4, 8.
- Agent 2 values goods 1, 2, 3, 4 at 2, 3, 4, 8.

Order (1, 0, 2) gives the picks (4, 0, 3) and junk {1, 2}. Agent 0 holds its second good 4, since agent 1 took good 0.
- The picks have no one-absorber completion.
- Exactly 3 of the 13 improving chains repair, and in each agent 0 gives 4 to agent 2 and takes {1, 3} (4 + 5 > 6)
  from the junk and agent 2's pick. All three results are valid.
- At k = 3 this move never improves an agent. A b-holder values every junk good below b (it was free at its turn), and
  at most one other good of its three is below b. At k = 4 a b-holder gains from {c, d} whenever c + d > b.
- That is also why b-holders can be threatened by the owner's bundle at k = 4, while at k = 3 only top-holders can.

**Second failure, (DE-b): T3** (n = 3, m = 6, `k4/sdc/nof_var.py` SPECIAL).
- Agent 0 values goods 5, 0, 4, 2 at 1, 38, 36, 6.
- Agent 1 values goods 3, 1, 4 at 12, 22, 30.
- Agent 2 values goods 4, 1, 3, 0 at 28, 20, 12, 38.

Order (0, 2, 1) gives the picks (0, 1, 4) and junk {2, 3, 5}.
- Exactly 3 of the 32 improving chains repair, and **no repairing result is valid**. In each, agent 0 gives its top 0 to
  agent 2 and takes {2, 4} (6 + 36 > 38), so agent 1's top 4 (30 > 22) sits in a two-good bundle. The completion gives
  agent 1 the junk good 3 (22 + 12 ≥ 30), for instance X = ({2, 4, 5}, {1, 3}, {0}).
- At k = 3 such a compensation is a b-holder taking its c (an upgrade), and OT never needs it after the trade.

Replay of both instances without SAT and without shared code: `python3 attempts/k4_k3oc1_lift.py`. It runs a brute
force over every improving chain and every one-absorber placement of the junk, with the raw EFX₀ definition.

**Repair.** Drop (DE-a) and weaken (DE-b) to (DE-b*). Then one chain repairs every hard start of the three sets (last
row of the table). But the k = 3 selection rule does not survive the larger class. Counted over distinct hard picks, every max rank-score chain repairs
only on 162 of 194 for the screen set and 165 of 196 for the suite; the least-ω chain on 149 of 194 and 151 of 196. At
k = 3 the max-score rule also fails over general chains (517 of 1,500 hard n = 4 starts, `k3_general_rule.py`). It is a
property of DE's narrow trades, which do not exist at k = 4.
