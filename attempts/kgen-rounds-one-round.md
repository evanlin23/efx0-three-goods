# One round of disjoint chains at positive values (ROUND⁺) fails at n = 4 (workstream `proof/kgen-rounds`)

**Idea.** The ksens session observed (`k4/ksens.md` §8, branch `claude/k4-ksens`) that with strictly positive values
(every agent values every good, so EFX₀ = EFX) no serial-dictatorship start needed more than one round of
vertex-disjoint improving chains (`k4/sdc.md` §29 chains; rounds as in `k4/ksens.md` §6) before an EFX completion.
The data were random n = 3, 4 profiles and climbs with n ≤ 5, m ≤ 9.
- *Conjecture ROUND⁺ (coordinator).* For every positive additive instance and every order, the picks extend to a
  complete EFX allocation after at most one round.
- At n = 4 it would imply EFX for four additive agents. At n = 3 it would give a structured proof of CGM.

**Where it breaks.** At n = 4, m = 7, and with two valuation types. It also fails at n = 4, m = 8, 9 and at n = 5,
m = 8, 9 (61 distinct failing starts, `results/kgen_rounds/fails*.jsonl`).
- Random profiles never show it: 177,000 starts at n = 4, 5.
- Climbs that minimize the number and the margin of the witnessing EFX allocations find it within minutes from seeds
  near known obstructions (GM4, RD5, PW5 lifted).

**The mechanism (one obstruction behind every failure found; `kgen/rounds.md` §1, §3).**
- A round only reaches allocations that value-dominate the picks.
- After one round every base contains at most one foreign pick.
- In every failure, every EFX allocation that value-dominates the picks has a **starved agent**. That agent lost its
  pick and holds two foreign picks; one of them plus its junk does not beat its pick.
- This is RD5's "two foreign picks" mechanism (`k4/ksens.md` §6). ksens's zero-value failure survives the lift to
  positive values; their lift happened to keep a tie, v₀(4) + v₀(5) = v₀(1), that hides it.

**Smallest configuration: RD5⁺** (n = 4, m = 7; RD5 with v₀(4) lowered from 24 to 23, ×100, zeros → ε, any
ε ∈ [1, 99]):

| agent | g0 | g1 | g2 | g3 | g4 | g5 | g6 |
|---|---|---|---|---|---|---|---|
| 0 | 2600 | 5700 | ε | 4400 | 2300 | 3300 | ε |
| 1 | ε | 1200 | 1100 | 600 | ε | ε | ε |
| 2 | ε | 900 | 800 | 600 | 100 | ε | ε |
| 3 | 3600 | ε | 5300 | ε | ε | 4700 | 400 |

- *Picks.* Order (0, 3, 1, 2): agent 0 takes 1, agent 3 takes 2, agent 1 takes 3, agent 2 takes 4. Junk {0, 5, 6}.
- *One round fails.* There are 26 EFX allocations, 6 of which value-dominate the picks. In all six agent 0 holds {3, 4}
  and has lost pick 1. Its best one-round base is worth at most 4400 + ε < 5700.
- *Two rounds repair it* (the referee's form).
  - Round 1: agent 3 → agent 1 with agent 3 taking {0, 5}, which releases pick 3.
  - Round 2: the ring 0 → 2 → 0. Agent 2 receives {1}; agent 0 takes 4 plus the released 3.
  - Completion: ({3, 4, 6}, {2}, {1}, {0, 5}).
- *Also:* a two-type instance (agents 0 = 1, 2 = 3; `kgen/rounds.md` §3.3). ROUND⁺ fails there although EFX is known
  for two types (Mahara [unverified]).
- *No smaller failure found.*
  - Deleting goods from any of the 61 failures never gives m < 7 at n = 4 (`results/kgen_rounds/shrink_fails.log`).
  - Climbs at n = 4, m = 5, 6 found none (`results/kgen_rounds/small_n4m*.log`).
  - At n = 3 there was no failure on this workstream's data, but ksens's **N3K5⁺** (n = 3, m = 6, every good valued;
    `k4/ksens/refute_oc1_k5_n3.py`) refutes ROUND⁺₃. It is re-checked here in `kgen/rounds/n3k5plus.py`
    (`kgen/rounds.md` §5.1).

**The same for the pooled variant ROUND-X** (chain starts may also take any chain end's released pick).
- *Smallest failure X4* (n = 4, m = 7): values [[1,642,31,987,363,2866,764], [136,705,266,1148,475,2515,985],
  [146,133,242,1670,1,2701,633], [245,119,75,2148,140,2806,653]], order (3, 1, 0, 2).
- The starved agent is the middle agent of the chain 0 → 1 → 2, and two rounds repair it.

**Reproduce.**
```
python3 kgen/rounds/refute_roundplus.py      # pure Python, raw definitions: RD5+, C4G, C5a; certificate + two-round repair
python3 kgen/rounds/verify_fail.py '[[2600,5700,1,4400,2300,3300,1],[1,1200,1100,600,1,1,1],[1,900,800,600,100,1,1],[3600,1,5300,1,1,4700,400]]' 0 3 1 2 --two-brute
                                             # rnd.c, bruter.py, ksens ocsat/ocseq (KSENS = checkout of claude/k4-ksens)
python3 kgen/rounds/mechanism.py results/kgen_rounds/fails.jsonl results/kgen_rounds/fails_twins.jsonl
```

**What survives:** two rounds (RD²⁺) on every failure, N3K5⁺ included (`kgen/rounds.md` §4, §5).
