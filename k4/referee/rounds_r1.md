# Referee report: Lemma R1 and the starved-agent certificate (`kgen/rounds.md` §1, with §3's uses, branch `proof/kgen-rounds`, PR #111)

Referee: `proof/k4-referee`, 2026-11-26.
- Read: `kgen/rounds.md` at `a33b135`: the status, §1 (definitions, Lemma RC, Lemma R1, the Corollary), §3 (RD5⁺, C4G,
  the two-type instance) and §6 (proposed ledger rows).
- Check: `k4/referee/rounds_ref.py`, run by `rounds_ref_runs.sh`, log `results/k4_referee/rounds_ref.log`.
  - Rounds are enumerated forward from the definitions, with two enumerators written separately (picks-only and
    general bases). They agree on every named start.
  - Completions are checked against all n^m allocations with the raw definition.
  - No code from `kgen/rounds/` was run or imported.

## Verdict

| item | verdict |
|---|---|
| Lemma R1 (MD and one foreign pick per base after one round) | **CORRECT** |
| Corollary (starved-agent certificate) | **CORRECT** |
| Its use on RD5⁺ (ε = 1 and 99), C4G, the two-type instance: one round fails | **CONFIRMED** (certificate and, independently, forward enumeration of every round) |
| "Two rounds repair" these three | **CONFIRMED**. **Fix needed** in §3.1: the printed two-round repair of RD5⁺ is not valid as written (below), but a one-line correction of it is |
| Lemma RC, RC2, Lemma ID, §4–§5 | not refereed |

## 1. Lemma R1 and the Corollary

**Lemma R1.** After one round from the picks:
- off-chain agents and t = 0 starts keep their pick in their base;
- a receiver x_i gets {y_{x_{i−1}}} ∪ H_i with H_i ⊆ J;
- a start of a chain with t ≥ 1 gets H₀ ⊆ J ∪ {y_{x_t}}, its own chain's end only (the round definition, `k4/ksens.md`
  §6).

So every base holds at most one foreign pick. Chain agents gain strictly over their pick, and bases lie inside the
final bundles. So v_i(X_i) ≥ v_i(base) ≥ v_i(y_i), strictly for every agent that passed its pick, which are exactly
the agents with y_i ∉ X_i. Correct. Only nonnegativity is used, so it holds with zeros too.

**Corollary.** Let X be a completion after one round. By R1, X is EFX and value-dominates the picks, so by hypothesis
some agent a in X is starved.
- y_a ∉ X_a, so a passed its pick and lies on a chain with t ≥ 1.
- Its base is worth more than v_a(y_a) and lies inside {f} ∪ (X_a ∩ J) for its foreign pick f ∈ X_a (if any).
- Values are monotone, so the max in the definition of starved exceeds v_a(y_a). That is a contradiction.

The argument covers free and one-absorber completions alike. Correct.

## 2. The instances of §3 (evidence; my brute force)

| instance | picks | EFX allocations | MD ones | starved agent in every MD one | rounds from the picks (base tuples) | one round completes | first rounds with a completing second round |
|---|---|---|---|---|---|---|---|
| RD5⁺, ε = 1 | (1, 3, 4, 2) | 26 | 6 | agent 0 (holds {3, 4}) | 225 | no | 27 |
| RD5⁺, ε = 99 | (1, 3, 4, 2) | 26 | 6 | agent 0 | 225 | no | 27 |
| C4G | (4, 3, 5, 6) | 18 | 8 | agent 2 (holds {4, 6}) | 255 | no | 20 |
| two types | (2, 3, 6, 4) | 20 | 8 | agent 0 or 1 (holds {4, 6}) | 424 | no | 45 |

- The MD allocations of RD5⁺ are exactly as stated: agent 0 holds {3, 4} (+ 6), agent 3 holds {0, 5} (+ 6), and
  agents 1 and 2 hold the goods 1 and 2.
- "The other 9 distinct starts of RD5⁺ need at most one round": confirmed (5 extend, 4 need one round).
- (Not claimed otherwise in the note, but for the record: C4G has one more failing start, (4, 6, 5, 3), and the
  two-type instance three more.)

**The printed two-round repair of RD5⁺ (§3.1) is wrong as written.**
- The printed repair:
  - Round 1 (valid): the chain 3 → 1 with H₀ = {0, 5}, plus agent 0's t = 0 addition of good 6. Bases
    ({1, 6}, {2}, {4}, {0, 5}).
  - Round 2: "agent 2 takes 1 from agent 0's base {1, 6}".
- That breaks the chain rule (`k4/sdc.md` §29: x_i takes all of B_{x_{i−1}} plus junk), under which agent 2 takes
  {1, 6}. The state reached is ({3, 4}, {2}, {1, 6}, {0, 5}). It uses every good, and it is not EFX.
- The printed final allocation ({3, 4, 6}, {2}, {1}, {0, 5}) does not contain agent 2's base.
- **Fix:** drop the t = 0 addition in round 1. Then round 2's ring hands agent 2 exactly {1}, and agent 0 takes
  {3, 4}, worth 6700 > 5700. The printed final allocation is then a valid completion. Checked by forward enumeration.
- The claim "two rounds suffice" is unaffected: 27 of the 225 first rounds have a completing second round.

**Random positive instances** (n = 3, m ≤ 7; n = 4, m ≤ 6):
- every (round, completion) pair: 398,577 pairs from 8,050 starts, 0 violations of R1;
- no random start satisfied the certificate's hypothesis, consistent with the note ("random sampling found none").

## 3. For the coordinator

- Lemma R1 and the starved-agent certificate: CORRECT. Their part of the proposed KGEN.RC row can be PROVED. RC and RC2
  are not refereed here.
- The ROUND⁺ refutations (RD5⁺, C4G, two types) are confirmed by an independent brute force.
- §3.1's printed two-round repair needs the one-line fix above: no t = 0 addition of 6 in round 1.
