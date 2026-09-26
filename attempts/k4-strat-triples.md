# Three-good bases: Theorem K3's statement in 𝒫_T (route 4a)

Workstream `proof/k4-strategy` (`k4/strategy.md` §2.4). Ledger row K4.STRAT.X. Code: `k4/suite/triples.py`.

**Idea.** The first way the extremal principle breaks at k = 4 is (G1) of `k4/c4x.md` §5. A big-top agent
(4 goods, a > b + c) has no base of at most two goods worth more than its top, only the triple {b, c, d}. So a
frozen big-top agent cannot be "rotated" onto a better base inside 𝒫. Add the triples:
- **𝒫_bt**: a big-top agent may hold its lower triple R_i ∖ {a_i}. 𝒫_low: every 4-good agent may. 𝒫_any: any three
  of its goods.
- Needs are value-based, and validity is as in 𝒫. A triple has no slot.
- A completion must also leave every triple of a non-owner unthreatened, since a three-good bundle can be strongly
  envied.
- The D2 shape is given up; TARGET₄ does not need it. Every completion found is re-checked by the raw EFX₀
  definition.

**Statement tried** (Theorem K3's): every Pareto-maximal P of 𝒫_T is (removal-only) completable.

**Result.** Of the eight Pareto counterexamples of 𝒫 first tested, the triple spaces repair six: the n = 3 profiles of
`attempts/k4-c4x-pareto-potentials.md` and `hall-btown-core46`. Run on the whole suite, they fail on smaller instances
(found by the PR #56 review, confirmed with `triples.pareto_every`):
- **𝒫_low, n = 2, m = 4: `adaptive-cover-multi4`**: twins on {0, 1, 2, 3} valued 2, 4, 5, 8. At the Pareto-maximum
  {3} | {0, 1, 2}, agent 0 values {0, 1, 2} ∖ 0 at 9 > 8, and there is no junk.
- **𝒫_bt, n = 3, m = 5: `c4x-n3m5-big-bases`** (also `induct-gps-q4-b`): the big-top agent 0 holds {0, 2, 4}, which
  agent 2 values at 5 > 4 after removing good 0.

The two of the eight that remain:
- **n = 3, m = 7: `hall-local3`**:
  - sets and values: agent 0 values {0, 1, 2, 3} at 3, 2, 10, 6; agent 1 values {2, 4, 5, 6} at 8, 2, 3, 4; agent 2
    values {3, 4, 5, 6} at 7, 3, 5, 6.
  - In 𝒫_bt and in 𝒫_low the Pareto-maximum with bases {0, 2} | {4, 5, 6} | {3} has ω = 0 and no frozen agent, yet no
    completion exists.
  - Agent 1's triple {4, 5, 6} (worth 9 > 8 to it) threatens agent 2: agent 2 values it at 3 + 5 + 6 − 3 = 11 > 7.
  - So the new bases bring a new obstruction.
- **n = 4, m = 7: `hall-bt4`** (#52's bt4). Its frozen agents are not big-top, so the Pareto-maximum
  {2, 5} | {0, 3} | {4} | {6} of 𝒫 stays Pareto-maximal and non-completable in every 𝒫_T.
- 𝒫_any also breaks `c4-pareto-moves-n3m6`, which 𝒫 and 𝒫_bt pass.

**Smallest failing configurations:** 𝒫_low at n = 2, m = 4 (`adaptive-cover-multi4`); 𝒫_bt at n = 3, m = 5
(`c4x-n3m5-big-bases`); for frozen agents that are not big-top, n = 4 (`hall-bt4`).

**Replay.** `python3 attempts/k4_strat_attempts.py` (single implementation: `k4/suite/triples.py`). The runner has
`pareto-T:bt` and `pareto-T:low` (`python3 k4/suite/run.py --expected --only=hall-local3,hall-bt4,adaptive-cover-multi4,c4x-n3m5-big-bases,induct-gps-q4-b`).
The claim about 𝒫_any and `c4-pareto-moves-n3m6` is not replayed by the script.
