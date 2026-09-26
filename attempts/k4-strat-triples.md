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

**Result.** The triple spaces repair six of the eight Pareto counterexamples of 𝒫 tested: the n = 3 profiles of
`attempts/k4-c4x-pareto-potentials.md` and `hall-btown-core46`. Two remain:
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

**Replay.** `python3 attempts/k4_strat_attempts.py` (single implementation: `k4/suite/triples.py`). The runner has
`pareto-T:bt` and `pareto-T:low` (`python3 k4/suite/run.py --expected --only=hall-local3,hall-bt4`).
