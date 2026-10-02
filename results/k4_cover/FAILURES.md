# COVER⁺ fails as stated: a key with def* > 0 where none of A⁺, B⁺, C⁺, C′⁺ applies (compute/k4-cover)

**Status: the statement COVER⁺ (k4/f2.md §5 and §7 on proof/k4-f2, PR #82; the hypothesis of Theorem Z′⁺) is false
as stated.** 1,280 uncovered keys are known. At every one, DL on the key graph (DLKey) still holds, and so does Theorem
Z′⁺'s conclusion: a (T3) move with one helper from P_Q to deficit ≤ 0, or at 9 keys a (T3⁺) move with |W| = 1. This is
EVIDENCE of a counterexample to a conjectured covering statement, confirmed by two implementations. COVER (f = 1) has
no failure.

The statement tested: for every strict profile of a connected k = 4 core with f ≥ 2 and ω ≥ 1, every key κ with
def*(κ) > 0 has a maximum Q of (r′, Λ′) at which Lemma A⁺ (any chain length j), Lemma B⁺ (threat path length 1),
Lemma C⁺ or Lemma C′⁺ (any need path length k) applies at P_Q with its exact hypotheses.

## The first instance found: a crossed pair (n = 4, m = 10)

n = 4, m = 10, f = 2, ω = 4. The core of K4.F2.X (2) (`k4/f2.md` §5, the crossed n = 4, m = 10 instance), with
other values:

| agent | goods: values |
|---|---|
| 0 | 0:2, 2:3, 4:6, 8:10 |
| 1 | 1:2, 3:3, 7:10, 9:6 |
| 2 | 4:2, 5:3, 6:4, 7:8 |
| 3 | 5:2, 6:3, 8:8, 9:4 |

`{"sets": [[0,2,4,8],[1,3,7,9],[4,5,6,7],[5,6,8,9]], "vals": [[2,3,6,10],[2,3,10,6],[2,3,4,8],[2,3,8,4]], "m": 10}`

- A k = 4 core (`model.Inst.core_violations()` is empty), strict, connected; each value vector is a strict balanced type
  of `k4/check4.py`'s `core_domains`.
- 4 keys; one has def* > 0: **κ = (agent 0 on 8, agent 1 on 7), def* = 1**, 7 states. def* by Lemma H1
  (`k4/dl2_classify.py`), by main's `k4/suite/model.py` direct removal-only deficit (`--verify`), and by
  `k4/rt4_n5_indep.py` (no repository code): all 1.
- Two maxima of (r′, Λ′), found by both implementations:
  - Q = {2: {4,5}, 3: {6,9}}, L = {0,1,2,3}, P_Q = ({8}, {7}, {4,5}, {6,9}), def(P_Q) = 1;
  - Q = {2: {4,6}, 3: {5,9}}, L = {0,1,2,3}, P_Q = ({8}, {7}, {4,6}, {5,9}), def(P_Q) = 1.
- At both, both free agents are robust leaves; leaf 2's bundle threatens only agent 0, whose good 8 only leaf 3 needs;
  leaf 3's bundle threatens only agent 1, whose good 7 only leaf 2 needs. This is the crossed pair of K4.F2.X (2).

**Why each lemma fails** (at both maxima; the same verdicts from PR #80's `k4/sx_f2.py` and PR #82's `k4/f2_cc.py`
through `k4/cover_check.py`, and from `k4/cover_indep.py`, written from the statements):
- **A⁺.** Each leaf threatens exactly one frozen agent, but no need chain from it ends at a good the leaf needs. Leaf 2
  threatens agent 0, and no frozen agent needs 8, so the only chain is (0), ending at 8, which leaf 2 does not value.
  Symmetrically for leaf 3 and agent 1. PR #80's reason: "the free needers are off the path to the leaf".
- **B⁺.** It needs a threat path τ → o into the leaf. Both free agents are robust, so neither is threatened, and
  there is no path.
- **C⁺ and C′⁺.** Their need paths are [3, 0] (τ = 3 needs φ(0) = 8) and [2, 1]. Both lemmas take x's new base A
  inside J ∪ B_τ, without a helper.
  - For x = 0: (J ∪ B_3) ∩ R_0 = {0, 2}, but U_0 = {0, 2, 4} and v_0(4) = 6 > v_0({0,2}) = 5. No admissible A exists,
    because the good x needs, 4, lies in the other leaf's pair H_2.
  - For x = 1: (J ∪ B_2) ∩ R_1 = {1, 3}, but v_1(9) = 6 > 5, and 9 ∈ H_3.

  So neither lemma has a candidate move, and PR #82's test_max applies nothing (nor its 'full' form, which needs the
  same helper-free move).

**What does repair it.** From P_Q there are (T3) moves with one helper to deficit 0 (both implementations; kinds by
`k4/rt4_n5_indep.py`'s classify: T3). Example: x = 0 takes {4}, z = 3 takes 8, and the helper 2 gives up 4:
({8}, {7}, {4,5}, {6,9}) → ({4}, {7}, {6}, {8}), deficit 0. Also x = 1 → {9}, z = 2 → {7}, helper 3. So the
conclusion of Theorem Z′⁺ (one (T3⁺) move from P_Q to deficit ≤ 0) holds here, but by none of the four lemmas. The
missing shape is a C⁺ with a helper: x's admissible base needs a good of another leaf's pair, and that leaf is paid
from τ's old base.

**DLKey holds.** The key has (T3) edges to keys of def* ≤ 0 from all 7 of its states. From ({8}, {7}, {6}, {9}) a (T3)
move without helper reaches ({4}, {7}, {6}, {8}), deficit 0.

## A smaller instance, of a second kind: the (R) leaf of Lemma B′ at f ≥ 2

n = 4, m = 7, f = 2, ω = 1, from compute/k4-rt4's dump `results/k4_rt4/dump_n4_3_x2.jsonl.gz` (on main):
`{"sets": [[0,2,3,6],[1,3,4,5],[2,4,5,6],[4,5,6]], "vals": [[2,4,8,5],[1,4,6,8],[2,8,4,3],[3,4,2]], "m": 7}`.
- κ = (agent 2 on 5, agent 3 on 4), def* = 1 (k4/dl2_classify.py, model.py and `k4/rt4_n5_indep.py`). It has one
  maximum, Q = {0: {2,6}, 1: {1,3}}, L = {0}, with P_Q = ({2,6}, {1,3}, {5}, {4}) and def(P_Q) = 1.
- Leaf 0 threatens only agent 2. Agent 1 threatens leaf 0 and needs φ(2) = 5. So B⁺'s path τ = 1 → o = 0 exists with
  j = 0 and k = 1. But o = 0 is of kind (R): its top in U_0 is 3, it holds {2,6}, it is not robust, and its fourth
  good 0 lies in L. That is B⁺'s exception, and COVER⁺ has no f ≥ 2 form of Lemma B′.
- A⁺ fails as well: no need chain from 2 ends at a good leaf 0 needs. C⁺ and C′⁺ apply nowhere (PR #82's test_max
  and `k4/cover_indep.py`).
- The repair from P_Q is a (T3) move with helper 0, the B′ shape. x = 2 takes {6}, z = 1 takes 5, and the helper 0
  takes {3} (its top, from τ's pair): ({2,6}, {1,3}, {5}, {4}) → ({3}, {5}, {6}, {4}), deficit −1, by both
  implementations.
- DLKey holds.

Log: `results/k4_cover/failure_n4_m7.log`, `failure_n4_m7_indep.log`.

## The kinds of failure seen

Final counts over the 1,280 distinct uncovered keys (`uncovered_*.jsonl.gz`, `k4/cover_uncovered.py`; all confirmed by
`k4/cover_indep.py`). The reason is PR #80's `sx_f2` reason why A⁺ and B⁺ fail at the maxima:
1. *Crossed pair* ("the free needers are off the path to the leaf"), the first instance above: x's admissible base needs
   a good of another leaf's pair. 796 keys.
2. *An (R) leaf with s in L* on B⁺'s path, the missing f ≥ 2 form of Lemma B′ (the second instance above). 411 keys.
3. *A leaf threatening two or three frozen agents*, the obstruction of K4.SX.X (3), with neither C⁺ nor C′⁺
   applying. 72 keys.
4. *Only B⁺ with a threat path of length 2* applies (n = 5, `k4_portfolio/n5_4.json` on compute/k4-portfolio). 1 key.

def* = 1 at 1,241 keys and def* = 2 at 39 (`failure_n5_m12_def2.log` is one, at n = 5, m = 12, f = 3).

At every one, at some maximum, one move from P_Q reaches a state of deficit ≤ 0, so the conclusion of Theorem Z′⁺ holds
and only its hypothesis, COVER⁺, fails:
- a plain (T3) move with one helper, at 1,271 keys;
- a (T3⁺) move with |W| = 1 and no helper, at 9.

DLKey holds at all 1,280.

## Extent

- In the first minute of `k4/cover_hunt.py` from the K4.F2.X (2) seed (`results/k4_cover/hunt/first_f2x2_1min.jsonl.gz`):
  320 distinct strict profiles of this core with an uncovered key. All have f = 2, and DLKey holds at every one.
  The smallest by the sum of values is the first instance above (sum 76). The smallest instance overall so far is
  the n = 4, m = 7 one of the second kind.
- In all: 1,280 distinct uncovered keys at n = 4 (f = 2) and n = 5 (f = 2, 3), every one confirmed by `k4/cover_indep.py`.
  None was found at n = 3 (all 193,744 f = 2 keys of every strict profile are covered), at n = 4 with at most two
  4-good agents (all 69,024 keys of every strict profile), or at n = 6. Rates in random data: 3 in 9,517 (n = 4, three
  4-good agents), 26 in 7,687 (n = 4 pure), 6 in 1,155 (n = 5). Details: `results/k4_cover/SUMMARY.md`.

## Reproduce

```
python3 k4/cover_check.py OUT.jsonl.gz inst:INST.json --indep=1   # INST.json: [the profile above]; prints UNCOVERED
python3 k4/cover_failure.py '{"sets": [[0,2,4,8],[1,3,7,9],[4,5,6,7],[5,6,8,9]], "vals": [[2,3,6,10],[2,3,10,6],[2,3,4,8],[2,3,8,4]], "m": 10}'
python3 k4/cover_indep.py --one '{"sets": [[0,2,4,8],[1,3,7,9],[4,5,6,7],[5,6,8,9]], "vals": [[2,3,6,10],[2,3,10,6],[2,3,4,8],[2,3,8,4]], "m": 10}'
```
Logs: `results/k4_cover/failure_n4_m10.log` (`k4/cover_failure.py`: both maxima, the lemma counters, every improving
move from P_Q with `k4/rt4_n5_indep.py`'s deficit and kind, DLKey per state) and `results/k4_cover/failure_n4_m10_indep.log`
(`k4/cover_indep.py`: the maxima, with no lemma applying).
