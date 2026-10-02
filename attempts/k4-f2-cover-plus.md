# From Theorem Z′'s state at f ≥ 2: "COVER⁺ as first stated"

Workstream `proof/k4-f2` (`k4/f2.md` §5.1, §6, §7). Ledger row K4.F2.X (REFUTED); the restated conjecture is
K4.F2.COVER. Found by compute/k4-cover (`results/k4_cover/FAILURES.md` on origin/compute/k4-cover, commit 96010ea).

**Candidate (K4.F2.COVER as first stated, PR #82 review round 1).** For every strict profile of a connected k = 4 core
with f ≥ 2 and ω ≥ 1, every key κ with def*(κ) > 0 has a maximum Q of (r′, Λ′) at which one of the following applies
at P_Q with its exact hypotheses: Lemma A⁺ (any chain length), Lemma B⁺ (threat path of length 1), Lemma C⁺ or
Lemma C′⁺ (any k). Otherwise κ must have a (T4) edge to a key with smaller def*.

**Smallest failing configuration** (n = 4, m = 10, f = 2, ω = 4; the core of K4.F2.X (2), with other values):
- sets [[0,2,4,8],[1,3,7,9],[4,5,6,7],[5,6,8,9]], values [[2,3,6,10],[2,3,10,6],[2,3,4,8],[2,3,8,4]];
- κ: agent 0 frozen on 8, agent 1 on 7, def*(κ) = 1. The frozen need digraph of κ has no arc, so it is acyclic and κ
  has no (T4) edge at all.
- Two maxima: Q = {2: {4,5}, 3: {6,9}} and Q = {2: {4,6}, 3: {5,9}}, both with L = {0,1,2,3}. At both, both free agents
  are robust leaves, crossed as in K4.F2.X (2).
- A⁺ and B⁺ fail (PR #80's `k4/sx_f2.py`). C⁺ and C′⁺ have no candidate move: x's admissible base needs a good of the
  other leaf's pair (x = 0 needs 4 ∈ H₂; x = 1 needs 9 ∈ H₃), and these lemmas allow no helper.
- The repair is one (T3) move with one helper: x = 0 takes {4}, τ = 3 takes 8, and the helper 2 gives up 4 and takes 6
  from τ's old base. This reaches ({4},{7},{6},{8}), def 0. It is Lemma C⁺ₕ of `k4/f2.md` §5.1.

**A second instance, failing only without the (T4) alternative** (n = 4, m = 7, f = 2, ω = 1; compute/k4-cover):
- sets [[0,2,3,6],[1,3,4,5],[2,4,5,6],[4,5,6]], values [[2,4,8,5],[1,4,6,8],[2,8,4,3],[3,4,2]];
- κ: agent 2 on 5, agent 3 on 4, def* 1. One maximum, P_Q = ({2,6},{1,3},{5},{4}).
- The leaf 0 is of kind (R) with its fourth good in L, so B⁺ does not apply. No A⁺, C⁺ or C′⁺ applies either.
- κ's frozen need digraph is the 2-cycle 2 ⇄ 3. The rotation reaches a key with def* = −1, which is a (T4) edge, so
  COVER⁺ as stated holds here through its (T4) alternative.
- C⁺ₕ also applies: x = 2, τ = 1, and the helper 0 owns the bundle {0,1,2,3}. The move reaches ({3},{5},{6},{4}),
  def −1.

**Frequency** (`results/k4_f2/cc_cover_hunt.log`, `cc_cover_n5seeds.log`).
- 688 records of compute/k4-cover's first-minute hunt on this core have a key that none of A⁺, B⁺, C⁺, C′⁺ covers.
- So do 3 keys of its n = 5 seeds.
- Every one is covered by C⁺ₕ or C′⁺ₕ, with a plain (T3) move with one helper.

**Reproduce.** `python3 attempts/k4_f2_attempts.py` (the two "COVER+" cases).
- Implementation A (PR #80's `k4/sx_f2.py` with `k4/f2_cc.py`, on k4/suite/model.py) finds the maxima and checks that
  no lemma applies and that C⁺ₕ does.
- Implementation B (main's k4/dl134_xcheck.py) checks:
  - def* = 1 over the states of the key;
  - the acyclicity of the frozen need digraph;
  - the deficit of the helper repair;
  - that the repair is a (T3) move.
- compute/k4-cover's `k4/cover_indep.py` independently finds the same maxima with no lemma applying
  (`results/k4_cover/failure_n4_m10_indep.log`, `failure_n4_m7_indep.log` on origin/compute/k4-cover at 96010ea).
