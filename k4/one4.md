# TARGET₄¹: at most one 4-good agent (proof focus from 2026-11-28)

Workstream `proof/k4-one4`. This synthesizes where TARGET₄ for instances with at most one 4-good agent q stands, and
what is left. Everything cited is on main: `k4/c4.md` (PR #33), `k4/c4one.md` (PR #37), K4.ONE.FRAME (Lean, PR #39).

## The reduction chain (all proved except one link)

TARGET₄¹ ⟸ C₄¹∃ (K4.ONE.FRAME, Lean) ⟸ **Exchange Lemma X** (or its state form X\*) + the theorems of K4.C4.AB / K4.C4.AO
(`k4/c4one.md` §6, Corollary; written, refereed). Lemma X:
- a run of Phase 1 that the theorems do not cover (ω ≥ 1 and none of A₄, B₄, B₄ʷ, A₄ᵀ, A₄⁺(o) applies)
- can be changed at one insertion step so that the run is covered or key(τ) = (ω, q frozen, −pos(q)) drops.

**Lemma X is the only open link.** It holds on all data: every insertion sequence of every certified core with one
4-good agent and n ≤ 5 (5.78·10⁹ run–profile pairs at n = 5), also over runs with P-steps in any order. The stronger
X′ holds from index order on all 26,866 n = 6 cores (5.47·10¹⁰ profiles).

## What is proved toward Lemma X (X\* form)

The four moves Ω, Ω_q, Ψ, Ψ_q (`k4/c4one.md` §6) give a key-decreasing move on the share of uncovered runs below:

| runs | n = 3 | n = 4 | n = 5 |
|---|---|---|---|
| LB's P-step key | 90% | 80% | 80% |
| P-steps in any order | 90% | 73% | 62% |

## The residual cases: where a proof of X must add a move

`k4/one4_residual.py` lists the uncovered runs to which none of Ω (any x), Ω_q, Ψ, Ψ_q applies. Log
`results/k4_one4_residual_n3.log`, LB's key, n = 3.
- **218 residual runs at n = 3:** 206 in class G2 (LB⁺'s bad case with r = q exposed after the rotation) and 12 in
  "q frozen, no need chain to r". This matches `k4/c4one.md` (2,134 − 1,916).
- **Smallest residual instance** (class G2): n = 3, m = 5, sets [[0,2,3,4],[1,3,4],[2,3,4]], q = agent 0.
  - Values: q = (good 0: 3, good 2: 6, good 3: 5, good 4: 7); agent 1 = (1: 2, 3: 3, 4: 4); agent 2 = (2: 3, 3: 2, 4: 4).
  - Insertion order (1, 2, 0) gives picks q → 3 (its c), 1 → 4, 2 → 2 (q's top a = 4 and b = 2 are taken), with junk
    {0, 1} and agents 1, 2 frozen (q needs both their picks).
  - This is not a rotation along one need chain: q's two needed goods are held by two different agents, each holding
    its own top or second good.
  - The same sets carry the G2 instance quoted in `k4/c4one.md` §6 that Lemma Ψ handles, with values
    [[2,8,3,4],[2,3,4],[4,2,3]].

## Next steps (proof, kill rule 3 bursts per sub-idea)

1. Hand-analyze the smallest residual G2 run. Find the insertion change that covers it (X′ says one exists) and
   state the move as a lemma in the style of Ω/Ψ: hypotheses, the new run ρ′, the key drop. Check it with a script on
   all 206 n = 3 G2 residuals, then on n = 4.
2. The same for the 12 "q frozen, no chain to r" residuals.
3. Each proved move goes into this file with its coverage numbers. The target is a set of moves covering every
   residual class, followed by a proof that the classes are exhaustive.
