# Attempt: reduce two P3 agents that value the same two shared goods ("twins")

Workstream `proof/k4-mincex`, round 2 (β = 4, `k4/MINCEX.md` §8). Partly failed; not needed for K4.MC7. Kept for the
record.

**Why try it.** Several slow β = 4 cores (n = 9, one or two Q4 agents and many P3 agents) contain pairs of P3 agents
with the same two shared goods.

**Configuration twins.** S = {e, f}, both P3: R_e = {G1, G2, p_e}, R_f = {G1, G2, p_f}, with p_e, p_f private. So
I = {p_e, p_f} and ∂ = {G1, G2}. By K4.MC3, G1 and G2 have degree ≥ 3: a good of degree 2 shared by two P3 agents
cannot occur. So both are valued by some outside agent, and are boundary goods. 36 ranking profiles.

**Reductions tried.** DEL, and every one-agent gadget h on G1, G2 and one gadget good z′, over the menu of all 43
valuation classes of 3 goods (values 0..10). All use the unenvied bundle (Lemma M1(b)). Two gadget goods would also be
legal (h would have 4 goods, G1, G2, z′₁, z′₂, still at most 4, and the gadget would still be smaller, one
agent instead of two), but were not tried.

**Result.** 26 of 36 profiles reduce. The 10 left are listed in `results/k4_attempt_twins.log`. They include all 4
profiles in which both agents rank their private good last. In the other 6, one agent ranks its private good in the
middle and has the other agent's top as its own bottom, or vice versa.

**What would be needed.** Gadgets with two gadget goods, two-agent gadgets, or a reduction that uses more of Y.

**Smallest failing configuration.** e and f both rank G1 > G2 > p (values 4, 3, 2).
- DEL fails at the state where G1 and G2 lie together in one outside bundle without outside goods, and nobody envies
  it. Then θ_e({G1, G2}) = v(G1) + v(G2) − v(G2) = 4, but e can hold only interior goods, worth at most v(p_e) = 2
  to it.
- The gadget h with G1 = G2 = 2, z′ = 3 (the one that reduces the most profiles in configurations single-PP4 and px)
  fails at the state where h holds {G1, z′}, and G2 lies in an outside bundle with outside goods, and h's bundle is
  unenvied. G1 must go to e or f. The other agent then faces the bundle holding G2 and outside goods, a threat of
  v(G2) = 3, with only its private good (2) to hold. The exhaustive search finds no extension.

Reproduce: `cd k4 && python3 mincex_attempts.py twins` (the coverage, the 10 profiles left, and the two failing states;
log `results/k4_attempt_twins.log`), or `python3 mincex4.py explore twins` for the coverage alone.
