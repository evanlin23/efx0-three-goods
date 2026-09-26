# PS_W: closing the PS induction under another agent's private good (route 2)

Workstream `proof/k4-strategy` (`k4/strategy.md` §2.2). Ledger row K4.STRAT.X.

**Setting.**
- PS(J, w): some EFX₀ allocation of J leaves w unenvied (#43, `k4/induct.md`).
- In a minimal counterexample (I, w*) to PS₄, Proposition 5 leaves two configurations unreduced. One is a private good
  p of an agent i ≠ w*.
- Removing p needs an EFX₀ allocation of I − p in which both w* and i are unenvied (Lemma 2 for i). The hypothesis
  that closes under this step is
  > **PS_W**: for every instance J and every set W of agents, some EFX₀ allocation of J leaves every agent of W unenvied,

  with W = the agents whose private goods were removed.

**Result: PS_W is false at n = 2, m = 4, although the core it comes from is fine.**
- Let I be the twins core: agent 0 values {0, 2, 3} at 2, 5, 4, and agent 1 values {1, 2, 3} at 2, 5, 4. Each is
  balanced (5 < 2 + 4), goods 0 and 1 are private, and I is a k = 3 core (hence a k = 4 core).
- TARGET(I), PS(I, 0) and PS(I, 1) hold. For example, 0 takes {0, 2} and 1 takes {1, 3}: agent 1 sees
  {0, 2} ∖ 0 = {2}, worth 5 < 2 + 4.
- PS_{0,1}(I − 1) holds: agent 1 keeps only its shared goods, 0 takes {0, 3}, 1 takes {2}.
- PS_{0,1}(I − {0, 1}) is **false**: two agents with the same ranking on one pair {2, 3}. Whoever gets the worse bundle
  envies the other.
- So the induction that strips private goods one at a time reaches a false statement, starting from a core where
  everything holds.

*Scope (PR #56 review).* As literally stated (every instance J and every W), PS_W is trivially false: two agents
sharing one good, with W = both. The twins show more: it fails on an instance derived from a core by removing the
private goods of the agents of W. If the induction never removes w*'s own private good (the step removes p of an agent
i ≠ w*), the twins reach only PS_{0,1}(I − 1), which holds; whether that narrower form fails is not settled here.

The restriction that would save it ("W = agents that had private goods in the original core") is not a property of the
smaller instance, so it is not inductive. In `k4/MINCEX.md` this configuration (a degree-2 good
shared by two P3 agents) is removed by a gadget reduction (K4.MC3), not by a hypothesis.

**Replay.** `python3 attempts/k4_strat_attempts.py`, with this PR's SAT encoding (`k4/suite/model.py`) and #43's
`k4/induct_sat.py` (an independent encoding) for the PS_W query.

## PS-OWNER: a prescribed unenvied owner in the D2 shape

A stronger target, and the k = 4 form of #43's Lemma 7 (LB⁺ with the target processed last makes it the owner):
> **PS-OWNER.** For every agent w, some EFX₀ allocation leaves w unenvied and gives every other agent at most two goods.

It would make w the owner of the large bundle, which is what an induction on private goods of w needs. **It fails at
n = 3, m = 6 on cores**, with both implementations (this PR's SAT in `k4/suite/model.py` and a D2 extension of #43's
`k4/induct_sat.py`, `k4/suite/predicates.py` `psd2`).
- It fails on 28 of the suite's cores and on the non-core LIL instance (`results/k4_strategy/suite_baseline2.log`).
- PS itself (no shape constraint) holds on every one of them.

Smallest found: `c4-lbplus-rotation-n3m6`.
- Sets and values: agent 0 values {0, 1, 2, 5} at 2, 4, 8, 5; agent 1 values {2, 3, 4, 5} at 8, 3, 4, 6; agent 2 values
  {3, 4, 5} at 2, 3, 4.
- Agent 1 is never the unenvied owner of a D2 EFX₀ allocation.

So Lemma 7's route does not carry over to k = 4 as a statement about every agent.

Replay: `python3 k4/suite/run.py psd2 --only=c4-lbplus-rotation-n3m6`.
