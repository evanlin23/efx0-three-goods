# Attempt: insert a shared good of a Q4 agent into a PS-selected allocation

Workstream `proof/k4-induct` (`k4/induct.md` §5). Failed; kept for the record.

**Idea.** For a private good, Lemma 2 of `k4/induct.md` is exact: d → w keeps EFX₀ iff nobody envies w, so the step
needs an X′ ∈ E(I − d) with w unenvied (conjecture PS). For a 4-good agent w with no private good (Q4), every d ∈ R_w is
shared. Candidate rules H(w, d, h): among the X′ ∈ E(I − d) with the fewest agents envying h, give d to h (h = w, another
valuer of d, or a non-valuer). A rule *works* if d → h keeps EFX₀ for every such X′. If some rule always worked, PS
(for the smaller instance) would drive the Q4 step as it drives the P4 step.

**Result** (`k4/induct_rules.py`, 200 random profiles per n = 3 core, `results/k4_induct_rules_n3.log`):
- P4 agents: "d private, h = w" works for all 13,600 (agent, profile) pairs (Lemma 2 plus PS).
- Q4 agents: some (d, h) works for 6,577 of 7,600; h = w for 5,208; another valuer of d for 5,624.
- Cores whose 4-good agents are all Q4 (the only ones left by Theorem 4 of `k4/induct.md`): on 128 of 2,200 profiles
  **no** triple (w, d, h) works.

**Why.** d → h needs, besides h unenvied by the non-valuers of d, the margin θ_j(X′_h ∪ {d}) ≤ v_j(X′_j) for every other
valuer j of d (w included when h ≠ w). Minimizing the enviers of one agent says nothing about these margins. In the
example below the two EFX₀ allocations of I − d that leave the Q4 agent unenvied differ in exactly the place where d
would have to go.

**Smallest failing configuration** (n = 3, m = 5): agent 0 on {0, 3, 4} with values (2, 4, 3) (P3, good 0 private),
agent 1 on {1, 2, 3, 4} with (6, 4, 8, 3) (Q4), agent 2 on {1, 2, 4} with (2, 3, 4) (Q3). For each d ∈ {1, 2, 3, 4} and
each h, some X′ ∈ E(I − d) with the fewest enviers of h does not admit d → h. (Other failing profiles of the same core
are listed in the log.)

Reproduce: `python3 attempts/k4_induct_attempts.py q4-rules` (independent brute force);
`python3 k4/induct_rules.py results/k4_certs_3.json.gz --samples=200 --seed=1 --log=results/k4_induct_rules_n3.log`.
