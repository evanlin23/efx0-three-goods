# Attempt: insert d into an extremal EFX₀ allocation of I − d

Workstream `proof/k4-induct` (`k4/induct.md` §2). Failed; kept for the record.

**Idea.** E(I − d) is finite and, by induction, nonempty, so a proof may take the X′ that maximizes a potential Φ and
argue that d can be placed without any repair (else a better X′ exists). Tested for eight potentials; "fails" means:
for *every* 4-good agent w and every d ∈ R_w, some maximizer of Φ on E(I − d) admits no placement of d that keeps EFX₀.

**Result** (smallest failure found; counts on 25,500 sampled n = 3 profiles, `results/k4_induct_n3.log`):

| Φ (maximized) | smallest failure | n = 3 profiles failing |
|---|---|---|
| v_w(X′_w) | n = 3, m = 4 | 1,092 |
| −v_w(X′_w) | n = 2, m = 4 | 3,348 |
| −#agents envying w | n = 3, m = 5 | 74 |
| (−#agents envying w, v_w) | n = 3, m = 5 | 10 |
| utilitarian welfare | n = 3, m = 6 | 3 |
| Nash welfare | n = 3, m = 6 | 3 |
| (−#agents envying w, utilitarian) | n = 3, m = 5 | 10 |
| −#agents envying someone | n = 3, m = 4 | 239 |

**Why.** For a private good d the right choice is known exactly (Lemma 2 of `k4/induct.md`: d → w works iff w is
unenvied), and the potentials that minimize the enviers of w do find such an X′ whenever the removed good is private.
The failures are at shared goods (w with no private good, or a shared d chosen), where placing d needs margins for the
other valuers of d that none of these potentials controls.

**Smallest failing configurations** (agent: goods, values):
- v_w: {0, 1, 2, 3} (8, 4, 7, 2); {1, 2, 3} (4, 3, 2); {1, 2, 3} (3, 2, 4).
- −v_w: {0, 1, 2, 3} (4, 8, 6, 1); {1, 2, 3} (4, 2, 3).
- −#enviers(w): {0, 3, 4} (2, 3, 4); {1, 2, 3, 4} (3, 2, 8, 4); {1, 2, 4} (2, 3, 4).
- (−#enviers(w), v_w) and (−#enviers(w), utilitarian): {0, 3, 4} (2, 4, 3); {1, 2, 3, 4} (4, 2, 10, 7); {1, 2, 4} (2, 3, 4).
- utilitarian: {0, 2, 4, 5} (3, 6, 4, 8); {1, 4, 5} (2, 4, 3); {3, 4, 5} (2, 4, 3).
- Nash: {0, 2, 4, 5} (4, 3, 6, 8); {1, 4, 5} (2, 3, 4); {3, 4, 5} (3, 4, 2).
- −#agents envying someone: {0, 1, 2, 3} (2, 8, 5, 4); {1, 2, 3} (4, 2, 3); {1, 2, 3} (4, 3, 2).

Reproduce: `python3 attempts/k4_induct_attempts.py pot-maxvw pot-minvw pot-env pot-env-vw pot-util pot-nash
pot-env-util pot-envy`.
