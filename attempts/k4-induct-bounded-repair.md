# Attempt: insertion lemma with bounded repair (k = 4 induction on the number of 4-good agents)

Workstream `proof/k4-induct` (`k4/induct.md` §2). Failed; kept for the record.

**Idea.** Step j → j + 1 of an induction on the number j of 4-good agents: for some 4-good agent w and some d ∈ R_w,
*every* EFX₀ allocation X′ of I − d (d deleted) can be turned into an EFX₀ allocation of I by placing d and changing the
owner of at most ρ other goods, for a constant ρ.

**Result.** False for every ρ ≤ 3, and the least ρ that works (for the best (w, d)) grows with n in every test:
at most 2 for n = 2 (all 189,216 strict profiles; 96 need 2), 3 for n = 3 and n = 4 (samples), 4 for n = 5 (samples).
`k4/induct.c` computes r(X′) exactly (direct search to radius 3, then a scan of every EFX₀ allocation of I);
`results/k4_induct_n2.log`, `results/k4_induct_n3.log`, `results/k4_induct_n4.log`, `results/k4_induct_n5.log`.

**Why.** The induction hypothesis hands over an arbitrary X′. Some X′ are rigid: w is envied, and every bundle into
which d could go is envied by an agent that sees d as a worthless extra good (Lemmas 2 and 3 of `k4/induct.md`), so the
fix has to move whole bundles. Choosing X′ (Lemma 2: w unenvied) removes the need for any repair when d is private to w.

**Smallest failing configurations** (agent i's goods and its integer values on them, a strict balanced type):
- ρ = 0 (n = 2, m = 4): {0, 1, 2, 3} (2, 3, 8, 4); {1, 2, 3} (2, 4, 3). For d = 0, 1, 2, 3 the worst X′ needs 3, 2, 1, 2.
- ρ = 1 (n = 2, m = 5): {0, 2, 3, 4} (4, 10, 8, 3); {1, 2, 3, 4} (4, 8, 10, 3). Every (w, d): 2.
- ρ = 2 (n = 3, m = 5): {0, 1, 3, 4} (5, 3, 7, 6); {2, 3, 4} (2, 3, 4); {2, 3, 4} (2, 3, 4). Every d: 3.
- ρ = 3 (n = 5, m = 6, one 4-good agent): {0, 3, 4, 5} (10, 4, 3, 8); {1, 4, 5} (4, 2, 3); {2, 4, 5} (2, 3, 4);
  {3, 4, 5} (3, 4, 2); {3, 4, 5} (4, 3, 2). Every d: 4. (Its private good 0 inserts with no repair into every X′ that
  leaves agent 0 unenvied, and such X′ exist.)

Reproduce (independent brute force, no code shared with `k4/induct.c`):
`python3 attempts/k4_induct_attempts.py G-r0 G-r1 G-r2 G-r3 ctrl-private` (log: `results/k4_induct_attempts.log`).
