# T′_k fails at n = 7: after the rotation the owner must be the terminal, not k

Workstream `proof/k4-k3-oc1` (`k4/k3_oc1.md` §12). Setting: k = 3, a ledger core, a hard perfect draft in the gap
of Theorems R1C and B\*.

**The idea tried.** Conjecture T′_k says that some rotation from an exposed agent k of a terminal t into t (a chain,
or a ring through t) has a one-absorber completion with **no owner or owner k**, B\*'s owner. kgen-n3's T1-k is its
one-terminal form along earliest-wanter chains. It holds on every hard perfect draft of every core with n ≤ 6
(338,916 at n = 6, `tprime_k_*.log`), on (P)'s whole class at n = 4 and 5, and on all earlier samples.

**Counterexample** (n = 7, m = 11; a core of `results/certs_7_11.json.gz`; found by `k4/k3oc1/te_sample.py`,
`te_sample7_11e_0.log`):

| agent | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|---|
| a > b > c | 7 > 0 > 8 | 5 > 7 > 9 | 5 > 10 > 7 | 0 > 3 > 2 | 1 > 2 > 6 | 1 > 6 > 4 | 3 > 4 > 6 |

- **The draft.** Order (2, 1, 0, 5, 6, 3, 4) gives the picks (0, 7, 5, 2, 6, 1, 3) and J = {4, 8, 9, 10}. The draft
  has no one-absorber completion, is not R1-compatible, and B\* does not apply.
- **Terminal and exposures.** The only terminal is 4, which holds its c, 6. Its exposed agents are 5 and 6, and they
  **share the pair {4, 6}**.
- **The rotations into 4.** There are exactly two, both rings with the pair arrow 4 → k:
  - k = 5: agent 5 takes {6, 4} and agent 4 receives 1;
  - k = 6: agent 6 takes {4, 6}, agent 3 receives 3 and agent 4 receives 2.
- **Who can own afterwards.** After either rotation, every one-absorber completion has absorber 3 or 4 (the
  terminal t). None has no absorber, and none has absorber k. E.g. ({0}, {7}, {5}, {2,8,9,10}, {1}, {6,4}, {3}).
- **Why owner k fails.** The other exposed agent holds its top and has the same pair, now inside k's bundle, so k's
  bundle plus any junk good threatens it. For any other owner the sharer is harmless (Lemma 4). This is B\*'s
  condition (iii) failing for every k.

**What survives.**
- T-E∃, some Rule E rotation completes with owner nobody, **e (here the terminal t)** or k, holds here. Owner e = 4
  works for both rotations. Owner t is kgen-n3's T-E owner set {none, t, k}.
- T-ω (any owner) holds as well.
- Across all n = 7 samples (30,045 hard drafts), this is the only draft where T′_k fails.

Replay (no repository code, raw EFX₀ definition, values 10 > 8 > 7): `python3 attempts/k4_k3oc1_tprime_k.py`.
