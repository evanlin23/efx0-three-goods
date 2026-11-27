# "Every earliest-wanter rotation completes" fails at n = 7

Workstream `proof/k4-k3-oc1` (`k4/k3_oc1.md` §12.1). Setting: k = 3, a ledger core, a hard perfect draft (every agent
picks, no one-absorber completion) in the gap of Theorems R1C and B\*.

**The idea tried.** Remove the choice of the rotation. Take the earliest-wanter chains of kgen-n3's Rule E
(`kgen/n3.md` §15.6 on `claude/kgen-n3`). Then claim that *every* valid Rule E rotation, from a frozen exposed agent k
into the terminal e where its chain ends, has a one-absorber completion:
- kgen-n3's **T1-E**: one terminal, any owner;
- this session's **T-E**: owner nobody, e or k.

Both hold on every gap draft with n ≤ 6. That is 122,680 one-terminal and 10,240 two-terminal drafts, all rotations
(`te_gap_*.log`, kgen-n3's §15.7).

**Counterexample** (n = 7, m = 12; a core of `results/certs_7_12.json.gz`; found by `k4/k3oc1/te_sample.py`):

| agent | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|---|
| a > b > c | 3 > 9 > 0 | 4 > 6 > 10 | 5 > 11 > 8 | 2 > 0 > 8 | 3 > 2 > 1 | 5 > 1 > 7 | 7 > 4 > 6 |

- **The draft.** Order 0, 1, …, 6 gives the picks (3, 4, 5, 2, 1, 7, 6), so J = {0, 8, 9, 10, 11}. The only terminal
  is 6, which holds its c, and nobody wants it. E_6 = {0, 1, 2, 3}. The draft is not R1-compatible, and B\* does not
  apply.
- **The failing rotation.** Rotate k = 1, whose pair {6, 10} contains Y_6. Its only chain is (1, 6), since agent 6 is
  the only other agent valuing good 4. After the rotation, J′ = {0, 8, 9, 11} and T′ = {6}, and **no one-absorber
  completion exists** (exhaustive search, any owner).
- **The repairing rotations.** The rotations of k = 0, 2, 3 along their Rule E chains (0,4,5,6), (2,5,6) and
  (3,4,5,6) each have one.

Two more one-terminal gap drafts in the same n = 7 sample fail the same way: one exposed agent's length-one chain
(k, t) fails, and longer chains repair. In the same sample "every least-ω′ rotation completes" fails once, on a
two-terminal draft covered by B\*. (`results/k4_k3oc1/te_sample7_*.log`, classified in `te_sample7_classify.log`.)

**What survives** on the n = 7 sample: 4,759 hard perfect drafts (3,103 m = 11 cores × 40 random profiles, 541 m = 12
cores × 200), every order's draft.
- **T′_k** (some rotation into a terminal completes, with owner nobody or k) has no failure.
- **"Some valid Rule E rotation completes with owner nobody, e or k"** has no failure.

So the choice of k cannot be removed: the target is the "some k" form (kgen-n3's T1-k), and the proof must say which
k to rotate.

Replay (no repository code, raw EFX₀ definition, explicit values 10 > 8 > 7):
`python3 attempts/k4_k3oc1_every_k.py`.
