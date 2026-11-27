# Referee spot check: Theorem N2's type reduction (`k4/haxell.md` §6, branch `claude/k4-haxell` at `158b4d9`)

Referee: `proof/k4-referee`, 2026-11-27, coordinator's queue (burst 5, item 5).
- Read: `k4/haxell.md` §6 in full, i.e. the move class of W^sub (T, S, R), Theorem N2, Lemmas TD and OR, and how the
  check is said to be complete.
- Check: `k4/referee/haxell_n2_ref.py`, run by `haxell_n2_ref_runs.sh`, log `results/k4_referee/haxell_n2_ref.log`.
  It is my own code, and nothing from `k4/haxell/` was run or imported.

## Verdict: the type reduction is CORRECT

Theorem N2 is a computer-verified statement. Its completeness rests on two written lemmas, both of which are correct.

**Lemma TD.**
- (a) v_i(X_j ∖ h) ≤ v_i(X_i) compares A = (X_j ∖ h) ∩ R_i with B = X_i ∩ R_i, which are disjoint:
  - if A = ∅, it holds;
  - if A ≠ ∅ = B, it fails, since values are positive on R_i;
  - otherwise the strict type decides it, and equality never occurs.
- (b) v_i(Y_i) − v_i(X_i) = v_i(Y_i ∖ X_i) − v_i(X_i ∖ Y_i), the same three cases.
- The theorem's strictness ("no two distinct sets have equal value") is equivalent to "no two disjoint nonempty sets",
  since S, T with v(S) = v(T) give v(S ∖ T) = v(T ∖ S).
- So partial EFX₀, the pool-shrinking alternative and the both-gain swap all depend only on the types, and moves do not
  depend on values. W^sub and L^sub follow, since a both-gain swap raises welfare and leximin.

**Lemma OR.**
- Relabeling goods within a class (same set of valuers) is an isomorphism.
- The designated agent's values on a class are distinct, so the stabilizer is trivial, and exactly one relabeling sorts
  them increasingly.
- So the canonical profiles are one per orbit.

## Computation (evidence)

| check | result |
|---|---|
| **Class count.** Shapes (a, s, b) with 1 ≤ a + s, s + b ≤ 4. Canonical profiles: t(a+s)/(a! s!) · t(s+b)/b!, with t(d) = 1, 1, 2, 12, 336 strict labeled types (K4.OT) | **46 shapes, 45,999 classes**, exactly the note's count. So the enumeration is complete under Lemma OR |
| Strict types realized by random values on d = 1–4 goods | 1, 2, 12, 336, as K4.OT says |
| **Lemma TD** on 1,500 random instances (n = 2, m ≤ 6, k ≤ 4), each realized twice with the same strict types: partial EFX₀ status of every partial allocation, and the improvement relation | 332,442 allocations and 600,000 pairs, **0 mismatches**. Control (one agent's type changed): mismatches in 1,081 of 1,082 instances |
| **Theorem N2 itself** on 4,300 random strict instances (n = 2, every good valued, 1 ≤ \|R_i\| ≤ 4, m ≤ 8), at every partial EFX₀ state with a nonempty pool. My own generator of the T/S/R moves: some composite of ≤ 2 moves shrinks the pool, or one A–B swap makes both gain | 687,499 states, **0 failures** (657,716 by one move, 31,783 needing two). No state needed the swap alternative. The note finds 20 such states in 6.6 million, so random sampling is not expected to hit one |

## For the coordinator

The type reduction behind Theorem N2 is sound and its class enumeration is complete. N2 stays computer-verified: one
C implementation over every class, with an independent Python re-run of every class (the note's
`n2types_k4_fullcheck.log`, which I did not re-run). My random check of the statement found no failure.
