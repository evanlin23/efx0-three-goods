# Other spaces of pre-allocations for the extremal principle (k = 4)

Workstream `proof/k4-c4x` (`k4/c4x.md`). The space 𝒫 of `k4/c4x.md` §1 has bases of at most two goods, value-based
needs, and completions with the owner's needs taken from its bundle (as in `lean/EFX/PreAllocK.lean`'s
`SoundCompletion`). Three natural changes to that space were tried first. Each fails, already in the weakest sense
tested, and each failure explains one ingredient of 𝒫.

1. **The owner's needs from its base** (as at k = 3, and as in LB₄'s `-w0`): then some profiles have *no* completable
   pre-allocation at all, already at n = 2 (720 of 189,216 profiles; `k4/c4x.c -w0 -a`). The completion must be allowed
   to use a large owner bundle that is worth more than the goods the owner needed, which unfreezes their holders and
   frees their slots. (`k4/lb4.md` §3 found the same need for LB₄, first at n = 4; in 𝒫 it appears at n = 2 because 𝒫
   has no owner bases of three or more goods.)
2. **Only envy-free two-good bases** (v_i(B) ≥ v_i(R_i ∖ B), LB₄ʳ's second upgrade policy): then some profiles have no
   completable pre-allocation at all, at n = 3 (50 of 1,020,000 sampled profiles; none at n = 2, exhaustive). The
   solutions need a 4-good agent holding a pair that is not envy-free.
3. **One base of three or four goods allowed** (its agent then has to be the owner; LB₄ʳ's rotated owner): with the
   fewest frozen agents first, even the some-form fails at n = 3, m = 5 (949 of 1,020,000 sampled profiles; none at
   n = 2, exhaustive). A large base lowers the frozen count (the owner needs nothing), but the minimizers are then
   not completable; and the Pareto-type potentials get much worse in this space (leximin: 1,080 profiles with a
   non-completable maximum at n = 3 with one 4-good agent, against 0 in 𝒫), because a base of all four goods has the
   highest level and dominates the maxima.

## Smallest failing configurations (checked by both implementations)

1. Owner's needs from its base, no completable pre-allocation: **n = 2, m = 5** (smallest n): agents 0: goods 0, 2, 3, 4
   with values 2, 3, 4, 8; 1: goods 1, 2, 3, 4 with values 2, 3, 4, 8 (8 valid pre-allocations, none completable with
   the owner's needs from its base; with them from its bundle, some are).
2. Envy-free two-good bases only, no completable pre-allocation: **n = 3, m = 6** (smallest n; found by sampling, so m
   is the smallest found): agents 0: goods 0, 3, 4, 5 with values 3, 5, 6, 7; 1: goods 1, 3, 4, 5 with values 4, 6, 5, 8;
   2: goods 2, 3, 4, 5 with values 5, 4, 6, 8.
3. Bases of three or four goods allowed, −frozen, some-form: **n = 3, m = 5** (smallest n): agents 0: goods 0, 1, 2, 4
   with values 2, 10, 6, 3; 1: goods 1, 3, 4 with values 4, 3, 2; 2: goods 2, 3, 4 with values 3, 4, 2.

Replay: `python3 attempts/k4_c4x_attempts.py` (`k4/c4x.c` with `-w0`, `-E`, `-3`, and the independent
`k4/c4x_check.py` with `w0`, `ef`, `big`; prints "confirmed" for each).
