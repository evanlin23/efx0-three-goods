# Choosing the insertion sequence so that the theorems cover the run, with several 4-good agents (k4/adaptive.md §6)

**Idea.** #37 (`k4/c4one.md` §6) found that with one 4-good agent some insertion sequence, even index order with one
step changed, gives a run covered by the theorems of `k4/c4.md` and `k4/c4one.md` (after envy-free upgrades, ω ≤ 0 or
one of A₄, B₄, B₄ʷ, A₄ᵀ, A₄⁺, A₄⁺(o) applies), which with an exchange lemma would prove LB₄ʳ with one rotation. The
same choice rule would be a proof-backed adaptive rule for all cores (`k4/adaptive.c -A20`, `-A21`, `-A22`).

**Where it breaks.** With two or more 4-good agents some profiles have no covered insertion sequence at all: 12,420 of
the 189,216 profiles at n = 2, 7,503,039 at n = 3; none at n = 4 with one 4-good agent (as #37 found)
(`results/k4_adaptive_crosscheck.log`: the port agrees with #37's `k4/c4check.c` on each count). LB₄ʳ with rule F
solves each of them, at n ≤ 3 without rotation, mostly with need-shrinking upgrades (`results/k4_adaptive_uncovered.log`),
which the theorems do not treat.

**Smallest failing configuration** (n = 2, m = 4). Both agents have goods {0, 1, 2, 3} and values (2, 4, 5, 8). Either
insertion order: the first agent takes 3, the second takes 2 and needs 3, so the first is frozen, exposed to
W = {0, 1, 2} (5 + 4 > 8), and ω = 1; there is no envy-free upgrade ({2, 1} = 9 < 10). The only rotation makes the
4-good r exposed, so B₄ʷ does not apply, and A₄⁺ counts one good against no slot. LB₄ʳ's first policy upgrades the
second agent to {2, 1} (need-shrinking: 8 < 5 + 4); then nobody is frozen, ω = 0, no owner is needed, and the
allocation {3, 0} | {2, 1} is EFX₀.

Reproduce: `python3 attempts/k4_adaptive_attempts.py` (last line: no covered sequence, rule F needs no rotation);
the counts: `C4CHECK_BIN=... python3 k4/adaptive_crosscheck.py results/k4_certs_2.json.gz`.
