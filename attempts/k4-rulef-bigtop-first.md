# A big-top agent first, else index order (k4/rulef.md §5.2)

**Idea.** A static first-agent rule, read off the profile without running Phase 1: insert first the first *big-top*
agent in index order (four goods, top worth more than the next two together, a > b + c), and use index order if
there is none. Motivation: on the n = 3 profiles where index order is not certified by Lemma K, every sampled
profile with a big-top agent had its first big-top agent in class K0 or K1 (`results/k4_rulef/features_n3.log`), and a
big-top agent is the type whose loss of its top no pair compensates (`k4/c4x.md` (G1), BT1 of `k4/hall_bt.md`). The
same rule with a second static fallback (an agent whose least good is another agent's top; `-Q1`) was also tried.

**Where it breaks.** The big-top part survives: whenever some agent is big-top, the first one is in class K0 or K1
on every profile of the classes run (`k4/rulef.c -A42 -Q2`, which falls back to rule RK when there is no big-top
agent: no profile open; `results/k4_rulef/btrk_*.log`). The fallback does not: without a big-top agent, index order
fails with one rotation on 9,632 profiles at n = 3 (all with m = 6 and no big-top agent; `-Q0` and `-Q1` fail on the
same 9,632), while rule RK (k4/rulef.md §4) needs at most one rotation there. Without a big-top agent the working first
agent is one whose top is also another agent's top, but not the one with two private goods (`k4/rulef.md` §5.2); a
rule built on that (`-Q3`) is index-dependent like every static rule, and on relabelings of H_t (no big-top agent) a
static rule must find gadget 1, which only the structure of the cascade identifies (Proposition H″).

**Smallest failing configuration** (n = 3, m = 6; none at n = 2 or at n = 3 with m ≤ 5): agents {0, 1, 4, 5},
{2, 3, 4, 5}, {2, 3, 4, 5} with values (1, 4, 6, 8), (3, 5, 7, 6), (2, 4, 5, 8); no big-top agent, so agent 0 first,
and LB₄ʳ(τ₀) needs two rotations (`k4/rulef.c` and PR #33's independent model, `k4/c4_verify_H/lb4r.py`); rule RK
takes agent 2 (class K1, one rotation). Brute force finds EFX₀ allocations with at most one large bundle.

Reproduce: `python3 attempts/k4_rulef_attempts.py` (part 3; `results/k4_rulef/attempts.log`); the counts:
`python3 k4/rulef_run.py results/k4_certs_3.json.gz -A42 -Q0 -r1`.
