# Pareto-type potentials over valid pre-allocations (k = 4)

Workstream `proof/k4-c4x` (`k4/c4x.md`). Approach: take P ∈ 𝒫 (valid pre-allocations, bases of at most two goods,
value-based needs) maximizing a potential that increases with every agent's base value (Σℓ, Σ 2^ℓ, leximax, leximin,
Σ v with the type representatives, or plain Pareto-maximality), and show that it is completable. At k = 3 this works:
Theorem K3 (`k4/c4x.md` §3; every Pareto-maximum is completable, checked on every k = 3 core with n ≤ 6). At k = 4 it
does not, not even in the existence form for most of them.

**Exhaustive results** (every strict profile of every core; `results/k4_c4x_n3_pareto.log`, and for the some-form of
Pareto-maximality `results/k4_c4x_n3_pareto_some.log`): at n = 2 every maximum of
every one of these potentials is completable. At n = 3 (299,837,376 profiles), profiles with a non-completable maximum
("every" fails) / with no completable maximum ("some" fails):

| potential | every fails | some fails |
|---|---|---|
| Σℓ | 85,588 | 128 |
| Σ 2^ℓ | 172,872 | 133,960 |
| leximax | 175,304 | 136,392 |
| leximin | 38,016 | 128 |
| Σ v (type representatives) | 87,700 | 128 |
| Pareto-maximality | 1,149,696 | 128 |
| (Σℓ over 3-good agents, Σℓ over 4-good agents) | 87,640 | 128 |

The some-form of Pareto-maximality ("no Pareto-maximum is completable") fails on the same 128 profiles as Σℓ's: every
Σℓ-maximum is Pareto-maximal, so it can fail only where Σℓ's does, and it does on all 128 (all on pure cores, like
instance 3 below).

With at most one 4-good agent, leximin and "3-good agents first" have no failure (n ≤ 4 exhaustive; `k4/c4x.md` §4); all
their failures have two or three 4-good agents. Pareto-maximality fails already with one (the first instance below).

**Why.** (G1) of `k4/c4x.md` §5: a 4-good agent of type a > b + c has no base of at most two goods worth more than its
top, so at a Pareto-maximum it can hold its top, frozen, with all three lower goods in the junk, where every owner's
bundle threatens it; the potential rewards exactly the pre-allocation that blocks the rotation which would help. In the
first instance below the Pareto-maximum {5} | {1} | {3} lets the 4-good agent keep its top, while the completable
pre-allocations give that top to agent 1, for which it is also the top, and lower the 4-good agent: an improvement for
the 3-good agents that costs the 4-good one, which is what "3-good agents first" (§4) allows and Pareto-maximality does
not. With several 4-good agents no order of this kind works, and in the pure core of instance 3 no maximum of Σℓ or
leximin, and no Pareto-maximum, is completable. (Compare the dead ends of `k4/gm4.md` §2.4 for Σℓ and of
`k4/local_search4.md` Prop. 7 for leximin, in the larger space of junk-free EFX₀ partial allocations; both are in 𝒫 and
are stuck there too, `k4/c4x.c` on their profiles.)

## Smallest failing configurations (checked by both implementations)

1. Σℓ every-form; Σ 2^ℓ, leximax some-form; Pareto-maximality: **n = 3, m = 6** (smallest n and m; exhaustive), one
   4-good agent: agents 0: goods 0, 2, 4, 5 with values 2, 3, 4, 8 (a > b + c); 1: goods 1, 3, 5; 2: goods 3, 4, 5. With
   values (2, 3, 4) for agent 1 and (3, 2, 4) for agent 2, the Pareto-maximum {5} | {1} | {3}, J = {0, 2, 4} is stuck
   (agent 0's b, c, d are all in the owner's bundle), and the Σ 2^ℓ- and leximax-maxima are stuck too; with values
   (2, 4, 3) and (4, 2, 3), a Σℓ-maximum is stuck.
2. leximin every-form: **n = 3, m = 8** (smallest m at n = 3; exhaustive), two 4-good agents: agents 0: goods 0, 2, 5, 6
   with values 2, 3, 8, 4; 1: goods 1, 4, 5, 7 with values 3, 4, 8, 2; 2: goods 3, 6, 7 with values 3, 2, 4.
3. leximin, Σℓ and Pareto-maximality some-form: **n = 3, m = 8** (smallest m; exhaustive), pure: agents' goods {0, 2, 6, 7}, {1, 4, 6, 7},
   {3, 5, 6, 7}, each with values 3, 4, 2, 8 (good 7 is everyone's top, a > b + c for everyone): no maximum is
   completable, and neither is any Pareto-maximum.
4. (Σℓ over 3-good agents, Σℓ over 4-good agents) every-form: **n = 3, m = 6**, two 4-good agents: agents 0: goods 0, 1,
   2, 5 with values 2, 3, 4, 8; 1: goods 2, 3, 4, 5 with values 1, 4, 8, 6; 2: goods 3, 4, 5 with values 2, 4, 3.

Replay: `python3 attempts/k4_c4x_attempts.py` (both `k4/c4x.c` and the independent `k4/c4x_check.py`; prints
"confirmed" for each).
