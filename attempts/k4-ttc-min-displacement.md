# Attempt: every closest dominating EFX₀ allocation is reached by one chain (k = 4)

Workstream `proof/k4-ttc` (`k4/ttc.md` §7). Status: the "every" form **fails** at n = 4 (brute-force replay below).
The "some" form survives on all data.

## The idea

In a housing market, moving from the endowment to an individually rational target decomposes into trading cycles.
Here the endowment is the picks Y of an order, and the target is a complete EFX₀ allocation X that value-dominates
them (v_i(X_i) ≥ v_i(Y_i) for all i; MD, `k4/sdc.md` §28).
- An agent is *displaced* if its pick is not in its bundle.
- X is *one-path* if the displaced agents can be listed x₀, …, x_t so that Y_{x_{i−1}} ∈ X_{x_i} for 1 ≤ i ≤ t,
  while the pick of x_t lies anywhere (it becomes junk). That is the shape of one improving chain followed by a free
  completion.

Conjecture MDP ("minimal displacement is a path"), every form: every dominating EFX₀ allocation with the fewest
displaced agents is one-path. Together with MD this would give Conjecture OC (one chain, free completion) by an
extremal choice, with no rule for choosing the chain.

## What happens

`k4/ttc/displace.py` (SAT on sdclib's encoding; the distinct placements of the displaced picks among the minimal
allocations are enumerated); logs `results/k4_ttc/displace.log`, `displace_all.log`.

| data (distinct hard starts) | every minimal allocation one-path | some minimal allocation one-path |
|---|---|---|
| special (16) | 16 | 16 |
| screen (194) | 194 | 194 |
| suite (196) | 196 | 196 |
| logged hard profiles (1,364) | 1,364 | 1,364 |
| random cores n ≤ 3 (293) | 293 | 293 |
| random cores n = 4 (215) | **214** | 215 |
| random cores n = 5 (30) | **29** | 30 |

## Smallest failing configuration

r617 (n = 4, m = 8), from the random n = 4 cores:
- sets [[0, 2, 6, 7], [1, 3, 6, 7], [3, 4, 5, 7], [4, 5, 7]], values [[5, 3, 6, 7], [6, 7, 3, 5], [5, 3, 6, 7],
  [2, 4, 3]];
- picks (7, 3, 5, 4).

By brute force from the raw EFX₀ definition, the fewest displaced agents is 2, attained by 19 allocations. One of
them is not one-path: X = ({0, 2}, {1, 6}, {5, 3}, {4, 7}). Agents 0 and 1 each give up their pick for junk (worth
11 > 7 and 9 > 7 to them), and the picks land with the agents 2 and 3, who keep their own picks. These are two
separate pool swaps, not one path. The other 18 minimal allocations are one-path.

Reproduce: `python3 k4/ttc/repro_attempts.py` (part (d); log `results/k4_ttc/repro_attempts.log`). Part (c) of the
same script is a brute-force cross-check that every minimal allocation is one-path on rt4-n5m10-chain, where a first
version of `displace.py` with a wrong one-path test reported a counterexample. That version required in-degree at
most 1 before setting aside the end's pick.

## What survives

The some-form, **MDP∃**: among the dominating EFX₀ allocations with the fewest displaced agents, some allocation is
one-path. It holds on every start in the table. Together with MD it implies OC, up to strictness of the chain
agents' gains under ties; nothing known implies it. Counting displaced agents alone does not force one path. A proof needs a
second extremal criterion that rules out two independent pool swaps, such as the fewest junk goods moved or the
least total gain, both untested.
