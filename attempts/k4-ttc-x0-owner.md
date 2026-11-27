# Attempt: after the chain, its start x₀ is the owner (LB⁺'s Theorem B shape at k = 4)

Workstream `proof/k4-ttc` (`k4/ttc.md` §8). Status: **fails** at n = 3, m = 7 (brute-force replay below). The
head-owner form OC₁-H fails too, at n = 6 (`attempts/k4-ttc-head-owner.md`). What survives is the endpoint form
OC₁-E: x₀ or the head absorbs.

## The idea

At k = 3, LB⁺'s Theorem B (`proofs/lb_last_step.md` §5) runs as follows:
- Theorem A's owner r fails in the bad case;
- the frozen leader k rotates its top along a need chain k = x₀, …, x_t = r;
- k takes {b_k, c_k};
- after the rotation **k is the owner** (or no owner is needed).

The natural k = 4 analogue of OC₁ asks for the same owner: from every order, the picks have a one-absorber
completion, or some improving chain x₀, …, x_t has a one-absorber completion whose absorber is x₀.

## What happens

`k4/ttc/head_owner.py` (logs `results/k4_ttc/head_owner.log`, `head_owner_all.log`). Among the distinct hard starts
(picks without a one-absorber completion), x₀ can own after some repairing chain on all of them except one: dich3,
the n = 3 instance that refutes §29's strict dichotomy. That start appears in the logged profiles too, as
1,363 of 1,364. The head x_t can own on every one of these starts. That was Conjecture OC₁-H, later refuted at
n = 6, where x₀ is the one that works.

## Smallest failing configuration

dich3 (n = 3, m = 7; `k4/sdc/refute_dich.py`):
- agent 0 values goods 0, 2, 4, 3 at 5, 10, 1, 12; agent 1 values 6, 3, 1 at 10, 12, 11; agent 2 values 1, 2, 0, 5
  at 11, 8, 6, 1;
- order (0, 2, 1), picks (3, 6, 1).

By brute force from the raw EFX₀ definition:
- the picks have no one-absorber completion;
- no improving chain's result has a one-absorber completion owned by its x₀;
- two have one owned by the head. In the first, agent 0 trades its top 3 for {0, 2}, and agent 1, the head, takes 3
  and absorbs {4, 5, 6}.

Reproduce: `python3 k4/ttc/repro_attempts.py` (part (e); log `results/k4_ttc/repro_attempts.log`).

## Lesson

At k = 3 the owner moves from r to k after the rotation. At k = 4 neither endpoint alone always works:
- here only the head r can own;
- at n = 6 only x₀ can, apart from an agent off the chain (`attempts/k4-ttc-head-owner.md`).

A Theorem B₄ in LB⁺'s format has to allow both of its owners: Theorem A's r and Theorem B's k.
