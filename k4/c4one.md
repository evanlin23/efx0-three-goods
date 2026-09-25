# Conjecture C₄¹: at most one 4-good agent

Workstream `proof/k4-c4one` (ledger row K4.C4.1, open item 18). Builds on `k4/c4.md` (PR #33, under review): notation,
Lemma E, Theorems A₄, B₄, B₄ʷ, A₄ᵀ, A₄⁺ and the conventions of its §1.1. Throughout, q is the unique 4-good agent.

## Status

- **C₄¹ as stated in `k4/c4.md` §6.2 is false** (§2): with at most one 4-good agent, one rotation is not enough at
  n = 5, for every run and even for index insertion, under every convention (smallest: n = 5, m = 9;
  `attempts/k4-c4one-one-rotation.md`). Two rotations suffice on those cores.
- **The existence form C₄¹∃** (§1) is open. It is what TARGET₄ for these instances needs, and LB₄ (a search over
  insertion sequences) never fails on the certified cores (K4.LB4.E).
- **Where the theorems of `k4/c4.md` leave gaps with one 4-good agent** (§3): measured by case on every run with
  n ≤ 5, with the repairs that work in each case.

## 1. Statements

**C₄¹∃ (existence form).** For every strict profile of every k = 4 core in which at most one agent has four relevant
goods, there is a valid pre-allocation with a completion satisfying (OC₄) in which frozen agents hold exactly their
bases and only the owner's bundle has more than two goods. This is PR #35's `EFX.LB4R.TheoremC4exists` restricted to
such cores. With Theorem 1′₄ (K4.LB4.S), K4.CORE (whose peeling never adds a 4-good agent) and K4.TIE it gives
**TARGET₄ for every instance in which at most one agent values four goods**.

**C₄¹ (LB₄ʳ form, `k4/c4.md` §6.2; false).** For every run of Phase 1 on such a core: after envy-free upgrades, some
free agent is a valid owner with its needs from its base, or one rotation (any frozen k, any need chain, any
O ⊆ R_k ∩ (J ∪ B_{x_t})) gives a valid pre-allocation that needs no owner or has a valid owner.

## 2. One rotation is not enough (`attempts/k4-c4one-one-rotation.md`)

On the 1,735 certified cores with n = 5 and one 4-good agent (`results/k4_certs_5_n4_1.json.gz`, every strict profile,
every insertion sequence; `results/k4_c4one_n5_lb4.log`):

| search (`lb4.c`) | failing (run, profile) pairs | cores |
|---|---|---|
| C₄¹'s own: `-i1 -u2 -o0 -r1 -w0 -c0` | 140 | 5 (m = 8, 9, 10) |
| owner's needs from its bundle (a rotated one-good base gets a slot, as in PR #35): `-w1` | 8 | 2 (m = 8, 9) |
| all three policies, chains to upgraded agents: `-i1 -u3 -o0 -r1 -w1 -c1` | 6 | 2 |
| the same with index insertion, `-i0` | 4 | 1 (m = 9) |
| two rotations, `-i1 -u2 -o0 -r2 -w1 -c1` (on the 5 cores) | 0 | |

The independent tracer (`k4/c4tools/c4trace.py`) confirms the index-order failure at m = 9 under each policy and all
four owner/slot conventions, and finds two nested rotations that work; brute force confirms K4.D on that profile.
The mechanism is two agents to protect and one slot, both for owner r and for owner q (see the attempt file).

So the number of rotations LB₄ʳ needs is not 1 even with one 4-good agent. Whether it is bounded (by 2) for one
4-good agent is open; unlike H_t (`k4/c4.md` §7), whose gadgets have three 4-good agents each, a single 4-good agent
cannot be repeated along a chain.

## 3. The runs the theorems of `k4/c4.md` leave open, by case (`results/k4_c4one_classes.log`)

`k4/c4check.c -X -Y` (driver `k4/c4one_run.py`) classifies every run with ω ≥ 1 that §2–§4c of `k4/c4.md` do not
prove, and tests repairs: owner r; another owner; owner q; rotating q along a need chain to any end t, q taking all its
goods in J ∪ B_t, then owner q; owner t; `lb4.c`'s single-rotation search. Cases: (G2) LB⁺'s bad case with r = q
exposed after the rotation; q frozen and exposed with no need chain to r, or with (i)/(ii) of B₄ʷ failing; q free and
exposed with (Tc) or (Tb) of A₄ᵀ. "q first" means the first insertion step picks q.

- n ≤ 4: every unproved run has a repair among these (as §6.2 of `k4/c4.md` says). With q first, (G2), (Tc) and
  failures of B₄ʷ's (i)/(ii) do not occur; (Tb) is always repaired by owner q (10,044 runs); the rest is "q frozen, no
  chain to r", where rotating q, owner t or owner r cover all but 1,104 runs (repaired by another owner or another
  rotation).
- n = 5: the 140 failures of §2 are all in case (Tb) with q not first, where nothing among these repairs works. With q
  first, owner q still repairs every (Tb) run (390,432), and every run has a repair.

The existence form can choose the insertion sequence (`k4/c4one_tau.py`, `results/k4_c4one_tau.log`: `k4/c4check.c
-X -P`, where a run counts as a success when the theorems of `k4/c4.md` prove it, with `-i2` searching the insertion
sequences). With q first (`-Q`), no choice of the later insertion steps gives a proved run on 260 profiles (n = 3) and
10,786 (n = 4); with every insertion sequence allowed, on 24 profiles at n = 3 and none at n = 4. So a proof of C₄¹∃ along these
lines needs new theorems for at least the (Tb) and "no chain" cases, not only a choice of τ.
