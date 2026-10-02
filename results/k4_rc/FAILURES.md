# DL_RC failures (compute/k4-rc)

EVIDENCE: these are the outputs of `k4/dlrc.c` (sha256 `f1cf4cc169a347625e5a84bd9c7a8c218f791de6e2a7ce466f59ce357000b1f7`). Every failure is
confirmed by two further implementations, written independently of dlrc.c:
- `k4/dlrc_ref.py`, built on `dl134_xcheck.py` / `c4x_check.py`;
- `k4/dlrt4_ref.py`, built on model.py and dl2_relations.py. At f = 1 a T3c move and a T4 move both need a second frozen agent, so R_C = RT4 there, and dlrt4_ref.py's verdict is a third verdict on DL_RC.

Conjecture DL_RC is the statement of `k4/dlrc.c`'s header. At f ≥ 1, every min-frozen P with def(P) > 0 must have an R_C neighbour P′ with def(P′) < def(P), where R_C = T1 ∪ T2 ∪ T3⁺ ∪ T4. LEDGER.md is not edited here.

**Status: DL_RC fails in two pure n = 5 cores.**

| core (pos in `k4_certs_5_pure`) | m | f | profiles | failing states | def | nearest distance k | nearest better states |
|---|---:|---:|---:|---:|---:|---:|---|
| 4604 | 13 | 1 | 369 | 369 | 1 | 3 | role swap, one helper that grows |
| 4515 | 12 | 2 | 1,076 | 4,304 | 1 | 4 | role swap with two helpers |

- At core 4604 it is the same state in every profile.
- At core 4515 there are four states per profile, which differ only in agent 3's base.
- Section 1 below covers core 4604, section 2 core 4515. **DL on the key graph holds at all of them.** These states are also DL_RT4 failures of a new kind: they are at f = 1 (the known ones were at f = 3) and are not chain states. DL_RC fails nowhere else in the inputs of the n = 5 failures (task (c)), or anywhere else the hunt went so far (SUMMARY.md).

## How it was found and confirmed

- **Found by:** the hunt `python3 k4/dlrc_hunt.py ranked_pure ranked results/k4_certs_5_pure.json.gz ... --top=200 --steps=800 --jobs=4 --seed=4` (`k4/dlrc_hunt_runs.sh`, log `hunt_ranked_pure.log`). Climb unit `{"file": "k4_certs_5_pure.json.gz", "pos": 4604}` printed every profile it met with a DL_RC failure ("# DL_RC FAILS"). The dump `dump_hunt_ranked_pure.jsonl.gz` holds those profiles with dlrc.c's "D" records.
- **More failing profiles:** 12 climbs from the first failing profiles (run `core4604`, log `hunt_core4604.log`) found 324 more. `rc_fail_all_inst.json` holds all 369 distinct failing profiles found by the hunt.
- **Confirmation of all 369:**
  - `ref_rc_fail_all.log`: dlrc_ref.py finds 16,605 def > 0 states, all at f = 1. DL_RC fails at 369 of them, the key form at 0. There are 0 mismatches with dlrc.c on every field, and 0 with dlrt4.c and with the -DBIGPP=0 build.
  - `ref_rt4_rc_fail_all.log`: dlrt4_ref.py finds 369 DL_RT4 failures at f ≥ 1, with 0 mismatches.
  - `run_rc_fail_all.log`, `dump_rc_fail_all.jsonl.gz`: dlrc.c's records.
  - `rc_failures_n5_all.tsv`, `rc_failures_n5_all_inst.json`, `rc_failures_n5_all.log`: the listing, as below.
- **The first 45** (as found by `ranked_pure`), with their own logs:
  - `rc_fail_hunt_ranked_pure_inst.json`: the 45 distinct failing profiles, as an inst list.
  - `ref_rc_fail_hunt_ranked_pure.log`: dlrc_ref.py on them. It finds 2,025 def > 0 states, all at f = 1. DL_RT4 and DL_RC fail at 45 of them, the key form at 0. There are 0 mismatches with dlrc.c on every field and on the H lines, and 0 with dlrt4.c's K / L lines, tables and S lines. The -DBIGPP=0 build also agrees.
  - `ref_rt4_rc_fail_hunt_ranked_pure.log`: dlrt4_ref.py (model.py + dl2_relations.py + its own T4) on them. It finds DL_RT4 failures at f ≥ 1: 45, with 0 mismatches and 0 assertions.
  - `run_rc_fail_hunt_ranked_pure.log` and `dump_rc_fail_hunt_ranked_pure.jsonl.gz`: `dlrc_run.py inst` on them. Every failing state is there with every better min-frozen state and its shape.
- **Listing:** `k4/dlrc_failures.py` (log `rc_failures_n5.log`) writes:
  - `rc_failures_n5.tsv`: one line per failing state;
  - `rc_failures_n5_inst.json`: one record per profile in `k4/suite/instances` form, with `fail_bases`.
- **Key-form witnesses:** `rc_failures_n5_keyform.log` (recomputed with dlrc_ref.py's model for the first profile).

## 1. The failure at core 4604 (m = 13, f = 1)

Core pos 4604 (idx 58) of `results/k4_certs_5_pure.json.gz`, m = 13, sets
`[[0,2,9,11],[1,6,10,12],[3,7,11,12],[4,8,11,12],[5,9,10,12]]`. The simplest profile found (largest value 8, value sum 97) is profile (44, 118, 8, 8, 158), as indices into `check4.core_domains(sets, 13, False)`. Its values, in the order of each agent's set:

| agent | goods | values |
|---|---|---|
| 0 | 0, 2, 9, 11 | 3, 5, 6, 7 |
| 1 | 1, 6, 10, 12 | 6, 5, 4, 8 |
| 2 | 3, 7, 11, 12 | 2, 3, 8, 4 (big-top) |
| 3 | 4, 8, 11, 12 | 2, 3, 8, 4 (big-top) |
| 4 | 5, 9, 10, 12 | 6, 4, 1, 8 |

- The min-frozen class has 129 states, all with f = 1, and σ = 2n − m = −3. It has three keys:
  - agent 0, 2 or 3 frozen on good 11, with NA = {11};
  - def* is 1 for agent 0's key (35 states, **all with def = 1**) and −1 for the two others (47 states each).
- **The failing state** is P = ({11}, {12}, {3,7}, {4,8}, {5,9}):
  - agent 0 is frozen (agents 2 and 3 need 11);
  - NA = {11}, J = {0, 1, 2, 6, 10};
  - def(P) = 1, Pareto signature G, D2.
- P has 84 better min-frozen states, all with def ≤ 0 and NA = {11}. The nearest is at distance k = 3.
- **No T1, T2, T3 or T4 move improves P, and there is no T3c move** (there is no second frozen agent).
- **Every better state is a role swap:** agent 0 releases 11 and takes goods of J or 9, and agent 2 or agent 3 takes {11} and becomes frozen. The free agents then change in a way T3 does not allow. Shapes are (|U|, |Z|, |W|, |Y|), from dlrc.c's "better" lists:
  - **6 nearest states (k = 3), shape (1, 1, 0, 1).** The one helper, agent 1, *grows* its base {12} by a junk good ({1,12}, {6,12} or {10,12}) instead of giving one up. T3 requires the helper to give up a good. Example: P′ = ({0,2}, {1,12}, {3,7}, {11}, {5,9}), def 0; here x = 0 → {0,2}, z = 3 → {11}, helper 1 → {1,12}.
  - **78 states at distance 4, shape (1, 1, 0, 2):** role swaps with **two** helpers, agents 1 and 4. Example: P′ = ({9}, {1,6}, {3,7}, {11}, {12}), def −1; here x = 0 → {9}, z = 3 → {11}, agent 4 → {12}, agent 1 → {1,6}.
  - In all 45 failing states, the 270 nearest better states have shape (1, 1, 0, 1) and the 3,510 others shape (1, 1, 0, 2). None is an R_C move.
- **Moves from P that do exist:** P has 8 T3⁺ moves (W = ∅, i.e. T3), and every one leads to a state with def 1.
- **The key form holds** (def*(κ(P)) = 1, kmin = −1):
  - another state of P's key, ({11}, {6,10}, {12}, {4,8}, {5,9}), with the same deficit 1, has a T3h move to a key with def* = −1;
  - that move is x = 0 → {9}, z = 2 → {11}, helper 4 {5,9} → {12}, giving ({9}, {6,10}, {11}, {4,8}, {12}) with def −1;
  - 936 such witnesses are listed in `rc_failures_n5_keyform.log`.

  So P is stuck only because the T1 / T2 moves inside its key, which keep def = 1, are not improving moves.

All 369 failing profiles have the same core and the same failing state P, with f = 1, def 1, k = 3, frozen agent 0, NA = {11}, def* = 1 and kmin = −1. Each has the same 84 better states: 6 nearest of shape (1, 1, 0, 1) and 78 of shape (1, 1, 0, 2). They differ in the values of the five agents (`rc_failures_n5_all.tsv`). The hunt reached them by climbing from a random profile of the core. The core was ranked only by states at distance ≥ 2 in the earlier runs (rank [0, 0, 298, 23355]).

## 2. The failure at core 4515 (m = 12, f = 2)

**Found by** the extra random-core hunt (`k4/dlrc_hunt_runs_extra.sh`; run `certs_pure_x`, 1,500 random pure cores, `--bt=0.5`, seed 61; log `hunt_certs_pure_x.log`, dump `dump_hunt_certs_pure_x.jsonl.gz`).

**More failing profiles:** 12 climbs from the first failing profiles (run `core4515`, log `hunt_core4515.log`) raise the total to **1,076 distinct failing profiles with 4,304 failing states**.
- `rc_fail_4515_all_inst.json` holds the profiles.
- `ref_rc_fail_4515_all.log`: dlrc_ref.py confirms all of them. It finds 99,583 def > 0 states at f = 2; DL_RC fails at 4,304, the key form at 0; 0 mismatches with dlrc.c, dlrt4.c and the -DBIGPP=0 build.
- `run_rc_fail_4515_all.log`, `dump_rc_fail_4515_all.jsonl.gz`, `rc_failures_4515_all.tsv`, `rc_failures_4515_all_inst.json`, `rc_failures_4515_all.log`: dlrc.c's records and the listing.
- In every profile, agent 3's base in the four failing states is {5,6}, {5,7}, {6,7} and one singleton of {5}, {6}, {7}.
- Over the 4,304 states: 109,608 better states of shape (1, 1, 0, 2), all of them nearest, and 260,544 of shape (2, 2, 0, 1).

**Confirmed (the first 81 profiles):**
- `rc_fail_4515_inst.json` holds the 81 distinct failing profiles.
- `ref_rc_fail_4515.log` (dlrc_ref.py): 8,018 def > 0 states, all at f = 2. DL_RT4 and DL_RC fail at 324, the key form at 0. There are 0 mismatches with dlrc.c on every field and the H lines, and 0 with dlrt4.c and the -DBIGPP=0 build.
- `ref_rt4_rc_fail_4515.log` (dlrt4_ref.py, model.py): 324 DL_RT4 failures with 0 mismatches. At f = 2 a T3c move is possible, so the DL_RC verdict there rests on dlrc.c and dlrc_ref.py; neither finds an improving T3c move at these states.
- `run_rc_fail_4515.log`, `dump_rc_fail_4515.jsonl.gz`: dlrc.c's records.
- `rc_failures_4515.tsv`, `rc_failures_4515_inst.json` (suite form), `rc_failures_4515.log`: the listing.
- `rc_failures_4515_keyform.log`: the key-form witnesses.

**The core.** Core pos 4515 (idx 370), m = 12, sets `[[0,2,4,8],[1,8,10,11],[3,9,10,11],[4,5,6,7],[5,6,7,9]]`. The simplest failing profile (largest value 8, value sum 89) is profile (74, 153, 112, 227, 80) of `check4.core_domains`:

| agent | goods | values |
|---|---|---|
| 0 | 0, 2, 4, 8 | 4, 3, 8, 2 (big-top) |
| 1 | 1, 8, 10, 11 | 6, 3, 7, 5 |
| 2 | 3, 9, 10, 11 | 4, 8, 3, 2 (big-top) |
| 3 | 4, 5, 6, 7 | 8, 4, 2, 3 (big-top) |
| 4 | 5, 6, 7, 9 | 4, 2, 3, 8 (big-top) |

**The class.** The min-frozen class has 206 states, f = 2, σ = −2, and 4 keys.

**The failing states.** P = ({4}, {1,8}, {10,11}, B₃, {9}), with B₃ ∈ {{5}, {5,6}, {5,7}, {6,7}}; with agent 3 on {7} it also fails, in 7 profiles.
- Agents 0 and 4 are frozen, NA = {4, 9}, def(P) = 1, nearest distance k = **4**.
- **No T1, T2, T3, T4 or T3c move improves P.**
- Every better state keeps NA and has one of two shapes:
  - **Nearest (k = 4), shape (1, 1, 0, 2): a role swap with two helpers.** Example: from P = ({4}, {1,8}, {10,11}, {5,6}, {9}) to P′ = ({0}, {1,10}, {3}, {4}, {9}), def −1. Agent 0 releases 4 for {0}, agent 3 takes {4} and becomes frozen, and both agent 1 ({1,8} → {1,10}) and agent 2 ({10,11} → {3}) give up goods. T3 allows one helper.
  - **At distance 5, shape (2, 2, 0, 1): a double role swap**, two x's out and two z's in. Example: P′ = ({0}, {1,10}, {9}, {4}, {5}), def −1. Agents 0 and 4 become free, agent 2 takes {9} and agent 3 takes {4}, and helper 1 gives up a good.
  - Over the 324 states (at most 400 better states each): 8,604 better states of shape (1, 1, 0, 2), all of them the nearest, and 19,776 of shape (2, 2, 0, 1). None is an R_C move.
- From P itself there are 10 T3⁺ moves (W = ∅), all to states with def 1.
- **Smaller m.** Deleting one or two goods from the 81 first failing profiles, values kept, gives 209 smaller profiles (`rc_shrink_4515.log`) and 21 smaller cores (m = 10, 11). There is no DL_RC failure among the profiles, and 84 climbs on those cores (`hunt_shrink_cores_4515.log`, 2.0 M profiles) find none either.

**The key form holds** (def* = 1, kmin = −1):
- all 60 states of P's key have def 1;
- from the states of the key where agent 2 holds {3}, e.g. ({4}, {10}, {3}, {6,7}, {9}), plain T3p / T3h moves reach the keys with def* = −1;
- 992 such witnesses are listed in `rc_failures_4515_keyform.log`.

## The search around them (towards smaller n, m and simpler values)

- **Simplest values.** The simplest failing profile (largest value 8, value sum 97) is the one shown above. The values are the integer representatives of the strict balanced types (`check4.core_domains`), so smaller values would need other types.
- **Smaller m: deleting goods.** Deleting one or two goods from the failing core, keeping the remaining values, gives 350 smaller profiles that are cores (m = 11, 12) with valid values (`k4/dlrc_shrink.py`; `rc_shrink1.log`, `rc_shrink_any.log`). DL_RC holds on all 350. Climbs on the 40 cores obtained by deleting one or two goods (`hunt_shrink_cores.log`) find no DL_RC failure: 240 climbs, 8.7 M profiles, 13.4 M states.
- **n = 4.** The earlier dlrt4.c runs enumerated every profile of the n = 4 cores with one or two four-good agents (compute/k4-rt4: `b_n4_1.log`, `c_n4_2.log`) and found no DL_RT4 failure. At f = 1, R_C = RT4, and at f ≥ 2 R_C contains RT4, so DL_RC holds there too (single implementation for that enumeration). Here, every n = 4 core with three or four four-good agents (558 cores) was climbed twice: runs `n4_pure`, `n4_n4_3`, `n4_pure_k3`, `n4_n4_3_k3`, with 16.3 M profiles. They find **no DL_RC failure**. They do find DL_RT4 failures at n = 4 that are chain states (SUMMARY.md).
- **Other n = 5 cores.** Apart from cores 4604 and 4515, no core gave a DL_RC failure in the ranked and random hunts over the n = 5 cores with ≥ 3 four-good agents (SUMMARY.md). The second failure (m = 12) was found late, by the larger random sample, and the search around it is shorter (SUMMARY.md).

## What this bears on (for the coordinator; the ledger is unchanged here)

- **DL_RC is false** on this evidence, and so is **DL_RT4**:
  - at f = 1 (core 4604), where R_C adds nothing to RT4;
  - and at f = 2 (core 4515, m = 12).
  These are new refutations of DL_RT4 besides the chain states at f = 3 (and f = 2 and n = 4, SUMMARY.md).
- **The missing moves are role swaps with helpers that T3 does not allow:**
  - a helper that grows by a junk good (core 4604, distance 3);
  - two helpers (both cores, distance 4);
  - at core 4515 also a double role swap (two frozen agents out, two in, distance 5). This is the pattern `dl13-n4m9-rot` showed at n = 4, f = 1 ("role swaps with two helpers"); there, T2 rotations also helped, and here none does.
- **DL on the key graph is not refuted.** The deficit-minimal state of the key is not unique, and from another one a plain T3h move improves. In the key form, the T1 / T2 moves inside a key are free.
