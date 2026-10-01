# DL_RT4 failures on the pure n = 5 cores (compute/k4-rt4, n5c slice)

EVIDENCE: the output of `k4/dlrt4_run.py` (dlrt4.c sha256 `fcde494a3161279d47a7b80e614f69c58894ebc7b40d00e461f677b8810d7cae`,
unchanged). Every failing profile was re-run through `k4/dlrt4_ref.py`, which agrees with dlrt4.c on every state
(`ref_n5c_fails.log`). Conjecture DL_RT4 is the statement of `k4/dlrt4.c`'s header: at f ≥ 1, every min-frozen P with def(P) > 0
has a min-frozen P′ with def(P′) < def(P) reached by a T1, T2, T3 or T4 move. LEDGER.md is not edited here. What follows is
for the coordinator and the proof workstream to weigh.

**Status: written while run `n5c_purebt` was in progress** (4,369 of 4,674 cores done). §Counts is updated when the run ends.

## Counts

| run | profiles | def > 0 states with f ≥ 1 | DL_RT4 fails at | failing profiles | failing cores (pos, idx, m) |
|---|---:|---:|---:|---:|---|
| `n5c_purebt`: `k4_certs_5_pure`, `--bt=all`, 5,000 per core, seed 2 | (in progress) | (in progress) | **64** (so far) | 8 | 2614 (568, 10), 4170 (25, 12), 4214 (69, 12) |
| `n5c_pure`: `k4_certs_5_pure`, 5,000 per core, seed 1 | 23,370,000 | 725,850 | 0 | 0 | |
| `n5c_cat_*`: #53's n = 5 catalogues, hard_hunt, hard_hunt_smallest (every record) | 115,939 | 21,175 | 0 | 0 | |

(`--bt=all` restricts every 4-good agent to its big-top types, top > second + third: 48 of the 288 types.)

Files:
- `n5c_failures_purebt.tsv`: one line per failing state: core, profile (indices into `check4.core_domains` restricted to the
  big-top types), values, bases, f, def, k, signature, frozen agents, NA, and the shapes of the nearest better states.
- `n5c_fail_inst.json`: the failing profiles as a `dlrt4_ref.py` / `dlrt4_run.py inst` list.
- Both are written by `n5c_failures_list.py` from `dump_n5c_purebt.jsonl.gz`, whose "D" records with `"br": "none"` hold every
  failing state with every better min-frozen P′.

| core pos (idx, m) | sets | failing profiles | failing states | (f, def, k): signature |
|---|---|---:|---:|---|
| 2614 (568, 10) | [[0,2,4,8],[1,3,8,9],[3,4,8,9],[5,6,7,9],[5,6,7,9]] | 3 | 8 | (3, 1, 3): G,D2,PM 6, fO,G,D2 2 |
| 4170 (25, 12) | [[0,2,6,10],[1,4,9,11],[3,5,9,11],[6,7,8,10],[7,8,10,11]] | 3 | 32 | (3, 1, 3): fO,G,D2 17, G,D2 11, G,D2,PM 4 |
| 4214 (69, 12) | [[0,2,8,10],[1,4,9,11],[3,6,9,11],[5,7,10,11],[7,8,10,11]] | 2 | 24 | (3, 1, 3): fO,G,D2 14, G,D2 8, G,D2,PM 2 |

## The common shape: a role swap passed through a frozen agent

All 64 failing states have f = 3 (two free agents), def = 1, and nearest distance k = 3. **Every** better min-frozen P′ at
distance 3, in every failing state, is a move of one shape (`chain3` in the TSV), with the needed set NA unchanged:

- a frozen agent x with base {g} becomes free (it takes a new base from the junk J);
- a frozen agent y with base {h} takes {g} and stays frozen;
- a free agent z takes {h} and becomes frozen.

So x frees g, y moves from h to g, and z takes h. This is not a T3 role swap (there z takes x's good g itself, and z cannot:
g is not in z's set). It is not T4 either (T4 moves only agents that stay frozen; here x leaves the frozen set and z enters
it). It is the composition of a T4-type move of y, from h to g, with a T3 role swap of x and z. Every other better P′
recorded (up to 80 per state) also keeps NA and moves at least one frozen agent to another frozen good. Each is such a
chain plus re-bases or further frozen moves (sizes 4 and 5).

No failing state has an improving T1, T2, T3 or T4 move. In the same 8 profiles, each of the other 78 def > 0 states
(all with f = 3) has an improving T3p and an improving T3h move (`ref_n5c_fails.log`). At n = 4 the DL₁₃ failures (`results/k4_dl13/n4_FAILURES.md`) were exchanges between two frozen
agents, which T4 now covers. The n = 5 failures need the frozen agent y in the middle of a role swap.

## The smallest example

Core pos 2614 (idx 568) of `k4_certs_5_pure`, m = 10, profile (6, 9, 43, 24, 24) of the big-top domains:

- agent 0 on goods {0, 2, 4, 8} with values (2, 6, 3, 10); agent 1 on {1, 3, 8, 9}: (2, 8, 4, 3); agent 2 on {3, 4, 8, 9}:
  (10, 2, 6, 3); agents 3 and 4 (twins) on {5, 6, 7, 9}: (4, 2, 3, 8);
- state P = ({8}, {9}, {3}, {5}, {6, 7}): min-frozen with f = 3 (agents 0, 1, 2 frozen), NA = {3, 8, 9}, J = {0, 1, 2, 4},
  def(P) = 1;
- its 8 better min-frozen states at distance 3 are all chain3 moves:
  - x = 0, y = 1, z ∈ {3, 4}: agent 0 frees 8 and takes {2}, {0, 2} or {2, 4}; agent 1 moves from 9 to 8; z takes {9};
    def(P′) = −1 (6 states);
  - x = 2, y = 1, z ∈ {3, 4}: agent 2 frees 3 and takes {4}; agent 1 moves from 9 to 3; z takes {9}; def(P′) = 0
    (2 states);
- the core's 8 failing states (3 profiles) all have frozen agents {0, 1, 2} with bases {8}, {9}, {3} and NA = {3, 8, 9}.
  They differ only in the profile and in the bases of the free twins 3 and 4.

To reproduce: `python3 k4/dlrt4_ref.py inst results/k4_rt4/n5c_fail_inst.json` (seconds), or
`python3 k4/dlrt4_run.py inst results/k4_rt4/n5c_fail_inst.json`.

## What this bears on (for the coordinator; the ledger is unchanged here)

- **DL_RT4.** The data contradict it at n = 5 (m = 10 and m = 12), in 3 pure cores, on profiles where every agent is
  big-top. The repair the data show is the chain role swap above.
- The unrestricted sample (`n5c_pure`, 5,000 random profiles of all 288 types per core) found no failure. The failures
  are rare: 64 states among the big-top sample's f ≥ 1 states.
