# Conjecture VM1 (one move, then placement) at k = 7, and VM2 at k = 9: refuted in the PW family

Workstream proof/k4-vm (`k4/vm.md` §7.7). Conjecture VM1: from some V-M matching, at most one move (a pool upgrade
or an unrestricted two-agent exchange), then EFX₀-safe placements with envy-cycle rotation, give a complete EFX₀
allocation. It held on every k ≤ 5 instance tested and on 61 of the 63 instances of the k-sensitivity session's
family PW(f, W, r) up to k = 9 (`results/k4_vm/vm1_pwgrid.log`).

**It fails at k = 7.** The instance is PW(2, 3, 6)#0, with n = 5 and m = 11.

| agent | goods (value) |
|---|---|
| x₁ = 0 | p₁ = 0 (100); D = 5 (90), 6 (82), 7 (61), 8 (66), 9 (77), 10 (54) |
| x₂ = 1 | p₂ = 1 (100); D = 5 (95), 6 (62), 7 (83), 8 (92), 9 (93), 10 (78) |
| w₁ = 2 | p₁ (94), p₂ (60), q₁ = 2 (40) |
| w₂ = 3 | p₁ (98), p₂ (65), q₂ = 3 (54) |
| w₃ = 4 | p₁ (98), p₂ (83), q₃ = 4 (56) |

(The PW family: f frozen agents x_j with good p_j and a shared pool D of r goods, every pair of D worth more to x_j
than p_j; W wanters valuing every p_j above their own q_i. Definition from `k4/ksens/fam_pw.py` on `claude/k4-ksens`,
re-implemented in `k4/vm/data.py`.)

How it fails:
- **The V-M matchings.** Nobody strongly prefers its top. Good 0 is the top of x₁ and all three wanters, so one of
  them wins it. x₂ takes good 1, a loser x₁ takes good 5 (its second), and the wanters take their q's. That gives 4
  matchings.
- **With at most one move, nothing completes.** Neither the matchings nor any of the 90 states one move away can be
  completed by placements and rotations.
  - Checked exhaustively by `k4/vm/vm1_verify.py`, with no caps (`vm1_verify_pw236.log`).
  - Also by the independent replay `attempts/k4_vm_vm1_pw.py`, over a superset of the moves (non-minimal upgrades
    as well).
- **Two moves suffice.** Both x₁ and x₂ trade their picks for sets of D, and p₁ and p₂ go to wanters. Example:
  ({5, 6, 7}, {3, 8, 9}, {0}, {1}, {4, 10, 2}).

The mechanism is PW's:
- Both x's are frozen: every wanter wants both p's.
- Each x would see any two D-goods in another bundle as worth more than its pick, so D can only be absorbed by the
  x's themselves.
- One move frees only one x.

The general-k pattern of `k4/ksens.md` (c chains from every order fail at k = 2c + 3) suggested that c moves of VM
fail from k = 2c + 5. VM1 failing at k = 7 (above) and VM2 at k = 9 (below) fit that guess, **but it is wrong**:
VM1 already fails at k = 6, on PW(4, 3, 5)#1 (`attempts/k4-vm-vm1-k6.md`), which replaces this file's instance as the
smallest k known to fail.

## Two moves (VM2) fail at k = 9: PW(3, 3, 8)#0

n = 6, m = 14: frozen agents x₁, x₂, x₃ = 0, 1, 2 with picks p_j = j (worth 100) and the shared pool D = {6, …, 13};
wanters 3, 4, 5 with q_i = i.

| agent | goods (value) |
|---|---|
| x₁ = 0 | p₁ (100); D = 6 (60), 7 (91), 8 (59), 9 (79), 10 (53), 11 (83), 12 (98), 13 (55) |
| x₂ = 1 | p₂ (100); D = 6 (88), 7 (74), 8 (81), 9 (54), 10 (83), 11 (82), 12 (56), 13 (90) |
| x₃ = 2 | p₃ (100); D = 6 (75), 7 (52), 8 (60), 9 (55), 10 (87), 11 (72), 12 (68), 13 (96) |
| w₁ = 3 | p₁ (91), p₂ (82), p₃ (94), q₁ (77) |
| w₂ = 4 | p₁ (72), p₂ (71), p₃ (85), q₂ (36) |
| w₃ = 5 | p₁ (66), p₂ (78), p₃ (99), q₃ (24) |

- There are 4 V-M matchings. With at most two moves nothing completes: 4, 273 and 3,319 states at depths 0, 1 and 2,
  uncapped (`results/k4_vm/vm1_verify_pw338.log`).
- **Three moves suffice**, one per frozen agent: ({6, 7}, {8, 9, 10}, {13, 11, 4, 3}, {2}, {0}, {5, 12, 1}).
- On both instances in this file the least number of moves is f, the number of frozen agents: one move frees only
  one x, and only the x's can absorb D. That is not general: the k = 6 instance needs 2 moves with f = 4.

**What survives:** VMX₂ (any number of moves) completes both instances. VM1 is unrefuted at k ≤ 5, and at k = 4 in
particular (`k4/vm.md` §7.3–§7.5).

Reproduce:
- `python3 attempts/k4_vm_vm1_pw.py`: an independent replay from the definitions, sharing no code with `k4/vm/`;
- `python3 attempts/k4_vm_vm2_pw338.py`: the same for PW(3, 3, 8), at depth 2 (several minutes);
- `python3 k4/vm/vm1_verify.py '<the JSON>' --maxd=3`, with the JSON of `data.pw(2, 3, 6, 1, 237)` or
  `data.pw(3, 3, 8, 1, 339)` (the seeds of `pwgrid:9:1:1`; both JSONs are in `results/k4_vm/vm1_pwgrid.log`);
- `python3 k4/vm/vm1_fast.py pwgrid:9:1:1`: the run that found it.
