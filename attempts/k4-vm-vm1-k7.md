# Conjecture VM1 (one move, then placement) at k = 7: refuted in the PW family

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

The general-k pattern of `k4/ksens.md` (c chains from every order fail at k = 2c + 3) suggests c moves of VM fail
at k = 2c + 5. So far one data point supports that: VM1 survives k = 5 and fails at k = 7. PW(3, 3, 8) (k = 9) is
checked in `vm1_verify_pw338.log`.

**What survives:** VMX₂ (any number of moves) completes this instance. VM1 is unrefuted at k ≤ 6, and at k = 4 in
particular (§7.3–§7.5).

Reproduce:
- `python3 attempts/k4_vm_vm1_pw.py`: an independent replay from the definitions, sharing no code with `k4/vm/`;
- `python3 k4/vm/vm1_verify.py '<the JSON above>' --maxd=3`;
- `python3 k4/vm/vm1_fast.py pwgrid:9:1:1`: the run that found it.
