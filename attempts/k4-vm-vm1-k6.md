# Conjecture VM1 at k = 6: refuted in the PW family

Workstream proof/k4-vm (`k4/vm.md` §7.7). Conjecture VM1: from some V-M matching, at most one move (a pool upgrade
or an unrestricted two-agent exchange), then EFX₀-safe placements with envy-cycle rotation, give a complete EFX₀
allocation. Its first refutation was at k = 7 (`attempts/k4-vm-vm1-k7.md`). This one is at **k = 6**, so it replaces
that as the smallest k known to fail.

**The instance** is PW(4, 3, 5)#1, with n = 7 and m = 12 and k = max(r + 1, f + 1) = 6. It was found by
`k4/vm/vm1_fast.py pwgrid:6:3:1` (three instances per PW configuration up to k = 6) and by `vm1_plain.py` on the same
source. PW(4, 3, 5)#0, the only instance of this configuration in the earlier one-per-configuration grid, passes.

| agent | goods (value) |
|---|---|
| x₁ = 0 | p₁ = 0 (100); D = 7 (97), 8 (75), 9 (56), 10 (62), 11 (68) |
| x₂ = 1 | p₂ = 1 (100); D = 7 (56), 8 (78), 9 (95), 10 (99), 11 (94) |
| x₃ = 2 | p₃ = 2 (100); D = 7 (62), 8 (89), 9 (86), 10 (98), 11 (88) |
| x₄ = 3 | p₄ = 3 (100); D = 7 (96), 8 (56), 9 (80), 10 (95), 11 (71) |
| w₁ = 4 | p₁ (77), p₂ (75), p₃ (84), p₄ (76), q₁ = 4 (58) |
| w₂ = 5 | p₁ (73), p₂ (91), p₃ (95), p₄ (70), q₂ = 5 (16) |
| w₃ = 6 | p₁ (91), p₂ (90), p₃ (99), p₄ (65), q₃ = 6 (41) |

(The PW family, from `k4/ksens/fam_pw.py` on `claude/k4-ksens`, re-implemented in `k4/vm/data.py`: f frozen agents
x_j, each with a pick p_j worth 100, and a shared pool D of r goods, every pair of which is worth more to each x_j
than p_j; W wanters, each valuing every p_j above its own q_i. This instance is `data.pw(4, 3, 5, 3, 436)[1]`, seed
1 + 100f + 10W + r as in `pwgrid`.)

**How it fails.**
- There are 4 V-M matchings: every x holds its pick except that one wanter may take p₃, in which case x₃ takes good
  10.
- None of them, and none of the 112 states one move away, can be completed by placements and rotations.
  - Checked exhaustively, with no caps, by `k4/vm/vm1_verify.py` (`results/k4_vm/vm1_verify_pw435_1.log`).
  - Checked again by the independent replay `attempts/k4_vm_vm1_pw435.py`, which shares no code with `k4/vm/`. It
    uses a superset of the moves (non-minimal upgrades as well), and its one-move level also has 112 states.
- **Two moves suffice**, for example ({7, 8}, {1}, {10, 9}, {3}, {2}, {0}, {6, 5, 4, 11}). x₁ and x₃ trade their
  picks for two goods of D each, and the fifth D-good is parked on w₃, which does not value it.

**The mechanism** is the same as at k = 7:
- every wanter wants every p, so all the x's are frozen;
- only x's value D, and any two D-goods are worth more to every x than its pick;
- so a bundle holding three D-goods is safe only once the other x's hold more than a pick, and one move frees only one
  x.

Here two freed x's are enough for the five D-goods: two each, with the fifth parked on a wanter. So the number of moves
needed is not the number f of frozen agents: PW(4, 3, 5)#1 needs 2 moves with f = 4. That differs from the two
instances in `attempts/k4-vm-vm1-k7.md`, where it was f. More likely it depends on r against how many D-goods one
freed x can absorb (a guess, not checked).

**What survives:**
- VMX₂ (any number of moves) completes the instance;
- VM1 is unrefuted at k ≤ 5;
- VM1 at k = 4 is unaffected (§7.3–§7.5).

The guess in `attempts/k4-vm-vm1-k7.md` that c moves fail from k = 2c + 5 is wrong for c = 1: one move already fails at
k = 6.

Reproduce:
- `python3 attempts/k4_vm_vm1_pw435.py`: the independent replay (about 30 s);
- `python3 k4/vm/vm1_verify.py '<JSON>' --maxd=4`, with the JSON in the first line of `vm1_verify_pw435_1.log`;
- `python3 k4/vm/vm1_fast.py pw:4:3:5:3:436`: the three instances of this configuration; #1 fails.
