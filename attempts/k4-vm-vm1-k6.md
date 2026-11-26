# Conjecture VM1 at k = 6: refuted in the PW family

Workstream proof/k4-vm (`k4/vm.md` §7.7). Conjecture VM1: from some V-M matching, at most one move (a pool upgrade
or an unrestricted two-agent exchange), then EFX₀-safe placements with envy-cycle rotation, give a complete EFX₀
allocation. It was first refuted at k = 7 (`attempts/k4-vm-vm1-k7.md`). **It fails at k = 6**, which replaces k = 7 as
the smallest k known to fail.

The PW family comes from `k4/ksens/fam_pw.py` on `claude/k4-ksens` and is re-implemented in `k4/vm/data.py`:
- f frozen agents x_j, each with a pick p_j worth 100, share a pool D of r goods;
- every pair of D-goods is worth more to each x_j than p_j;
- W wanters each value every p_j above their own good q_i;
- k = max(r + 1, f + 1).

`pwgrid:K:T:SEED` takes T instances per configuration with k ≤ K, with seed SEED + 100f + 10W + r.

**How often VM1 fails** (`k4/vm/vm1_fast.py`, failures re-checked with 50× caps):
- **k ≤ 5:** 1,080 instances (`pwgrid:5:40:3`, 40 per configuration). All satisfy VM1: 1,039 need no move and 41 need
  one (`results/k4_vm/vm1_pwgrid_k5_T40.log`).
- **k ≤ 6:** 720 instances (`pwgrid:6:20:5`). There are 11 failures, all with r = 5 and W = 3: PW(2, 3, 5) 5 of 20,
  PW(3, 3, 5) 5 of 20, PW(4, 3, 5) 1 of 20 (`results/k4_vm/vm1_pwgrid_k6_T20.log`). All 11 were re-verified
  uncapped by `vm1_verify.py` (`results/k4_vm/vm1_verify_k6_all.log`): no completion within one move, and two moves
  suffice in each.
- A third pass, `pwgrid:6:3:1`, found PW(4, 3, 5)#1 (n = 7, m = 12) first. It is also verified (below).

## The smallest failing configuration: PW(2, 3, 5)#2, n = 5, m = 10, k = 6

This is `data.pw(2, 3, 5, 20, 240)[2]`.

| agent | goods (value) |
|---|---|
| x₁ = 0 | p₁ = 0 (100); D = 5 (71), 6 (85), 7 (61), 8 (72), 9 (65) |
| x₂ = 1 | p₂ = 1 (100); D = 5 (53), 6 (55), 7 (91), 8 (63), 9 (88) |
| w₁ = 2 | p₁ (63), p₂ (61), q₁ = 2 (13) |
| w₂ = 3 | p₁ (86), p₂ (65), q₂ = 3 (11) |
| w₃ = 4 | p₁ (91), p₂ (69), q₃ = 4 (62) |

- **The V-M matching.** There is exactly one: ({6}, {1}, {2}, {0}, {4}). Wanter w₂ wins p₁, x₁ takes its best D-good 6,
  and x₂ keeps p₂, which w₁ and w₃ want (so x₂ is frozen). The pool is {3, 5, 7, 8, 9}.
- **At most one move fails.** Neither the matching nor any of the 12 states one move away can be completed by
  placements and rotations.
  - Checked exhaustively, with no caps, by `k4/vm/vm1_verify.py` (`results/k4_vm/vm1_verify_pw235_2.log`).
  - Checked again by the independent replay `attempts/k4_vm_vm1_pw235.py`, which shares no code with `k4/vm/`. It
    uses a superset of the moves and also finds 12 one-move states (`results/k4_vm/replay_pw235.log`).
- **Two moves suffice.** For example ({5, 8}, {2, 7, 9}, {1}, {0}, {4, 6, 3}): x₁ and x₂ both end with D-goods, and
  x₂ parks w₁'s q₁ = 2 (worthless to x₂).

## The first one found: PW(4, 3, 5)#1, n = 7, m = 12

This is `data.pw(4, 3, 5, 3, 436)[1]`.

| agent | goods (value) |
|---|---|
| x₁ = 0 | p₁ = 0 (100); D = 7 (97), 8 (75), 9 (56), 10 (62), 11 (68) |
| x₂ = 1 | p₂ = 1 (100); D = 7 (56), 8 (78), 9 (95), 10 (99), 11 (94) |
| x₃ = 2 | p₃ = 2 (100); D = 7 (62), 8 (89), 9 (86), 10 (98), 11 (88) |
| x₄ = 3 | p₄ = 3 (100); D = 7 (96), 8 (56), 9 (80), 10 (95), 11 (71) |
| w₁ = 4 | p₁ (77), p₂ (75), p₃ (84), p₄ (76), q₁ = 4 (58) |
| w₂ = 5 | p₁ (73), p₂ (91), p₃ (95), p₄ (70), q₂ = 5 (16) |
| w₃ = 6 | p₁ (91), p₂ (90), p₃ (99), p₄ (65), q₃ = 6 (41) |

- There are 4 V-M matchings. None of them, and none of the 112 states one move away, can be completed. This was
  checked uncapped (`vm1_verify_pw435_1.log`) and by the replay `attempts/k4_vm_vm1_pw435.py`
  (`replay_pw435.log`), which also finds 112 states.
- Two moves suffice: ({7, 8}, {1}, {10, 9}, {3}, {2}, {0}, {6, 5, 4, 11}). x₁ and x₃ trade their picks for two
  D-goods each, and the fifth D-good is parked on w₃.

**The mechanism** is PW's, as at k = 7:
- only x's value D, and any two D-goods are worth more to every x than its pick;
- so a bundle holding two D-goods plus anything else is unsafe while some x holds only its pick;
- the five D-goods need two x's raised above their picks, and one move raises only one.

This is an explanation, not a proof. The number of moves needed is not the number f of frozen agents: it is 2 here
with f = 4, and 2 with f = 2.

**What survives:**
- VMX₂ (any number of moves) completes every failing instance, with two moves each (`vm1_verify_k6_all.log`);
- on the PW family, VM1 has no failure at k ≤ 5 (the 1,080 instances above). But VM1 was later refuted at k = 5 on a
  random instance and at k = 4, on cores too (`attempts/k4-vm-vm1-noncore.md`, `attempts/k4-vm-vm1-core.md`);
- VM1-chain (one VM1 move or one DE chain) completes all 12 k = 6 failures here (`results/k4_vm/vm1_chain_failures.log`).

The guess in `attempts/k4-vm-vm1-k7.md` that c moves fail from k = 2c + 5 is wrong for c = 1.

Reproduce:
- `python3 attempts/k4_vm_vm1_pw235.py`: the replay for PW(2, 3, 5)#2 (under a second);
- `python3 attempts/k4_vm_vm1_pw435.py`: the replay for PW(4, 3, 5)#1 (about 30 s);
- `python3 k4/vm/vm1_verify.py '<JSON>' --maxd=3`, with the JSON in the first line of each `vm1_verify_pw*.log`;
- `python3 k4/vm/vm1_fast.py pwgrid:6:20:5`: the grid that found the 11 failures.
