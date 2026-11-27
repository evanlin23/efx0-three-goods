# Deterministic move rules for VMˣ (V-M + EFX₀-safe placement + exchanges)

Workstream proof/k4-vm (`k4/vm.md` §6.2, §7). VMˣ runs, in this order:
1. V-M's Phases I–II;
2. Phase III with F2 (EFX₀-safe 3rd/4th choices);
3. a loop of three steps:
   - rotate envy cycles;
   - either apply an F6x move (a pool upgrade, or a two-agent exchange with pool goods) or place a pool good on an
     agent whose bundle stays EFX₀-unenvied (F1);
4. junk by L3.

With every choice open, some run ends EFX₀ on every instance tested (Conjecture VMX). The approach recorded here:
**fix the choices by a rule**, so that VMˣ becomes an algorithm. Every rule tried fails. The table gives the smallest
failure found for each.

| rule | what it fixes | smallest failure | where |
|---|---|---|---|
| lazy (`x-stuck`) | moves only when the chosen good has no safe place | `c4min-tlam-n3-m6` (n = 3, m = 6), all 8 runs stuck | `vm6_screen.log` |
| eager (`x-eager`) | a move whenever one exists | `c4x-n3m8-pure-top7` (n = 3, m = 8), all runs | `vm6_screen.log` |
| eager with lookahead (`x-eagerL`), first run | moves only if afterwards every pool good still has a safe place; all ties by index | `lb4-n2m5-upgrade` (n = 2, m = 5) | `vm6_screen.log` |
| VM-LL (`x-eagerLL`) | as above, plus placements by the same lookahead (rotation included), and moves that free a good another move absorbs; fully deterministic | `gen:5525` (n = 2, m = 5) | `vmll_gen.log` |

Notes on each failure:
- **Lazy, `c4min-tlam-n3-m6`.** The upgrade has to come early. Agent 0 must swap its top {5} for {0, 1, 2} before
  goods 0 and 1 are placed with agent 2.
- **Eager, `c4x-n3m8-pure-top7`.** Three agents have the same pattern: top 7, two private goods, and the shared good
  6. The winner of 7 upgrades to its private set {0, 2, 6} and releases 7, which then fits nowhere.
- **eagerL, `lb4-n2m5-upgrade`.** The order of placements matters. Good 0 placed first fits only with agent 0, and
  then good 1 fits nowhere. Placing 1 first creates an envy cycle; its rotation makes room.
- **VM-LL failure rates:**
  - 14 of 1,284 relabelled screen, SPECIAL and logged instances (`vmll_screen_relabel.log`). On the original labels it
    has 0 failures (`vmll_screen.log`), so the tie-break by index was luck there.
  - 6 of 13,000 random core profiles, n = 3–5 (`vmll_cores.log`).
  - 4 of 20,000 general instances (`vmll_gen.log`).
  - 2 of 492 relabelled suite instances (`vmll_suite.log`).

## The smallest one: VM-LL at n = 2, m = 5 (`gen:5525`)

| agent | ranking (good: value) |
|---|---|
| 0 | 4: 19 > 1: 18 > 3: 15 > 0: 8 |
| 1 | 2: 14 > 1: 13 > 0: 8 |

1. The tops are distinct, so V-M gives ({4}, {2}), and the pool is {0, 1, 3}.
2. Agent 0 can upgrade {4} → {0, 1} (26 > 19). Afterwards, goods 3 and 4 *each* have a safe place, namely agent 1, so
   the one-good lookahead accepts the move.
3. But {2, 3, 4} is unsafe: agent 0 sees it minus 2 (worthless to agent 0) as 34 > 26. And {0, 1, 3} and {0, 1, 4}
   are unsafe for agent 1, which sees 21 > 14.
4. No further upgrade exists, so the run is trapped.

Six EFX₀ allocations exist, e.g. ({0, 3, 4}, {1, 2}). VMˣ with free choices reaches EFX₀ on 34 of its runs.

The lookahead tests pool goods one at a time, and the trap is a joint one. This is P1 (K4.SDC.P1) in miniature: a
value-monotone step that is locally safe but leads to a dead end. Even with two agents, a rule needs a joint test (in
effect, solving the completion problem), and with that test the moves would be superfluous.

Reproduce:
- `python3 attempts/k4_vm_deterministic.py`: an independent replay of the n = 2 trap, sharing no code with `k4/vm/`;
- `python3 k4/vm/vmll_test.py gen:10000:64:6:10:20`;
- `python3 k4/vm/vm6_test.py screen --variants=x-stuck,x-eager,x-eagerL`.
