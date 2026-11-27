# F1 (EFX₀-safe placement) in an arbitrary order, even with distinct tops

Workstream proof/k4-vm (`k4/vm.md` §6). The approach: after V-M's matching, place the remaining goods one by one,
each on any agent whose bundle stays EFX₀-unenvied (F1), rotating envy cycles before each placement. The order of the
goods and the recipient are arbitrary.

The question was whether *every* run ends EFX₀ when the agents' tops are distinct. Then V-M gives everyone its top,
Phase III does nothing, and every good is worth at most v_i(a_i) to each i. This is the setting of Theorem DT
(K4.SDC.DT).

**It fails at n = 2, m = 5** (a general 4-limited instance; it has private goods, so it is not a core).

| agent | goods (value) |
|---|---|
| 0 | a₀ (10), a₁ (9), g (8), p (1) |
| 1 | a₁ (10), a₀ (9), g (8), q (1) |

Starting from ({a₀}, {a₁}):
- p goes to agent 0: safe, since a two-good bundle threatens nobody here.
- q goes to agent 1: safe for the same reason.
- Now g has no safe place.
  - Agent 1 sees {a₀, p, g} minus p (worthless to it) as 17 > 11.
  - Symmetrically, agent 0 sees {a₁, q, g} minus q as 17 > 11.
- Nobody envies anybody, so rotation does nothing.

An EFX₀ allocation is ({a₀, g}, {a₁, p, q}), and F1 reaches it when g is placed first.

So even in the easiest case the placement order matters. While some bundle is a single good, F1 can never get stuck
(a two-good bundle is safe there). But placing low goods first can use up the singletons. Theorem DT's proof avoids
this with rematching moves (m1)/(m2). F1 needs a rule ("high goods first"?) or moves.

Reproduce:
- `python3 attempts/k4_vm_f1_order.py`: an independent replay;
- `vmlib.all_runs(vmlib.vm0_run, ...)` on this instance gives 4 stuck runs of 16 (with or without rotation).
