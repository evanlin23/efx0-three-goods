# Induction on agents along the serial-dictatorship order

Workstream `proof/k4-sd-induct` (branch `claude/k4-sd-induct`). Angle of the k = 4 campaign (`k4/attack_log.md`):
grow the instance one agent at a time along a serial-dictatorship order, as agent-count results do, using the SD-C
structure of `k4/sdc.md` (§2, §6, §26–§30). Code: `k4/sdind/`; logs: `results/k4_sdind/`. Everything computed is
evidence only (PROMPT.md §5 rule 3). Notation as in `k4/sdc.md`: Y = SD(π) the picks, J the junk (unpicked goods), a
*one-absorber completion* gives every junk good to some agent with at most one agent (the absorber) receiving two or
more.

## Status (burst 1)

- **Proved** (§1, short): *deleting any agent with its pick is SD-consistent.* For every agent u, the picks of SD(π)
  on the other agents are the picks of SD(π − u) on I − u − Y_u, and the junk is the same set J. So the sub-instances
  I_U (agents U, goods Y[U] ∪ J) form a Boolean lattice with one fixed junk set, and a completion of every I_U is a
  map J → U.
- **Proved** (§1): when the inserted agent f is *first* in the sub-instance's order (it holds its top among the
  sub-instance's goods), a completion of the sub-instance extends with f alone iff f is not threatened by the
  absorber's bundle; two-good bundles never threaten f.
- **Evidence** (§2, `e2_paths.py`): inserting agents in **reverse** SD order (each new agent first) works with at most
  **one junk good moved per insertion** on every start tested that has a one-absorber completion: 580 screen and 529
  suite starts (n ≤ 5), for some order π producing the picks. Inserting in SD order (each new agent last) needs up to
  6 moves and has empty intermediate levels on 18–20 starts. So the first agent, not the last, is the one to delete.
- **Refuted** (§2): the plain "every completion of the sub-instance extends with a bounded repair" form, in both
  directions (`e1_delete.py`); and the suffix path with an arbitrary order producing the picks (25 starts have an
  empty level).
- **Next**: (1) a rule for the order and for the one move (greedy dead-end test); (2) the starts that need a chain;
  (3) the proof of the one-move insertion step in the cases: f not frozen; f frozen with a free slot.

## 1. Deleting an agent with its pick

**Lemma D (SD-consistency of deletion).** Let Y = SD(π) with junk J, and let u be an agent. In I − u − Y_u (u and its
pick deleted; I − u if u picked nothing), SD(π − u) gives every other agent its pick Y_i, and its junk is J.

*Proof.* Agents before u in π: Y_u was available at their turns and not taken, so deleting it changes none of their
choices. Agents after u: Y_u was already gone at their turns. By induction along π every agent i ≠ u faces the same
available goods minus at most Y_u, which it did not take, so it takes Y_i. The unpicked goods are the same. ∎

So for every set U of agents, I_U = (U, Y[U] ∪ J) has SD outcome Y restricted to U (π restricted to U), and junk J.
Write A(U) for the one-absorber EFX₀ completions of I_U, as maps J → U.
- A(U ∪ {u}) contains every X ∈ A(U) in which u, holding {Y_u} alone, is not threatened (u's singleton cannot be
  strongly envied, and nothing else changes for the agents of U);
- conversely, restricting X ∈ A(U ∪ {u}) with no junk at u gives an element of A(U) (deleting an agent and its bundle
  keeps EFX₀ for the rest).

**Which agents can be first or last.** By Lemma 1 of `k4/sdc.md`, the orders producing Y are exactly the topological
orders of the want relation (i before j whenever j wants Y_i). So u can be *last* iff nobody wants Y_u (u is not
frozen), and u can be *first* iff u wants nothing, i.e. Y_u is u's top.

**Lemma F (a first agent is threatened only by the absorber).** Let f be first in an order producing Y on I_U (Y_f
is f's top among the goods of I_U), and X a one-absorber completion of I_U ∖ f. Then X + (f ↦ {Y_f}) is EFX₀ iff f is
not threatened by the absorber's bundle B_o, i.e. iff v_f(B_o ∖ h) ≤ v_f(Y_f) for every h ∈ B_o.

*Proof.* f's singleton is never strongly envied, and the other agents' bundles and values do not change. A bundle
{Y_j} or {Y_j, g} with g junk: removing a good leaves a single good of I_U, worth at most v_f(Y_f) since Y_f is f's
top there. Only the absorber holds three or more goods. ∎

By contrast, an agent inserted *last* can want every earlier pick, so every two-good bundle {Y_j, g} with a pick it
wants threatens it.

## 2. Paths of completions (`k4/sdind/e2_paths.py`, `results/k4_sdind/e2_paths.log`)

An insertion sequence u_1, …, u_n adds one agent at a time; A({u_1}) is the single map J → u_1. A *path* picks
X_k ∈ A({u_1, …, u_k}) for every k; its step size is the largest Hamming distance (number of junk goods whose holder
changes) between consecutive X_k. For each SD outcome Y with a one-absorber completion (n ≤ 5, every order):

| insertion sequence | screen (580 starts) | suite (529 starts) |
|---|---|---|
| SD order (new agent last), best order producing Y: least step 0 / 1 / 2 / 3–6 / some level empty | 16 / 158 / 192 / 196 / 18 | 15 / 157 / 147 / 190 / 20 |
| reverse SD order (new agent first), first order producing Y: some level empty | 25 | 25 |
| **reverse SD order, best order producing Y: least step 0 / 1** | **298 / 282** | **249 / 280** |
| any insertion sequence: least step 0 / 1 | 298 / 282 | 249 / 280 |

So the reverse SD order is as good as any insertion sequence, and one move per insertion always suffices for some
order producing Y. The SD order (new agent last) needs up to 6 moves, and on 18 screen and 20 suite starts some
intermediate sub-instance has no one-absorber completion at all.

`e1_delete.py` (`results/k4_sdind/e1_delete.log`) shows that a bounded repair from *every* completion of the
sub-instance fails in both directions (distance 3–4 at n = 4, e.g. Q2 and A131), so the induction has to carry a
choice, not an arbitrary completion.

Cross-check of the brute force (`k4/sdind/xcheck_lib.py`, `results/k4_sdind/xcheck_lib.log`): existence of a
one-absorber completion agrees with the SAT test `oc_absorb.extends_A` on all 1,550 screen and 1,452 suite cases;
every returned assignment passes the raw EFX₀ check; the full sets agree with itertools enumeration on 82 sampled
cases.
