# OC₁ with GDT's completion shape (unfrozen single-good owner) is false

Workstream `proof/k4-oc1-hall` (`k4/oc1_hall.md` §2).

**Idea.** Lemma GDT (`k4/sdc.md` §30) completes states in a narrow shape:
- the owner is a single-good holder that nobody wants;
- frozen agents and pair holders take nothing;
- the other single-good holders take at most one junk good each.

A proof of OC₁ along GDT's lines would need: for every order, the picks, or the bases after one improving chain, have
a completion of this shape.

**Result: false.** `k4/oc1_hall/oc1_gdt.py` (default `OWNERS=unfrozen-single`, `HOLD=unfrozen-single`),
`results/k4_oc1_hall/oc1_shapes_screen.log`:
- 9 distinct screen starts (29 orders) have no repair in this shape: A131, B131, GM4, gap-ivmax-n5-m9-n5pc1347;
- also allowing frozen single-good holders to take junk changes nothing (9 again);
- letting **any** agent own, frozen or multi-good (shape S\*), repairs every start of every data set
  (`oc1_sstar.log`).

**Smallest failing configuration** (log1338, from `results/k4_sdc/*.log`; n = 3, m = 7):
- sets [[0,3,4,5],[0,3,6],[1,2,3,0]];
- values [[12,18,10,6],[18,12,15],[2,6,10,7]];
- order (0, 2, 1), picks (3, 6, 0); agents 0 and 2 are frozen.

Neither the picks nor any state one chain reaches has a GDT-shaped completion. The repairs are:
- chain (2, 1): agent 2 takes junk {1, 2}, agent 1 takes 0; or
- chain (1, 2): agent 1 takes 0, agent 2 takes 6 with junk {1, 2}.

In both, the only owner is agent 2, now a pair holder, so the owner must be allowed to hold several goods.

**Repro.** `python3 k4/oc1_hall/oc1_gdt.py logs | grep log1338` (prints the start under `NOT REPAIRED` only if it is
among the first 8 shown; `python3 k4/oc1_hall/oc1_gdt.py screen` shows the screen failures). With `OWNERS=any`, no
start fails.
