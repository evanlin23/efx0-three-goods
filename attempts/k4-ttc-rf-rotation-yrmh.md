# Failed: the rotation, YRMH-IGYT and its last-house variant as canonical receiver-first rules

Workstream `proof/k4-ttc` (`k4/ttc.md` §14.9; the coordinator's task of 06:36).

**The goal.** Find a canonical receiver-first rule: from a failing start Y, a listed order o and a receiver u, produce
one u-first SD order whose outcome is a maximum matching satisfying OC₁. The candidates below fail. They never fail
OC₁ at k = 4; they fail because they leave an agent pickless. The rule that survives, YRMH-F, has a guard that
provably keeps the matching maximum (Lemma PTR, §14.9).

## 1. The rotation (u, o − u): pickless at 3,460 n = 5 starts, and the twin image at k = 5

**Smallest failing configuration at k = 4** (n = 5, 5_pure#374, from the certifier's partial6 export):
- sets [[0,1,5,7],[1,4,5,7],[2,3,4,6],[2,3,6,7],[4,5,6,7]];
- vals [[2,3,10,6],[3,7,6,5],[3,5,6,7],[5,4,8,6],[6,5,8,4]];
- the only listed order is o = (3, 2, 1, 4, 0), giving Y = (g1, g5, g4, g6, g7), where OC₁ fails;
- the only receiver is u = 0.

The rotation (0, 3, 2, 1, 4) gives (g5, g7, g4, g6, —). Agent 4's goods g4, g5, g6, g7 are all taken before its turn.
- So the per-order form of RF ("move u to the front of the failing order") fails here even in its weakest reading
  (some listed order, some receiver), at all 3,460
  such starts.
- These are Hall's 3,460 pickless rotations. Other u-first orders are maximum and satisfy OC₁ (K4.SDC.RF holds).

**At k = 5** (ksens's twin instance; sets [[0,1,2,5,6],[1,2,4,5,6],[3,4,5,6],[3,4,5,6]], vals
[[3,35,33,43,39],[20,26,16,43,32],[8,2,7,4],[8,2,7,4]], Y = (g6, g5, g4, g3)):
- the rotation of the first listed order (1, 0, 3, 2) is (g6, g5, g3, g4);
- that is the image of Y under the twin swap, and it fails OC₁.

## 2. YRMH-IGYT (ejection only): pickless at 59,144 n = 5 starts

The rule: the queue is (u, o − u), with tenancy Y. When the head takes Y_b for an agent b still waiting, b moves to the
head.

**Smallest failing configuration** (n = 5, 5_pure#379, partial6):
- sets [[0,1,4,5],[1,3,4,7],[2,3,6,7],[2,5,6,7],[3,4,5,6]];
- vals [[4,1,6,8],[3,10,6,2],[3,6,7,5],[4,6,8,5],[4,2,8,5]];
- o = (0, 3, 2, 4, 1), Y = (g5, g1, g3, g6, g4), u = 1.

The ejection chain 1 → 2 → 3 → 0 → 4 takes g3, g6, g5 and g4 in turn. Agent 4, whose goods are g3, g4, g5 and g6, is
left with nothing.

## 3. YRMH-L ("you take my last house, I get your turn"): not maximum on random cores

YRMH-L adds a rule to YRMH: an agent whose last available good the head is about to take moves to the head first.
- It repairs both configurations above.
- It works on all export data (n = 4, n = 5) and at the twins.
- A last-house test cannot see a tight *set* of agents. On random K4.MC2 cores it is not maximum at 363 of 43,572
  (start, receiver) pairs (`rf_maxcheck.log`).

**Smallest failing configuration** (n = 5; a matching statement only, with no EFX check, because this is not a
failing start):
- sets [[1,3,4],[0,1,2,4],[0,1,4,5],[0,1,3,4],[0,1,2,4]];
- vals [[4,16,17],[5,29,28,36],[30,1,26,22],[40,6,15,32],[33,29,15,16]];
- o = (0, 1, 4, 3, 2), Y = (g4, g1, g5, g3, g0), and u = 2, a receiver.

The run:
- 2 takes g0, ejecting 4, which takes g1, ejecting 1, which takes g4.
- Now agents 0 and 3 both have only g3 left. No single agent's last house was taken, so the last-house rule never
  fires, and one of them ends pickless: (g3, g4, g0, —, g1).
- YRMH-F gives the perfect (g3, g2, g0, g4, g1) instead: its guard sees that 1's taking g4 leaves {0, 3} with one house.

## Reproduce

```
python3 -c "import sys; sys.path[:0]=['k4/sdc','k4/ttc']
from oc1_mc2_rand import Inst; from rf_rules import yrmh; from rf_diag import promote_sd, feasible_sd
for S,V,o,u in [([[0,1,5,7],[1,4,5,7],[2,3,4,6],[2,3,6,7],[4,5,6,7]],[[2,3,10,6],[3,7,6,5],[3,5,6,7],[5,4,8,6],[6,5,8,4]],[3,2,1,4,0],0),
                ([[0,1,4,5],[1,3,4,7],[2,3,6,7],[2,5,6,7],[3,4,5,6]],[[4,1,6,8],[3,10,6,2],[3,6,7,5],[4,6,8,5],[4,2,8,5]],[0,3,2,4,1],1),
                ([[1,3,4],[0,1,2,4],[0,1,4,5],[0,1,3,4],[0,1,2,4]],[[4,16,17],[5,29,28,36],[30,1,26,22],[40,6,15,32],[33,29,15,16]],[0,1,4,3,2],2)]:
    I=Inst(S,V); Y=I.sd(o); q=[u]+[a for a in o if a!=u]
    print('Y',Y,'| ROT',I.sd(q),'| YRMH',yrmh(I,Y,o,u)[0],'| YRMH-L',promote_sd(I,Y,q)[0],'| YRMH-F',feasible_sd(I,Y,q)[0])"
python3 k4/ttc/rf_rules.py rf5                    # the twin image (results/k4_ttc/rf_rules_rf5.log)
python3 k4/ttc/rf_maxcheck.py 3000 2 5 8          # results/k4_ttc/rf_maxcheck.log
```
