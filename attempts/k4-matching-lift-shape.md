# LIFT-SHAPE⁺ and LIFT-EX: the second move always ends at the holder (k4/matching.md §6)

**Idea** (this workstream, from the n = 4 data; ledger K4.MATCH.LIFT).
- At a perfect start with ≤ 4 relevant goods per agent and no one-move repair, there is exactly one holder z.
- Some official chain P₁ from a dangerous agent k ends at z and absorbs a pair H₀¹ ⊆ J ∪ {y_z}, which a second dangerous
  agent also values above its pick.
- After P₁, a second chain P₂ also ends at z and gives z its favourite good, and its head owns. LIFT-EX asks for Lemma
  EX\* there. LIFT-SHAPE⁺ asks for the explicit form: P₂ canonical, z's new bundle a single good, and (L3) with case (a)
  or (b) of Lemma LIFT-1.

LIFT-SHAPE⁺ is certified at n = 4: all 112,880 starts with no one-move repair (K4.MATCH.LIFT.N4). It also held on all
8,073 walk failures (n = 4, 5) near the known instances.

**Where it breaks.** At n = 5 the second chain need not touch z. After P₁ it can be a chain of its own, disjoint from
P₁, that settles a second, independent danger set. The two chains then commute: two augmenting paths for a deficiency
of two. LIFT-EX's condition (3), a second chain ending at z with z's favourite good, then fails for every first chain.

**Smallest failing configuration** (n = 5, m = 8, k = 4, strict profile). Every n = 4 start satisfies LIFT-SHAPE⁺, so
n = 5 is the smallest n. This is the first n = 5 two-move start found by compute/k4-oc1max-cert: list 5_pure, idx 164.
- Sets [[0,2,3,7],[1,2,6,7],[3,4,5,6],[3,4,5,7],[4,5,6,7]]. Values [[1,8,6,4],[4,8,2,7],[6,7,3,5],[7,10,2,6],[7,5,3,6]].
- Order (1, 4, 2, 0, 3) gives picks (7, 2, 3, 5, 4) and junk {0, 1, 6}.
- The single holder is z = 3, holding 5. Its favourite good is 4, agent 4's pick. Agents 0, 1, 2 and 4 are dangerous.
- No assignment of the junk at the picks is EFX₀. No official first move is followed by any EFX₀ assignment of the
  remaining junk. Both are stronger than "no one-absorber completion".
- LIFT-SHAPE⁺: two first chains have the shape, (2, 0, 3) and (4, 2, 0, 3), both taking {5, 6}. No second chain
  completes either shape.
- LIFT-EX: 75 first chains satisfy condition (2). After none of them does an official second chain end at z with z's
  favourite good 4 in z's new bundle.
- Two disjoint chains do repair it:
  - P₁ = (2, 3): 2 takes {5, 6} (z's pick and junk), and 3 takes 2's pick 3. Here z is frozen afterwards, because agent
    0 wants 3, but agent 0 becomes a holder.
  - P₂ = (1, 0): 1 takes {1, 7} (junk and 0's pick), and 0 takes 1's pick 2. This chain is also official at the picks,
    and the two commute.
  - The last junk good 0 goes to agent 1. The allocation [[2], [1,7,0], [5,6], [3], [4]] is EFX₀.

**Reproduce:** `python3 attempts/k4_matching_lift_n5.py`, output in `results/k4_matching/lift_n5_cex.log`. It is
self-contained, with raw definitions and brute force over every official chain (junk for the chain agents included)
and every assignment of the junk.

**What survives.**
- Lemmas LIFT-red and LIFT-1 (K4.MATCH.LIFT1) are conditional and unaffected. So is the n = 4 certificate.
- CM₂ holds here: a first move followed by a Lemma EX\* exchange.
- The proof/k4-oc1max-multi session's recursion also covers this start: Lemma LIFT, then sub-lemma OC2-REC. The first
  chain (2, 3) takes the shared pool pair T = {5, 6}. Deleting agent 2 and T leaves the n = 4 instance on agents
  0, 1, 3, 4. Its state (7, 2, 3, 4) with junk {0, 1} is the SD outcome of order (1, 4, 3, 0). One move, (1, 0),
  repairs it there, and the completion does not threaten agent 2. The script checks the SD outcome and the lifted
  allocation (step 6).
- So the second move is "OC₁ one size down", not "a second chain to z". At n = 4 every second move found ends at z
  (certified); the reduced instance there has three agents.
