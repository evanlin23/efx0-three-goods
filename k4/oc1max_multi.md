# OC₁ at perfect starts with two or more dangerous agents (workstream `proof/k4-oc1max-multi`)

Target: Conjecture OC₁^max (K4.SDC.OC1MAX, `k4/sdc.md` §31). By Lemma RED (§31, end) it reduces to *perfect starts*:
- every agent with a relevant good holds a pick;
- null agents are allowed, and they count as ordinary agents for absorbers;
- the instance need not be a core;
- values are strict.

This note treats the starts with |D| ≥ 2 dangerous agents. The Hall session (`claude/k4-oc1-hall`, `k4/oc1_hall.md`
§15, §21) owns |D| = 1.

Notation follows `k4/oc1_hall.md`:
- Y = SD(π) are the picks, J the junk, and p_i = v_i(Y_i);
- i *wants* g if v_i(g) > v_i(B_i);
- F is the set of frozen agents, D ⊆ F the dangerous ones (frozen, and valuing a junk good), U the unfrozen agents;
- a bundle S *threatens* i at value t if v_i(S ∖ h) > t for some h ∈ S. This is monotone: larger S and smaller t
  threaten more.

The tools are those of the Hall session, all refereed CORRECT (`k4/referee/oc1_hall.md` on `claude/k4-referee`):
- Lemma 2\*: the exact S\* count for an owner o, under (G1), (G2);
- Corollary 2.1: its Hall form, "a transversal of the demands with a system of distinct admissible holders";
- Lemma D1-red (§21): the |D| = 1 reduction.

All code is mine (`k4/oc1max_multi/`, raw EFX₀, enumeration, no SAT), and shares nothing with `k4/oc1_hall/ohlib.py`.
Logs are in `results/k4_oc1max_multi/`. Everything called *evidence* is evidence only (PROMPT.md §5 rule 3).

## Status

| | statement | status |
|---|---|---|
| Data (§1) | every one-absorber-hard perfect start with \|D\| ≥ 2 in the Hall data sets (n ≤ 5, every order) and in random profiles of all 31,584 n = 5 core hypergraphs: **8,383 starts**, all repaired by one move; the ED form (Hall's OC₁-ED\*) holds on all | evidence. The collector reproduces the Hall session's counts exactly (2,071 hard maximum-matching starts, 197 with \|D\| = 1) |
| **Lemma D-red** (§2) | D1-red for any \|D\|. After a canonical chain from k ∈ D with owner k, the obstacles are exactly HEAD, CROWD and **DEMAND**: some d ∈ D ∖ {k}, still frozen after the chain, is threatened by the pool at its new value. With none of the three, an S\* completion owned by k exists | written proof; 0 violations in 11,988 clean chains |
| **Proposition T0** (§2) | at a hard perfect start, every unfrozen z (null agents included) has a dangerous agent threatened by J ∪ B_z: Θ(z) ≠ ∅. Every k ∈ Θ(z) has an improving set in J ∪ B_z | written proof; 0 violations |
| Corollary TR (§2) | if the head z of a canonical chain from k has Θ(z) ⊆ {k}, DEMAND cannot occur, and the chain behaves as in the case \|D\| = 1 (Hall §21: HEAD and CROWD only) | written proof |
| **Lemma KEEP** (§3) | let D_T be the *truly dangerous* agents (threatened by the junk alone). Take a canonical chain from k with an improving H₀ inside J, with no crowding, with the other truly dangerous agents and the head unthreatened by J, and with a holder admissible for the head's released pick Y_z. That holder is the head itself when the head is unfrozen, or the second wanter that froze it. Then that holder takes Y_z, and k owns an S\* completion. **Every pick-dangerous agent (D ∖ D_T) is harmless there, however many there are** | written proof; 0 violations in 18,916 chains |
| Corollary KEEP-1 (§3) | if D_T = {k}, the case reduces to the crowding and head obstacles of the case \|D\| = 1. **3,244 of the 3,259 starts with \|D_T\| = 1 have a KEEP chain**; the other 15 (all n = 5) have crowding by every minimal junk improving set (13) or a frozen, threatened head (2) | written proof; evidence for the count |
| **Lemma SET** (§4) | the overlap step of PWk(a), in general. After a canonical chain in which k takes a junk pair, k is settled for every owner other than k and x₁ whose base k does not want: it neither envies nor is envied. So k and the pair can be deleted. Agents that share the pair keep at most one junk good (Lemma PL(c)) | written proof; 0 mismatches in 3,373 owner tests |
| **Lemma OWN** (§4) | the overlap completion, PWk(a)'s owner w₂ in general. After a chain in which k takes a junk pair, an owner o ∉ {k, x₁} with a *free base* (no frozen agent and not k values it) owns an S\* completion, if the other truly dangerous agents are unthreatened by o's base plus J minus the pair (automatic when they share the pair, by Lemma PL(c)) and a holder takes the released pick. No crowding condition | written proof; 0 violations |
| Census (§5) | **7,602 of 8,383 starts (90.7%) are repaired by a chain to which KEEP, OWN or D-red applies** (proof modulo the chain's existence). 705 more are repaired by an obstructed canonical chain with owner k, and 76 need a chain whose head is a second dangerous agent (a *dangerous ring*) | evidence |
| Finding NC (§6) | D1-C (Hall §21) does not extend to \|D\| ≥ 2. In T3 (n = 3, m = 6) the only canonical chain with an improving set has CROWD, there is no other minimal H₀, and no canonical chain repairs. The repair is a ring through both dangerous agents | checked by enumeration (`attempts/k4-oc1max-multi-canonical.md`) |
| Step 2 of the plan (§4) | "after a chain from one dangerous agent, the others have at most one pool good left" (Lemma PL) holds only for agents that share two goods with H₀. For disjoint junk sets the other demands are untouched: they are removed by unfreezing, by raising values on the chain, or by slots (the head's slot first). In 95 starts with pairwise disjoint truly dangerous junk sets, every canonical chain leaves a demand, and only slots repair | `attempts/k4-oc1max-multi-pl-disjoint.md` |
| Open sub-lemmas (§7) | KEEP-C (\|D_T\| = 1, 4 starts), SLOT (\|D_T\| ≥ 2, and DEMAND when D_T = ∅; 701 starts), RING (76 starts, smallest T3), and the existence of the chains | open; each stated with its smallest instance |

## 1. The data

`k4/oc1max_multi/collect.py` (`runs.sh`; logs `collect.log`, `collect_n5.log`; starts in `hard2_starts*.jsonl.gz`).
For every instance and every order, the script:
1. computes the picks and keeps them if they form a maximum matching;
2. applies Lemma RED when a pickless agent has relevant goods. This happened 257 times, and none of the reduced starts
   was hard with |D| ≥ 2;
3. tests the one-absorber completion at the picks by enumeration;
4. keeps the start if it is hard and |D| ≥ 2, and tries every official move (additions, chains, rings; `mmlib.moves`).

| data | hard, \|D\| = 1 | \|D\| = 2 | \|D\| = 3 | \|D\| = 4 | kept, repaired by one move |
|---|---|---|---|---|---|
| special | 5 | 4 | 6 | 0 | 10 / 10 |
| screen | 14 | 84 | 77 | 7 | 166 / 166 |
| suite | 14 | 87 | 75 | 7 | 169 / 169 |
| logs | 112 | 678 | 364 | 46 | 1,088 / 1,088 |
| random cores n ≤ 3 (seed 91) | 41 | 252 | 0 | 0 | 252 / 252 |
| random cores n = 4 (seed 92) | 11 | 73 | 98 | 0 | 171 / 171 |
| random cores n = 5 (seed 93) | 0 | 2 | 8 | 6 | 16 / 16 |
| **all 31,584 n = 5 core hypergraphs, one random profile each** (seed 17, `oc1max_n5_lists.profile`) | 163 | 1,578 | 3,571 | 1,362 | 6,511 / 6,511 |

The |D| = 1 column matches `k4/oc1_hall.md` §15 (5, 14, 14, 112, 41, 11, 0).

**Shape.** Let u be the number of unfrozen pick holders. No kept start has a null agent.

| (u, \|D\|) | starts | no canonical chain repairs with owner k |
|---|---|---|
| (1, 2) | 1,943 | 49 |
| (1, 3) | 2,497 | 12 |
| (1, 4) | 1,428 | 0 |
| (2, 2) | 694 | 11 |
| (2, 3) | 1,700 | 7 |
| (3, 2) | 121 | 0 |

So 70% of the hard starts have a single unfrozen agent, which is then the head of every canonical chain, and the owner
at the picks has no holders.

**Overlap classes** (`analyze.py`, `analyze.log`). The junk sets J_d = J ∩ R_d (d ∈ D) are compared pairwise. A start
is *needs-pick* when some d ∈ D is not threatened by J alone, so that its danger needs another agent's pick.

| \|D\| | largest overlap of two J_d | needs-pick | starts | canonical chain from some k ∈ D, S\* owned by k |
|---|---|---|---|---|
| 2 | 0 | no | 322 | 322 |
| 2 | 0 | yes | 1,064 | 1,015 |
| 2 | 1 | no | 213 | 213 |
| 2 | 1 | yes | 934 | 925 |
| 2 | 2 | no / yes | 111 / 105 | 109 / 105 |
| 2 | 3 | no | 9 | 9 |
| 3 | 0 | no / yes | 25 / 673 | 25 / 660 |
| 3 | 1 | no / yes | 173 / 2,819 | 173 / 2,816 |
| 3 | 2 | no / yes | 101 / 373 | 101 / 370 |
| 3 | 3 | no / yes | 4 / 29 | 4 / 29 |
| 4 | 0 | yes | 70 | 70 |
| 4 | 1 | no / yes | 1 / 1,176 | 1 / 1,176 |
| 4 | 2 | no / yes | 3 / 176 | 3 / 176 |
| 4 | 3 | yes | 2 | 2 |

In all, 8,304 of 8,383 starts are repaired by a canonical chain with owner k: at n = 5, 6,506 of 6,511. All 8,383
satisfy OC₁-ED\* (an ED chain, S\* owned by x₀ or x_t).

## 2. Lemma D-red for any number of dangerous agents

**Setting.** Y is a perfect start with no one-absorber completion, k ∈ D, and P = (k = x₀, x₁, …, x_t = z), t ≥ 1, is a
*canonical chain*:
- each x_i (i ≥ 1) wants Y_{x_{i−1}} at the picks;
- the head z is unfrozen at the picks.

Write Π = J ∪ {Y_z} for the pool. Take H₀ ⊆ Π ∩ R_k with v_k(H₀) > p_k. Then B′ is the state after P:
- B′_k = H₀;
- B′_{x_i} = {Y_{x_{i−1}}} for 1 ≤ i ≤ t;
- every other agent keeps its pick;
- the junk is J′ = Π ∖ H₀.

The owner is k, so W_k = Π. For an unfrozen agent z, Θ(z) is the set of d ∈ D threatened by J ∪ B_z at p_d.

Facts from serial dictatorship:
- (π) If i wants Y_j, then j precedes i in π. If j precedes i, then v_j(Y_i) < p_j or Y_i ∉ R_j.
- (I2) Every agent values each junk good below its pick.
- (U) Nobody wants Y_z.
- At a perfect start the head holds a pick, since it wanted a good. Null agents value nothing.

**Lemma D-red (K4.MULTI.DRED).**
1. (G1) and (G2) hold at B′, and no agent other than k wants a good of Π.
2. Every agent frozen at B′, other than k, is frozen at the picks or is z.
   - A frozen agent of F ∖ D is threatened by no subset of Π, at any value at least its pick value.
   - Neither is any d ∈ D ∖ (Θ(z) ∪ {k}).
3. A holder at B′ that is exposed for some H ⊆ J′ is:
   - z;
   - an agent off P that is unfrozen at the picks; or
   - an agent of D ∖ {k} that is unfrozen at B′. This is new compared with |D| = 1: the chain *unfreezes* it.

   An exposed holder is non-movable in Lemma 2\*'s sense iff it is crowded by H₀.
4. Hence the condition C(B′, k) of Lemma 2\* reads: some H ⊆ J′ satisfies both of the following.
   - **(H1″)** No q ∈ (D ∖ {k}) ∪ {z} frozen at B′ is threatened by Π ∖ H at v_q(B′_q).
   - H has a system of distinct admissible holders that covers every crowded exposed holder.

   In particular, if none of the three obstacles below occurs, B′ has an S\* completion owned by k (H = ∅):
   - **HEAD:** z is frozen at B′ and threatened by Π;
   - **CROWD:** a holder u ≠ k has |H₀ ∩ R_u| ≥ 2 and v_u(H₀ ∩ R_u) > v_u(B′_u);
   - **DEMAND:** some d ∈ D ∖ {k} is frozen at B′ and threatened by Π at v_d(B′_d). By 2, d ∈ Θ(z).

*Proof.*
1. This is the proof of D1-red step 1, which does not use |D| = 1. Let g ∈ Π and i ≠ k.
   - If g ∈ J, then v_i(g) < p_i ≤ v_i(B′_i) by (I2).
   - If g = Y_z and i ≠ z, then v_i(g) ≤ p_i by (U).
   - If i = z, then v_z(Y_z) = p_z < v_z(Y_{x_{t−1}}).

   Every agent other than k holds at most one good, so (G1) holds.
2. The first sentence is D1-red step 2: an agent off P that was unfrozen at the picks stays unfrozen, since only
   values on P rose, and x₁, …, x_{t−1} are frozen at the picks.
   - An agent of F ∖ D values no junk, so it values at most one good of Π (Y_z). A set holding one good it values
     never threatens it.
   - For d ∈ D ∖ (Θ(z) ∪ {k}): Π does not threaten d at p_d, so by monotonicity no subset of Π threatens it at any
     value v ≥ p_d.
3. Let u be an exposed holder.
   - If u ∈ F ∖ D, then u values at most one good of Π and cannot be exposed.
   - The middle agents x₁, …, x_{t−1} are in F, so a middle agent that is exposed lies in D.
   - So u is z, off P and unfrozen at the picks, or in D ∖ {k}. In the last case u is unfrozen at B′, since it is a
     holder.
   - Non-movable means wanting a good of B′_k = H₀, which is impossible by 1, or having a danger set inside H₀, which
     is crowding.
4. Lemma 2\* applies by 1. Its condition (H1) concerns the frozen agents of B′ other than k. By 2, those other than z
   and D ∖ {k} are never threatened. ∎

**Proposition T0 (K4.MULTI.T0).** At a hard perfect start, every unfrozen agent z, null agents included, has
Θ(z) ≠ ∅. Every k ∈ Θ(z) values the pool J ∪ B_z above p_k. So a canonical chain from k to z, if one exists, has an
improving H₀.

*Proof.* Suppose Θ(z) = ∅. Apply Lemma 2 at the picks with owner z and H = ∅ (the hypotheses are checked as in Hall's
Proposition 3′):
- (G1): every agent other than z holds at most one good.
- (G2): by (I2), and pickless agents are null.
- (G5′): z is unfrozen.
- (H3): |B_z| ≤ 1.
- (H1): agents of F ∖ D value no junk. Those of D are unthreatened, by Θ(z) = ∅.
- (H2): θ ≤ |N₁|.

So an S\* completion owned by z exists. It is a one-absorber completion, a contradiction.

For k ∈ Θ(z), some h has v_k((J ∪ B_z) ∖ h) > p_k, so v_k((J ∪ B_z) ∩ R_k) > p_k. ∎

**Corollary TR.** If Θ(z) ⊆ {k} for the head z of a canonical chain from k, then DEMAND cannot occur on that chain.
Lemma D-red then has exactly the obstacles of D1-red (Hall §21), and Hall's analysis of HEAD and CROWD applies
unchanged, except where it uses that no other frozen agent values junk.

**Checks** (`dred.py`, `dred.log`; `theta.py`, `theta.log`). All canonical chains from every k ∈ D, with every
inclusion-minimal improving H₀, at all 8,383 starts: 24,404 chains, 11,988 of them clean (no HEAD, CROWD or
DEMAND). All 11,988 clean chains have an S\* completion owned by k, so there are 0 violations of D-red. T0 has 0
violations.

| obstacle (canonical chains, minimal H₀) | chains | repaired with owner k |
|---|---|---|
| none (clean) | 11,988 | 11,988 |
| DEMAND only | 10,469 | 8,858 |
| DEMAND + HEAD | 721 | 239 |
| CROWD only | 558 | 438 |
| CROWD + DEMAND | 293 | 131 |
| HEAD only | 368 | 288 |
| CROWD + HEAD, with or without DEMAND | 7 | 4 |

6,637 starts have a clean chain. A clean chain is of one of two kinds:
- **single-θ** (Θ(z) = {k}): 4,015 starts;
- one that neutralizes Θ(z) ∖ {k}, by unfreezing it or raising its value on the chain: 2,634 starts.

## 3. Truly dangerous agents: Lemma KEEP

Call d ∈ D **truly dangerous** if J threatens d at p_d (its junk alone is a danger set). Write D_T for this set. A
dangerous agent outside D_T is *pick-dangerous*: no subset of J threatens it at any value v ≥ p_d (monotonicity).
Typically it is threatened only through a pick it values. The exception is when it values every junk good: then a
worthless extra good in the owner's bundle is enough.

**Lemma KEEP (K4.MULTI.KEEP).** Let P = (k, …, z) be a canonical chain and H₀ ⊆ J ∩ R_k an improving set inside the
junk (the head's pick is not used). Let B′ be the state after P, and write Y_z for the head's released pick. Suppose:
- **(K1)** some holder u ≠ k at B′ is *admissible for Y_z against J*: J does not threaten u at v_u(B′_u), or u
  values Y_z and J does not threaten u at v_u(B′_u) + v_u(Y_z);
- **(K2)** no holder at B′ is crowded by H₀;
- **(K3)** every frozen q ∈ (D_T ∖ {k}) ∪ {z} at B′ is not threatened by J at v_q(B′_q).

Then B′ has an S\* completion owned by k in which u receives Y_z.

*If z is unfrozen at B′,* then (K1) holds with u = z, and (K3) for z is void. To see the first: R_z contains
a = Y_{x_{t−1}} and Y_z, so it holds at most two junk goods, each worth less than p_z (I2). Hence
v_z(J ∩ R_z) < 2p_z < v_z(a) + p_z, because v_z(a) > p_z. So J never threatens z at v_z(a) + p_z.

*Proof.* Apply Lemma 2\* at B′ with owner k and H = {Y_z}, so that W_k ∖ H = Π ∖ {Y_z} = J.
- (G1), (G2) hold by Lemma D-red 1.
- (H1): by D-red 2, the frozen agents of B′ other than k are frozen agents of the picks, or z. None of them is
  threatened by J at its value at B′:
  - an agent of F ∖ D values no junk;
  - an agent of D ∖ D_T is pick-dangerous, and its value at B′ is at least its pick value;
  - the agents of D_T ∖ {k}, and z, are covered by (K3).
- The system Y_z ↦ u consists of distinct admissible holders, by (K1).
- *There is no non-movable exposed holder.* Wanting a good of H₀ is impossible by D-red 1, and crowding is excluded by
  (K2).

Lemma 2\*'s (⇐) construction now gives the completion:
- u takes Y_z;
- the other exposed holders serve themselves by Theorem DT's moves inside J ∖ H₀;
- k takes the rest.

The two-good bundle {B′_u, Y_z} threatens nobody: B′_u is unwanted, since u is a holder, and Y_z is unwanted by
(U). ∎

**Corollary KEEP-1 (K4.MULTI.KEEP1).** If D_T = {k}, every canonical chain from k with an improving H₀ ⊆ J satisfying
(K1) and (K2) repairs, provided the head is unthreatened by J at its new value whenever it is frozen. Such chains always
exist as chains:
- k is frozen, so a canonical chain from k exists (Lemma D1-chain);
- J threatens k, so v_k(J ∩ R_k) > p_k, and an improving H₀ ⊆ J exists.

So |D_T| = 1, whatever |D| is, reduces to two local obstacles:
- crowding by every minimal junk improving set;
- no holder for the released pick, or a frozen head threatened by the junk.

These are the obstacles of the case |D| = 1 (Hall's D1-C and D1-H). The other dangerous agents, all pick-dangerous,
play no role.

*Why the released pick is kept out.* After P, the only pick in the pool is Y_z. Giving it to a holder (the head, or
the second wanter that froze the head) makes the owner's bundle a subset of J, and no subset of J threatens a
pick-dangerous agent.

**Checks** (`lemma_b.py`, `lemma_keep.log`). For each KEEP chain, the explicit completion of the lemma (u takes Y_z,
raw EFX₀) exists:
- 18,916 KEEP chains (all holders u), 0 violations;
- among them the 6,751 chains with u = z an unfrozen head, also 0 violations.

By |D_T|:

| \|D_T\| | starts | some KEEP chain | other |
|---|---|---|---|
| 0 | 2,512 | none possible | §5 |
| 1 | 3,259 | **3,244** | 15, all at n = 5: 13 with crowding by every minimal junk improving set, 2 with a frozen head threatened by J or no holder for Y_z |
| 2 | 2,205 | 1,443 | 762 |
| 3 | 403 | 152 | 251 |
| 4 | 4 | 0 | 4 |

The 15 are repaired by D-red (7) or by an obstructed canonical chain with owner k (8). The smallest is n4_4#1715.0
(n = 5, m = 8). r197 (n = 4, m = 7) is the smallest start whose head is always frozen: its two unfrozen wanters 2 and 3
both want 6. It is a KEEP start with u the second wanter: [[3], [1,4,0], [6], [5,2]].

## 4. Steps 2 and 3 of the plan: disjoint and overlapping danger sets

**Disjoint junk sets: Lemma PL does not reach them.** Lemma PL(c) (`k4/ksens.md`, refereed CORRECT) bounds the
leftover junk of an agent z only when z values two goods of k's set H. If J_d ∩ H₀ = ∅, the chain from k does not
touch J_d. A truly dangerous d keeps its whole danger set in the pool (`attempts/k4-oc1max-multi-pl-disjoint.md`).

What removes such a demand, in this order of frequency on the data:
- *Unfreezing.* d's wanters are on the chain and prefer their new goods. 2,634 starts have a clean chain of this kind
  or one that raises d's value on the chain.
- *Slots.* At least one good of J_d is kept out of the owner's bundle by a holder. The chain itself makes one new
  holder, the head z.

In 95 starts whose dangerous agents are all truly dangerous, with pairwise disjoint junk sets, *every* canonical chain
leaves a demand, and only slots repair. The smallest is n4_3#211.0 (n = 5, m = 9), shown in the attempts file. There
the chain 0 → 3 → 2 gives agent 0 the set {0, 2}, and the head 2 keeps junk good 1 out of the owner's bundle, which
breaks agent 1's danger set {1, 3}.

So the lemma step 2 needs is a count, sub-lemma SLOT (§7), not a leftover bound.

**Overlapping junk sets: Lemma SET**, the general form of PWk(a)'s step x₁ → w₁ (`k4/ksens.md` §7).

**Lemma SET (K4.MULTI.SET).** Let P be a canonical chain from k with an improving junk pair H₀ = {g, g′} ⊆ J. Let X be
an S\*-shaped completion of B′ whose owner o satisfies:
- o ∉ {k, x₁};
- k does not want B′_o.

Then k takes nothing in X (it holds two goods), and:
- (a) nobody strongly envies k: removing a good of H₀ leaves one junk good, worth less to every agent with a pick than
  its pick, by (I2);
- (b) k strongly envies nobody.

Hence such completions of B′ are exactly X_k = H₀ together with an EFX₀ S\*-shaped completion of the *reduced state*:
- agent k and the goods H₀ are deleted;
- the holders are those of B′.

Every d ∈ D that values g and g′ keeps at most one good of J ∖ H₀ (Lemma PL(c)).

*Proof of (b).* |R_k| ≤ 4, so R_k = {Y_k, g, g′} plus at most one good ℓ. Y_k is held by x₁ ≠ o.
- *x₁'s bundle.* If x₁ is a holder with slot good s, removing s leaves Y_k, worth p_k < v_k(H₀). Removing Y_k leaves
  s, a junk good: s ∈ J′ = (J ∖ H₀) ∪ {Y_z}, worth at most p_k by (I2) and (U).
- *The owner's bundle* X_o meets R_k in at most ℓ, since Y_k, g and g′ are elsewhere. So removing any of its goods
  leaves k at most v_k(ℓ):
  - if ℓ = B′_o, k does not want it, so v_k(ℓ) ≤ v_k(H₀);
  - otherwise ℓ ∈ J′, worth at most p_k.
- *A holder's bundle* {B′_u, s} with u ≠ x₁ meets R_k in at most ℓ, and v_k(ℓ) ≤ v_k(H₀): a holder's base is
  unwanted, and a slot good is in J′.
- *Frozen agents* hold one good and take nothing. ∎

*Check* (`lemma_set.py`, `lemma_set.log`). At every canonical chain with an improving junk pair, for every admissible
owner: 3,373 owner tests on the small data sets, 0 mismatches between the S\* test in the instance and in the reduced
instance.

Both owner conditions are needed:
- in Q2 (picks (1, 3, 5, 4), chain 3 → 0), the owner 2 holds the pick 5 that k = 3 wants;
- in hall-local3 (picks (0, 2, 3), chain 2 → 0), the owner x₁ = 0 holds k's old pick 3 together with k's last junk
  good 6, and 7 + 6 > 8.

PWk(a) is the case o = w₂.

**Lemma OWN (K4.MULTI.OWN): the overlap completion.** This is PWk(a)'s owner w₂, in general. Let P = (k, …, z) be a
canonical chain from k with an improving junk pair H₀ = {g, g′} ⊆ J, and B′ the state after P. Let o be the owner, and
W = B′_o ∪ (J ∖ H₀). Suppose:
- **(W2)** o ∉ {k, x₁}, o holds at most one good, o is unfrozen at B′, and neither k nor any agent frozen at B′
  values the good of B′_o (o has a *free base*; a null agent always qualifies);
- **(W1)** every frozen d ∈ D_T ∖ {k} at B′ is not threatened by W at v_d(B′_d);
- **(W3)** some holder u ≠ o is admissible for Y_z against W. Moreover, if z is frozen at B′, W does not threaten z
  at v_z(B′_z).

Then B′ has an S\* completion owned by o in which u receives Y_z and k keeps exactly H₀.

(W1) holds automatically for every d ∈ D_T that values both g and g′. By Lemma PL(c), d values at most one good of
J ∖ H₀, and d does not value B′_o, so W contains at most one good of R_d.

*Proof.* Apply Lemma 2\* at B′ with owner o and H = {Y_z}. Then W_o ∖ H = W.
- *(G1).* The non-holders other than o are k (bundle H₀) and frozen singletons. H₀ threatens nobody: removing one of
  its goods leaves one junk good, worth less than the pick of every agent that values it (I2), and values only rose.
  Null agents value nothing.
- *(G2)* holds by D-red 1. In addition, k wants no junk good: each is worth less than p_k < v_k(H₀), and
  v_k(Y_z) ≤ p_k by (U).
- *(H1).* Every non-holder q ≠ o is unthreatened by W at v_q(B′_q):
  - *q = k.* R_k is Y_k, H₀ and at most one more good ℓ, since |R_k| ≤ 4. Y_k is x₁'s and x₁ ≠ o, and H₀ ∩ W = ∅. So
    W ∩ R_k ⊆ {ℓ}, a single good, which never threatens.
  - *q frozen at B′, q ∈ F ∖ D.* q values no junk, and does not value B′_o, so W ∩ R_q = ∅.
  - *q frozen at B′, q ∈ D ∖ D_T* (pick-dangerous). W ∩ R_q ⊆ J ∖ H₀. If J has a good outside R_q, then
    v_q(J ∩ R_q) ≤ p_q, because J does not threaten q. If J ⊆ R_q, then v_q(J) − min_J v_q ≤ p_q, and J ∖ H₀ omits
    at least one good of J. Either way, v_q(W ∩ R_q) ≤ p_q ≤ v_q(B′_q).
  - *q ∈ D_T ∖ {k}* is covered by (W1), and *q = z* by (W3). By D-red 2, there are no other frozen agents.
- *The system Y_z ↦ u* consists of distinct admissible holders, by (W3).
- *No non-movable exposed holder.* o is unfrozen at B′, so no holder wants B′_o, and |B′_o| ≤ 1 leaves no room for a
  danger set inside B′_o.

Lemma 2\*'s (⇐) construction gives the completion, and k, a non-holder, receives nothing. ∎

No crowding condition is needed: the pair H₀ lies in k's bundle, not in the owner's. That is the difference from
KEEP, where k owns. The two lemmas are complementary:
- KEEP needs the other truly dangerous agents unthreatened by all of J;
- OWN needs them unthreatened by J ∖ H₀ only, which is automatic for agents sharing the pair, at the price of a
  free-base owner.

*Checks* (`lemma_own.py`, `lemma_own.log`). Every (chain, junk pair, owner, holder) quadruple satisfying
(W1)–(W3) has the explicit completion, checked with raw EFX₀: 0 violations.

The first version of the check tested (W1) against J ∖ H₀ instead of W, and failed on 9 quadruples. For example, in
log732, picks (7, 6, 3, 4), agent 0 values {2, 0} at 9 > 8. A set threatens d through its goods *outside* R_d too,
because removing a worthless good removes nothing.

## 5. The census: which mechanism repairs each start

`regimes.py`, `regimes.log`. For each start, the first mechanism in this list that repairs it:
1. KEEP (a written proof applies);
2. OWN (a written proof applies);
3. CLEAN (D-red applies);
4. CAN-k (a canonical chain with obstacles, owner k);
5. ED (an ED chain, owner x₀ or x_t);
6. any move.

| regime | starts | KEEP | OWN | CLEAN | CAN-k | ED | none |
|---|---|---|---|---|---|---|---|
| D_T = ∅ | 2,512 | – | 410 | 1,867 | 161 | **74** | 0 |
| \|D_T\| = 1 | 3,259 | **3,244** | 7 | 4 | 4 | 0 | 0 |
| \|D_T\| ≥ 2 | 2,612 | 1,595 | 469 | 6 | 540 | 2 | 0 |
| all | 8,383 | 4,839 | 886 | 1,877 | 705 | 76 | 0 |

The smallest instances in each cell are listed in `regimes.log`:
- D_T = ∅, ED: **T3** (n = 3, m = 6), order (0, 1, 2);
- D_T = ∅, CAN-k: induct-q4-rules (n = 3, m = 5);
- |D_T| = 1, CAN-k: n4_4#1715.0 (n = 5, m = 8);
- |D_T| ≥ 2, CAN-k: hall-local3 (n = 3, m = 7);
- |D_T| ≥ 2, ED: r640 (n = 4, m = 8).

So **7,602 of the 8,383 starts (90.7%) are repaired by a chain to which a written lemma (KEEP, OWN or D-red)
applies**. With |D_T| = 1, 3,255 of 3,259 are. The
lemma proves the repair once the chain is given; the chain's existence is the open part.

## 6. Finding NC: canonical chains do not suffice at |D| ≥ 2, and D1-C does not extend

T3, order (0, 1, 2), picks (0, 4, 1), J = {2, 3, 5}:

| agent | ranking (pick \*, junk j) | pick | wanted by |
|---|---|---|---|
| 0 | 0(38)\* > 4(36) > 2(6)j > 5(1)j | 0 | 2 (frozen) |
| 1 | 4(30)\* > 1(22) > 3(12)j | 4 | 2 (frozen) |
| 2 | 0(38) > 4(28) > 1(20)\* > 3(12)j | 1 | none |

Here D = {0, 1}, D_T = ∅, and Θ(2) = {1}.
- *No other canonical chain.* The only unfrozen agent is 2. The chain 0 → 2 has no improving set: J ∪ {1} gives agent 0
  only 6 + 1.
- *The single-θ chain 1 → 2 fails.* Agent 1 takes {1, 3}, its only improving set (22 + 12 > 30). The head 2 then holds
  4 (28) and is crowded by {1, 3} (20 + 12 > 28). Agent 2 values neither remaining junk good, so it cannot be
  compensated, and no owner works.

So the |D| ≥ 2 analogue of Hall's D1-C ("another minimal H₀ on the same chain") is false: Corollary TR's
single-θ chain has CROWD and nothing else.

*The repair* is a ring through both dangerous agents, written as the ED chain 0 → 2 → 1:
- agent 2 takes 0;
- agent 1 takes 2's pick 1 plus junk 3 (34 > 30);
- agent 0 takes 1's pick 4 plus junk 2 (42 > 38).

All 79 starts without a canonical repair have a repair of this kind or with an unfrozen head taking junk. Of their
repairing ED chains:
- 50 + 27 + 6 + 3 have a frozen dangerous head whose pick goes to k (so 1 ∈ D is the head and Y_1 ∈ H₀);
- 17 + 2 have an unfrozen head with head junk.

`attempts/k4-oc1max-multi-canonical.md` has the script. That canonical chains alone do not suffice was known
(adaptive-p1, `attempts/k4-oc1-hall-canonical-chains.md`). New here: it fails even on single-θ chains, and in T3 no
alternative H₀ exists.

## 7. What is left: the open sub-lemmas

Each statement is local. Each is checked on all 8,383 starts, and is stated with its smallest instance.

- **KEEP-C (K4.MULTI.KEEPC).** Suppose D_T = {k}, and no KEEP or OWN chain exists: every canonical chain from k with a
  minimal improving H₀ ⊆ J has crowding, a frozen head threatened by J, or no holder for Y_z, and no free-base owner
  fits. Then some canonical chain from k repairs with owner k: the crowded holder is compensated by a junk good, or H₀
  uses Y_z.
  - Data: 8 starts, all n = 5. D-red covers 4 of them, and an obstructed canonical chain the other 4.
  - Smallest: n4_4#1715.0 (n = 5, m = 8).
  - The |D| = 1 analogue is Hall's D1-C (smallest r1179). Since KEEP makes the pick-dangerous agents irrelevant, a
    proof of D1-C for an agent k ∈ D_T that does not use "no other frozen agent values junk" would cover KEEP-C.
- **SLOT (K4.MULTI.SLOT).** Either |D_T| ≥ 2, or D_T = ∅ with DEMAND from a second dangerous agent that values Y_z.
  Some canonical chain from some k ∈ D leaves demands that fit Lemma 2\*'s count at B′, with owner k.
  - The head z is the chain's new slot. If it is unfrozen afterwards, it is admissible for its own old pick (KEEP's
    argument).
  - In the smallest disjoint example (`attempts/k4-oc1max-multi-pl-disjoint.md`), the head keeps out a good of the
    other agent's danger set instead.
  - Data: 540 + 161 starts are repaired only this way.
  - The slot structure (`slot_stats.py`, `slot_stats.log`), counting the fewest kept-out goods over the repairing
    chains of each of the 705 starts:
    - one good in 544 starts: the head takes it in 315, and another holder in 229;
    - two goods in 155;
    - three goods in 6.

    In most one-good repairs the good belongs to another truly dangerous agent's junk set (the head: 222 starts).
    So the count to prove is that one or two slots, the head's among them, cover what the chain leaves.
  - Smallest: hall-local3 (n = 3, m = 7) and induct-q4-rules (n = 3, m = 5).
- **RING (K4.MULTI.RING).** If no canonical chain repairs, some ED chain repairs with owner k. In it, either the head
  is a dangerous agent d with Y_d ∈ H₀ (a ring through two dangerous agents), or an unfrozen head takes junk.
  - Data: 76 of 76 starts (74 with D_T = ∅).
  - Smallest: T3 (n = 3, m = 6).
- **The existence part.** In every regime the lemmas assume the right chain. What is missing is an argument that a
  hard start has a KEEP, OWN or clean chain, or else the SLOT or RING configuration.

*Honest scope.* The written proofs here are reductions. They prove that a chain *with property X* repairs, and the data
show such a chain exists in 90.7% of the starts. The existence of the chain is not proved in any regime.

The most promising next step is |D_T| = 1. There KEEP or OWN chains exist on 3,251 of 3,259 starts, and the 8
exceptions have exactly the crowding obstacle of |D| = 1. So the existence argument should be done together with the
Hall session's D1-C.

For D_T = ∅, Proposition T0 says every unfrozen z has some d ∈ Θ(z). Such a d values Y_z together with junk, unless
d values every junk good: then J ∪ {Y_z} can threaten d through the worthless good Y_z, while J alone cannot. Outside
that exception, each dangerous agent values at most two picks besides its own (|R_d| ≤ 4, with at least one junk
good). So there are at most 2|D| unfrozen pick holders. That is the start of a count.
