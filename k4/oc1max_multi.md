# OC₁ at perfect starts with two or more dangerous agents (workstream `proof/k4-oc1max-multi`)

**Update (2026-11-27): OC₁^max is refuted at n = 4** (`compute/k4-oc1max-cert`; coordinator's `k4/sdc.md` §31; Hall
§22). The 11 n = 4 failures and the TTC session's n = 5 core are perfect starts with |D| ≥ 2 and a *shared pool danger
set*. The corrected target is **OC₂^max**: at most two sequential moves. Everything in §1–§7 is about given states or
about the 8,383 starts of §1, which are all repaired by one move, so all of it stands. §8 checks the failures against
these lemmas and treats the second move.

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

The tools are those of the Hall session:
- Lemma 2\*: the exact S\* count for an owner o, under (G1), (G2);
- Corollary 2.1: its Hall form, "a transversal of the demands with a system of distinct admissible holders";
- Lemma D1-red (§21): the |D| = 1 reduction, whose proof §2 generalizes.

Lemma 2\* and Corollary 2.1 are refereed CORRECT (`k4/referee/oc1_hall.md` on `claude/k4-referee`).

**Refereed (2026-11-27, `k4/referee/oc1max_multi.md` on `claude/k4-referee`):** Lemma D-red, Proposition T0, Corollary
TR, Lemma KEEP with Corollary KEEP-1, Lemma SET, Lemma OWN and Lemma RING-red are CORRECT. Finding NC (T3) is
confirmed. The referee's independent check covered 172,394 chains with every improving H₀, and dropping any one
hypothesis produces failures. Its four wording fixes are applied below. Theorem U and Lemma LIFT are not yet
refereed.

All code is mine (`k4/oc1max_multi/`, raw EFX₀, enumeration, no SAT), and shares nothing with `k4/oc1_hall/ohlib.py`.
As a cross-check, `xcheck_hall.py` compares my one-absorber enumeration with the Hall session's independent
`ohlib.absorb_brute` at every kept start and every repaired state of the small data sets: 16,518 states, 0
mismatches. Logs are in `results/k4_oc1max_multi/`. Everything called *evidence* is evidence only (PROMPT.md §5
rule 3).

## Status

| | statement | status |
|---|---|---|
| Data (§1) | every one-absorber-hard perfect start with \|D\| ≥ 2 in the Hall data sets (n ≤ 5, every order) and in random profiles of all 31,584 n = 5 core hypergraphs: **8,383 starts**, all repaired by one move; the ED form (Hall's OC₁-ED\*) holds on all | evidence. The collector reproduces the Hall session's counts exactly (2,071 hard maximum-matching starts, 197 with \|D\| = 1) |
| **Lemma D-red** (§2) | D1-red for any \|D\|. After a canonical chain from k ∈ D with owner k, the obstacles are exactly HEAD, CROWD and **DEMAND**: some d ∈ D ∖ {k}, still frozen after the chain, is threatened by the pool at its new value. With none of the three, an S\* completion owned by k exists | written proof; 0 violations in 11,988 clean chains |
| **Proposition T0** (§2) | at a hard perfect start, every unfrozen z (null agents included) has a dangerous agent threatened by J ∪ B_z: Θ(z) ≠ ∅. Every k ∈ Θ(z) has an improving set in J ∪ B_z | written proof; 0 violations |
| Corollary TR (§2) | if the head z of a canonical chain from k has Θ(z) ⊆ {k}, DEMAND cannot occur, and the chain behaves as in the case \|D\| = 1 (Hall §21: HEAD and CROWD only) | written proof |
| **Lemma KEEP** (§3) | let D_T be the *truly dangerous* agents (threatened by the junk alone). Take a canonical chain from k with an improving H₀ inside J, with no crowding, with the other truly dangerous agents and the head unthreatened by J, and with a holder admissible for the head's released pick Y_z. That holder is the head itself when the head is unfrozen, or the second wanter that froze it. Then that holder takes Y_z, and k owns an S\* completion. **Every pick-dangerous agent (D ∖ D_T) is harmless there, however many there are** | written proof; 0 violations in 18,916 chains |
| **Theorem U, Corollary U1** (§3) | **OC₁ holds at every perfect start with one truly dangerous agent and exactly one unfrozen pick holder** (any \|D\|, null agents allowed): every longest canonical chain from k with every improving H₀ ⊆ J repairs. More generally (Theorem U), it holds when the junk threatens no unfrozen pick holder other than the head of a longest chain | written proof, **unconditional on its class**; 2,234 starts (U1) and 2,880 (U), 0 violations |
| Corollary KEEP-1 (§3) | if D_T = {k}, the case reduces to the crowding and head obstacles of the case \|D\| = 1. **3,244 of the 3,259 starts with \|D_T\| = 1 have a KEEP chain**; the other 15 (all n = 5) have crowding by every minimal junk improving set (13) or a frozen, threatened head (2) | written proof; evidence for the count |
| **Lemma SET** (§4) | the overlap step of PWk(a), in general. After a canonical chain in which k takes a junk pair, k is settled for every owner other than k and x₁ whose base k does not want: it neither envies nor is envied. So k and the pair can be deleted. Agents that share the pair keep at most one junk good (Lemma PL(c)) | written proof; 0 mismatches in 47,248 owner tests |
| **Lemma OWN** (§4) | the overlap completion, PWk(a)'s owner w₂ in general. After a chain in which k takes a junk pair, an owner o ∉ {k, x₁} with a *free base* (no frozen agent and not k values it) owns an S\* completion, if the other truly dangerous agents are unthreatened by o's base plus J minus the pair (automatic when they share the pair, by Lemma PL(c)) and a holder takes the released pick. No crowding condition | written proof; 0 violations in 21,440 cases |
| **Lemma RING-red** (§6) | a dangerous ring k → … → d (d ∈ D takes its predecessor's pick plus junk, d's pick goes to k), owner k, with four local conditions: Lemma 2\* with H = ∅. It covers T3 with the order (0, 1, 2) | written proof; 0 violations in 7,347 rings |
| Census (§5) | **7,753 of 8,383 starts (92.5%) are repaired by a chain to which KEEP, OWN, D-red or RING-red applies** (proof modulo the chain's existence, except under Theorem U). 585 more are repaired by an obstructed canonical chain with owner k (SLOT), and 45 by other ED chains | evidence |
| Finding NC (§6) | D1-C (Hall §21) does not extend to \|D\| ≥ 2. In T3 (n = 3, m = 6) the only canonical chain with an improving set has CROWD, there is no other minimal H₀, and no canonical chain repairs. The repair is a ring through both dangerous agents | checked by enumeration (`attempts/k4-oc1max-multi-canonical.md`) |
| Step 2 of the plan (§4) | "after a chain from one dangerous agent, the others have at most one pool good left" (Lemma PL) holds only for agents that share two goods with H₀. For disjoint junk sets the other demands are untouched: they are removed by unfreezing, by raising values on the chain, or by slots (the head's slot first). In 95 starts with pairwise disjoint truly dangerous junk sets, every canonical chain leaves a demand, and only slots repair | `attempts/k4-oc1max-multi-pl-disjoint.md` |
| Known OC₁^max failures (§8) | all 12 (the certifier's 11 n = 4 cores, the TTC n = 5 core) re-verified with this note's code. None meets the hypotheses of any lemma here (consistency). All have one unfrozen pick holder and a shared pool danger set, with DEMAND or CROWD only | checked (`cex_check.log`) |
| **Lemma LIFT** (§8) | the second move as a move of a smaller instance: after k takes a pair everyone else values below their holding, deleting k and the pair turns moves and completions of the reduced instance into moves and completions of the original, provided nothing threatens k | written proof |
| Sub-lemma OC2-REC (§8) | some sharer's first chain leaves a perfect SD start of the reduced instance where one move repairs: OC₂ = settle one sharer, then OC₁ one size down. It holds on all 12 known failures and on all 4,955 walk failures near them (D-red proves the reduced repair at 4,923) | open; evidence |
| Open sub-lemmas (§7) | KEEP-C (\|D_T\| = 1, 4 starts), SLOT (\|D_T\| ≥ 2, and DEMAND when D_T = ∅; 581 starts), RING (45 starts not covered by RING-red), and the existence of the chains outside Theorem U | open; each stated with its smallest instance |

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

*Which repairing chain works.* Counting over every canonical chain from every k ∈ D and every improving H₀ (per class
in `analyze.log`):

| repair | starts (of 8,383) |
|---|---|
| canonical chain, S\* owned by k | 8,304; at n = 5, 6,506 of 6,511 |
| the same with an inclusion-minimal H₀ | 8,304 |
| canonical chain, S\* owned by the head z | 8,020 |
| canonical chain with a minimal H₀, S\* owned by an agent outside {k, z} | 8,073 |
| canonical chain, any one-absorber completion | 8,309 |
| ED chain, S\* owned by x₀ or x_t (OC₁-ED\*) | **8,383** |

So minimality of H₀ never costs anything, and owner k is the best single choice. The 74 starts with no canonical
repair at all lie in the RING class of §7.

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

   Moreover k wants no good of J′: junk is worth less than p_k < v_k(H₀), and v_k(Y_z) ≤ p_k by (U). So (G2) holds.
   Every agent other than k holds at most one good, so (G1) holds.
2. The first sentence is D1-red step 2: an agent off P that was unfrozen at the picks stays unfrozen, since only
   values on P rose, and x₁, …, x_{t−1} are frozen at the picks.
   - An agent q ∈ F ∖ D values no junk, so it values at most one good of Π, namely Y_z, and
     v_q(Y_z) ≤ p_q ≤ v_q(B′_q) by (U). So removing any good from a subset of Π leaves at most v_q(B′_q), and q is
     never threatened.
   - For d ∈ D ∖ (Θ(z) ∪ {k}): Π does not threaten d at p_d, so by monotonicity no subset of Π threatens it at any
     value v ≥ p_d.
3. Let u be an exposed holder.
   - If u ∈ F ∖ D, then u values at most Y_z in Π, worth at most p_u by (U), so u cannot be exposed (as in 2).
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

**Theorem U (K4.MULTI.U): one truly dangerous agent, and the junk threatens no other unfrozen agent.** Let Y be a
perfect start with no one-absorber completion, and D_T = {k}, with |D| arbitrary. Let E_J be the set of unfrozen pick
holders u that J threatens at p_u. Let P = (k = x₀, …, x_t = z) be a *longest* canonical chain from k, and H₀ ⊆ J ∩ R_k
any improving set. Suppose:
- E_J ⊆ {z};
- if z ∈ E_J, then z is unfrozen at B′.

Then B′ has an S\* completion owned by k. Its owner's bundle is a subset of J, and the released pick Y_z goes to the
head z, or to an unfrozen second wanter of the head's new good.

The hypothesis D_T = {k} says that J threatens no dangerous agent other than k at its pick value. Values only rise
along the chain, so J also threatens none of them at its value after the chain. This covers every frozen dangerous
agent after P, including a dangerous middle agent of P. That is what (H1) of Lemma 2\* needs, since the owner's
bundle is a subset of J. (The Hall session asked; the condition is part of D_T = {k}.)

**Corollary U1 (K4.MULTI.U1).** *OC₁ holds at every perfect start that has exactly one unfrozen pick holder and exactly
one truly dangerous agent*, whatever |D| is, null agents allowed. Every longest canonical chain from k, with every
improving H₀ ⊆ J, repairs. Here the existence of the chain is part of the statement, not an assumption.

*Proof of Theorem U.*
0. *The chain exists.* k is frozen, so canonical chains from k exist (Lemma D1-chain), and a longest one exists. J
   threatens k, so v_k(J ∩ R_k) > p_k, and an improving H₀ ⊆ J exists.
1. *The holder for Y_z.* If z is unfrozen at B′, let u = z; it is admissible for Y_z (see Lemma KEEP).

   Otherwise a = Y_{x_{t−1}} has a wanter w at B′. By D-red (proof of 2), w is off P and wanted a at the picks.
   - w is unfrozen at the picks. Otherwise the walk up from w (w's wanter, that agent's wanter, …) would give a
     canonical chain (x₀, …, x_{t−1}, w, …) with more agents than P. Its agents are distinct by (π), as in Hall's §21
     Remark 2. That contradicts the choice of P.
   - w holds a pick: it wants a good, and pickless agents at a perfect start are null.
   - So w is an unfrozen pick holder, w ≠ z, and w ∉ E_J. By D-red 2, w is unfrozen at B′, so it is a holder, with
     value p_w.
   - J does not threaten w at p_w, so w is unexposed, hence admissible for every good. Let u = w.

   In this case z ∉ E_J, by the hypothesis. So J does not threaten z at p_z, nor at v_z(a) > p_z.
2. *Lemma 2\* at B′, owner k, H = {Y_z}.* Then W_k ∖ H = J.
   - (G1), (G2): D-red 1.
   - (H1): the frozen agents of B′ other than k are frozen at the picks, or z (D-red 2). Agents of F ∖ D value no junk.
     Agents of D ∖ D_T are not threatened by any subset of J at any value ≥ their pick value. D_T ∖ {k} is empty. z, if
     frozen, is covered by step 1.
   - *System of representatives:* Y_z ↦ u, admissible by step 1.
   - *Every exposed holder other than u is covered.* By D-red 3, an exposed holder is z, an off-P agent unfrozen at the
     picks, or an agent of D ∖ {k} unfrozen at B′.
     - An off-P agent v unfrozen at the picks has value p_v. It is exposed iff v ∈ E_J ⊆ {z}, so it is not exposed.
     - An agent d ∈ D ∖ {k} unfrozen at B′ is exposed only if J threatens it at v_d(B′_d) ≥ p_d. Then J threatens it
       at p_d, so d ∈ D_T = {k}, which is impossible.
     - z is a holder only when it is unfrozen at B′, and then it is u, which is covered.

   So every exposed holder is covered by the system, crowded or not, and Lemma 2\* gives the completion. ∎

*Proof of Corollary U1.* At a perfect start the head of a canonical chain holds a pick, so with one unfrozen pick
holder z, every chain ends at z, and E_J ⊆ {z}. By step 1, a wanter of a at B′ would be an unfrozen pick holder other
than z, so z is unfrozen at B′. Theorem U applies to every longest chain and every improving H₀ ⊆ J. ∎

*Why crowding disappears.* A crowded holder is a problem only when it is exposed. Under the hypothesis the only
possible exposed holder is the head, and its slot (its own old pick) already makes it safe, because
v_z(J ∩ R_z) < 2p_z < v_z(a) + p_z.

*Checks* (`theorem_u1.py`, `theorem_u.log`).
- Among the 8,383 starts, 3,259 have |D_T| = 1. Theorem U's hypothesis holds for some longest chain at **2,880** of
  them, and every (longest chain, improving H₀ ⊆ J) pair meeting it repairs: 5,266 pairs, 0 violations.
- Corollary U1 covers **2,234** starts, at each of which every longest chain repairs.
- On the 197 one-absorber-hard starts with |D| = 1 (the Hall session's class), 41 have k ∈ D_T. Theorem U applies at
  15 of them, with 0 violations.

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
owner: 47,248 owner tests on all 8,383 starts, 0 mismatches between the S\* test in the instance and in the reduced
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
    W ∩ R_k ⊆ {ℓ}. By (W2), ℓ ∉ B′_o, so ℓ is junk, with v_k(ℓ) < p_k < v_k(H₀). Hence W does not threaten k.
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
(W1)–(W3) has the explicit completion, checked with raw EFX₀: 21,440 quadruples, 0 violations.

The first version of the check tested (W1) against J ∖ H₀ instead of W, and failed on 9 quadruples. For example, in
log732, picks (7, 6, 3, 4), agent 0 values {2, 0} at 9 > 8. A set threatens d through its goods *outside* R_d too,
because removing a worthless good removes nothing.

## 5. The census: which mechanism repairs each start

`regimes.py`, `regimes.log`. For each start, the first mechanism in this list that repairs it:
1. KEEP (Lemma KEEP applies);
2. OWN (Lemma OWN applies);
3. CLEAN (Lemma D-red applies);
4. RING (Lemma RING-red applies, §6);
5. CAN-k (a canonical chain with obstacles, owner k);
6. ED (an ED chain, owner x₀ or x_t);
7. any move.

| regime | starts | KEEP | OWN | CLEAN | RING | CAN-k | ED | none |
|---|---|---|---|---|---|---|---|---|
| D_T = ∅ | 2,512 | – | 410 | 1,867 | 97 | 95 | 43 | 0 |
| \|D_T\| = 1 | 3,259 | **3,244** | 7 | 4 | 0 | 4 | 0 | 0 |
| \|D_T\| ≥ 2 | 2,612 | 1,595 | 469 | 6 | 54 | 486 | 2 | 0 |
| all | 8,383 | 4,839 | 886 | 1,877 | 151 | 585 | 45 | 0 |

The smallest instances in each cell are listed in `regimes.log`:
- D_T = ∅, ED: **T3** (n = 3, m = 6), order (0, 1, 2);
- D_T = ∅, CAN-k: induct-q4-rules (n = 3, m = 5);
- |D_T| = 1, CAN-k: n4_4#1715.0 (n = 5, m = 8);
- |D_T| ≥ 2, CAN-k: hall-local3 (n = 3, m = 7);
- |D_T| ≥ 2, ED: r640 (n = 4, m = 8).

So **7,753 of the 8,383 starts (92.5%) are repaired by a chain to which a written lemma (KEEP, OWN, D-red or
RING-red) applies**. With |D_T| = 1, 3,255 of 3,259 are. At 2,880 starts Theorem U proves the repair outright (§3). The
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

There are 79 starts with no canonical repair owned by k (all data). Each has a repair of one of three kinds:
- **58**: an ED repair whose head is a frozen dangerous agent, and whose H₀ contains that head's pick (a dangerous
  ring, as in T3);
- **20**: an ED repair whose head is unfrozen and takes junk (Hall's Finding C);
- **1**, log1480 (the §29 dichotomy instance): a canonical chain 0 → 1 with the junk pair {0, 2}, owned by agent 2.
  Lemma OWN covers it.

**Lemma RING-red (K4.MULTI.RING).** A *dangerous ring* from k ∈ D is a sequence k = x₀, x₁, …, x_t = d (t ≥ 1) such
that:
- each x_i with 1 ≤ i < t wants Y_{x_{i−1}} at the picks;
- d ∈ D takes Y_{x_{t−1}} plus junk H_t, with v_d(Y_{x_{t−1}} ∪ H_t) > p_d;
- k takes H₀ = {Y_d} ∪ G with G ⊆ J ∖ H_t and v_k(H₀) > p_k.

No pick is released. In terms of the official moves, this is the ED chain k → x₁ → … → d with head junk H_t, in which
k's set contains the head's pick. Let B′ be the state and J′ = J ∖ (G ∪ H_t). Suppose:
- **(R1)** d's bundle threatens nobody at B′;
- **(R2)** no agent other than k wants a good of H₀;
- **(R3)** d, and every agent other than k that is frozen at B′, is unthreatened by H₀ ∪ J′ at its value at B′;
- **(R4)** no holder is crowded by H₀.

Then B′ has an S\* completion owned by k.

*Proof.* Apply Lemma 2\* with owner k and H = ∅:
- (G1) is (R1), together with singletons for everyone else;
- (G2) holds because J′ ⊆ J and values only rose, by (I2);
- (H1) is (R3);
- non-movable exposed holders are excluded by (R2) and (R4);
- the empty system of representatives suffices. ∎

T3 satisfies (R1)–(R4) with the ring (0, 2, 1), with head junk H_t = H₂ = {3} and H₀ = {4, 2}.

*Checks* (`ring.py`, `ring.log`). Every ring meeting (R1)–(R4) has an S\* completion owned by k (raw enumeration):
7,347 rings, 0 violations. RING-red covers some of the RING starts. The rest need an unfrozen head taking junk (Hall's Finding C),
or a ring whose obstacles are resolved by slots. See the census in §5.

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
  - Data: 486 + 95 starts are repaired only this way.
  - The slot structure (`slot_stats.py`, `slot_stats.log`), counting the fewest kept-out goods over the repairing
    chains of each of these 585 starts:
    - one good in 442 starts: the head takes it in 260, and another holder in 182;
    - two goods in 138;
    - three goods in 5.

    In most one-good repairs the good belongs to another truly dangerous agent's junk set. So the count to prove is
    that one or two slots, the head's among them, cover what the chain leaves.
  - Smallest: hall-local3 (n = 3, m = 7) and induct-q4-rules (n = 3, m = 5).
- **RING (K4.MULTI.RINGX).** If no canonical chain repairs, some ED chain repairs with owner k. In it, either the head
  is a dangerous agent d with Y_d ∈ H₀ (a ring through two dangerous agents), or an unfrozen head takes junk.
  - Lemma RING-red (§6) proves the repair for rings without obstacles: 151 starts.
  - Data: 45 starts are left (43 with D_T = ∅), all repaired by ED chains.
  - Smallest left: T3 with the order (0, 2, 1), picks (0, 1, 4), D = {0, 2}. Its repair is the swap 0 ↔ 2: agent 2
    takes 0, and agent 0 takes 2's pick 4 plus junk 2. But agent 1 wants 4 (30 > 22), so k = 0 cannot own ((R2)
    fails), and the S\* owners are 1 and 2. T3 with the order (0, 1, 2) is covered by RING-red.
  - *RING-OWN* (`ring.py`, `ring.log`; written proof, Lemma 2\* with H = ∅ and owner o ≠ k). The conditions are:
    (O1) every multi-good bundle other than o's threatens nobody; (O2) o holds at most one good and is unfrozen;
    (O3) every non-holder other than o is unthreatened by B′_o ∪ J′. Checked: 22,571 (ring, owner) pairs, 0
    violations. But it covers *none* of the 45.
  - *Why* (`ring_comp.py`, `ring_comp.log`):
    - At 27 of the 45, a repair has an agent off the chain that wants a good of x₀'s new bundle (in T3 (0, 2, 1),
      agent 1 wants the pick 4 that agent 0 receives). That agent is safe only because the completion gives it its
      own junk good (agent 1 takes 3: 22 + 12 > 30). So x₀'s bundle violates (G1) of Lemma 2\*. What is needed
      there is Lemma 2\* with *compensated (G1)*: agents threatened by a fixed multi-good bundle are matched to
      compensating junk, as they are for the owner's bundle.
    - The other 18 are repaired only by ED chains without such a wanter, such as an unfrozen head taking junk with
      slots. The smallest is Q2, picks (3, 7, 5, 4).
- **The existence part.** In every regime the lemmas assume the right chain. What is missing is an argument that a
  hard start has a KEEP, OWN or clean chain, or else the SLOT or RING configuration.

*Honest scope.* Most written proofs here are reductions. They prove that a chain *with property X* repairs, and the
data show such a chain exists in 92.5% of the starts. The exception is Theorem U. Its hypothesis is a property of the
start, and the chain's existence is part of the proof, so OC₁ is proved outright at the starts it covers (2,880 of the
8,383; Corollary U1, one unfrozen pick holder and one truly dangerous agent: 2,234).

The most promising next step is |D_T| = 1 without Theorem U's hypothesis: some unfrozen agent other than the head is
threatened by the junk (379 starts). In that class, these unfrozen *junk-exposed* agents are the new difficulty:
they may be crowded by H₀, and they may be the only possible holders for the released pick. KEEP or OWN chains still
exist on all but 8 of the 3,259 starts with |D_T| = 1, and the 8 exceptions have exactly the crowding obstacle of
|D| = 1. So this step should be done together with the Hall session's D1-C.

For D_T = ∅, Proposition T0 says every unfrozen z has some d ∈ Θ(z). Such a d values Y_z together with junk, unless
d values every junk good: then J ∪ {Y_z} can threaten d through the worthless good Y_z, while J alone cannot. Outside
that exception, each dangerous agent values at most two picks besides its own (|R_d| ≤ 4, with at least one junk
good). So there are at most 2|D| unfrozen pick holders. That is the start of a count.

## 8. The OC₁^max failures and the second move (OC₂)

**The known failures against this note's lemmas** (`cex_check.py`, `cex_check.log`). The instances are the
certifier's 11 n = 4 cores (`results/k4_oc1max_multi/oc1max_cex_n4_from_cert.json`, copied from
`compute/k4-oc1max-cert`) and the TTC session's n = 5 core.
- *Independent re-verification.* With this note's code (raw EFX₀, enumeration), all 12 are perfect starts with no
  one-absorber completion at the picks or after any official move.
- *Consistency.* At none of them do the hypotheses of KEEP, OWN, D-red (a clean chain), RING-red or Theorem U hold. A
  lemma whose hypotheses held there would be refuted. None is.
- *Structure.* All 12 have exactly one unfrozen pick holder z and E_J = ∅. The 11 n = 4 cores have |D_T| = 2: the two
  agents sharing the pair are both truly dangerous, so Theorem U does not apply. The TTC core has D_T = ∅: its shared
  set {2, 4} contains the released pick 4. The obstacles of the canonical chains are DEMAND and CROWD only, never HEAD.

**Leaf 4f: does sharing explain the failures?** (`sharing.py`). The 8,383 starts of §1, split by the integrator's
definition of a shared pool danger set (k ≠ k′ ∈ D, an unfrozen pick holder z, a minimal improving set T of k inside
(J ∪ B_z) ∩ R_k with v_{k′}(T) > p_{k′}):

| class | starts | one move repairs | canonical chain, owner k | a written lemma applies | obstacles where owner k fails |
|---|---|---|---|---|---|
| no sharing | 7,755 | 7,755 | 7,681 | 7,237 | CROWD only (58); no canonical chain with an improving set (16, T3-type rings) |
| shared | 628 | 628 | 623 | 516 | DEMAND, with CROWD or HEAD (5) |

So DEMAND never blocks a no-sharing start, and every known two-move start is in the shared class. Sharing is not
sufficient, though: the 628 shared starts of §1 need one move.

**More failures** (`walk_fail.py`, `walk_fail.log`, starts in `oc1_fail_walk.jsonl.gz`). Walks in the value
neighbourhood of the 12 (±1..3 per step, strictness kept, 2,000 steps each, seed 7) give 4,955 distinct failing
(profile, start) pairs: 4,378 at n = 4 and 577 at n = 5 from the TTC core. All are hard perfect starts with no
one-move repair, by raw enumeration.

**The shape of the second move** (`lift.py`, `lift.log`; `lift_shape.py`, `lift_shape.log`; all 4,955 walk
failures, which include the 12).
- At every one, some repairing pair (P₁, P₂) has:
  - P₁ a canonical chain from a dangerous agent k;
  - P₂ a canonical chain *at the intermediate state* B₁, ending at the same head z;
  - every DEMAND agent of P₁ unfrozen after P₂ (the integrator's OC2-LIFT condition 1);
  - P₂'s first agent q absorbing a₁, z's good after P₁;
  - P₁'s improving set a shared pair, or containing z's pick Y_z.
- At all 4,378 n = 4 failures, more is true:
  - P₁'s improving set is a junk pair T shared with another dangerous agent;
  - z ends at its top good;
  - q takes both goods z vacated, Y_z and a₁;
  - each of k, z and q owns an S\* completion afterwards.
- At the 577 failures near the TTC core, P₁ takes the pool pair {junk, Y_z}, z ends at its top, and k, z and q own.

**Lemma LIFT (K4.MULTI.LIFT; the second move as a move of a smaller instance).** Let B be a state, and k an agent
holding a pair T such that every other agent with a relevant good values each good of T below its value at B. This
holds after a canonical chain whose improving set is a junk pair, by (I2). Let I⁻ be the instance without agent k
and the goods T, and B⁻ the restriction of B.
1. Every official move of I⁻ from B⁻ is an official move of I from B that leaves k's bundle unchanged.
2. Let C⁻ be reached from B⁻ in I⁻ by official moves, and X⁻ a one-absorber completion of C⁻ in I⁻ in which no
   bundle threatens k at v_k(T). Then X⁻ with X_k = T is a one-absorber completion of C⁻ ∪ {k: T} in I.

*Proof.*
1. The junk of B⁻ in I⁻ is the junk of B in I, since k holds T. Agents other than k keep their values. The conditions
   of an official move compare values agent by agent.
2. Pairs of agents other than k behave as in I⁻. For an agent i ≠ k with a relevant good: removing a good of T leaves
   one good of T, worth less than v_i(B_i) ≤ v_i(X_i), because moves and completions only raise values. Agents
   without relevant goods value nothing. The pairs (k, j) are the hypothesis. k receives no junk, so the absorber
   count is that of X⁻. ∎

By |R_k| ≤ 4, k's goods outside T are Y_k and at most one more good ℓ. So "no bundle threatens k" fails only if:
- some bundle holds both Y_k and ℓ, worth more than T together; or
- k wants ℓ, and ℓ sits in a bundle of two or more goods.

This generalizes Lemma SET to any later state.

**The recursion on the data** (`reduce_check.py`, `reduce_check.log`; `reduce_mech.py`, `reduce_mech.log`; all 4,955
failures). At every one, some canonical first chain from k takes a shared improving *pool* pair T (two junk goods, or
junk plus Y_z), and then:
- the reduced state B₁⁻ is the serial-dictatorship outcome of an order of I⁻, i.e. a perfect start of the smaller
  instance;
- I⁻ has no truly dangerous agent at B₁⁻ (D_T(I⁻) = ∅);
- one move of I⁻ repairs B₁⁻, and the repair lifts by Lemma LIFT (some S\* completion with an owner other than k).

At 4,923 of the 4,955, including all 12 known failures, that move in I⁻ is a clean canonical chain, so Lemma D-red
proves the repair in I⁻. The other 32 need an obstructed canonical chain with owner k in I⁻.

So at the known failures, **OC₂ = one chain that settles a sharer (Lemma SET/LIFT), then OC₁ in the smaller
instance**. In the smaller instance, the remaining sharer has at most one junk good left (Lemma PL(c)) and is no longer
truly dangerous. This is the coordinator's "one chain per independent danger set", made precise.

**Sub-lemma OC2-REC (K4.MULTI.REC, open).** At a hard perfect start with no one-move repair, some canonical chain P₁
from a dangerous agent k with a shared improving junk pair T has these properties:
- (a) its reduced state B₁⁻ is a perfect serial-dictatorship start of I⁻;
- (b) B₁⁻ completes in I⁻ after at most one official move, with a completion that does not threaten k.

By Lemma LIFT, OC2-REC implies OC₂ at such starts. (b) is OC₁ for I⁻, for which §1–§7 apply verbatim: D-red, KEEP,
OWN, RING-red and Theorem U.

At the TTC core and its 577 neighbours the pair is the pool pair {junk, Y_z}. Lemma LIFT's hypothesis still holds
there, since Y_z is unwanted by (U).

*Evidence for (a), (b):* all 4,955 failures, with (b) given by Lemma D-red in I⁻ at 4,923 of them. Evidence only: the
walks stay near the 12 known instances, all with one unfrozen pick holder and two sharers. Three sharers, the case
where two moves may not be enough (Hall §22), are being searched for by `compute/k4-oc1max-cert`.

