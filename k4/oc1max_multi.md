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
| **Theorem S** (§10) | **Theorem U with a junk good kept out.** OC₁ holds at every perfect start where, for some k ∈ D, longest chain P (head z) and junk good h, W = (J ∖ h) ∪ {Y_z} is improving for k, threatens no other dangerous agent and no other unfrozen pick holder at its pick value, and z values no junk good but h (or W does not threaten z at its final value). The repair: P, then h to the head (or to an unfrozen second wanter), k takes W. **Theorems U and S together prove OC₁ outright at 7,441 of the 8,383 starts (88.8%)**, 424 of the 585 SLOT starts | written proof, **unconditional on its class**; 0 violations in 23,000 cases |
| SLOT residue (§10) | 161 SLOT starts outside Theorems U and S: one kept-out good 18, two 138, three 5; smallest log613 (n = 3, m = 7), where the second slot strips the goods the threatened holder does not value from the owner's bundle | open (Sub-lemma SLOT2); evidence |
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
      agent 1 wants the pick 4 that agent 0 receives), and the agent is compensated by its own junk good (agent 1
      takes 3: 22 + 12 > 30). With an owner other than x₀ this violates (G1) of Lemma 2\*. Lemma M^c (§9) certifies
      it. But §9's census shows that every RING start also has a repair certified by plain Lemma M (owner x₀ or
      another), so the compensation is not essential.
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

**Lemma LIFT (K4.MULTI.LIFT; the second move as a move of a smaller instance).** *Refereed CORRECT (with SD-E and REC-S, §12).* Let B be a state, and k an agent
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


## 9. Lemma M^c: the compensated matching form of the completion

Requested by the coordinator as a shared tool. It extends the matching session's Lemma M (`k4/matching.md` §1,
refereed CORRECT) in two ways:
- *frozen slots:* a frozen single-good agent may take a junk good if every wanter of its good is compensated
  (Lemma 1's (S1));
- *compensated (G1):* a fixed multi-good bundle may threaten an agent, if that agent is compensated by its own junk
  good.

Both are needed: frozen slots for the one-absorber completions that S\* misses (Hall §13, matching §5), compensated
(G1) for RING (§7: 27 of its 45 starts).

**Shape S^c.** At a state B with owner o:
- o takes the junk not handed out;
- every other agent with at most one base good takes at most one junk good. These agents are the *holders* N₁
  (unfrozen, base unwanted, empty bases included) and the *frozen singles* F₁;
- agents with two or more base goods, Q_m, take nothing.

At a state of single goods (a perfect start), S^c is exactly the one-absorber shape. Checked: S^c ⟺ one-absorber at
all 13,338 single-good states below.

**Lemma M^c (K4.MULTI.MC).** Let B satisfy (G2): no junk good is wanted, i.e. v_i(g) ≤ v_i(B_i) for every agent i and
every junk good g. Fix an owner o, and write b_i = v_i(B_i). For a set H of junk goods and a set F_s ⊆ F₁ of frozen
slots, put X = B_o ∪ (J ∖ H), and define each agent's requirement τ_i as the largest of:
- b_i (for i ≠ o);
- max_h v_i(B_q ∖ h), over the non-owner multi-good bundles B_q, q ∈ Q_m ∖ {i};
- v_i(y_j), over the j ∈ F_s whose good y_j agent i wants at B.

An agent i ≠ o is *needy* if τ_i > b_i or X threatens i at b_i. The *eligible* agents are N₁ ∪ F_s. The graph
Γ^c(H, F_s) on H × eligible has h ~ i iff either:
- i is not needy; or
- i values h, b_i + v_i(h) ≥ τ_i, and X does not threaten i at b_i + v_i(h).

Then, for every d ≥ 0, B has an S^c completion with owner o and d dummy slots iff some (H, F_s) satisfies all three
conditions:
- **(C1)** every needy agent is eligible;
- **(C2)** v_o(X) ≥ τ_o;
- **(C3)** Γ^c(H, F_s) has a matching that covers every needy agent and has at least |H| − d edges.

Hence the compensated deficiency is

> δ^c(B, o) = min over (H, F_s) with (C1), (C2) and the needy agents coverable of |H| − ν(Γ^c(H, F_s)).

*Proof.* The heart is a claim about a fixed S^c-shaped allocation. Write t_i = v_i(X_i), and let F_s be the frozen
singles that receive a good.

**Claim.** The allocation is EFX₀ iff t_i ≥ τ_i(F_s) for every agent, and X_o threatens no agent i ≠ o at t_i.

*Proof of the claim.* Bundles of at most one good never violate EFX₀. The others are of three kinds.
- *X_o.* It threatens i at t_i or not, which is the second condition.
- *A multi-good B_q (q ∈ Q_m, unchanged).* It threatens i iff max_h v_i(B_q ∖ h) > t_i. The case q = o is X_o.
- *A two-good bundle X_j = B_j ∪ {z_j}, j ∈ N₁ ∪ F₁.* Removing one good leaves the other, so it threatens i iff
  v_i(y_j) > t_i or v_i(z_j) > t_i.
  - By (G2), v_i(z_j) ≤ b_i ≤ t_i.
  - For a holder j, y_j is unwanted, so v_i(y_j) ≤ b_i ≤ t_i.
  - For a frozen single j, it threatens i iff i wants y_j at B and v_i(y_j) > t_i.

  (If B_j = ∅, X_j is a singleton.) ∎

*(⇒)* Given a completion, let H be the junk given away (to agents or dummies) and F_s the frozen singles that receive
a good. Then t_i ≥ τ_i for every agent, by the claim.
- An agent that receives nothing has t_i = b_i. So it is not needy, and non-eligible agents receive nothing: (C1).
- (C2) holds, since t_o = v_o(X).
- A needy agent with t_i > b_i received a good h with b_i + v_i(h) = t_i ≥ τ_i, not threatened by X at t_i: an edge
  of Γ^c.
- A needy agent with τ_i ≤ b_i that received nothing would be threatened by X at b_i. So every needy agent received a
  good, and the received goods form a matching covering them, with at least |H| − d edges.

*(⇐)* Given (H, F_s) and such a matching:
- o takes X;
- matched agents take their goods;
- the unmatched goods of H go to dummies (at most d).

Then t_i ≥ τ_i for every agent:
- a non-needy agent has τ_i ≤ b_i;
- a needy agent is matched along a compensating edge;
- the owner has (C2).

X threatens nobody else:
- a non-needy agent is unthreatened at b_i ≤ t_i;
- a needy agent is unthreatened by its edge condition.

If some j ∈ F_s receives nothing, the requirements were only raised, so they still hold. The claim gives EFX₀.

*The formula.* As for Lemma M: by Mendelsohn–Dulmage, a matching covering the needy agents and a maximum matching
combine into one that does both. ∎

*Special cases.*
- F_s = ∅ with no multi-good bundle threatening anybody ((G1)) is Lemma M. The needy agents are then the exposed
  holders.
- At a perfect start (no Q_m), Lemma M^c is an exact matching form of Lemma 1. The coupling of frozen slots that Lemma
  M's Remark 2 mentions is handled by enumerating F_s: for each choice of frozen slots, the condition is an ordinary
  bipartite matching.

*Checks* (`mc.py`; `mc_small.log`, `mc_walk.log`, `mc_n5.log`). States: every hard |D| ≥ 2 start of §1 and every
state one official move reaches from it; every walk failure of §8, every state one move reaches, and a sample of
two-move states. Every owner; d = 0 and 1. The model is compared with a raw brute force over all S^c-shaped
allocations (`mc.brute`, raw EFX₀).

| data | states with (G2) | owner tests (× 2 values of d) | mismatches |
|---|---|---|---|
| the small data sets (1,872 starts) | 34,824 | 139,436 | **0** |
| the 4,955 walk failures (one and two moves) | 152,009 | 625,326 | **0** |
| n = 5 core lists (6,511 starts) | 292,312 | 1,461,560 | **0** |
| all | 479,145 | **2,226,322** | **0** |

States without (G2) are skipped (3,740, 8,994 and 66,863).

*Independent confirmation* (matching session, `k4/matching/mc_check.py`, `results/k4_matching/mc_check.log`, commit
bebfd52 on `proof/k4-matching`). The matching session wrote the formula from this text in its own code (`mlib.M.mc_def`)
and compared it with its own raw S^c search:
- 65,201 owner tests, 0 mismatches;
- its pruned search against a pruning-free brute force: 33,200 tests, 0 mismatches;
- S^c = one-absorber at the picks: 21,880 owner tests.

It also reports that "some single move gives an S^c completion" holds exactly when OC₁ holds, on all 2,371 of its hard
perfect starts. That includes 60 walk starts that OC₁ repairs only through a non-S\* completion. So Lemma M^c after
one move is an exact one-move criterion on that data. There a junk good is wanted, which canonical chains never produce
(D-red 1).

**Uses.**
- **SLOT and RING** (`mc_apply.py`, `mc_apply.log`). For every repairing move and every absorber, I took the least
  certificate kind. On **all 585 SLOT and all 45 RING starts**, some repair has a *plain* certificate: F_s = ∅, and no
  needy agent's requirement comes from a fixed multi-good bundle. That is Lemma M (refereed) with a nonempty kept-out
  set H.
  - So the compensated-(G1) repairs seen at 27 RING starts (§7) also have an alternative repair with another owner,
    often x₀ itself. There the wanter is an exposed holder compensated against the owner's bundle.
  - This corrects §7's remark: SLOT and RING do not need M^c's extensions, only Lemma M's slot count with H ≠ ∅.
  - What is open in both is existence: that a chain exists whose post-state satisfies Lemma M's Hall condition.
- **Frozen slots** (the matching session's 88 non-S\* starts; TTC's R2★ step 4): F_s ≠ ∅.
- **The deficiency δ^c** is the right measure for an exchange argument with compensation: an EX\*-type lemma with
  Γ^c in place of Γ.

## 10. SLOT as an existence statement: Theorem S

The coordinator asked for SLOT as a pure existence count: some chain reaches a state where Lemma M's Hall condition
holds. This section proves that outright on a class covering 424 of the 585 SLOT starts, together with 7,441 of all
8,383 starts once Theorem U is included. It names the residue.

**The owner's bundle does not depend on H₀.** After a canonical chain P = (k, …, z) with an improving H₀ ⊆ Π = J ∪ {Y_z},
an S\* completion with owner k and kept-out set H ⊆ J′ = Π ∖ H₀ gives k the bundle H₀ ∪ (J′ ∖ H) = Π ∖ H. So the
completion is fixed by H and its receivers. H₀ only has to be an improving subset of Π ∖ H, so that the chain is an
official move.

**Theorem S (K4.MULTI.S): Theorem U with a junk good kept out.** *Refereed CORRECT, in both forms, together with Lemma
HS and HS-U1 (`k4/referee/oc1max_multi.md` §10, commit fabd4cf on `claude/k4-referee`; 205,634 independent tests, 0
failures; mutations of each hypothesis fail).* Let Y be a perfect start, k ∈ D, P a *longest*
canonical chain from k with head z and a = Y_{x_{t−1}}, and h ∈ J. Put W = (J ∖ {h}) ∪ {Y_z}. Suppose:
- **(S-a)** v_k(W) > p_k;
- **(S-b)** W threatens no agent of D ∖ {k} at its pick value;
- **(S-c)** W threatens no unfrozen pick holder other than z at its pick value;
- **(S-d)** z values no junk good other than h.

Then OC₁ holds at Y. Take any improving H₀ ⊆ W. The move is P with H₀. The completion depends on whether z is
unfrozen after P:
- if so, z takes h;
- otherwise, some unfrozen wanter w of a takes h.

k takes the rest, so its final bundle is W. The others keep their state goods.

*Relaxed form (S-d′).* (S-d) may be replaced by: W does not threaten z at its value in that allocation. This form is
chain-level, like Theorem U's condition on z.

*h = Y_z.* With h = Y_z, W = J, and the relaxed form *contains* Theorem U. It is more general: it needs no hardness,
(S-a) is weaker than k ∈ D_T, and (S-d′) is weaker for a frozen head. Then:
- (S-b) says D_T ⊆ {k};
- (S-c) says E_J ⊆ {z};
- (S-d′) for the head is KEEP's computation v_z(J ∩ R_z) < 2p_z < v_z(a) + p_z, or z ∉ E_J when the wanter takes Y_z.

*Proof.*
0. *The move exists.*
   - k ∈ D is frozen, so canonical chains from k exist (D1-chain), and a longest one exists.
   - By (S-a), W ∩ R_k is an improving set inside W ⊆ Π, so an improving H₀ ⊆ W exists.
   - The chain is official: every x_i gains, and z gains, since it wants a.
   - h ∉ W ⊇ H₀, so h ∈ J′.
1. *The receiver of h is a holder after P.* If z is unfrozen after P, the receiver is z. Otherwise a has a wanter w
   after P, and Theorem U step 1 applies (Hall's Remark 2 on longest chains):
   - w is off P and wanted a at the picks;
   - w is unfrozen at the picks, since otherwise there would be a longer chain;
   - w holds a pick;
   - w is unfrozen after P (D-red 2).

   So w is a holder with value p_w, and w is an unfrozen pick holder other than z.
2. *The allocation A.* A_k = W. The receiver r takes {B′_r, h}. Every other agent keeps its state good. Every agent's
   value in A is at least its value at B′, which is at least its pick value: values only rise along a chain, and
   W ⊇ H₀.
3. *A is EFX₀.*
   - Singletons never violate EFX₀.
   - *The two-good bundle {B′_r, h}* threatens i iff v_i(B′_r) > v_i(A_i) or v_i(h) > v_i(A_i).
     - B′_r is unwanted at B′, because r is a holder.
     - v_i(h) ≤ p_i by (G2) at the picks: h was available at i's turn.
     - For k, v_k(h) ≤ p_k < v_k(W).
   - *W threatens no i ≠ k at v_i(A_i).* Threat is monotone: it is weaker at higher values and on subsets. Every
     agent other than k is one of the following.
     - i = z. With (S-d), W ∩ R_z ⊆ {Y_z}, so every W ∖ g is worth at most p_z to z. But z's value in A is v_z(a) > p_z,
       or more. (S-d′) assumes this directly.
     - i ∈ D ∖ {k}: (S-b).
     - i an unfrozen pick holder other than z (this includes w): (S-c).
     - i ∈ F ∖ D. Such an agent values no junk, so W ∩ R_i ⊆ {Y_z}. Then every W ∖ g is worth at most
       v_i(Y_z) ≤ p_i to i: Y_z is unwanted at the picks, since the head of a canonical chain is unfrozen there.
     - i pickless. At a perfect start it is null, so it is never threatened.

   This is an S\* completion of B′ with owner k and H = {h}. ∎

*Remarks.*
- Hardness is not used.
- "Longest" is used only when z is frozen after P. Any canonical chain whose head is unfrozen after P does as well.
- When u = 1, the head of a longest chain is always unfrozen after P (**HS-U1**, the argument of Corollary U1; checked
  on 753 chains, `slot_hs.log`), so the wanter case does not arise.
- **Lemma HS** is the chain-level statement used in the census below: (S1) z is unfrozen at B′; (S2) z is admissible
  for h against W = Π ∖ {h}; (S3) every agent other than k and z is unthreatened by W at its value at B′. Its proof is
  step 3.

**Checks** (`theorem_s.py`, `theorem_s.log`; raw EFX₀ for every (k, longest P, h, minimal H₀) meeting the hypotheses).
There were **0 violations** in every row, and a wanter always exists when the head is frozen.

| form | cases checked (z takes h / wanter takes h) | starts covered (of 8,383) | SLOT (CAN-k) starts covered (of 585) |
|---|---|---|---|
| Theorem S with (S-d), h ∈ J | 13,025 / 1,265 | 5,945 | 337 |
| Theorem S with (S-d′), h ∈ J | 15,790 / 1,614 | 6,679 | 409 |
| **Theorems U and S, (S-d′), h ∈ J ∪ {Y_z}** | 20,640 / 2,097 | **7,441** | **424** |

By regime (§5), the union covers:

| regime | covered |
|---|---|
| KEEP | 4,291 of 4,839 |
| OWN | 769 of 886 |
| CLEAN | 1,860 of 1,877 |
| RING-red | 97 of 151 |
| SLOT | 424 of 585 |
| ED | 0 of 45 |

So OC₁ is now proved *outright* (existence included) at 88.8% of the starts, against 2,880 (34%) from Theorem U alone.

**The SLOT census** (`slot_hs.py`, `slot_hs.log`). This is plain Lemma M after canonical chains with owner k. (G1) and
(G2) hold there, by D-red 1.

| strategy | SLOT starts (of 585) |
|---|---|
| Lemma HS: one slot, at the head (some chain; the longest when any) | 390 |
| one slot at any holder | 442 |
| least kept-out set \|H\| = 1, 2, 3 | 442, 138, 5 |

Violations: 0. Among the starts without HS, the obstruction at the longest chains (per h, `slot_hs.log`) is mostly a
frozen truly dangerous agent that W still threatens: one good of its junk set cannot be cut.

**The SLOT residue (K4.MULTI.SLOT2).** 161 SLOT starts are outside Theorems U and S:

| least \|H\| | head slot at some chain | starts | smallest |
|---|---|---|---|
| 1 | yes | 7 | |
| 1 | no | 11 | log720 (n = 4, m = 9), picks (3, 7, 6, 5) |
| 2 | no | 138 | **log613 (n = 3, m = 7)**, picks (1, 2, 3) |
| 3 | no | 5 | n4_3#947.0 (n = 5, m = 9) |

The one-slot part (18 starts) is Lemma HS or Lemma M with |H| = 1 at a chain that the start-level hypotheses do not
see. The rest needs two or three slots.

*Sub-lemma SLOT2 (open).* If no (k, longest P, h) meets Theorem S or U, then some canonical chain from some k ∈ D has a
Lemma M certificate (owner k) with |H| ≤ 3.

*Smallest instance and its Hall-violating set.* log613: R₀ = {0: 3, 1: 4, 2: 10, 3: 8}, R₁ = {2: 8, 4: 4, 5: 2, 6: 3},
R₂ = {3: 8, 4: 3, 5: 4, 6: 2}, picks (1, 2, 3), J = {0, 4, 5, 6}. Both dangerous agents are truly dangerous, they
share their whole junk set {4, 5, 6}, and u = 1 with z = 0.
- *k = 1.* The only improving H₀ is {4, 5, 6}, so J′ = {0, 1}, and agent 2 becomes an unfrozen holder.
  - With |H| = 1, X ⊇ {4, 5, 6} together with a good that 2 does not value. So X threatens 2 at 8 (9 > 8), and 2
    values neither good of J′. The needy set {2} has an empty neighbourhood: this is the Hall violation.
  - With H = {0, 1}, X = {4, 5, 6} ⊆ R₂, and removing 2's cheapest good leaves 7 ≤ 8. Agent 0 takes 1 and agent 2
    takes 0, which is EFX₀.
- *k = 2.* The only improving H₀ is the triple {4, 5, 6}, and every (chain, H₀) leaves agent 1 frozen and threatened
  (DEMAND).

So the second slot does not cut a danger set. It removes the goods that agent 2 does not value from the owner's bundle,
so that EFX₀'s removal of the least valued good bites. The residue needs a lemma for this *worthless-good* effect.
That is the natural next target.

## 11. RING as an existence statement: the residue

At none of the 45 RING starts does a canonical chain repair with owner k, and Theorems U and S cover none of them
(§10). The shortest repairing move with an S\* completion at each (`ring_len.py`, `ring_len.log`):

| shortest repair | \|D_T\| = 0 | \|D_T\| = 2 | smallest |
|---|---|---|---|
| a swap of two dangerous agents (ring or chain of length 2, both ends in D) | 23 | 0 | T3, picks (0, 1, 4) (n = 3, m = 6) |
| length 2, x₀ ∈ D, other end not | 0 | 2 | r640 (n = 4, m = 8) |
| length 2, x₀ ∉ D | 8 | 0 | nsw-strict-n4m9 (n = 4, m = 9) |
| length 3, both ends in D | 4 | 0 | c4-g2-other-runs-n4m7 (n = 4, m = 7) |
| length 3, x₀ ∈ D | 8 | 0 | ls-alt-rule-n4m7 (n = 4, m = 7) |

So 43 of the 45 have no truly dangerous agent (all dangerous agents are pick-dangerous), and every one is repaired by a
move of length at most 3.

**The Hall obstruction at T3 (0, 2, 1)** (`ring_hall.py`, `ring_hall.log`). The values are
R₀ = {0: 38, 2: 6, 4: 36, 5: 1}, R₁ = {1: 22, 3: 12, 4: 30} and R₂ = {0: 38, 1: 20, 3: 12, 4: 28}, with picks
(0, 1, 4), J = {2, 3, 5} and D = {0, 2}.
- The only canonical chain with an improving set is (2, 1), with H₀ = {1, 3}. After it, agent 0 is frozen (2 wants
  its good), and agent 1 is the only holder.
- For |H| ≤ 1, the owner's bundle X ⊇ {1, 3} also contains a good that agent 1 does not value. So X threatens 1 at 30
  (22 + 12 = 34 > 30), and 1 values neither junk good 2 nor 5. The needy holder 1 has an empty neighbourhood.
- For H = {2, 5}, X = {1, 3} ⊆ R₁ leaves 22 ≤ 30 after the least good is removed. But |H| = 2 exceeds the single
  holder, which violates (C3).
- No canonical chain from 0 has an improving set.
- The repair is the swap 0 ↔ 2: 2 takes 0, and 0 takes {4, 2}. It has S\* owners 0, 1 and 2. The agent 1, who wants 4,
  is compensated by junk 3 (22 + 12 ≥ 30). This is (R2) of RING-red failing.

*Sub-lemma RING2 (K4.MULTI.RING2, open).* At a hard perfect start where no canonical chain from D repairs with owner k:
- some move of length at most 3 repairs;
- if D_T = ∅ and no other move repairs, the repair is a swap of two dangerous agents k and d (d takes Y_k, k takes Y_d
  plus junk), with the wanters of Y_d compensated by their own junk goods.

**The common obstruction.** The smallest residues of SLOT (log613) and RING (T3) fail one-slot Lemma M for the same
reason. A holder is threatened by the owner's bundle only because that bundle contains goods the holder does not value:
EFX₀ removes a zero-valued good, which costs nothing. Keeping all such goods out cures the threat, but it costs one
slot per good. Two lemmas would close both residues:
1. a count of the holders available for these *worthless* goods (SLOT2);
2. a swap lemma with compensated wanters (RING2).

## 12. OC2-REC (item 4b): Lemma SD-E and Theorem REC-S

This section proves OC2-REC's part (a) in general, and part (b) on a class that contains every known failing start.
Values are strict: each agent's values are distinct, as in §23.4 of `k4/oc1_hall.md`.

**The earliest-wanter chain.** Let Y be the SD outcome of the order σ, and let k be frozen. The chain
E(k) = (k = x₀, x₁, …, x_t = z) is defined by:
- x_l is the σ-earliest wanter of Y_{x_{l−1}};
- it stops at the first agent z whose pick nobody wants.

A wanter of Y_j picks after j: Y_j was gone at its turn. So σ increases along E(k), its agents are distinct, it is a
canonical chain, and it exists for every frozen k.

**Lemma SD-E (K4.MULTI.SDE).** *Refereed CORRECT, together with Theorem REC-S and Lemma LIFT
(`k4/referee/oc1max_multi.md` §11, commit e746fc2c on `claude/k4-referee`).* Let T ⊆ J ∪ {Y_z}. Let B₁ be the state after E(k) in which k takes T: x_l holds
Y_{x_{l−1}}, and every other agent keeps its pick. Let I⁻ be the instance without k and T. Then B₁ restricted to I⁻ is
the SD outcome of σ with k deleted. If Y is a perfect start, so is this state, in I⁻. (Without that hypothesis it
need not be: v₀ = {0: 9}, v₁ = {0: 5, 1: 4}, v₂ = {0: 1}, σ = (0, 1, 2), E(0) = (0, 1) leaves agent 2 pickless
while it values good 0. This is the referee's example.)

*Proof.* Write b_a for a's good at B₁. We run σ ∖ k in I⁻ and show by induction that every agent a takes b_a.
- *b_a is available at a's turn.* Only a holds b_a. b_a ∉ T, since b_a is a pick other than Y_z.
- *a values no other available good g more.* Suppose v_a(g) > v_a(b_a) ≥ p_a.
  - A junk good of I is worth less than p_a to a: it was available at a's turn (strict values).
  - Y_z is worth less than p_a to every a ≠ z, since nobody wants it; and z's new value exceeds p_z.
  - So g is a pick Y_j, and a wants Y_j at the picks. Hence σ(j) < σ(a).
  - g is available, so its holder at B₁ comes after a. That holder is j itself unless j = x_l, in which case it is
    x_{l+1}.
  - It cannot be j, because σ(j) < σ(a).
  - So σ(x_l) < σ(a) < σ(x_{l+1}), and a wants Y_{x_l}. That contradicts the choice of x_{l+1} as the earliest wanter.

Since every agent takes its B₁ good, the goods left over are exactly the junk of B₁ in I⁻. ∎

So part (a) of OC2-REC holds for E(k) with *any* pool pair. Checked (`reduce_s.py`) at every dangerous k and every
pool pair T of E(k), for every listed order, at all 4,955 walk failures, the 12 known failures and the matching session's 23,943
n = 5 walk rows: 0 violations.

**Theorem REC-S (K4.MULTI.RECS): OC₂ by settling a sharer, then Theorem S or U one size down.** Let Y be a perfect start
with strict values, k ∈ D, E(k) with head z, and T ⊆ (J ∪ {Y_z}) ∩ R_k an improving pair. Suppose:
- **(L)** every other agent with a relevant good values each good of T below its value after E(k) (Lemma LIFT's
  hypothesis);
- **(R)** in I⁻ at B₁⁻, some (k′, P′, h) meets the hypotheses of Theorem S in its relaxed form, with h ∈ J⁻ ∪ {Y_{z′}}
  (this contains Theorem U);
- **(K)** no bundle of the resulting allocation X⁻ threatens k at v_k(T).

Then OC₂ holds at Y. The repair is:
1. E(k), in which k takes T;
2. P′, an official move of I from B₁ that leaves k's bundle unchanged (LIFT 1);
3. the completion X⁻ together with X_k = T.

*Proof.*
- B₁⁻ is a perfect start of I⁻ by Lemma SD-E.
- Theorem S (refereed CORRECT; it needs no hardness) gives the move P′ in I⁻ and the EFX₀ S\* completion X⁻.
- LIFT 1 makes P′ an official move of I.
- LIFT 2 with (L) and (K) makes X⁻ ∪ {k: T} a one-absorber completion in I. ∎

Every hypothesis is checked at the start; the existence of the moves is part of the proof.

*Remarks (referee).*
- **(L) is automatic.** Values are strict, Y is perfect and T ⊆ J ∪ {Y_z}, so every i ≠ k with a pick values each good
  of T below p_i:
  - a junk good was available at i's turn;
  - for i ≠ z, Y_z is unwanted;
  - for i = z, v_z(Y_z) = p_z < v_z(a).

  Values only rise along E(k), and pickless agents at a perfect start are null. (L) never failed in 128,679 pairs.
- **(K) is genuine.** It fails at 188 of 6,065 random Theorem S cases, and every allocation where it fails is not EFX₀.
- **LIFT 1 when P′ uses agents of E(k).** An official move depends only on the agents' values on the current bundles
  and the pool. J(I, B₁) = J(I⁻, B₁⁻), because k holds T. In the data, P′'s head is an agent of E(k) in all 9,943
  repairs, and its owner is one in 57.

*Checks* (`reduce_s.py`, `reduce_s.log`, `reduce_s_cex12.log`; raw EFX₀ in I for every lifted allocation). Both the
general form (any canonical P₁ with B₁⁻ an SD start) and the E(k)-only form were run:

| data | starts | (L) holds for some E(k), T | REC-S repairs | violations |
|---|---|---|---|---|
| the 12 known OC₁^max failures (`oc1max_cex12.jsonl`) | 12 | 12 | **12** | 0 |
| the walk failures near them (`oc1_fail_walk.jsonl.gz`) | 4,955 | 4,955 | **4,955** | 0 |
| the matching session's n = 5 walks near 5_pure#164 (`results/k4_matching/n5_walk164.jsonl`, `n5_walk164_long.jsonl.gz` on `proof/k4-matching`, commit 60d4ab1; rows with every order; `reduce_s_matching_n5.log`) | 1,498 + 22,445 | all | **all** | 0 |

*Status of OC2-REC.*
- (a) is proved (Lemma SD-E).
- (b) is proved wherever (L), (R) and (K) hold, which is every known failing start.
- What remains is existence on all hard starts with no one-move repair: that some k ∈ D and some pool pair T of E(k)
  meet (L), (R) and (K). The matching session's n = 4 certification (K4.MATCH.REC.N4, 112,880 starts) is the natural
  test set for this exact form.

**Certified at n = 4 (K4.MULTI.RECS.N4).** REC-S's mechanism repairs *every* n = 4 start with no one-move repair. The
data is the certifier's export: all 112,880 (type profile, picks) pairs over the n = 4 core hypergraphs,
`results/k4_matching/data/two_move_starts_n4.json.gz` on `proof/k4-matching`; all have strict values.
- `recs_witness.py` writes one witness per start (`recs_witnesses_n4.json.gz`, `recs_witness_n4.log`): an order, k,
  E(k), T, the second chain P′ with H₀′ and h, and the final allocation. 112,880 of 112,880 have one.
- `check_recs.py` checks every witness from the definitions and imports nothing from this workstream
  (`check_recs_n4.log`):
  - the picks are the SD outcome of the order;
  - k is dangerous;
  - P₁ is E(k);
  - move 1 is official, and (L) holds;
  - Lemma SD-E holds;
  - move 2 is an official canonical chain from a dangerous agent of the reduced state, and does not touch k;
  - Theorem S's owner bundle W, with h going to one other agent;
  - the final allocation is complete, extends move 2 by junk only, has one absorber, and is raw EFX₀.
- Result: **112,880 ok**. All 8,241 negative tests (mutated witnesses) are rejected. The checker also matches the witness file to the export as a multiset
  of (sets, vals, picks), with sha256: 0 missing and 0 extra.
- *Audit:* the referee read the checker against the definitions and re-validated every witness with its own code
  (`k4/referee/oc1max_multi.md` §12, commit 3db66cb7): **CONFIRMED**. Every witness is Theorem S's allocation for a
  longest chain of I⁻, and (K) holds. As for OC₁′^max, "every n = 4 start" inherits the completeness of the
  certifier's export.
- The matching session also ran `reduce_s.py` unmodified on the same export, with the same result
  (`results/k4_matching/reduce_s_n4export.log` on `proof/k4-matching`, commit 4551d91).

So at n = 4, OC₂^max holds by an explicit mechanism: the earliest-wanter chain settles a sharer, then one Theorem S
chain in the reduced instance. No 4b sub-lemma needs naming at n = 4.

*Smallest test (the integrator's 4_n4_3#58; it is 4a-type, and REC-S covers it too).* The values are R₀ = {0: 2, 1: 10,
2: 4, 5: 7}, R₁ = {1: 10, 2: 3, 5: 4, 6: 8}, R₂ = {3: 3, 4: 5, 5: 6, 6: 7} and R₃ = {3: 3, 4: 2, 6: 4}, with picks
(1, 2, 5, 6), J = {0, 3, 4} and D = {0, 2, 3}. The repair:
1. E(2) = (2, 1), with agent 2 taking T = {3, 4};
2. in I⁻, the chain (0, 1) of Theorem S with h = 0 kept out for agent 1.

The final allocation is 0: {2, 5}, 1: {1, 0}, 2: {3, 4}, 3: {6}. An independent raw check confirms it is EFX₀.

## 13. Lemma WG: worthless goods (standalone statement, for the referee)

EFX₀ removes a good of value 0 at no cost to the remover. So a bundle S with |S| ≥ 2 threatens i at t iff
v_i(S) − μ_i(S) > t, where μ_i(S) = min_{g∈S} v_i(g). Here μ_i(S) = 0 exactly when S contains a good that i does not
value. Keeping such goods out of the owner's bundle lowers the threat to i by i's cheapest good in it, but each kept-out
good needs a holder. This is the obstruction at the smallest residues of both SLOT (log613) and RING (T3), §10–§11.

**Lemma WG (K4.MULTI.WG).** Let B be a state satisfying (G1) and (G2) (for instance the state after a canonical chain,
by D-red 1). Let o be the owner, J the junk, and i ≠ o an agent. Put H = J ∖ R_i (the junk goods worth 0 to i) and
X = B_o ∪ (J ∩ R_i). Suppose:
- **(W1)** B_o ⊆ R_i, so that X ⊆ R_i;
- **(W2)** X threatens no agent other than o at its value at B. For i this reads v_i(X) − min_{g∈X} v_i(g) ≤ v_i(B_i);
- **(W3)** there are at least |H| holders: agents other than o with at most one base good, which nobody wants.

Then B has an S\* completion with owner o and kept-out set H: o takes X, and |H| distinct holders take one good of H
each.

*Refereed CORRECT (`k4/referee/oc1max_multi.md` §13, commit 9ef2fed0). The referee notes that (W1) is never used:
the statement holds for any kept-out set H ⊆ J such that X = B_o ∪ (J ∖ H) threatens nobody and there are |H|
holders (79,459 random cases, 49,466 of them without (W1), 0 failures). (W1) is what makes this H the useful choice
for agent i.*

*Proof.* Lemma M (refereed) applies at B with owner o and kept-out set H. By (W2) the owner's bundle X threatens nobody
at its base value, so no agent is needy, and (C1) holds. A non-needy holder accepts every good. So by (W3) any |H|
distinct holders give a matching saturating H, which is (C3). ∎

*Why it is worth stating.* Without (W1), the kept-out goods change nothing for i: i's threat value stays v_i(X),
because a good worth 0 to i remains in X. With (W1), the threat value drops by i's cheapest good in X. The lemma
isolates the count that matters: one holder per worthless junk good.

**Checks** (`wg.py`, `wg.log`; canonical chains from D, minimal H₀, owner k, every i; raw EFX₀):

| residue | starts | covered by Lemma WG | WG cases | violations | smallest not covered |
|---|---|---|---|---|---|
| SLOT2 (§10) | 161 | **41**, including log613 | 75 | 0 | lb4-last-block-leader-index-n4m8 (n = 4, m = 8) |
| RING2 (§11) | 45 | 0 | 0 | 0 | T3, picks (0, 1, 4) |

At T3 (W1) and (W2) hold after the chain (2, 1): B₂ = {1, 3} ⊆ R₁, and X = {1, 3} leaves 22 ≤ 30. But |H| = |{2, 5}| = 2
and there is one holder, so (W3) fails. The swap repair of §11 avoids the count altogether.

So 120 SLOT2 starts remain. They need a slot that cuts a danger set and a worthless-good cure at the same time; Lemma M
decides each such combination exactly. RING2 needs the swap lemma.

## 14. The existence half of REC-S: (K) locally, and the phantom class

**(K) is local.** k keeps T. Outside T it values only Y_k and at most one more good ℓ, since |R_k| ≤ 4. Neither good
alone can threaten k in most positions:
- v_k(Y_k) = p_k < v_k(T);
- a junk good alone is worth at most p_k, by (G2).

So the allocation X of the reduced instance threatens k only if one of two things happens:
- **(K-a)** one bundle holds both Y_k and ℓ, worth more than T to k after the least good is removed;
- **(K-b)** ℓ is a pick that k values above T, and ℓ sits in a bundle of two or more goods (in Theorem S's allocation,
  ℓ is the receiver's good next to h, or the released Y_{z′} in W).

`rec_k.py` (`rec_k.log`) runs over E(k) for every order, every improving pool pair T and every Theorem S case of I⁻:

| data | (R) cases | (K-a) fails | (K-b) fails | k's best pool pair T\* has a case with (R) and (K) |
|---|---|---|---|---|
| walk failures (4,955 starts) | 8,686 | 0 | 0 | 4,955 |
| matching session's n = 5 walks (22,445) | 134,670 | 0 | 0 | 22,445 |
| n = 4 export (112,880) | 605,360 | 0 | 9,600 | **112,880** |

"(K) fails iff (K-a) or (K-b)" matched the raw threat test in every case. So the coordinator's suggestion holds on all
data: **choosing T as k's best improving pool pair always leaves a (K)-safe Theorem S case.** Only (K-b) ever bites, and
only for a worse pair. A proof needs one of two things:
- an argument that the best pair rules out (K-b), i.e. k never values a pick above its best pool pair while that pick's
  holder receives the slot;
- or a Theorem S case avoiding ℓ's holder, which (S-c) permits whenever another holder exists.

**The phantom class (the inductive form of REC-S).** After settling k, the reduced instance carries k as a *phantom*:
an agent with a fixed bundle T_k and a threshold τ_k = v_k(T_k), which values at most two goods outside T_k (Y_k and ℓ).
In the language of Lemma M^c, a phantom is a non-eligible agent with requirement τ_k and no base:
- (C1) asks that no multi-good bundle threaten it;
- a holder whose good the phantom values above τ_k becomes *phantom-frozen*: it may not take a slot, which is exactly
  (K-b);
- (L) is automatic for the real agents (§12, remark): they value each good of T_k below their holding, so the phantoms
  never threaten them.

A class closed under "settle, delete, recurse" (RSD) is therefore: *an SD start of the real agents, plus a set of
phantoms with fixed pairs, where each phantom is unthreatened by every other phantom's pair.* Each step settles one
more sharer by E(k) with its best pool pair T. It must check one new condition, that T threatens no existing phantom;
k values at most two goods of the rest, so this is again a local "keep b and c apart" test. Lemma SD-E, Theorem S
(with phantom-frozen holders removed from the receivers) and Lemma M^c (phantoms as non-eligible agents with fixed
requirements) all apply verbatim in this class. If every two-move start reaches a phantom-class start where Theorem S
applies after at most one settlement, OC₂^max follows. What remains is the existence argument (Sub-lemma
**RSD-EX**, open, as reworded after the referee's §13). At a hard start with no one-move repair, k's best pool pair T\*
leaves a Theorem S case (k′, P′, h) of I⁻ in which:
- **ℓ does not end at the receiver** (ℓ⁺ ≠ r);
- P′'s head does not hold ℓ (q ≠ z′);
- not (z′ = x₁ while ℓ is a pool good).

By Proposition K-loc (corrected), these give (K).

> **SUPERSEDED** (the first version of K-loc, at 8924c6b3; WRONG, kept for the record; the corrected form is below):
> In Theorem S's allocation X⁻ of the reduced instance, the multi-good bundles are W⁻ = (J⁻ ∖ h) ∪ {Y_{z′}} and
> {B₁_r, h}.
> - (K-b) needs a pick ℓ with v_k(ℓ) > v_k(T) > p_k. Such a pick was taken before k's turn, by an agent q that picked
>   before k. Hence q ∉ E(k), since σ increases along E(k), and q still holds ℓ at B₁. In X⁻, ℓ is in a multi-good
>   bundle only if q is the receiver r of h, or q is P′'s head z′ (ℓ released into W⁻, or ℓ = h).
> - (K-a) needs Y_k ∈ W⁻. Y_k is held by x₁ at B₁, so Y_k ∈ W⁻ forces z′ = x₁. It also needs ℓ ∈ W⁻, so ℓ is a pool
>   good of E(k) outside T, and p_k + v_k(ℓ) > v_k(T).
>
> So (K) holds for every Theorem S case of I⁻ whose receiver and head avoid q, and whose head is not x₁ when k values a
> third pool good.

**Proposition K-loc (K4.MULTI.KLOC): where (K) can fail.** *Corrected after the referee's verdict
(`k4/referee/oc1max_multi.md` §13, commit 9ef2fed0). The first version said "q is the receiver or the head". That is
WRONG: P′ can move ℓ from q to q's successor on P′. The referee's counterexample is from the n = 4 export: picks
(5, 1, 4, 6), k = 3, E(3) = (3, 2, 1), T = {2, 3}, ℓ = 5, q = 0, and P′ = (0, 1) hands ℓ to the receiver 1. All 9,600
(K) failures in `rec_k.log` are of this kind.*

Setting: k keeps T with τ = v_k(T). R_k ∖ T ⊆ {Y_k, ℓ}, and q is ℓ's holder at B₁ when ℓ is a pick. q picked before k,
so q ∉ E(k). Let ℓ⁺ be ℓ's holder after P′: q itself, or q's successor if q is on P′ before its head. In Theorem S's
allocation of I⁻, the multi-good bundles are W⁻ = (J⁻ ∖ h) ∪ {B₁_{z′}} and {B₂_r, h}. **(K) holds if all three of these
hold:**
- q ≠ z′;
- ℓ⁺ ≠ r;
- not (z′ = x₁ and ℓ is a pool good of E(k) outside T).

*Proof.* k values only Y_k and ℓ outside T, and v_k(Y_k) = p_k < τ. A pool good is worth less than p_k to k.
- *{B₂_r, h}* threatens k iff v_k(B₂_r) > τ or v_k(h) > τ.
  - v_k(B₂_r) > τ forces B₂_r = ℓ, i.e. r = ℓ⁺.
  - v_k(h) > τ forces h = B₁_{z′} = ℓ, i.e. z′ = q.
- *W⁻.* If W⁻ ∩ R_k is a single good, it is worth at most max(p_k, v_k(pool good)) < τ. Two goods of R_k ∖ T in W⁻
  need Y_k ∈ W⁻, so B₁_{z′} = Y_k and z′ = x₁. They also need ℓ ∈ W⁻, so ℓ ∈ J⁻ (a pool good), or ℓ = B₁_{z′}, which
  means z′ = q.
- Singletons never threaten. ∎

The referee found the three conditions exact on all data: 636,720 export cases and 32,164 walk cases, with 0
counterexamples and 0 false alarms. In the phantom language, **ℓ's bundle must stay exactly {ℓ} after P′**, wherever
P′ moves ℓ. (The charity session, `kgen/charity.md` §10, says the same: ℓ's holder is frozen for every pool good.) The
census shows that a Theorem S case meeting the three conditions always exists for k's best pool pair (`rec_k.log`).
RSD-EX asks for a proof of this.

**Phantom class: a gap, and its fix (referee).** The class above lacks (G2) for phantoms: no junk good may be worth
more than τ_φ to a phantom φ. Theorem S's step 3 and Lemma M^c's Claim use it.
- The gap: if a later settlement chain ends at the holder of a pick that a phantom wants, that pick is released into
  the junk, and putting it into the new pair T′ instead threatens the phantom.
- The referee's hand-built instance (`k4/referee/phantom_cex.py`) has no EFX₀ completion left. Its data: v₀ = {0: 10,
  6: 6, 7: 5}, v₁ = {0: 9, 1: 5}, v₂ = {1: 10, 2: 6, 4: 4, 5: 3}, v₃ = {2: 8, 3: 4}, σ = (0, 1, 2, 3). It settles 2 by
  E = (2, 3) with T = {4, 5}, and then 0 by E = (0, 1) with T′ = {6, 7}, which releases good 1.
- **Fix:** no settlement chain and no final P′ may end at a phantom-frozen agent. Phantoms count as wanters when heads
  (and slot receivers) are chosen. An agent is *phantom-frozen* if some phantom φ values its good above τ_φ.
- *(G2) for phantoms, by induction.* Claim: at every stage, every junk good g of the current instance has
  v_φ(g) ≤ τ_φ for every phantom φ.
  - *Base.* When k becomes a phantom, the junk of I⁻ is (J ∪ {Y_z}) ∖ T. Each of these goods is worth less than
    p_k < τ_k to k: a junk good was available at k's turn, Y_z is unwanted, and values are strict.
  - *Step.* A later move (a settlement chain E(k′) with its pair, or the final P′ with H₀′) changes the junk in only two
    ways. It removes the goods that the move's first agent takes, and it adds the head's old good B_{z″}. By the fix,
    the head is not phantom-frozen, so v_φ(B_{z″}) ≤ τ_φ for every phantom φ.
  - So the claim holds at every stage.
- Without the fix the step fails, which is the referee's instance. The fix never binds in the data (0 of 9,600 second
  settlements at n = 4), and it cannot bind at the first settlement, because there are no phantoms yet.

The referee also checked the class's other invariants. Real agents' (L) is automatic. Earlier phantoms' pairs never
threaten later phantoms, because a later phantom was a real agent at each earlier settlement. So only the new pair
needs a check.

**Satisfied and active phantoms** (`phantom_sat.py`, `phantom_sat.log`; the charity session's question). A settled k is
*satisfied* if v_k(R_k ∖ T) ≤ τ. Then neither (K-a) nor (K-b) can occur, and k imposes no constraint. Otherwise it is
*active*. Counting E(k) for every order with k's best pool pair:

| data | settlements | satisfied | active, ℓ a pick | active, ℓ a pool good | starts with a satisfied option |
|---|---|---|---|---|---|
| walk failures | 9,910 | 1,235 | 7,603 | 1,072 | 879 of 4,955 |
| n = 4 export | 584,160 | 113,600 | 387,680 | 82,880 | 38,720 of 112,880 |
| n = 5 walks near 5_pure#164 | 134,670 | 0 | 134,670 | 0 | 0 of 22,445 |

So active phantoms are the rule. An inductive argument must bound how many there are: each active phantom freezes the
bundle of ℓ, at most one per phantom.

*Locking (the charity session's Proposition PH-L, `kgen/charity.md` §10 on `claude/kgen-charity`, not read here in
full).* An active phantom k with ℓ a pick held by q is neutralised if q is *content with ℓ alone*:
v_q(R_q ∖ ({ℓ} ∪ T\*)) ≤ v_q(ℓ) and v_q(T\* ∖ h) ≤ v_q(ℓ). Then q can be settled with {ℓ}.

| data | active settlements, ℓ a pick | q content with ℓ alone | q itself dangerous | starts with an active ℓ-pick settlement whose q is content |
|---|---|---|---|---|
| walk failures | 7,603 | 1,539 | 6,501 | 1,539 of 4,599 |
| n = 4 export | 387,680 | 268,800 | 383,600 | 89,600 of 112,880 |
| n = 5 walks | 134,670 | 67,335 | 134,670 | 22,445 of 22,445 |

So the lock is not always available, and q is almost always a sharer itself, so the lock cascades. The depth of that
cascade is the quantity to bound.

## 15. Can Part 1 be dropped? The RSD census (the integrator's §24.3 request)

The question: can "settle a sharer first" (REC-S, or its iteration RSD) replace the one-move theory at *every* hard
start, and not only at the two-move ones? `rsd.py` runs on the 8,383 hard |D| ≥ 2 perfect starts. A settlement is
E(k) with an improving pool pair T. Every final allocation is checked raw in I, with the settled agents keeping their
pairs.

| variant | log | completes | fails |
|---|---|---|---|
| Theorem S last, zero settlements allowed, at most two | `rsd.log` | 7,441 + 515 (one settlement) + 17 (two) = 7,973 | 410 |
| exactly one settlement, then Theorem S (REC-S) | `rsd_recs.log` | 3,278 | 5,105 |
| at least one settlement, at most two, Theorem S last | `rsd_d2.log` | 3,301 | 5,082 |
| one settlement, then any official move or none, any one-absorber completion | `rsd_any.log` | 8,021 | 362 (a lower bound: one witness completion per absorber is lifted) |

Settling first breaks most of the starts that a chain repairs at the picks (the KEEP, CLEAN and OWN mechanisms). The
smallest failures are:
- T3, picks (0, 1, 4) (RING);
- c4x-n3m5-big-bases (n = 3, m = 5): its reduced start completes with no move, which Theorem S does not produce;
- with any last step, c4x-n3m6-3good-first (n = 3, m = 6).

**Conclusion: Part 1 (OC₁ where one move suffices) cannot be dropped.** REC-S is the second move. It is not a
replacement for the first.

## 16. Theorem S^φ: Theorem S with phantoms (the inductive step of RSD)

**Setting (the phantom class, with the fix of §14).** I₀ is the full instance. Φ is a set of settled agents, the
phantoms, each with a fixed pair T_φ and threshold τ_φ = v_φ(T_φ). I is the current instance: the agents outside Φ and
the goods outside ∪T_φ. Y is a perfect SD start of I, with strict values. The invariants are:
- **(P1)** every real agent i values each good of each T_φ below p_i. This is automatic: at φ's settlement it is (L)
  (§12, remark), and values only rise.
- **(P2)** no pair T_φ threatens another phantom at its threshold. Only the newest pair needs a check: earlier pairs
  never threaten later phantoms, because a later phantom was a real agent at each earlier settlement (referee, §13).
- **(P3)** (G2) for phantoms: every junk good of I is worth at most τ_φ to every phantom φ. This holds by induction
  when no chain ends at a phantom-frozen agent (§14).

**Theorem S^φ (K4.MULTI.SPHI).** In this setting, let (k, P, h) meet Theorem S's hypotheses in I (relaxed form,
h ∈ J ∪ {Y_z}). Let W be the owner's bundle and r the receiver of h. Suppose:
- **(S-φ1)** W threatens no phantom φ at τ_φ;
- **(S-φ2)** r's good is not phantom-wanted: v_φ(B′_r) ≤ τ_φ for every φ;
- **(S-φ3)** if h = Y_z, then v_φ(Y_z) ≤ τ_φ for every φ. (If h is junk, a phantom-wanted Y_z sits in W, and (S-φ1)
  catches it.) *Added after the referee's verdict (`k4/referee/oc1max_multi.md` §14, commit 117ff9ea): CORRECT WITH
  THIS FIX. Without it, 44 random n = 5–6 cases meet (S-φ1) and (S-φ2) and are not EFX₀.*

Then Theorem S's allocation of I, with every phantom keeping T_φ, is EFX₀ in I₀. Its move P is an official move of I₀
(Lemma LIFT 1, once per phantom, since the junk of I is the junk of I₀). So OC_{|Φ|+1} holds via the settlements, then
P; with one settlement, this is OC₂.

*Proof.* Every pair of agents is covered by one of these cases:
- *Real vs real:* Theorem S (refereed).
- *A real agent i vs T_φ:* removing a good of T_φ leaves one good, worth less than p_i ≤ v_i(X_i) by (P1). This uses
  |T_φ| = 2; for a triple, (L\*) replaces (P1).
- *A phantom φ vs a real bundle:*
  - singletons never threaten;
  - W is covered by (S-φ1);
  - the two-good bundle {B′_r, h} threatens φ iff v_φ(B′_r) > τ_φ or v_φ(h) > τ_φ. The first is excluded by (S-φ2).
    The second is excluded by (P3) for h junk, and by (S-φ3) for h = Y_z.
- *Phantom vs phantom:* (P2). ∎

Corrected Proposition K-loc (§14) is (S-φ1) ∧ (S-φ2) for a single phantom, spelled out through ℓ's travel along P′.

**Checks** (`sphi.py`, `sphi.log`). RSD runs with at most two settlements. At the last step, *every* Theorem S case is
evaluated against S^φ's hypotheses and the raw EFX₀ definition in I₀.

| data | starts | last-step cases | S^φ hypotheses hold | raw EFX₀ | hypotheses without EFX₀ | EFX₀ without hypotheses |
|---|---|---|---|---|---|---|
| walk failures, the 12, n = 5 walks, n = 4 export | 140,292 | 748,744 | 739,144 | 739,144 | **0** | **0** |

So the hypotheses are sufficient (the theorem) and, on this data, also necessary. (`sphi.py` tests (S-φ2) on both goods of the receiver's
bundle, h included, so the census already contains (S-φ3).) The referee's independent check, own code: n = 4 export 636,720
cases, walks 32,164, random 80,486 with one phantom, and random 1,632 with two. With (S-φ3), the hypotheses equal raw
EFX₀ everywhere. Every one of the 140,292 failing
starts reaches an S^φ case after exactly one settlement (two moves in all).

*What RSD-IND (K4.MATCH.RSDIND) now needs is existence alone:* at every stage, some settlement or some Theorem S case
meets (S-φ1), (S-φ2) and the head condition. Everything else is a written proof:
- SD-E (refereed) for the starts;
- LIFT (refereed) for the moves;
- S^φ for the completion;
- (P1)–(P3) for the invariants.

**Triple settlements, and the seven REC-S gaps of kgen-rounds** (`sphi.py` with TMAX=3 and ZERO=1;
`sphi_gaps7.log`; the rows are in `recs_gaps7_kgen.jsonl`).

kgen-rounds found seven n = 5 starts with no REC-S repair: 5_pure #38, #419, #447, #773, #813, #963 and #1073
(`results/kgen_rounds/recs_gaps_5pure.log` on `proof/kgen-rounds`). At #773 and #963 no frozen agent has an improving
junk pair. Two extensions are tried there.

*Extension 1: settling by a triple.* k takes an improving pool triple T, so |R_k ∖ T| ≤ 1 and k values only Y_k
outside T. Then v_k(Y_k) = p_k < τ_k, so k is a *satisfied* phantom and never threatened.
- LIFT's hypothesis is no longer automatic: removing one good of T leaves two goods. So the settlement must check
  **(L\*)**: T threatens no other agent of the current instance. 55 triples fail it on these seven starts.
- With (L\*) in place of (P1), Theorem S^φ's proof goes through unchanged.

*Extension 2: completing at once.* The last step may also be a completion of the reduced start with no further move.
This is the matching session's RSD form.

Counting total moves (two moves = OC₂^max):

| settlement sets | last step | repaired in two moves |
|---|---|---|
| pairs | S^φ move | 0 (#38 needs three) |
| pairs and triples | S^φ move | #773, #963 |
| pairs | completion at once | 3 |
| pairs and triples | either | **#38, #773, #813, #963, #1073** |

**5_pure #419 and #447 are repaired by none of these forms** within two settlements. Their repairs need a first move
that is not a settlement, such as the wider OC₁′ move. (*Correction:* a first version of this table also listed #1073
as unrepaired. That version's completion-at-once check lifted only one witness completion per absorber. With every
completion tried, #1073 is repaired by two pair settlements and a completion at once, as in the matching session's
witnesses, `results/k4_matching/rsd_5pure_witnesses.json.gz` on `proof/k4-matching`, commit 36ef09e6.) "Hypotheses ⇒ raw EFX₀" held in every case here, with 0
violations.

**Depth ≥ 3, and the exact obstruction** (`rsd_gaps.py`, `rsd_gaps.log`; coordinator's request). Depth 3 and 4 with
S^φ change nothing. The available settlements at the seven starts were therefore listed directly. For each, the
completions of the reduced instance after at most one move were counted, and how many of them lift.
- *#38, #773, #813, #963* are repaired by settle-then-complete, as above.
- *#1073:* settling 2 by (2, 3) with T = {4, 5} leaves 171 completions after at most one move, and 20 of them lift.
  Settling 4 by (4, 3) with T = {4, 5} leaves 116, and 12 lift. Every one-absorber completion is counted here; the first
  version counted one witness per absorber. So #1073 is repaired by "settle, then one move of I⁻", and also by two
  settlements and a completion at once.
- ***#419 and #447: RSD cannot repair them at any depth.*** The obstruction is the same at both:
  - The other sharers (1 and 2 at #419; 2 and 3 at #447) have only *triples* as improving pool sets. Each of these
    triples threatens agent 4, so (L\*) fails.
  - The only settlement is therefore agent 4, by (4, 3) with T = {8, 9} at #419, and by (4, 1) with T = {9, 10} at
    #447.
  - After it, the reduced instance has 29 completions (#419) and 43 (#447) after at most one move, counting every
    one-absorber completion. Every one of them threatens the phantom 4. No second settlement is possible.

  So agent 4 blocks both routes. As a real agent it is threatened by every other sharer's settlement. As a phantom,
  every repair of the rest threatens it. This is the **central-sharer obstruction (RSD-X)**.
- The repair of these two is kgen-rounds' ROUND-P: one OC₁′ move or two disjoint moves. RSD-IND therefore needs a
  first step that is not a settlement. The natural candidate is an OC₁′-style move that gives agent 4 its pair *and*
  moves the others at once.

## 17. Rounds: Lemma SD-E for a round, and (L\*) at the end of a round (ROUND-RSD's proof tools)

A *round* settles a set K of dangerous agents at once. Each k ∈ K gets a chain P_k, and the chains are vertex-disjoint.
P_k is a **prefix** of the earliest-wanter chain E(k): x_l is the σ-earliest wanter of Y_{x_{l−1}}, and P_k stops at
some head z_k, which may be frozen at the picks. k takes an improving T_k ⊆ (J ∪ {Y_{z_k}}) ∩ R_k, with |T_k| ≤ 3, and
the T_k are pairwise disjoint.

Full chains E(k) never form disjoint rounds in these data. When u = 1 they share their head. The repairs of ROUND-P
stop a chain early, at a head whose wanters the round serves. At 5_pure (10, 419) this is (0, 4) with {0, 7}, where
7 = Y_4 is the head's pick, together with (1, 3) with {1, 8, 9}.

**Lemma SD-E(round) (K4.MULTI.SDER).** *Refereed CORRECT (`k4/referee/oc1max_multi.md` §15, commit 135c4ef0: 312,732
random rounds, 45,542 of them with a chain stopped early; (H) ⇔ conclusion; arbitrary want-chain prefixes instead of
E(k) prefixes give 8,457 violations, so earliest-wanter prefixes are needed).* Values are strict. Suppose:
- **(H)** every agent outside K that wants a *released* head pick Y_{z_k} at the picks (a pick not taken into any
  T_k′) values its good after the round above that pick.

Then the state after the round, without K and ∪T_k, is the SD outcome of σ with K deleted.

*Proof.* This is the proof of SD-E (§12) with one new case. Let a be an agent outside K, b_a its good after the round,
and g an available good with v_a(g) > v_a(b_a) ≥ p_a.
- If g is junk of I, then v_a(g) < p_a. Contradiction.
- If g is a pick Y_j, then a wanted it, so σ(j) < σ(a). g's holder after the round comes after a, so j lies on some
  P_k and σ(x_l) < σ(a) < σ(x_{l+1}). This contradicts x_{l+1} being the earliest wanter. The chains are disjoint, so
  each good has one holder, and the argument runs inside the chain that moved g.
- *New case:* g is a released head pick Y_{z_k}. Then a wanted it at the picks, and (H) excludes that.
(H) is vacuous when every chain is a full E(k), because the head is unwanted, or when every frozen head's pick goes into
the T of its chain, as at (10, 419). ∎

Without (H) the lemma fails. Single chains stopped early fail it 29 times on the seven gaps, every time with a frozen
head's pick released.

**(L\*) at the end of a round.** No T_k may threaten any other agent at its value *after* the round:
- real agents at their new values;
- the other members of K at their thresholds τ_k′.

For a single full-E(k) pair settlement this is automatic (§12). In a round it is not, for two reasons. A released or
taken head pick may be wanted by someone. And the agents a triple threatens at their pick values may be lifted by the
round's other chains. That second effect is exactly what makes (10, 419) work: {1, 8, 9} threatens agent 4 at its pick
value, but not after 4 takes 0's pick in the chain (0, 4).

*When a round follows earlier settlements* (referee's remark), it must also satisfy two conditions toward the earlier
phantoms φ:
- the new T_k threaten no earlier phantom at τ_φ ((P2) for the newest pairs);
- every released head pick is worth at most τ_φ to the earlier phantoms ((P3), the §14 fix).

Earlier pairs never threaten the new phantoms, because those were real agents then.

With (L\*) at the end of the round as invariant (P1\*)–(P2) for the round's phantoms, Theorem S^φ's proof (§16) goes
through unchanged. Its (P3) base case additionally needs every released head pick to be worth at most τ_k to each
k ∈ K. In the census below this is checked raw, as part of the lifted EFX₀ test.

**Census** (`round_sde.py`, PREFIX=1; `round_sde_gaps7.log`):

| at the seven gaps | rounds | SD-E(round) | (L\*)-round | repaired (raw EFX₀, every completion lifted) |
|---|---|---|---|---|
| \|K\| = 1 (prefix chains) | 248 | 219, and 29 failures, exactly the 29 rounds where (H) fails | 70 | #773, #963 (by a Theorem S move) |
| \|K\| = 2 (disjoint prefix chains) | 163 | **163** | 150 | **#419, #447, #1073**, all 150 by a completion at once |

**Every one of the seven gaps is repaired:**
- #419, #447 and #1073 by one round of two simultaneous settlements and a completion;
- #38, #773, #813 and #963 by sequential settlements (§16).

So ROUND-RSD's proof tools are SD-E(round) under (H) and (L\*) at the end of the round, with Theorem S^φ and the
completion at once as the last step.

**Corollary S^φ(round) (K4.MULTI.SPHIR).** Theorem S^φ (§16, with (S-φ3)) holds verbatim when the phantoms were settled
in rounds (SD-E(round), refereed). The invariants then read:
- **(P1\*)** (L\*) at the end of each round: no T_k threatens a real agent at its value after the round. Values only rise
  afterwards, so it persists.
- **(P2)** within a round, (L\*) at the round's end toward the round-mates at their τ. Toward earlier phantoms, the new
  sets must threaten none of them. Earlier sets never threaten later phantoms.
- **(P3)** every pick a round releases is worth at most τ_φ to every phantom, those of the round included. After that,
  the induction of §14 applies.

*Proof.* S^φ's proof uses the invariants only at the final state, as a case split over real/real, real/phantom,
phantom/real and phantom/phantom pairs. (P1\*) gives the real/phantom case for sets of any size. (P2) and (P3) give the
rest as before. ∎

This makes S^φ the step of the matching session's ROUND-RSD, which repairs every start of its data with rounds of at
most two settlements and a completion at once (`proof/k4-matching`, commit 56e64a9f; at (11, 447) the round is
{(0, 4), {0, 8}} + {(2, 1), {3, 9, 10}}). **The base case is not a pure reduction.** The matching session finds
reduction failing at 35 of 10,109 one-move starts:
- T3-type starts, where the settled head must also absorb a junk good;
- 6 starts that need a junk-taking chain agent after the head; the smallest is ls-alt-rule-n4m7.

So the base case must be an OC₁-type move with phantoms. Theorem S^φ's own move is such a move, but it does not cover
those 35. They are this note's RING2 and the T3 family (§11).

**ROUND-RSD inside the refereed tools** (`round_prefix.py`, `round_prefix.log`; `round_e.py`, `round_e.log`).
- The matching session's ROUND-RSD (`k4/matching/round_rsd.py` on `proof/k4-matching`, commit 47e0bfd9) allows any
  canonical chains and checks the SD property directly. So Lemma SD-E(round), which needs earliest-wanter prefixes,
  does not cover its witnesses as found. On its 280 5_pure witnesses, 146 of the 410 rounds use a chain that is not an
  E-prefix under any SD order of the round's start. (H) holds in all 410.
- `round_e.py` therefore searches only the rounds SD-E(round) covers:
  - every chain is an E-prefix;
  - (H) holds;
  - (L\*) holds at the round's end, toward every agent and every earlier phantom;
  - (P3) holds for released picks.

  At most two rounds of at most two settlements are allowed, followed by a completion at once (every one-absorber
  completion, lifted, raw EFX₀).

| data | starts | repaired | rounds needed | SD-E(round) violations |
|---|---|---|---|---|
| 5_pure, 280 two-move starts (`n5_5pure_s5o0`) | 280 | **280** | 1 round: 2; 2 rounds: 278 | 0 |
| n = 5 walks near 5_pure#164 | 22,445 | **22,445** | 2 rounds | 0 |
| n = 4 export | 112,880 | **112,880** | 2 rounds | 0 |

So on all these data the repair is built entirely from refereed parts:
- the starts, by SD-E(round);
- the moves, by LIFT;
- the invariants, by (L\*) at the end of each round, (P2) and (P3);
- the completion, which is checked raw.

What remains open:
- the existence of such rounds at every two-move start (ROUND-IND);
- the base case at the one-move starts that pure reduction misses (the T3 family, §11).
