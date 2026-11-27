# The base case of ROUND-RSD: OC₁ with phantom constraints (workstream `proof/k4-base-phantom`)

Campaign: TARGET₄ (EFX₀ exists when every additive agent values at most four goods). Route: ROUND-RSD (`k4/matching.md`
§6 on `proof/k4-matching`; `k4/oc1max_multi.md` §13–§17 on `proof/k4-oc1max-multi-2`). This note owns piece (ii) of that
route, the base case. Code: `k4/base_phantom/`. Logs and data: `results/k4_base_phantom/`. Every completion is decided
against the raw EFX₀ definition in the whole instance. Every negative claim below has two implementations:
- `bplib.py`, `base.py`, `deadends.py`, `rules.py` (bit masks);
- `check_deadends.py`, `check_rules.py`, `verify_nop1_gap.py` (Python sets, written again from the definitions; they import
  nothing from the first group or from `k4/`).

Everything called evidence is evidence only (PROMPT.md §5 rule 3).

## Summary

| | statement | status |
|---|---|---|
| Reproduction (§1) | pure reduction fails at 35 (RSD), 35 (ROUND-RSD), 23 ((L\*) deferred), 18 (deleted agents receiving), 6 (both) of the 8,539 distinct one-move starts; per file (multi, Hall, PW) 35/35/23/18/6, 32/32/21/17/6, 0 | reproduces K4.MATCH.RSD.BASE and the referee's count with independent code |
| **The base case as stated** (§2) | "at a state reached by admissible rounds, with no lifted completion and no admissible round, some one-move repair respects the phantoms" | **REFUTED.** False at every one of the 32,480 dead-end states of the n = 4 export (from 16,240 starts); 29,280 of them admit **no EFX₀ allocation at all** that keeps the phantoms' sets. Smallest: T3 (n = 3, m = 6), §2.2, by hand |
| Dead ends elsewhere (§2) | n5 partial export 9,260 dead ends (3,499 starts), 0 with a one-move repair; walks 6,008, 0; 5_pure 251, 9; one-move starts 629, 6 at Φ = ∅ and 6 with phantoms | computed, two implementations |
| Base class at Φ = ∅ (§3) | the least class of a one-move repair at the 8,539 one-move starts: **C0** (settlement-shaped canonical chains and rings from a dangerous agent, no junk after x₀) at 8,515; **ED** (only the end takes junk, possibly without wanting its predecessor's good alone) at 24, the 6 included. Canonical chains whose *middle* agents take junk are never needed | evidence |
| **Proposition SEP** (§4.1) | a phantom k with no "ℓ alone" constraint (every good of R_k ∖ T_k worth at most v_k(T_k): *P1-free*) is threatened only by bundles of three or more goods containing two goods of R_k ∖ T_k; for a pair T this is "y_k and ℓ_k together in a bundle of ≥ 3 goods". So (P3) and S^φ's (S-φ2), (S-φ3) hold automatically | **PROVED** (written proof, from Lemma PHANTOM) |
| The ℓ-alone trap (§4.2) | every dead end of the n = 4 export, of the walks and of the n5 partial export carries an "ℓ alone" constraint on a present agent's good | computed, two implementations |
| **P1-free greedy at n = 4** (§4.3) | from every one of the 112,880 n = 4 two-move starts, *every* sequence of admissible rounds whose settlements are P1-free ends in a lifted completion; no dead end is reachable | **CERTIFIED** (exhaustive over the complete export; `rules.py` and `check_rules.py`, 112,880 / 112,880) |
| "A P1-free round exists at every two-move start" (§4.4) | | **REFUTED** at n = 5: 12 of the 280 sampled 5_pure two-move starts (smallest m = 9) have admissible rounds, but each settles some agent with an ℓ-alone constraint; two implementations |
| **Conjecture BASE-R** (§5) | the base case in the P1-free class: every state that the greedy process GR visits (it takes P1-free rounds only where there is no completion, final round or ED repair), and that has no lifted completion, no *final round* (one admissible round of any kind followed by a lifted completion at once) and no *ED repair*, has an admissible P1-free round. So **GR never gets stuck**, and ROUND-IND needs no existential choice | evidence: GR is safe at **every start of every data set**: 112,880 (n = 4), 1,285,930 (the certifier's whole n = 5 export), 14,047, 4,955, 280 and 8,539. Independent re-check on all but the n = 5 export, where it runs on the complete sel2 lists |
| Strong form of BASE-R (§5) | the same for every state reached by P1-free rounds (rounds also taken where a final round exists) | **REFUTED** at 8 of the 280 5_pure starts; two implementations |
| **Lemma B3, Corollary B3′** (§5.1) | the lift at the last step: an official move plus completion, EFX₀ in the present instance and threatening no phantom, is EFX₀ in I. Theorems U, S, RING-red, D-red, KEEP and OWN in the present instance therefore give ED repairs once the bundles of three or more goods separate the phantoms' pairs. BASE-R ⟸ B1 (ED repair where no round exists) ∧ B2 (final round or ED repair where every round creates an ℓ-alone phantom) | **PROVED** (written proofs); B1, B2 open. On all data B1 occurs only at the 6, and B2 with phantoms at 134,835 states |

**Bottom line.**
1. The base case cannot be stated for all reachable phantom states. The dead ends of ROUND-RSD are not a base case
   waiting for a better move: 90% of them are *infeasible* (no EFX₀ allocation keeps the phantoms' sets), and almost
   none has a one-move repair. The round that led there was the mistake.
2. The mistake is always an "ℓ alone" phantom on a present agent's good at n = 4 and in the large n = 5 sample. Rounds
   whose settled agents carry no such constraint (P1-free) never lead to a dead end at n = 4 (certified). P1-free
   phantoms only forbid a bundle of three or more goods containing their former pick and their fourth good (Proposition
   SEP), so the phantom class they generate is nearly constraint-free.
3. The base case is then a statement about the P1-free class (Conjecture BASE-R): a final round of any kind, or an
   ED move, then a completion at once. ED (Hall's ED chains, `k4/oc1_hall.md` §14) is the right move class, not
   "canonical chains whose middle agents take junk".
   - The process GR, "stop when a completion, a final round or an ED repair exists, otherwise take any P1-free
     round", never gets stuck on all data, including the certifier's whole n = 5 export (1,285,930 starts).
   - BASE-R would make the whole ROUND-RSD induction greedy.
   - It splits into two open lemmas, B1 and B2, plus a proved lift (B3) that transfers the existing Part 1 theorems
     to phantom states (§5.1).

## 0. Setting

Notation of `k4/matching.md` §6 and `k4/oc1max_multi.md` §14–§17.
- A *state* S has present agents, present goods, and bases: every present agent holds one good (a perfect SD start of
  the present instance) and every deleted agent k (a *phantom*) holds its fixed set T_k, with threshold τ_k = v_k(T_k).
  J is the junk: present goods outside the present bases.
- i *wants* g if v_i(g) > v_i(B_i). A single-good holder is *frozen* if a present agent wants its good, *dangerous* if
  frozen and valuing a junk good. Phantoms do not count as wanters.
- A *settlement* (k, P, T): k dangerous, P = (k = x₀, x₁, …, x_t) a canonical chain (each x_l wants x_{l−1}'s good), T ⊆
  (J ∪ B_{x_t}) ∩ R_k improving for k. A *round* is one or two settlements with vertex-disjoint chains and disjoint
  sets, applied at once. It is *admissible* when:
  - (L\*) at the round's end: no T threatens another agent present at the round's start, at its value after the round
    (round-mates at their τ);
  - (P2): no T threatens an earlier phantom at its threshold;
  - the reduced state is a perfect SD outcome of the reduced instance (`bplib.is_sd`: strict values, every agent holds
    a good it values, values no unpicked present good above it, and the wants digraph is acyclic; cross-checked
    against brute force over orders at all 8,539 starts; the 3 starts with a tie, log459, use brute force).
- A *lifted completion*: a one-absorber completion of the present agents (one present owner takes any junk, every other
  present agent at most one junk good, phantoms nothing), raw EFX₀ in the whole instance I.
- A *dead end*: a reachable state with no lifted completion and no admissible round. *Feasible*: some EFX₀ allocation of
  I gives every phantom exactly its T (the present goods go to the present agents in any way; exact search).
- An *official move* (`k4/sdc.md` §29): a chain x₀, …, x_t (t ≥ 1) of present agents, x₀ taking H₀ ⊆ (J ∪ B_{x_t}) ∩
  R_{x₀} improving, each x_l taking B_{x_{l−1}} ∪ H_l with H_l ⊆ J ∩ R_{x_l}, gaining. A *one-move repair*: an official
  move, then a lifted completion. Move classes (`base.py`), each containing the previous one:
  - **C0**: x₀ dangerous, every link canonical, no junk after x₀ (settlement-shaped; rings, H₀ ∋ B_{x_t}, included);
  - **ED**: x₀ dangerous, links before the last canonical with no junk; the end x_t may take junk and need not want
    B_{x_{t−1}} alone (Hall's ED chains);
  - **C1**: adds canonical chains whose middle agents take junk; **C2**: any first agent; **C3**: every official move.
- Lemma PHANTOM (K4.MATCH.LIFTSTAR, refereed CORRECT): with R_k = T ∪ {y, ℓ} (y the former pick), X threatens k iff
  (P1) ℓ ∈ X, |X| ≥ 2, v_k(ℓ) > τ_k, or (P2) {y, ℓ} ⊆ X, |X| ≥ 3, v_k(y) + v_k(ℓ) > τ_k; a triple T is never
  threatened. A settlement is **P1-free** if every good of R_k ∖ T is worth at most τ_k to k.

## 1. Reproduction of K4.MATCH.RSD.BASE (`base_census.py`, `base_census.log`)

On the 8,539 distinct starts (multi 8,383 rows, Hall 2,071, PW 291; 1,570 starts in both the multi and Hall files), all
perfect SD starts and all one-absorber-hard, pure reduction (rounds, then a completion at once) fails at:

| form | fails (distinct) | multi | Hall | PW |
|---|---|---|---|---|
| (i) RSD, (L\*) at the step | 35 | 35 | 32 | 0 |
| (iR) ROUND-RSD, rounds of ≤ 2 | 35 (the same) | 35 | 32 | 0 |
| (ii) (L\*) deferred | 23 | 23 | 21 | 0 |
| (i′) deleted agents may receive junk | 18 | 18 | 17 | 0 |
| (iii) both | 6 | 6 | 6 | 0 |

The 6 are ls-alt-rule-n4m7 (n = 4, m = 7), Q2, nsw-strict-n4m8, nsw-strict-n4m9, c4one-one-rotation-m8 and -m9, a
subset of the 35. By (n, m) the 35 are (3, 6): 15, (3, 7): 3, (4, 7): 7, (4, 8): 4, (4, 9): 1, (5, 8): 3, (5, 9): 2. This
is exactly matching's and the referee's count (`k4/referee/lift.md` §9).

**What the 35 are** (`deadends.py`, `deadends_onemove.log`).
- At the 6, **no admissible round exists at all**: they are dead ends at Φ = ∅.
- At the other 29, every sequence of admissible rounds ends at a dead end with phantoms. None of these 30 dead-end
  states has a one-move repair, and 29 of them are infeasible.
- So at all 35 the only repair is OC₁ at the start itself.

## 2. The base case as stated is false

**Statement tested (the coordinator's "base case").** At a state S reached from a hard perfect start by admissible
rounds, if S has no lifted completion and no admissible round, then some one-move repair (any official move, then a
lifted completion) respects every phantom.

### 2.1 The dead-end census (`deadends.py`; second implementation `check_deadends.py`)

Every state reachable by admissible rounds is generated, from every start. Each dead end is tested for feasibility and
for a one-move repair of each class.

| data | starts | starts with a reachable dead end | dead-end states | infeasible | feasible, no one-move repair | with a one-move repair |
|---|---|---|---|---|---|---|
| n = 4 export (all two-move starts) | 112,880 | **16,240** | 32,480 | **29,280** | 3,200 | **0** |
| n5 partial export, every 50th start | 14,047 | 3,499 | 9,260 | 7,127 | 2,133 | 0 |
| walks near the n = 4 failures (multi) | 4,955 | 3,004 | 6,008 | 6,008 | 0 | 0 |
| 5_pure sample (certifier) | 280 | 123 | 251 | 221 | 21 | 9 (C0: 6, ED: 3) |
| one-move starts | 8,539 | 321 | 629 | 531 | 86 | 12 (6 at Φ = ∅, the 6 of §1) |

- 16,240 is the referee's number.
- Every record was re-checked from the raw definitions by `check_deadends.py` (logs `check_deadends_*.log`):
  - the path of rounds is admissible and reaches the stored state;
  - the state has no one-absorber completion and no admissible round;
  - a one-move repair exists exactly where recorded;
  - the feasibility flag is right (all allocations of the present goods enumerated).
- 0 mismatches: 32,480 / 32,480 at n = 4, 9,260, 6,008, 251 and 629.

So the statement fails at every n = 4 dead end, and no choice of move class can save it: 90% of the n = 4 dead ends
have no EFX₀ allocation at all that keeps the phantoms' sets. A base lemma at reachable states is impossible. Rounds
must be chosen so that dead ends are never reached.

### 2.2 The smallest instance: T3 (n = 3, m = 6), by hand

T3 with picks (0, 1, 4) (one of the 35):
- R₀ = {0: 38, 2: 6, 4: 36, 5: 1}, R₁ = {1: 22, 3: 12, 4: 30}, R₂ = {0: 38, 1: 20, 3: 12, 4: 28}; junk {2, 3, 5}.
- Agent 1 wants agent 2's good 4, so 2 is dangerous.
- **The only admissible round:** settle 2 by the chain (2, 1), T = {1, 3} (32 > 28). Agent 1 takes 4.
  - (L\*): T leaves 22 ≤ 30 to agent 1 and is worthless to agent 0.
  - The rest is SD: 0 holds its top good 0, and 1 holds 4, its best good left.
- **The state is infeasible.** Phantom 2 has τ = 32, and v₂(0) = 38 > 32, so good 0 must be alone in its bundle (P1).
  Two present agents share the goods {0, 2, 4, 5}:
  - 0 holds {0}: then 1 holds {2, 4, 5}, which leaves agent 0 a threat of 36 + 6 + 1 − 1 = 42 > 38.
  - 1 holds {0}, worth 0 to it: then 0 holds {2, 4, 5}, and removing a good agent 1 does not value leaves 30 > 0.
- T3's repair is the swap ring 0 ↔ 2 of `k4/oc1max_multi.md` §11, a C0 move at the start. Pure reduction cannot use
  it: the only round leads to a hopeless state.

### 2.3 An n = 4 example (two-move start; where the choice of round matters)

Sets [[0,1,4,5],[1,4,5,6],[2,3,4,6],[2,3,5,6]], values [[1,4,6,8],[3,4,8,10],[5,3,6,7],[4,3,8,6]], picks (5, 1, 4, 6),
junk {0, 2, 3}. No completion and no one-move repair. Three admissible rounds:

| round | phantom constraint | after it |
|---|---|---|
| settle 2 by (2, 1), T = {2, 3}, τ = 8 | none of type P1 (R₂ ∖ T worth 6, 7) | settle 0 by (0, 3, 1) with {1, 4}, then a completion |
| settle 3 by (3, 1), T = {2, 3}, τ = 7 | good 5 alone (v₃(5) = 8 > 7), on agent 0's base | **dead end** (feasible, no one-move repair) |
| settle 3 by (3, 2, 1), T = {2, 3}, τ = 7 | the same | settle 0 by (0, 1) with {0, 1, 4}, then a completion |

The second row is the trap. The P1-free first row is always safe here.

## 3. Which moves the base case needs at Φ = ∅ (`classes.py`, `classes.log`, `ring2.py`, `ring2.log`)

At the 8,539 one-move starts, the least class with a one-move repair:

| least class | starts | pure reduction repairs |
|---|---|---|
| C0 (settlement-shaped, rings included) | 8,515 | 8,486 (29 fail) |
| ED, not C0 | 24 | 18 (6 fail: the 6) |
| C1, C2 or C3 only | 0 | |

- Among the 24 ED starts, 15 need one junk good at the end (Theorem S's allocation with a *weak* last link: the end
  takes its predecessor's good plus Theorem S's slot good h, and does not want the good alone). The other 9 need more
  junk at the end.
- Their shapes: 16 rings of length 3, 2 of length 4, and 6 chains of length 3, all from a dangerous agent. The
  shortest repair at the three length-2 cases (nsw-strict-n4m9, c4one m8, m9) starts at a non-dangerous holder, but
  each also has an ED ring from a dangerous agent.
- At the 6 the ED ring has one shape. Two dangerous agents k, d have single wanters w_k, w_d. The ring
  k → w_k → w_d → k: w_k takes Y_k, w_d takes Y_{w_k} plus junk, and k takes Y_{w_d} plus junk. It is the dangerous
  ring of Lemma RING-red (`k4/oc1max_multi.md` §6), whose end takes its predecessor's pick plus junk.
- At the 6 **no settlement exists at all**: each dangerous agent has exactly one canonical chain, and its pool (the
  junk plus the end's good) is worth less than its pick. By Proposition T0 (K4.MULTI.T0, refereed), some dangerous k
  has an improving set inside J ∪ B_z for an unfrozen z. At each of the 6, the ED ring ends at such an unfrozen z, and
  x₀'s set lies inside J ∪ B_z; z is reached by the weak last link because no canonical chain from k ends at z. This is
  a pointer for a Part 1 lemma, checked on these 6 only.
- So "canonical chains whose middle agents may take junk" add nothing on the data: every repair that needs junk after
  x₀ needs it at the *end*, with a weak last link. The class is ED (Hall/TTC's OC₁-ED, `k4/oc1_hall.md` §14), where it
  is already the evidence class.

**RING.** My own reading of multi's RING class gives 23 starts: no C0 chain from a dangerous agent k has an S\*
completion owned by k. Multi's count is 45 (`k4/oc1max_multi.md` §11), with its own mechanism order and with rings
counted outside "canonical"; I did not reproduce that list. On my 23: C0 repairs 5 (another owner), ED 18, and pure
reduction fails at 6. T3 with picks (0, 1, 4) is not among my 23, because its swap ring is a C0 move owned by agent 0.

## 4. The ℓ-alone trap, and the P1-free class

### 4.1 Proposition SEP (P1-free phantoms are separations)

**Proposition SEP (K4.BASE.SEP).** Let a phantom k hold T ⊆ R_k with τ = v_k(T) > p_k, where |R_k| ≤ 4, and suppose k is
P1-free: v_k(g) ≤ τ for every g ∈ R_k ∖ T. Let X be a bundle disjoint from T.
1. If |X| ≤ 2, or X contains at most one good of R_k ∖ T, then X does not threaten k.
2. If |T| = 3, nothing threatens k. If |T| = 2 and R_k = T ∪ {y, ℓ}, X threatens k iff {y, ℓ} ⊆ X, |X| ≥ 3 and
   v_k(y) + v_k(ℓ) > τ.
3. Consequently, in a state all of whose phantoms are P1-free:
   - (P3) of `k4/oc1max_multi.md` §14 holds automatically (every junk good is worth at most τ_k to k);
   - no agent is phantom-frozen;
   - in Theorem S^φ (K4.MULTI.SPHI) and its round form (K4.MULTI.SPHIR), (S-φ2) and (S-φ3) hold automatically, and
     (S-φ1) reduces to the condition of 1–2 for the owner's bundle W.

*Proof.* A threat to k by X is a value v_k(X ∖ h) > τ for some h ∈ X.
1. If |X| ≤ 2, X ∖ h has at most one good, worth at most τ to k, since X ∩ R_k ⊆ R_k ∖ T. If X has at most one good
   of R_k ∖ T, every X ∖ h holds at most that good of R_k, worth at most τ.
2. For |T| = 3, R_k ∖ T ⊆ {y} and 1 applies. For |T| = 2, Lemma PHANTOM gives (P1) or (P2), and (P1) needs
   v_k(ℓ) > τ, which P1-freeness excludes.
3. Junk goods lie in R_k ∖ T or outside R_k. Phantom-frozen means some phantom values the agent's good above its
   threshold. (S-φ2) and (S-φ3) are statements that single goods are worth at most τ_φ. ∎

*Corollary LIFT-SEP.* In a state reached by rounds whose settlements are all P1-free, an EFX₀ allocation X of the
present instance that extends the state is EFX₀ in I iff no bundle of X threatens a phantom. By SEP only a bundle of
three or more goods containing at least two goods of some R_k ∖ T_k can; for a pair T_k, exactly a bundle of three or
more goods containing {y_k, ℓ_k} when v_k(y_k) + v_k(ℓ_k) > τ_k. *Proof:* Lemma LIFT\* for rounds (refereed CORRECT,
`k4/referee/lift.md` §9) reduces the lift to (Φ), "no bundle of X threatens a phantom". (L\*) at each round's end
handles the real agents against the T's, and SEP describes the threats to phantoms. ∎

So the phantom constraints of the P1-free class are exactly *separations*. A bundle of at most two goods is always
safe. In particular every holder's bundle of an S\* completion is safe, and so is every bundle in which y_k still sits
as a single base. Only bundles of three or more goods that contain both y_k and ℓ_k matter.

### 4.2 The trap is the ℓ-alone constraint (`deadends.py`, `check_deadends.py`)

At every dead end with phantoms, the constraint kinds of its phantoms:

| data | dead ends with phantoms | some phantom with "ℓ alone" on a present agent's base | only pair or no constraints |
|---|---|---|---|
| n = 4 export | 32,480 | **32,480** | 0 |
| n5 partial | 9,260 | **9,260** | 0 |
| walks | 6,008 | **6,008** | 0 |
| 5_pure sample | 251 | 225 | 26 |
| one-move starts | 623 | 298 | 325 |

At the one-move starts the pair-only dead ends do not matter: there GR (§5) stops at the start, by a final round or an
ED repair. The second implementation agrees: `check_deadends.py` recomputes, for each record, whether some phantom values a
present agent's base above its threshold.

### 4.3 The P1-free greedy process at n = 4 (`rules.py`, `check_rules.py`; logs `rules_*.log`, `check_rules_*.log`)

For a rule R on settlements, the *R-greedy process* takes any admissible round all of whose settlements satisfy R, until
a lifted completion exists. R is *safe* at a start if no reachable state of the process is stuck (no completion and no
R-round). Then every greedy run ends in an EFX₀ allocation.

| data | starts | rule "any" (ROUND-RSD as is) | rule **P1-free** | P1-free, independent check |
|---|---|---|---|---|
| n = 4 export | 112,880 | 16,240 unsafe | **0 unsafe** | **112,880 safe** (746,000 states) |
| walks | 4,955 | 3,004 unsafe | **0 unsafe** | 4,955 safe |
| n5 partial | 14,047 | 3,499 unsafe | 1,165 unsafe | 1,165 unsafe (the same) |
| 5_pure sample | 280 | 123 unsafe | 28 unsafe | 28 unsafe |

**At n = 4 the P1-free greedy process is safe from every two-move start (K4.BASE.P1FREE.N4, CERTIFIED).** The start set
is compute/k4-oc1max-cert's complete export (its certificate, PR #114). The claim is a finite exhaustive statement,
decided by two independent implementations. So at n = 4 ROUND-IND holds greedily, with no existential choice, once
the settled agents are P1-free.

Other rules, on every 10th n = 4 start (11,288; `rules_n4_allrules_s10.log`, evidence). Safe at all of them:
- P1-free;
- P1-free with E-prefix chains;
- "every ℓ-alone good is junk";
- "ℓ held by an agent content with ℓ alone" (charity's lock, `P1ok`), alone or with E-prefixes.

Unsafe at 1,314 to 1,635 starts: any round, E-prefix chains, full E(k), full chains, best sets and k's best set.
Satisfied phantoms only, pairs only and triples only are worse (8,722, 2,417 and 11,288 unsafe), and P1-free with k's
best set is unsafe at 72. So the safe rules are exactly those that forbid an ℓ-alone constraint on a base that can
still move.

### 4.4 P1-free rounds do not always exist at n = 5 (`verify_nop1_gap.py`, `verify_nop1_gap_5pure.log`)

At 12 of the 280 sampled 5_pure two-move starts (idx 59, 738, 783 ×2, 1009 ×2, 1073 ×3, 1164 ×3; all n = 5, m = 9 or 10),
every admissible round settles an agent with an ℓ-alone constraint. Both implementations confirm:
- the start is hard;
- it has no one-move repair;
- admissible rounds exist, and none is P1-free.

So "a P1-free round exists at every two-move start" is **false** (K4.BASE.P1FREE, REFUTED). Example, 5_pure idx 738:
- R₀ = {0: 3, 2: 7, 7: 5, 8: 6}, R₁ = {1: 2, 5: 3, 7: 6, 8: 10}, R₂ = {2: 10, 4: 3, 6: 6, 7: 8}, R₃ = {3: 10, 4: 6, 6: 3,
  8: 8}, R₄ = {3: 7, 5: 5, 7: 6, 8: 3}; picks (2, 5, 7, 8, 3).
- The single settlements are (2, (2, 1), {4, 6}) and (3, (3, 1), {4, 6}). Both have τ = 9 and lock a pick worth 10 to
  the settled agent: 2 locks agent 0's pick 2, and 3 locks agent 4's pick 3.

At all 12, the *round of two* "one P1-free settlement and one P1 settlement" is followed by a completion at once. At
738 it is (0, (0, 2), {0, 7}) with (3, (3, 1), {4, 6}). The ℓ-alone phantom is created in the last round, where it
costs nothing. This is what BASE-R's final round does.

## 5. The base case in the P1-free class: Conjecture BASE-R, and the greedy process GR

**The process GR** (greedy P1-free reduction). At the current state S (start: a hard perfect start, Φ = ∅):
1. if S has a lifted completion, stop;
2. if S has a **final round**, apply it and stop. A final round is an admissible round of any kind (ℓ-alone phantoms
   allowed) after which a lifted completion exists at once;
3. if S has an **ED repair**, apply it and stop. An ED repair is an ED move of the present instance followed by a lifted
   one-absorber completion;
4. otherwise apply *any* admissible round whose settlements are all P1-free, and repeat.

Every stop is a raw EFX₀ allocation of I. Each round deletes at least one agent, so GR terminates. Every phantom it
creates before the last step is P1-free. Its constraints are therefore separations (Proposition SEP), and (P3),
(S-φ2), (S-φ3) are automatic along the way.

Call a state **GR-visited** if it is a hard perfect start (strict values, at most four relevant goods per agent), or if
it arises from a GR-visited state S′ by an admissible P1-free round, where S′ has no lifted completion, no final round
and no ED repair. These are exactly the states GR can reach.

> **Conjecture BASE-R (K4.BASE.GR).** Every GR-visited state that has no lifted completion, no final round and no ED
> repair has an admissible P1-free round. Equivalently, GR never gets stuck.

*The hypothesis "GR-visited" is needed.* Drop it, so that rounds may also be taken at states that already have a final
round or an ED repair (MODE=GRR: P1-free rounds are taken wherever one exists, and the base is used only where none
does). Then some reachable state has no completion, no final round, no ED repair and no admissible round, at 8 of the
280 5_pure starts (K4.BASE.GRR, REFUTED; `gr.py` and `check_rules.py` agree). At all of them the stuck states have two
phantoms and no admissible round. *Correction:* the first version of this section, at f2d9304, stated BASE-R for every
state reached by P1-free rounds; that form is this refuted one.

BASE-R says exactly that GR never gets stuck. With Lemma MAXSD and Lemma RED (`k4/sdc.md` §31) reducing TARGET₄ to
perfect starts, as for K4.MATCH.CM2, it would imply TARGET₄. It is ROUND-IND (piece (i)) and the base case (piece
(ii)) in one statement, and it has no existential choice: any P1-free round works.

*Evidence:*
- `rules.py`, with terminal "completion, a final round or a base repair ≤ ED";
- `gr.py`, GR itself, fast, with the lemma census of §5.1;
- the independent `check_rules.py` with MODE=GR.

| data | starts | GR stuck | where the base is used |
|---|---|---|---|
| n = 4 export | 112,880 | **0** | never: the P1-free rounds alone end in completions (§4.3) |
| walks | 4,955 | **0** | final rounds only |
| n5 partial, every 50th start | 14,047 | **0** | final round or C0 at the 1,165 starts where P1-free rounds alone fail |
| 5_pure sample | 280 | **0** | final round (the 12 of §4.4 included) |
| one-move starts | 8,539 | **0** | ED is needed: with final rounds and C0 only, 7 get stuck; the 6 of §1 have no round at all |
| **n5 sel2**: 5_pure #419, #447, #38, every profile (the certifier's complete lists, its certificate) | 583,680 | **0** | final rounds only, with a P1-free round also available |
| **n5 partial6**: six 5_pure hypergraphs, time-capped lists | 702,250 | **0** | final rounds; B2 (§5.1) at 134,822 states with one phantom |

So GR never gets stuck on **1,285,930 n = 5 starts**, the certifier's whole n = 5 export, in about 22 minutes (`gr.py`,
`gr_n5sel2.log`, `gr_n5partial6.log`). The independent `check_rules.py` re-check of the sel2 lists, in ten chunks,
is in `check_rules_GR_n5sel2_part*.log`.

Further facts:
- Without step 2, GR with an ED or even a C3 base gets stuck at the 12 starts of §4.4.
- Without step 3, it gets stuck at 47 one-move starts.

### 5.1 The proof skeleton: Lemmas B1, B2 and B3

Let S be a GR-visited state with no lifted completion. BASE-R at S follows from two lemmas, according to which
admissible rounds S has.

> **Lemma B1 (OC₁-ED where no round exists; open).** If S has no admissible round at all, then S has an ED repair.

> **Lemma B2 (the final mixed round; open).** If S has admissible rounds but none of them is P1-free, then S has a final
> round or an ED repair.

*BASE-R ⟸ B1 ∧ B2.* Suppose S has no final round, no ED repair and no admissible P1-free round. If S has no
admissible round, B1 gives an ED repair, a contradiction. Otherwise every admissible round of S settles some agent
with an ℓ-alone constraint, and B2 gives a final round or an ED repair, a contradiction. ∎

> **Lemma B3 (the lift at the last step; PROVED).** Let S be a state reached from a hard perfect start by admissible
> rounds (P1-free or not). Let X be an allocation of the present goods to the present agents, obtained from S by at most
> one official move followed by a one-absorber completion. Suppose:
> - X is EFX₀ among the present agents;
> - no bundle of X threatens a phantom at its threshold.
>
> Then X together with every T_φ is EFX₀ in I. For a P1-free phantom φ (Proposition SEP), the second condition concerns
> only bundles of three or more goods: for a pair T_φ, such a bundle must not contain both y_φ and ℓ_φ when
> v_φ(y_φ) + v_φ(ℓ_φ) > τ_φ. A final round followed by a lifted completion is the case "no move" at the state after
> that round.

*Proof.* Values of present agents never decrease: in a round every chain agent gains and the others keep their goods;
in an official move every chain agent gains; and a completion only adds goods. Take agents a ≠ b of I.
1. *a, b present in X.* X is EFX₀ among them.
2. *a present, b a phantom.* a was present when b was settled. (L\*) at the end of b's round says T_b does not
   threaten a at a's value then, and a's value only rose since.
3. *a a phantom, b present.* The second hypothesis. For a P1-free a, Proposition SEP says X_b can threaten a only if
   X_b has three or more goods, at least two of them in R_a ∖ T_a (for a pair T_a: both y_a and ℓ_a).
4. *a, b phantoms.* Three cases:
   - b settled after a: (P2) at b's round;
   - b settled in a's round: (L\*) at that round's end, toward round-mates at their thresholds;
   - b settled before a: a was present at b's round. (L\*) there holds at a's value at that round's end, which is at
     most a's value when a was settled and so below τ_a.

   A threshold never changes, since a phantom keeps T_a. ∎

This is Lemma LIFT\* for rounds (refereed) extended to a last official move, with (Φ) read through SEP. Its use: at
GR-visited states every phantom before the last step is P1-free, so in B1 and B2 the repair only has to be EFX₀ *in
the present instance* and separate the pairs. A final round's own phantoms may carry ℓ-alone constraints; for them
the second condition says that ℓ is alone in its bundle of X (PHANTOM (P1)).

> **Corollary B3′ (Part 1 transfers; PROVED).** At a GR-visited state S, suppose the hypotheses of one of the following
> hold for the present instance (a perfect SD start):
> - Theorem U (K4.MULTI.U), or Theorem S (K4.MULTI.S, relaxed form);
> - Lemma RING-red (K4.MULTI.RING), with its S\* completion owned by k;
> - Lemma D-red (K4.MULTI.DRED) with no obstacle, or Lemma KEEP or OWN (all refereed CORRECT).
>
> If every bundle of three or more goods in that allocation separates the phantoms' pairs, the allocation is an ED
> repair of S that respects every phantom. In particular, B1 and B2 hold at S whenever such a case exists.

*Proof.* Each of these results gives an allocation, EFX₀ in the present instance, made of one canonical chain or one
dangerous ring followed by a one-absorber completion. A canonical chain is C0 ⊆ ED; a dangerous ring takes junk only
at its end d, so it is ED. Apply B3. ∎

In these allocations the bundles with three or more goods are:
- the owner's bundle (k's W in Theorems U and S, k's H₀ ∪ J′ in RING-red);
- k's H₀ when it has three goods and another agent owns;
- in RING-red, d's {Y_{x_{t−1}}} ∪ H_t when \|H_t\| ≥ 2.

So the condition is at most three separation checks. A P1-free phantom's y_φ sits as the single base of the agent that
took it, unless a later chain released it.

*What the data say about B1 and B2* (`gr.py`, logs `gr_*.log`: at every state where GR stops by its base, whether a
P1-free round, some other round, or no round existed there):

Counts are of GR-visited states where GR stops by its base (a final round or an ED repair). The three columns of each
block are: no admissible round (B1), rounds but none P1-free (B2), a P1-free round also available (base not needed).

| data | starts | Φ = ∅: B1 / B2 / not needed | with phantoms: B1 / B2 / not needed |
|---|---|---|---|
| one-move, multi file | 8,081 | 6 / 252 / 7,823 | 0 / 0 / 0 |
| one-move, Hall file | 1,737 | 6 / 83 / 1,648 | 0 / 0 / 0 |
| one-move, PW file | 291 | 0 / 0 / 291 | 0 / 0 / 0 |
| 5_pure sample | 280 | 0 / 12 / 138 | 0 / 13 / 314 |
| walks | 4,955 | 0 / 0 / 577 | 0 / 0 / 7,182 |
| n = 4 export | 112,880 | 0 / 0 / 0 | 0 / 0 / 302,320 |
| n5 sel2 | 583,680 | 0 / 0 / 391,680 | 0 / 0 / 192,000 |
| n5 partial6 | 702,250 | 0 / 0 / 367,433 | 0 / 134,822 / 743,400 |

The 6 B1 states of the multi and Hall files are the same 6 starts. ED repairs are used only at Φ = ∅ (`gr_*.log`).

- **B1 is needed only at Φ = ∅ on all data, at exactly the 6** of §1. At those, the repair is the dangerous ED ring of
  §3 (Lemma RING-red's shape). No GR-visited state with phantoms ever lacks an admissible round.
- **B2 with phantoms** occurs at the 5_pure sample and the n5 exports: there every admissible round creates an
  ℓ-alone phantom, and a final round repairs. The tool for a proof is Theorem S^φ(round) (K4.MULTI.SPHIR), with the
  P1 phantoms created in the final round itself: then (S-φ2) asks that the ℓ-holder take no junk.
- **B2 at Φ = ∅** is OC₁ in its two-settlement form (a final round is two simultaneous settlements and a completion).
  At one-move starts an ED repair always exists (§3), so B2 is needed at Φ = ∅ only at two-move starts.

*The shape of B2's final rounds* (`b2_shapes.py`; `b2_shapes_5pure.log`, `b2_shapes_n5partial6_s50.log` on every 50th
start of partial6):

| B2 states | final rounds available |
|---|---|
| Φ = ∅ (the 12 5_pure starts) | only rounds of **two** settlements, exactly one of them with an ℓ-alone constraint; no single settlement completes |
| one phantom (5_pure: 13; partial6 sample: 2,681) | always a **single** settlement with an ℓ-alone constraint, then a completion |

So B2 has two forms:
- **B2⁰**, at Φ = ∅: a mixed round of one P1-free and one P1 settlement, then a completion. This is the round form of
  OC₁ at two-move starts; ROUND-P and the matching session's round repairs (#419, #447) are of this kind.
- **B2⁺**, with P1-free phantoms: one settlement whose phantom keeps an ℓ-alone constraint, then a completion. This is
  a C0 one-move repair of the present instance. By Lemma B3 it only needs EFX₀ in the present instance, the
  separations, and ℓ alone in its bundle. That is Theorem S^φ's setting with the new phantom's (S-φ2): the holder of
  ℓ takes no junk.

## 6. Reproduction

```
python3 k4/base_phantom/base_census.py            # §1, ~20 s
python3 k4/base_phantom/classes.py                # §3
python3 k4/base_phantom/ring2.py                  # §3, RING
python3 k4/base_phantom/deadends.py n4 results/k4_base_phantom/data/two_move_starts_n4.json.gz      # §2, ~3 min
python3 k4/base_phantom/check_deadends.py results/k4_base_phantom/deadends_n4.jsonl.gz             # §2, second implementation
RULES=any,noP1 python3 k4/base_phantom/rules.py n4 results/k4_base_phantom/data/two_move_starts_n4.json.gz   # §4.3, §5
python3 k4/base_phantom/check_rules.py results/k4_base_phantom/data/two_move_starts_n4.json.gz      # §4.3, second implementation
MODE=GR python3 k4/base_phantom/check_rules.py FILE                                                 # §5, second implementation
python3 k4/base_phantom/verify_nop1_gap.py results/k4_base_phantom/data/n5_5pure_s5o0_two_move_starts.jsonl.gz   # §4.4
python3 k4/base_phantom/gr.py n5sel2 results/k4_base_phantom/data/two_move_starts_n5_sel2.json.gz          # §5, GR with the lemma census
sh results/k4_base_phantom/runs.sh; sh results/k4_base_phantom/runs_gr.sh                           # every log (about 40 min, 4 CPUs)
sh results/k4_base_phantom/runs_gr_n5.sh                                                            # gr.py on every data set, n = 5 exports included (~25 min)
sh results/k4_base_phantom/runs_sel2_check.sh                                                       # second implementation on sel2 (~4 h)
```

Data (`results/k4_base_phantom/data/`, copied byte for byte):
- from `proof/k4-matching` `results/k4_matching/data/`: the three one-move files, the n = 4 export (sha256 6159e38d…,
  the certifier's export), the 5_pure sample, the n5 partial subsample, and multi's walk starts;
- from `compute/k4-oc1max-cert` `results/k4_oc1max/n5/`: `two_move_starts_n5_partial6.json.gz` (702,250 starts, six
  hypergraphs, time-capped lists) and `two_move_starts_n5_sel2.json.gz` (583,680 starts, complete lists of three
  hypergraphs, with the certifier's logs);
- sha256 sums in `results/k4_base_phantom/data/SHA256SUMS`.
