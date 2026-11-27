# RKMAX: OC₁ at rank-extremal maximum-matching starts (proof/k4-rkmax)

Workstream proof/k4-rkmax. Goal: TARGET₄ through Conjecture RKMAX (`k4/sdc.md` §31 end, ledger K4.SDC.RKMAX on
claude/kind-lamport-y8fdme): at a maximum-matching serial-dictatorship pick vector whose rank signature is
lexicographically maximal, OC₁ holds. RKMAX ⟹ OC₁^∃max ⟹ TARGET₄ (Lean: `EFX.OC1Max.target4_of_conjOC1exmax`).

## Status (2026-11-27)

| item | statement | status |
|---|---|---|
| Lemmas W, TC, COMP, PO, GAIN, 2AG (§1) | ranks are wants out-degrees; σ, RS, leximin are threshold counts; σ-maximality is local; undominated ⟹ SD outcome; gainers never beat the losers' best old rank at a σ-max start | proved (written, short), not refereed; K4.RKMAX.LEM |
| RKMAX at n ≤ 4 (§2) | OC₁ at every σ-maximal maximum-matching start | certified, second implementation; K4.RKMAX.N4 |
| **RKDOM** (§3) | OC₁ at every maximum matching that no maximum matching rank-dominates (sorted ranks); implies RKMAX, RS, leximin | certified at n ≤ 4 (witness + minimal checker); on the complete n = 5 lists every failing start is dominated (K4.RKMAX.N5) |
| Starved receivers (§4) | at every known failing start a receiver has rank 3 or 4 and a two- or three-agent change through it dominates | evidence |
| **Lemma S′** (§5) | Theorem S with any canonical chain and the kept-out good to any single-good holder | proved (written), not refereed; K4.RKMAX.SPRIME |
| HS-MAX (§5) | at a perfect σ-maximal start: picks complete, or Lemma S′, or Lemma RF-B | **refuted** at n = 4 by an adversarial climb (44 σ-maximal starts, OC₁ holds at all; §7), after 0 gaps on 2.5 million σ-optimal vectors of the exports and random cores; K4.RKMAX.HSMAX |
| **Lemma SINK₁, HS-MAX′ ⟹ RKMAX** (§7) | one canonical chain, then owner k or head z absorbs, one good to one other agent; HS-MAX′: picks complete or SINK₁ | SINK₁ proved (definitions); HS-MAX′ conjecture: covers everything above, and climbs against it find nothing; K4.RKMAX.SINK1, K4.RKMAX.HSMAX2 |
| Zero-move form | every σ-optimal start completes at the picks | refuted at n = 2 (`attempts/k4-rkmax-zero-move.md`) |
| Open | HS-MAX′; the U0 analysis of §6 shows a proof cannot be local to the conflict | — |

Notation as in `k4/sdc.md` §29–§31 and `k4/oc1_hall.md`: picks Y (a matching of agents to relevant goods), p_i =
v_i(Y_i), junk J (unmatched goods), *i wants j's pick* if v_i(Y_j) > p_i, *frozen* agents (someone wants their pick),
*receivers* U (pick holders nobody wants), dangerous D (frozen, values a junk good), truly dangerous D_T (frozen, and the
bundle J threatens it at p_i). Values are strict.

## 1. Ranks are out-degrees of the wants digraph; the signature as threshold counts

rank_i(M) = 1 + #{g ∈ R_i : v_i(g) > v_i(M_i)} (5 if i is unmatched); σ(M) = (#rank 1, …, #rank 4). Write
c_t(M) = #{i : rank_i(M) ≤ t} for t = 1, …, 4, so σ_t = c_t − c_{t−1} (c_0 = 0).

**Observation W.** At a Pareto-optimal matching (in particular at SD picks), every good that i prefers to Y_i is the
pick of another agent (junk ranks below every pick, `k4/sdc.md` (I2)). So rank_i(Y) − 1 is the out-degree of i in the
wants digraph W(Y) (i → j when i wants Y_j). The signature is the out-degree distribution of W(Y), the rank sum is
n + |W(Y)|, and the receivers are the agents of in-degree 0. An agent of rank r freezes exactly r − 1 agents.

**Lemma TC (threshold counts; proved).** For matchings M, M′ write Δc_t = c_t(M′) − c_t(M).
- (a) σ(M′) >_lex σ(M) iff the first t with Δc_t ≠ 0 has Δc_t > 0.
- (b) The sorted rank vector of M′ is pointwise at most that of M, and differs, iff Δc_t ≥ 0 for every t and Δc_t > 0
  for some t. Call this *M′ rank-dominates M*.
- (c) Rank dominance implies a strictly larger σ, a strictly smaller rank sum (RS), and a strictly better leximin
  vector (LMR).
- (d) If M and M′ differ only on a set A of agents, then Δc_t = #{a ∈ A : r′_a ≤ t < r_a} − #{a ∈ A : r_a ≤ t < r′_a}:
  each gainer contributes its *rise* [r′_a, r_a) and each loser its *drop* [r_a, r′_a).

*Proof.* (a) Δσ_t = Δc_t − Δc_{t−1}, so the first nonzero Δσ_t equals the first nonzero Δc_t. (b) For sorted vectors
a, b of equal length, a ≤ b pointwise iff #{k : a_k ≤ t} ≥ #{k : b_k ≤ t} for every t. (c) σ by (a); the rank sum is
Σ_i rank_i = Σ_{t=0}^{4} (n − c_t), so it falls by Σ_t Δc_t > 0; leximin compares the counts of agents above each
threshold from the top, n − c_t, which weakly fall and do not all stay. (d) An agent is counted in c_t exactly when its
rank is ≤ t. ∎

**Lemma COMP (σ-maximality is local; proved).** Let Y be a maximum matching. Then σ(Y) is maximal among maximum
matchings iff no single alternating component raises σ: no alternating cycle, no *chain* (a₁ takes a junk good, a_{s+1}
takes Y_{a_s}, Y_{a_s} of the last agent is released), and no *shift* (an unmatched agent a₀ takes Y_{a₁}, a_{s+1}
takes Y_{a_{s+2}}, the last agent becomes unmatched).

*Proof.* Every maximum matching Y′ is Y ⊕ C₁ ⊕ … ⊕ C_q for the vertex-disjoint components C_j of Y ⊕ Y′. These are
even cycles and paths with equally many edges of Y and Y′ (a path with more Y′ edges would augment Y), i.e. cycles,
chains (both ends goods) and shifts (both ends agents), and each Y ⊕ C_j is a maximum matching. The components change
disjoint sets of agents, so by TC(d) Δc(Y′) = Σ_j Δc(Y ⊕ C_j). The lexicographic order on ℤ⁴ is compatible with
addition, so if every Δc(Y ⊕ C_j) ≤_lex 0 then so is the sum, and by TC(a) σ(Y′) ≤_lex σ(Y). The converse is clear. ∎

**Lemma PO (proved).** A maximum matching that no maximum matching rank-dominates is Pareto optimal among all
matchings, hence an SD outcome (Lemma SDPO, `k4/sdc.md` §28; Lean `EFX.OC1Max.sdpo`). In particular σ-maximal,
RS-minimal and leximin-optimal maximum matchings are SD outcomes.

*Proof.* A Pareto improvement M″ of M keeps every matched agent matched, so it is a maximum matching, and every agent's
rank weakly improves, one strictly: Δc_t ≥ 0 for all t, and Δc_t > 0 at that agent's new rank. ∎

So RKMAX is a statement about rank-maximal maximum matchings, with no reference to orders; the restriction to SD
vectors in the statement on `k4/sdc.md` is automatic.

**Lemma 2AG (two-agent changes; proved).** Let a change move one gainer a from rank r_a to r′_a < r_a and one loser b
from r_b to r′_b > r_b (a swap a ↔ b, or a chain "b takes a junk good, a takes Y_b"). Then:
- it rank-dominates iff [r_b, r′_b) ⊆ [r′_a, r_a) and the two intervals differ, i.e. r′_a ≤ r_b and r′_b ≤ r_a, not
  both with equality;
- it raises σ iff r′_a < r_b, or r′_a = r_b and r′_b < r_a.

*Proof.* TC(d) with one rise and one drop. ∎

**Lemma GAIN (proved).** Let Y be σ-maximal among maximum matchings, and C an alternating component (cycle, chain or
shift) such that Y ⊕ C is a maximum matching. Every agent of C changes its good, so with strict values it is a
*gainer* (r′ < r) or a *loser* (r′ > r; becoming unmatched counts as rank 5). Then C has a loser, and every gainer a
has r′_a ≥ ρ := min_{b loser} r_b: no gainer's new rank beats the best old rank among the losers.

*Proof.* If C had no loser, Y ⊕ C would be a Pareto improvement, which raises σ (Lemma PO's computation). Suppose a
gainer has r′_a < ρ, and let t₀ < ρ be the least new rank of a gainer. For t < t₀ nobody crosses t (gainers end at
≥ t₀, losers start at ≥ ρ), so Δc_t = 0; at t₀ some gainer crosses upward and no loser crosses downward, so Δc_{t₀} >
0. By TC(a), σ(Y ⊕ C) > σ(Y), against maximality. ∎

Instances used below:
- *A dangerous agent and its wanters.* If k is dangerous (frozen, values a junk good g) and w wants Y_k, the chain
  "k takes g, w takes Y_k" gives rank_w(Y_k) ≥ r_k. So k's wanters all rank Y_k no better than k does, and
  r_w > rank_w(Y_k) ≥ r_k: **every wanter of a dangerous agent has a strictly worse rank than it.**
- *Canonical chains.* For a canonical chain k = x₀ ← x₁ ← … ← x_t (x_i wants Y_{x_{i−1}}, head x_t unfrozen) and any
  good g of k in J ∪ {Y_{x_t}}, every x_i ranks Y_{x_{i−1}} at rank ≥ r_k.
- *Receiver first.* If a receiver u does not hold its top and the RF rotation (RF-PATH) gives a maximum matching, u is a
  gainer to rank 1, so some ejected agent held its own top (the level-1 cancellation of `k4/sdc.md` §31).

## 2. Evidence: RKMAX at n = 4 by a second implementation

`k4/rkmax/rklib.py` is written from the definitions and shares no code with `k4/sdc/oc1_mc2_rand.py` or
`k4/oc1cert/`: it enumerates all matchings directly (not through SD orders), and has its own raw EFX₀, one-absorber
completion and official move generator (§29: additions, chains with H₀ ⊆ J ∪ B_{x_t}, rings; no empty base handed on).
On instance 1 of `k4/sdc.md` §31 it finds the 15 one-move states that §31 reports.

`k4/rkmax/rk_check_n4.py` (log `results/k4_rkmax/rk_check_n4.log`, 160 s): on all 111,600 profiles of the certifier's
complete n = 4 export (`results/k4_oc1max/two_move_starts_n4.json.gz`):
- **every σ-maximal maximum matching satisfies OC₁**: 198,400 vectors (187,560 complete at the picks, 10,840 after one
  move), every one Pareto optimal and an SD outcome of some order;
- the same for RS (213,120 optimal vectors) and LMR (197,120);
- all 112,880 exported starts fail OC₁ under rklib (an independent re-check of the export), are SD outcomes and
  maximum matchings, and have σ below the maximum.

With the certifier's OC₁^max certificate (a profile outside the export has no failing maximum-matching start) and the
type reduction, this is a second, independent implementation of the n = 4 check of RKMAX.

Classes (|U|, |D_T|) of the σ-optimal vectors: (2, 0) 74,920, (2, 1) 95,000, (2, 2) 640, all complete at the picks;
(1, 1) 10,360 + 9,720 after a move (Corollary U1's class); (1, 0) 5,680 + 160; (1, 2) 960 + 960.

## 3. A stronger form: rank dominance (RKDOM)

**Conjecture RKDOM.** In every strict connected k = 4 core, OC₁ holds at every maximum matching that no maximum matching
rank-dominates (TC(b)). Equivalently: every OC₁-failing maximum-matching start is rank-dominated.

By TC(c) and PO, RKDOM implies RKMAX and its RS and LMR forms. The equivalent form needs maximum matchings only, no
completion: an export that lists every failing start certifies RKDOM (and RKMAX) on its hypergraphs once every listed
start is shown to be dominated.

Evidence (`k4/rkmax/rk_dominance.py`, `results/k4_rkmax/rk_dominance_n4.log`; `k4/rkmax/rk_dom_export.py`):
- n = 4, complete export: all 112,880 failing starts are rank-dominated. A dominating maximum matching is stored for
  each (`results/k4_rkmax/dom_witness_n4.json.gz`, `k4/rkmax/rk_dom_witness.py`) and re-checked by a separate minimal
  checker (`k4/rkmax/rk_dom_check.py`, `results/k4_rkmax/rk_dom_check_n4.log`: matching validity, ν by augmenting
  paths, ranks from the raw values, sorted dominance; 112,880 ok). With the export's completeness this certifies
  RKDOM, hence RKMAX, at n ≤ 4 (K4.RKMAX.N4); at all 111,600 profiles every undominated
  maximum matching satisfies OC₁ (213,120 vectors). A dominating matching that changes only **two agents** exists at
  107,760 starts, three at the other 5,120.
- n = 5, the certifier's COMPLETE failure lists (`two_move_starts_n5_sel2.json.gz` on compute/k4-oc1max-cert; 5_pure
  #419, #447, #38): all 583,680 failing starts are rank-dominated, each by a matching that changes two agents
  (`results/k4_rkmax/rk_dom_export_n5_sel2.log`, 652 s). Since the lists are complete, **RKDOM, and so RKMAX, hold on
  every strict profile of these three hypergraphs** (given the type reduction; the lists themselves are the
  certifier's). The witnesses are stored (`results/k4_rkmax/dom_witness_n5_sel2.json.gz`, 1.5 MB) and the minimal
  checker accepts all 583,680 (`results/k4_rkmax/rk_dom_check_n5_sel2.log`; run it with the export from
  compute/k4-oc1max-cert).
- n = 5, the partial lists (`two_move_starts_n5_partial6.json.gz`; 5_pure #374, #379, #464, #808, #778, #164): all
  702,250 failing starts are rank-dominated, each by a two-agent change (`results/k4_rkmax/rk_dom_export_n5_partial6.log`).
  This is evidence only: the lists are partial.

**What the dominating changes are** (`k4/rkmax/rk_witness.py`, `results/k4_rkmax/rk_witness_n4.log`). At every n = 4
failing start the minimal dominating change raises **the receiver**, from rank 4 (or 3) to rank 1 (or 2): a swap with
the holder of its top, or a chain in which a dangerous agent steps down to a junk good. By Observation W a receiver of
rank 4 freezes three agents, which at n = 4 is everybody else: this is why every n = 4 failure has a single receiver.

## 4. Who fails: starved receivers

`k4/rkmax/rk_starve.py` (log `results/k4_rkmax/rk_starve_n4.log`), `rk_dom_export.py` (n = 5 logs):
- At every failing start of the n = 4 export, the receiver has rank 4 (106,880 starts) or 3 (6,000). On the complete
  n = 5 lists every failing start has one receiver of rank 4 (583,680); on the partial lists the receivers have rank 4
  (481,292) or 3 (220,958).
- By Observation W a receiver of rank r freezes r − 1 agents, so a starved receiver removes the slots a one-absorber
  completion needs (every kept-out junk good needs an unfrozen holder, `k4/oc1_hall.md` §4, Lemma 2).
- In 107,760 of the 112,880 n = 4 starts, and in every n = 5 start, a dominating change is a two-agent change in which
  the receiver u takes its top and the top's holder x falls back to Y_u (a swap) or to a junk good it values (a chain).
  By Lemma 2AG it dominates as soon as x's drop ends at rank ≤ r_u and the two intervals differ. With r_u = 4 the first
  condition always holds.

This explains the evidence but proves nothing yet: the open step is that failure forces a starved receiver with a
fallback for the holder of its top.

## 5. A static reduction: HS-MAX

A proof of RKMAX has to treat only the *hard* σ-maximal starts, those whose picks have no one-absorber completion. The
census (`k4/rkmax/rk_classes.py`, `rk_hsmax_n5.py`) asks which proved repair applies there. Three are used.
- **Prop. T0** (K4.MULTI.T0, refereed CORRECT; its converse half, Lemma 2 with H = ∅): if some receiver z has
  Θ(z) = ∅, that is no dangerous agent is threatened by J ∪ {Y_z} at its pick value, then the picks have an S\*
  completion owned by z.
- **Lemma RF-B** (`k4/oc1_hall.md` §24.8, refereed CORRECT on claude/k4-referee): hypotheses (B1)–(B5) on (k, d, S).
- **Lemma S′** below, which contains Theorems U and S (K4.MULTI.U, K4.MULTI.S, refereed CORRECT).

**Lemma S′ (Theorem S with the kept-out good at any holder; proved here, not refereed).** Let Y be SD picks at which
every agent with a relevant good holds a pick (null agents allowed), J the junk, p_i = v_i(Y_i); values strict and
additive, any number of relevant goods. Let P = (k = x₀, x₁, …, x_t = z), t ≥ 1, be distinct agents such that x_i
wants Y_{x_{i−1}} (1 ≤ i ≤ t) and z is unfrozen at Y. Let h ∈ J ∪ {Y_z} and W = (J ∪ {Y_z}) ∖ {h}, and suppose
- **(S′-a)** v_k(W) > p_k.

Let B′ be the state after the chain P with H₀ = W ∩ R_k: k holds H₀, x_i holds Y_{x_{i−1}} (1 ≤ i ≤ t), everyone else
its pick. Let r ≠ k be an agent with |B′_r| = 1, say B′_r = {g}, and let A be: A_k = W, A_r = {g, h}, A_i = B′_i for
every other i. Suppose
- **(S′-b)** no agent i ≠ r has v_i(g) > v_i(A_i);
- **(S′-c)** W threatens no agent i ≠ k at v_i(A_i).

Then the chain P with H₀ is an official move, A is a complete EFX₀ allocation that keeps every base of B′ and gives
every free good of B′ to k except h, which goes to r. So OC₁ holds at Y, with absorber k.

*Proof.*
1. *The move is official.* H₀ ⊆ W ⊆ J ∪ B_z and v_k(H₀) = v_k(W) > p_k. Each x_i (i ≥ 1) takes B_{x_{i−1}} = {Y_{x_{i−1}}},
   which it wants, with H_i = ∅. Every agent of P holds a pick, so no empty base is handed on. Y_z ∖ H₀ becomes junk.
2. *A is a complete allocation.* The free goods of B′ are (J ∪ {Y_z}) ∖ H₀ = (W ∖ H₀) ∪ {h}. k receives W ∖ H₀ on
   top of H₀, r receives h, and nobody else receives anything. g ∉ W ∪ {h}, because g is a pick other than Y_z (after
   P nobody holds Y_z). So A is a one-absorber completion of B′.
3. *Values.* v_i(A_i) ≥ p_i for every i: k has v_k(W) > p_k, the agents x_i gain, the others keep or add.
4. *EFX₀.* Every bundle except A_k and A_r is a singleton, and singletons never violate EFX₀.
   - A_r = {g, h} threatens i ≠ r iff v_i(g) > v_i(A_i) or v_i(h) > v_i(A_i), since removing one good leaves the
     other. The first is excluded by (S′-b). If h ∈ J, then v_i(h) < p_i ≤ v_i(A_i) for every agent with a relevant
     good, since h was free at i's turn (`k4/sdc.md` (I2)); a null agent values h at 0. If h = Y_z, then
     v_i(Y_z) ≤ p_i for i ≠ z, since z is unfrozen, and v_z(Y_z) = p_z < v_z(Y_{x_{t−1}}) ≤ v_z(A_z).
   - A_k = W threatens no i ≠ k, by (S′-c). ∎

*Theorem S (relaxed form, h ∈ J ∪ {Y_z}, hence also Theorem U) is the case where r is z (z unfrozen after P) or an
unfrozen wanter w of Y_{x_{t−1}}*: such an r is a holder at B′ and values only rise from B′ to A, which gives (S′-b),
and the proof of Theorem S (step 3) derives (S′-c) from (S-b), (S-c), (S-d′). Lemma S′ allows any canonical chain (not
only a longest one) and any holder r, in particular a second receiver.

**Conjecture HS-MAX** (REFUTED, §7; kept here because the censuses below are its evidence and carry over to
HS-MAX′). In every strict connected k = 4 core, at every σ-maximal maximum-matching start Y at which every
agent holds a pick:
- the picks have a one-absorber completion; or
- some (k, P, h, r) meets (S′-a)–(S′-c); or
- some (k, d, S) meets (B1)–(B5) of Lemma RF-B.

**Proposition HSR (proved).** HS-MAX implies RKMAX at every σ-maximal start at which every agent holds a pick.
*Proof.* Lemma S′, Lemma RF-B. ∎

So the open part of the route is a statement about the picks alone: inequalities between subset sums of single agents,
plus the existence of a one-absorber completion of single picks (an exact slot criterion, Lemma 1 of `k4/oc1_hall.md`
§1). No move has to be found. Non-perfect σ-maximal starts (some agent pickless) need Lemma RED (`k4/sdc.md` §31, written, not
refereed). σ-maximality does not transfer to RED's reduced instance, since ranks there are recomputed. The census
classifies such a start in the reduced instance and also checks OC₁ at it directly. In every non-perfect case found
(230, random cores) the reduced picks complete and OC₁ holds directly.

**Evidence** (`rk_hsmax_n5.py`, logs `results/k4_rkmax/rk_hsmax_*.log`; every σ-optimal vector, mechanisms tried in
the order T0, S′, RF-B, completion at the picks, with every claimed allocation re-checked by raw EFX₀):

| data | σ-optimal vectors | T0 | S′ | RF-B | picks complete otherwise | gap (hard, none applies) |
|---|---|---|---|---|---|---|
| n = 4, all 111,600 export profiles (`rk_hsmax_n4.log`) | 198,400 | 20,760 | 125,480 | 2,304 | 49,856 | **0** |
| n = 5, complete lists sel2, all 583,680 profiles (`rk_hsmax_n5_sel2.log`) | 1,004,160 | 860,160 | 115,200 | 12,960 | 15,840 | **0** |
| n = 5, partial lists partial6, all 700,500 profiles (`rk_hsmax_n5_partial6.log`) | 1,305,032 | 769,262 | 419,090 | 16,002 | 100,678 | **0** |
| 3,000 random strict MC2-class cores, n = 5 (`rk_hsmax_rand5.log`) | 4,709 | 3,841 | 532 | 42 | 100 + 194 non-perfect (RED) | **0** |
| 1,500 random strict MC2-class cores, n = 6 (`rk_hsmax_rand6.log`) | 2,349 | 1,978 | 256 | 18 | 61 + 36 non-perfect (RED) | **0** |

Counts are by the first mechanism that applies, in the order T0, S′, RF-B, completion. Before Lemma S′ was added
(Theorems U and S only), partial6 had 880 gap vectors, all on one hypergraph, all with the shape that S′ covers: the
kept-out good goes to a second receiver.

At n = 4 the hard σ-optimal starts are few and uniform (`rk_hard_profile.py`, `results/k4_rkmax/rk_hard_profile_n4.log`).
There are 10,840 of them. Each has a single receiver z of rank 3, and |Θ(z)| is 1 (8,680) or 2 (2,160). Lemma S′
covers 9,880, with k ∈ Θ(z) and r the chain's head, a chain agent or another holder. Lemma RF-B covers the other 960,
all with |D_T| = 2.

## 6. Where the proof stops

**The open statement was HS-MAX (§5); after §7 it is HS-MAX′.** Everything else on the route is proved:
- RKMAX ⟸ HS-MAX′ for perfect σ-maximal starts (Lemma SINK₁);
- RKMAX ⟹ OC₁^∃max ⟹ TARGET₄ (Lean `EFX.OC1Max.target4_of_conjOC1exmax`; the argmax step is Lemma PO plus
  finiteness).

At a hard σ-maximal start, a proof of HS-MAX′ must produce a SINK₁ case (in particular Lemma S′'s or Lemma RF-B's
inequalities) from two hypotheses:
- hardness: by Prop. T0, every receiver z has Θ(z) ≠ ∅;
- σ-maximality: Lemma COMP, in particular every inequality of Lemma GAIN.

**What the residue looks like** (`rk_residue.py`; a 1-in-10 sample of the n = 4 export profiles, all Pareto-optimal
maximum matchings, not only σ-optimal ones). 23,256 starts are hard and covered by none of T0, S′ and RF-B: 11,288 fail
OC₁, and 11,968 are repaired by other moves (rings, chains with middle junk). **None of them is σ-maximal.** Their
fewest-agent σ-raising changes are almost all two-agent swaps or chains in which a Lemma GAIN inequality fails. Two
typical ones:
- *chain[DT 2→3, DT 2→1]*: a truly dangerous agent of rank 2 steps down to its junk, and a wanter of rank 2 takes its
  pick, reaching rank 1 < 2;
- *swap[D 1→2, U 3/4→1]*: the starved receiver takes its top from a dangerous top-holder that falls back to the
  receiver's pick.

**The smallest open class, U0** (`rk_u0_class.py`). U0 is the class of perfect starts with one receiver z,
Θ(z) = {k} and D_T = ∅; |U| = 1 with |D_T| = 1 is Corollary U1. Lemma S′ reduces U0 to one local conflict:
1. Take a longest canonical chain P from k. Every chain from k ends at z, since z is the only receiver. As in the proof
   of Corollary U1, z is unfrozen after P, so r = z satisfies (S′-b).
2. W ⊆ Π threatens no dangerous agent other than k (they are not in Θ(z)) and no agent of F ∖ D. So (S′-c) reduces to
   z itself: W must not threaten z at v_z(a) + v_z(h), where a = Y_{x_{t−1}}.
3. With h = Y_z (W = J) that always holds (KEEP's computation, v_z(J ∩ R_z) < 2p_z < v_z(a) + p_z), so S′ applies
   whenever v_k(J) > p_k.
4. With a junk good h that k does not value, (S′-a) is automatic.

So S′ fails only if v_k(J) ≤ p_k (then k values Y_z) and, for every h ∈ J with v_k(Π ∖ h) > p_k, the bundle Π ∖ h
threatens z at v_z(a) + v_z(h). That is a competition for junk between k and z: k needs Y_z and some junk good j to
beat p_k, while z, holding a, is threatened by {Y_z, j, …}. For example p_z + v_z(j) > v_z(a) when Π ∖ h contains a
good z does not value. On the n = 4 sample all 11,544 such starts share
these features:
- k and z share exactly one junk good;
- k values Y_z;
- r_z = 3;
- each is σ-raised by a two-agent change between k and z ("z takes Y_k, k falls back to Y_z or to j"), or by a
  two-agent change between other dangerous agents.

A proof in U0 would have to show that the value conflict forces rank_z(Y_k) ≤ r_k (with Lemma 2AG's tie-break),
or else a repair outside S′. Ranks and the value conflict are logically independent, so σ-maximality has to be used
together with hardness, through the other agents. I did not find that argument.

**The σ-raise is not local** (`k4/rkmax/rk_u0_local.py`, `results/k4_rkmax/rk_u0_local_n4.log`; 1-in-20 sample).
- In 122 of the 5,763 U0 residue starts, no σ-raising matching differs from Y only on k, z and the agents of the
  longest canonical chains. In 436, none differs only on {k, z}.
- Example: sets [[0,1,2,6],[1,2,5,6],[3,4,5,6],[3,4,5,6]], vals [[1,4,8,6],[2,8,7,4],[3,5,7,6],[4,5,8,6]], picks
  (2, 5, 4, 6), k = 3, z = 2. Here σ is raised only through z's top: agent 1 holds it, and agent 1's top is held by
  agent 0, who can fall back to junk.
- So any proof of HS-MAX or HS-MAX′ in U0 must use the agents outside the conflict. These starts were the climb's seeds
  for the refutation of §7.

**Non-perfect starts.** HS-MAX is stated for perfect starts. A non-perfect σ-maximal start needs Lemma RED with ranks
recomputed in the reduced instance, and σ-maximality does not transfer directly. All 230 non-perfect σ-optimal
vectors met (random cores) complete at the reduced picks.

## 7. HS-MAX is false as stated; the sink form HS-MAX′

**Refuted by an adversarial climb** (`k4/rkmax/rk_climb.py`, `results/k4_rkmax/rk_climb_n4.log`; 45 s).
- *Seeds.* 200 residue starts of the n = 4 export profiles: Pareto-optimal maximum matchings that are hard and covered
  by none of T0, S′ and RF-B.
- *Moves.* Change one value of one agent, keeping the values strict and balanced and the start a residue start, to
  push the start towards σ-maximality.
- *Result.* 44 of the 200 climbs reach σ-maximality. These are 44 σ-maximal n = 4 starts, outside the export profiles,
  at which HS-MAX fails. At every one of them **OC₁ holds** (one move repairs), so RKMAX survives and is consistent with
  its n = 4 certificate.
- *Shape.* All 44 have one receiver of rank 3 and two truly dangerous agents sharing a junk pair S; 43 are in class
  (1, 3, 2), 1 in (1, 2, 2). Example: sets [[0,1,2,6],[1,2,5,6],[3,4,5,6],[3,4,5,6]], vals
  [[1,8,23,18],[24,28,15,26],[5,3,7,6],[7,3,9,8]], picks (2, 1, 6, 5).
  - Lemma RF-B's chain "k = 2 takes S = {3, 4}, the receiver d = 1 takes Y_2 = 6" is official, but (B5) fails. Agent 0
    values all three goods of Z = {6, 1, 0}, and 18 + 8 + 1 − 1 = 26 > 23.
  - The repair is Hall's RF-B″ shape (`k4/oc1_hall.md` §24.11). d absorbs Z ∖ {1}, and agent 3, unfrozen once k holds S,
    takes the good 1.

**Lemma SINK₁ (one canonical chain, then a sink-shaped completion).** Let Y be a perfect start (null agents allowed)
and P = (k = x₀, …, x_t = z) a canonical chain, i.e. x_i wants Y_{x_{i−1}} and z is unfrozen at Y. Let H₀ be an
improving set of k inside J ∪ {Y_z}, B′ the state after the chain P with H₀, and F = (J ∪ {Y_z}) ∖ H₀ the free goods.
Choose an owner o ∈ {k, z}, and optionally one good g ∈ F and an agent r ≠ o with |B′_r| = 1. Let A be: o takes F ∖ {g}
on top of B′_o, r takes g on top of B′_r, everyone else keeps B′. If A is EFX₀, then OC₁ holds at Y: the chain is an
official move, and A is a one-absorber completion of B′ with absorber o.

Lemma S′ is the case o = k (A_k = W for every H₀ ⊆ W), and Lemma RF-B is the case o = z = d, H₀ = S, no g. SINK₁ is the
canonical-chain case of girth's SINK form (`k4/girth.md` §7). Its proof is the definition of the moves and of the
one-absorber completion. The content is the census: for a given start the condition is a finite, explicit search
over chains, H₀, o, g and r, with no further moves. The three conditions behind "A is EFX₀" are local:
- r's state good is unwanted at A;
- A_o threatens nobody at A;
- when o = z, H₀ threatens nobody at A.

Every case is re-checked with raw EFX₀ (`sink1_cases` in `k4/rkmax/rk_classes.py`).

SINK₁ covers all 44 climb counterexamples to HS-MAX, each with owner = the head, one good to another agent.

**Conjecture HS-MAX′.** In every strict connected k = 4 core, at every perfect σ-maximal maximum-matching start, the
picks have a one-absorber completion, or Lemma SINK₁ applies. HS-MAX′ ⟹ RKMAX at perfect starts, and the earlier
censuses (0 gaps, §5) remain valid for it, since SINK₁ contains S′ and RF-B.
