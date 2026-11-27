# RKMAX: OC₁ at rank-extremal maximum-matching starts (proof/k4-rkmax)

Workstream proof/k4-rkmax. Goal: TARGET₄ through Conjecture RKMAX (`k4/sdc.md` §31 end, ledger K4.SDC.RKMAX on
claude/kind-lamport-y8fdme): at a maximum-matching serial-dictatorship pick vector whose rank signature is
lexicographically maximal, OC₁ holds. RKMAX ⟹ OC₁^∃max ⟹ TARGET₄ (Lean: `EFX.OC1Max.target4_of_conjOC1exmax`).

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
- n = 4, complete export: all 112,880 failing starts are rank-dominated; at all 111,600 profiles every undominated
  maximum matching satisfies OC₁ (213,120 vectors). A dominating matching that changes only **two agents** exists at
  107,760 starts, three at the other 5,120.
- n = 5: see §4 (runs in progress).

**What the dominating changes are** (`k4/rkmax/rk_witness.py`, `results/k4_rkmax/rk_witness_n4.log`). At every n = 4
failing start the minimal dominating change raises **the receiver**, from rank 4 (or 3) to rank 1 (or 2): a swap with
the holder of its top, or a chain in which a dangerous agent steps down to a junk good. By Observation W a receiver of
rank 4 freezes three agents, which at n = 4 is everybody else: this is why every n = 4 failure has a single receiver.
