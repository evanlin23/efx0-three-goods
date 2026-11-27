# Referee report: Theorem VM (branch `claude/k4-vm`, `k4/vm.md` §2, §8)

Referee: `proof/k4-referee`, 2026-11-26. Read: `k4/vm.md` at `7a78df6` (all of §1–§8; at `77c8953` §1–§5 and §8 are unchanged, and only the status block and new subsections of §7 were added), and the AAMAS 2024 extended
abstract itself. Checks: `k4/referee/vm_ref.py`, runs `k4/referee/vm_ref_runs.sh`, log
`results/k4_referee/vm_ref.log`. My implementation was written from the abstract's text and §2 of `k4/vm.md`. It shares
no code with `k4/vm/`.

## Verdict: CORRECT (for the algorithm as reconstructed in §2, main reading)

Theorem VM holds as stated. Every run of algorithm VM (§2: global ranks with ties by index; only the *matched* Phase-I
agents leave N^r (G1); Phase-I winners W are nodes of the EFX graph) ends in a complete **ordinary** EFX allocation.
At every EFX-graph step the graph is acyclic and its directed paths have at most two edges. I re-derived every step
and found no gap. The bound of two edges is attained. Scope, which the campaign must keep:
- The theorem is about **ordinary EFX** (V-M's notion). It says nothing about EFX₀ or TARGET₄. §5 of `k4/vm.md` shows
  the algorithm is not EFX₀, and its own Remark says so.
- It proves V-M's announced result for **this reconstruction**. The abstract gives the algorithm in about 25 lines
  with no proof, and its literal text is wrong at n = 2 (G1). So "completes a published but unproved claim" is accurate
  only in this form: *a reading of the abstract's algorithm, with one necessary correction, provably does what the
  abstract claims.* Whether it is the authors' intended algorithm cannot be checked from the source.

## 1. The reconstruction against the source

I extracted the text of the PDF myself with `pdftotext -layout`
(https://www.ifaamas.org/Proceedings/aamas2024/pdfs/p2534.pdf, 3 pages, sha256 `d0f6a352…7cd7`) and read all of it.
The quotations in `k4/vm.md` §1 are verbatim: the definitions of EFX-envy, l-limited, the k-th value graph and the EFX
graph (nodes: i ∈ S with v_i(j) > 0; edge i → i′ iff v_i(X_i) < v_i((X_{i′} ∪ {j}) ∖ {j′}) for some
j′ ∈ X_{i′} ∪ {j} with v_i(j′) > 0), the algorithm paragraph, and Example 2.1. The abstract contains no proof of the
source claim ("we are able to prove that ... there will be a source"), and it points to no full version.

The reading choices, checked against the text:

| point | abstract | reconstruction | referee |
|---|---|---|---|
| G1 | "Remove A from N^r" | remove only the matched A-agents | A **necessary correction**. Literally, the unmatched A-agents get nothing and are in no N_k. Reproduced: n = 2, m = 2, v₀ = (13, 8), v₁ = (7, 2); both runs of the literal reading end non-EFX, and both runs with G1 end EFX (log, first lines). |
| G2 | node set N₁ ∪ N₂ʳ; "Let N_k denote agents with their kth ranked object" | W ⊆ N₁ | Literal enough: Phase-I winners hold their 1st-ranked object. Without W, runs get stuck (mutation `VM_VARIANT=noW`: 5,559 stuck runs on 3,000 random instances). |
| G3 | "kth highest ranked object for agent i" | rank among all of R_i | Forced by the abstract's sentence "all the objects valued by an i ∈ N₄ ∪ N^r have been assigned", which needs global ranks. |
| Phase III order | N₃'s 4th choice first, then N₂'s 3rd, then N₂'s 4th | the same | **The order matters**, and the reconstruction follows the text. With N₂ served first, EFX fails (mutation `n2first`: 4 of 3,000 random instances, e.g. agent 0 = (2, 0, 8, 4, 2) holding its 3rd choice {0} sees {3, 4} in an N₂ bundle). In Step 2 of the proof, the N₃ case uses that (a) comes before (b) and (c). |
| A with < 3 goods | "more than their second and third ... combined" | missing ranks count 0 | Natural; Step 5(i) needs only v(r₁) > v(r₂) + v(r₃). |

Example 2.1 reproduces: with A ↦ a, B ↦ b, C ↦ c the EFX graph for d has the edges A→C, B→A, B→C, C→A, C→B and no
source (log).

## 2. The proof, step by step

Notation as in §8: st(i), r_i(k), a_i, L_i = R_i ∖ {a_i}, S = W ∪ N₁ ∪ N₂ʳ.

- **Fact 0** (i EFX-envies B iff |B ∩ R_i| ≥ 2 and v_i(B ∩ R_i) − min_{B∩R_i} v_i > v_i(X_i)). Correct. Removing
  h ∈ B with v_i(h) > 0 leaves v_i(B ∩ R_i) − v_i(h), and a single valued good leaves 0.
- **Lemma S and S′** (saturation). Correct. Each agent has at most one edge in G_k, so G_k is a disjoint union of
  stars centred at goods, and a maximum matching covers every good with an edge. Holders never change, so "assigned
  to an agent with st ≤ j" persists.
- **Step 1** (Phase II is EFX: singletons). Correct.
- **Step 2** (Phase III keeps EFX). Correct. I checked each case:
  - W ∪ N₁: the top bounds any single good;
  - N₄ ∪ N^r: g is unassigned, so worth 0;
  - N₃ in (a): y_s ∉ {r_i(1), r_i(2)} because those sit with st ≤ 2 < 3 = st(s); y_s ≠ r_i(3), which i holds; so
    y_s and g would both have to be r_i(4);
  - N₃ in (b), (c): r_i(4) is assigned by S′;
  - N₂: y_s ≠ r_i(1) (st(s) ≥ 2), y_s ≠ r_i(2), g ∉ {r_i(1), r_i(2)}, so max ≤ v(r_i(3)) ≤ v(r_i(2)).

  Several bundles change in one matching. That is harmless: each receiver's own value only rises, and the bound uses
  v_i(X_i) before the step.
- **Step 3** (only S values unassigned goods). Correct. Unmatched A-agents have no edge at k = 1 (their top went to
  W), so they land in N₂, N₃, N₄, N^r, or N₂ʳ ⊆ S.
- **Step 4** (X_i ⊆ R_i on S). Correct.
- **Step 5** (out-edges). Correct.
  - (i): for T ⊆ L_i, v(T) − min_T ≤ v(r₂) + v(r₃) < v(a_i).
  - (ii): |T| ≤ 2 gives at most one good's value, which is ≤ v(a_i). So T = L_i, |R_i| = 4, X_i = {a_i}, and two
    goods of L_i lie in X_{i′}.
  - (iv): T ⊆ {r_i(1), r_i(4)} forces v(r₁) > v(r₂) + v(r₃), so i ∈ A. i lost r_i(1) in Phase I to an agent of W,
    which keeps it, and r_i(1) ≠ j, so i′ is that agent.

  Paths: W stops; N₁ → (N₁ with ≥ 2 goods: stops) or W or N₂ʳ → W. So at most two edges, no cycle. The node set is
  nonempty by Step 3.
- **Step 6** (adding j to a source). Correct. Valuers of j are nodes, and no in-edge at s means no valuer EFX-envies
  X_s ∪ {j}. Non-valuers see the same X_s ∩ R_i.
- **Step 7** (junk). Correct for ordinary EFX (and only for it).

Ties are handled: every inequality used is non-strict in the ranking and strict only where A's definition or EFX-envy
supplies it.

## 3. Computation (evidence; the proof does not depend on it)

Every resolution of every choice point is enumerated: the winner of each contested good in Phase I, Phase II
(k = 1..4) and Phase III (a), (b), (c), the order of the EFX-graph goods, the source, and the junk recipient. The checks
run after every step: ordinary EFX of the partial allocation, acyclicity, longest path, a source, valuers outside S;
at the end, completeness and EFX. Values include 0 and ties.

| set | instances | runs | failures of any kind | longest path |
|---|---|---|---|---|
| exhaustive n = 2, m = 3, values 0..3 | 4,096 | 6,938 | 0 | 0 |
| exhaustive n = 3, m = 3, values 0..2 | 19,683 | 41,115 | 0 | 0 |
| exhaustive n = 2, m = 4, values 0..3 | 65,536 | 224,712 | 0 | 1 |
| exhaustive n = 2, m = 5, values 0..2 | 44,521 | 364,442 | 0 | 1 |
| exhaustive n = 3, m = 4, values 0..2 | 531,441 | 1,423,089 | 0 | 1 |
| exhaustive n = 2, m = 6, values 0..2 (4-limited only) | 223,729 | 4,817,822 | 0 | 1 |
| random n ≤ 4, m ≤ 7 (junk, top-heavy) | 20,000 | 129,238 | 0 | 1 |
| random n ≤ 6, m ≤ 10 (cap 500 runs) | 20,000 | 479,275 | 0 | **2** |
| contested tops, n = 3–6, m = 4–8 (two seeds) | 40,000 | 773,973 | 0 | **2** |

A hand-built instance attains two edges. Goods 0–4; w = (0, 10, 0, 0, 1), p = (0, 10, 4, 3, 1),
q = (10, 0, 6, 5, 4). w and p are in A with top 1, and w wins it; q ∈ N₁ holds {0}; p ∈ N₂ʳ holds {2, 3}. For good 4
the edges are q → p → w (log).

## 4. For the coordinator

- Theorem VM: **CORRECT** as stated (ordinary EFX, reconstruction of §2 with G1). It can be recorded as PROVED with
  the scope above. `proofs/citations.md` item 2 may say that the abstract's 4-limited algorithm, read as in
  `k4/vm.md` §2 with correction G1, has a complete written proof (refereed). It must not say that V-M's EFX result
  implies anything for EFX₀.
- One addition worth making to §8: Step 2's N₃ case depends on Phase III serving N₃ before N₂, which is the text's
  order. A remark would stop a later "simplification" from breaking it (mutation `n2first` above).
- Not refereed here: §6–§7 (Lemmas SND, TERM, the repairs and refutations). On reading, Lemma SND's F6x clause is
  sound by construction (moves are applied only if the raw EFX₀ check passes), and Lemma TERM's potential Φ is a
  correct strict-increase argument.

## 5. Addendum: new proved items at `77c8953` §7.4 (checked in passing)

- **Lemma P0** (no pool good is wanted at a V-M matching): correct. A good worth more than the pick is ranked above
  it, hence assigned by Lemma S; a pickless agent has all of R_i assigned.
- **Lemma P1′**: correct, with "prefers" read as "values strictly more" (with ties broken by index, "exactly when"
  needs strict values). The threat of {Y_u, d} is max(v_k(Y_u), v_k(d)), and v_k(d) ≤ v_k(Y_k) by P0.
- **Proposition HDT**: correct.
  - Place D one good per unfrozen slot (safe by P1′; receivers only gain).
  - Then add the rest to o. Every intermediate bundle of o is a subset of the final safe one, threats are monotone
    under inclusion, and o itself is safe toward {Y_u, d} by P0 and u's being unfrozen.
- The VMX₂ invariants (I1)–(I5) and the climbs were not refereed.

## 6. Addendum: Lemmas SND, TERM and the VM1 invariant (I1)–(I5) (coordinator's queue; `77c8953` §7, §7.3)

§7 is unchanged since `7a78df6`. Verdict: **CORRECT**, including with the unrestricted ("free-z") exchanges of VM1.
- **SND.**
  - After Phase II every bundle is a singleton.
  - F1 and F2 add g to X_s only if nobody EFX₀-envies X_s ∪ {g}; other bundles are unchanged and v_s does not drop.
  - A rotation permutes bundles and raises the rotated agents' values.
  - Moves (upgrades, exchanges, free-z included) are applied only after a raw EFX₀ check.
  - The junk step is L3: an unenvied receiver after rotations, and junk is worthless.
- **TERM.**
  - An upgrade takes ≥ 1 pool good and returns one. An exchange, free-z or not, takes ≥ 0 and returns none. So the
    pool never grows, and there are at most m placements.
  - Rotations, upgrades and exchanges raise some value strictly (both exchanging agents must gain) and lower none.
  - ℓ_i(B) = #{T ⊆ R_i : v_i(T) < v_i(B)} is non-decreasing in v_i(B) and rises when v_i rises, because T = B ∩ R_i
    becomes counted. So Φ rises strictly at every move and rotation, and Φ ≤ Σ(2^{|R_i|} − 1) ≤ 15n.
- **(I1)–(I5).**
  - (I1) is SND, and (I2) holds because no step lowers a value.
  - (I3) and (I4) follow from EFX₀. A good g with v_i(g) > v_i(X_i) sitting in a bundle of ≥ 2 goods leaves g after
    the removal of another good. A bundle of ≥ 2 goods envied by an agent that values one of its goods at 0 is
    strongly envied.
  - (I5) is TERM.
  - One reading point: (I3) is about *allocated* goods. An upgrade can return a good that someone values above its
    bundle to the pool, so "held alone" cannot be meant for pool goods.

## 7. Addendum: P34, VM1 fails on a connected k = 4 core (`attempts/k4-vm-vm1-core.md` on `claude/k4-vm` at `b5a2d6a`; coordinator's queue, 2026-11-27)

**Read.**
- `attempts/k4-vm-vm1-core.md`;
- `k4/vm.md` §2 (the V-M reconstruction), §6 (the moves) and §7.3 (Conjecture VM1).

**Check.** `k4/referee/vm1_ref.py`, log `results/k4_referee/vm1_ref.log`.
- It is my own code:
  - V-M's Phases I–II are written from §2, with every resolution of the matchings enumerated;
  - VM1's moves are written from §6 and §7.3;
  - an exhaustive search covers F1 placements and envy-cycle rotations.
- Raw EFX₀ comes from `cert_ref.py`.
- Nothing from `k4/vm/` or `attempts/` was run or imported, and the instance is copied from the note.

**Verdict: CONFIRMED.**
- **The instance is a strict connected k = 4 core.** Every agent has 4 goods and is strictly balanced (8 < 9 for
  every agent), there are no private goods, every agent's type is strict, and the incidence graph is connected.
- **The V-M matchings** (Phases I–II, every resolution) are exactly ({5}, {6}, {1}, {3}) and ({5}, {6}, {3}, {1}), as
  stated:
  - agents 0 and 1 are strong (8 > 4 + 3);
  - agents 2 and 3 tie on good 1 at rank 3.
- **No completion with zero moves or one move.** From both matchings, the only legal moves are agent 0's and agent 1's
  upgrades to {0, 2, 4}, as the note says. That holds for upgrades with *any* improving S, not only minimal ones, and
  for unrestricted exchanges.
- From the matchings and from every state one move away, the search over placements and rotations never reaches a
  complete EFX₀ allocation. The search is a superset of VM1's schedule: any envy cycle may rotate at any time, and
  goods are placed in any order.
- **The two-move completion** ({0, 2, 4}, {6}, {5}, {1, 3}) is EFX₀. It equals one DE chain of length 1 (agent 0
  takes {0, 2, 4}, agent 2 takes the released 5) followed by placing 1 on agent 3. So VM1-chain completes P34.
- **Remark: the failure is specific to V-M's matchings.** From the other one-good matchings (110 in all), 44 complete
  with no move. VM1 fails here because it starts from V-M's rank-greedy matching, which is what the conjecture says.
