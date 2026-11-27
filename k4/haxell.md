# Haxell-type alternating trees for k = 4 (workstream proof/k4-haxell)

Branch `claude/k4-haxell`. Angle (k4/attack_log.md): SD-C and OC₁ say that *some* serial-dictatorship order works, but
no simple rule or local move selects it, and no value-based potential can work (K4.SDC.P1). In restricted Santa Claus,
Haxell's hypergraph Hall theorem is made algorithmic by alternating trees whose termination is a lexicographic
signature of the tree's layers, not agents' values. This note records (1) exactly what those papers say, at the level
read; (2) a translation to EFX₀ states; (3) what the resulting searches do on the project's data. Evidence below is
evidence only (PROMPT.md §5 rule 3).

## Status

(Updated at the end of each burst.)

**Burst 3 (2026-11-27, coordinator's messages 3 and 4).** Evidence, two refutations, and one computer-verified
theorem; §6 states everything precisely. Some runs are still going; their logs are named in §6.
- **The set-move lemma** (§6, "W^sub stated precisely", defined on `EFX.Inst` with a Lean sketch). From a partial EFX₀
  allocation with a nonempty pool, at most r moves reach one with a smaller pool, or with the same pool and a better
  measure. A move is a set transfer, a swap or a rotation; any form of it implies TARGET₄.
- **Two moves fail at n = 4, k = 4, for every measure tried:**
  - with welfare (W^sub; `attempts/k4-haxell-wsub-welfare.md`);
  - with leximin (L^sub; `attempts/k4-haxell-lsub-leximin.md`);
  - with Pareto improvements (P^sub, which implies both).
  The witnesses are k = 4 cores with strict balanced values, found by adversarial climbs. Each was re-checked by the
  C checker and by Python with no shared code (`attempts/k4_haxell_wsub.py`).
- **Two moves do hold for n ≤ 3** where checked:
  - n = 2: **Theorem N2** (computer-verified on every strict type profile with k ≤ 4; C and an independent Python
    enumeration agree; §6). Either two moves shrink the pool, or a Pareto composite exists. So W^sub, L^sub and
    P^sub hold there, also with up to two goods valued by nobody.
  - n = 3: P^sub holds on every strict type profile with k ≤ 3 (14,100 classes). W^sub with welfare holds on the
    n = 3 value grids run so far.
  - Pool-shrinking alone (Claim A2) fails already at n = 2 with strict values
    (`attempts/k4-haxell-n2-pure-augmentation.md`), so the measure is needed.
- **Three moves rescue all 40 known two-move failures**, for welfare, leximin and Pareto, with set moves or
  single-good moves. The candidate is **P^sub₃** (three moves, Pareto). It is ordinal, so checks over types are
  complete for it. With single-good moves only, three moves fail at k = 5 (W5).
- **The radius grew from two to three at n = 4, and did not grow again at n = 5** (the decisive test, §6, n = 5).
  Seeded from the n = 4 failures, two moves failed once at n = 5 (Pareto only); three moves never failed under any
  measure. This is evidence from climbs. If the radius grows at larger n, no fixed-radius form gives TARGET₄.
- **Where k enters**: with k ≤ 3, two-move Pareto climbs found no failure at n = 4, 5, and P^sub holds exhaustively at
  n ≤ 3. So the conjecture is two moves for k ≤ 3 and three moves for k = 4.
- **The move class is nearly minimal**: six of its seven kinds are each necessary (§6 ablation).
- The ledger rows are staged in `k4/haxell/ledger_rows.md`; the assignment says the coordinator edits LEDGER.md.
- *Proof*: open beyond Theorem N2 (computer-verified, n = 2).

**Burst 2 (2026-11-26, coordinator's requests).** Evidence only; one new conjecture (W), stated precisely in §6.
- *CONN₂ on every counterexample to OC/OC₁/OC₁^max* (§5). PW5, RD5, the two kgen n = 4 instances (k = 5), their k = 4
  versions, the 39 TTC k = 4 cores and B<, B> (n = 6, m = 10): a full census of 3.7 million partial EFX₀ states, **no
  trap even for single moves**. What fails there is the one-chain shape, not local connectivity.
- *CONN₂ at k ≥ 5*: no G₂ trap in any full census at k = 5–10 (random instances, n ≤ 5). The PW grid up to k = 9
  (n ≤ 9, m ≤ 17) is too large for the census; probes found no trap (§5).
- *Conjecture W, the one-step lemma* (§6). From every partial EFX₀ allocation with a nonempty pool, at most **two
  moves** give a partial EFX₀ allocation with a smaller pool, or the same pool and larger welfare. A move is a
  single-good reassignment, a swap, or a **rotation of bundles along a cycle of agents**. (|pool|, −welfare) is
  well-founded, so W would imply CONN and hence TARGET₄.
  - **W is REFUTED at n = 2, k = 4** (`attempts/k4-haxell-conjecture-w.md`). In 576 of the 1.5 million n = 2 grid
    instances, the receiver of a pooled good must dump three goods at once. With single-good moves the needed radius
    grows with k: W₃ holds there but fails at k = 5. This is a place where k enters.
  - **Surviving forms**: **W₃** (three moves) at k ≤ 4, and **W^sub** (two moves, with a set transfer counting as one
    move) for every k. The evidence below was gathered for W and applies to both, since both contain W's moves.
  - Exhaustive checks found no stuck state. Coverage: every partial EFX₀ allocation of the screen set, suite, k = 4
    cores, PW5/RD5/kgen, the 39 TTC cores, **B< and B> (n = 6)**, the 1,520 logged hard profiles, and random
    instances at k = 3, 4, 5, 7 and with every good relevant, with and without ties. Also every n = 2 instance on the
    value grids. That is over 45 million states, 397,633 of them re-checked by an independent Python
    implementation. Leximin works equally well.
  - **The sharpest stress test passes**: at the CH-F welfare maxima that strand two goods (kgen-charity; k = 4,
    n = 9 and k = 3, n = 12) W shrinks the pool in two moves (welfare 198 → 197), and W-walks complete. They also
    complete from the stranded states of S(σ, k) and S′(σ, k), σ ≤ 5, n ≤ 40 (§7).
  - Sampled states on random instances with n = 6–8, k = 4, 5, ties included (18,687 states): every state has a W
    step and every walk completes (§7).
  - Why the move class is what it is: without rotations, no fixed radius works (the family CYC_n,
    `attempts/k4-haxell-fixed-radius-measures.md`). With one move instead of two, W fails (the n = 2 trap). Pure
    augmentation fails with rotations too.
- *Where k enters*: with single-good moves, the counterexamples to W and W₃ show the step radius must grow with k.
  W^sub removes that dependence and shows no failure at k = 5, 7 or with every good relevant, so it is a candidate
  for EFX₀ in general. That makes it at least as hard as the EFX conjecture.
- *Proof*: the opening is written (§6). A stuck state has an acyclic envy graph, and a placement at a source fails
  only through a cheaper good. The n = 2 case already needs moves that take a good from the placement's receiver; it
  is the first open case.

**Burst 1 (2026-11-26).** Evidence only; nothing here changes a ledger row.
- *Literature* (§1): Annamalai (Haxell's condition made algorithmic), AKS and Davies–Rothvoss–Zhang read in full;
  Haxell 1995 and Asadpour–Feige–Saberi not accessed.
- *Translation* (§2): a partial EFX₀ allocation is the matching, an unallocated good the unmatched unit (Model G; or
  an unhappy agent, Model A), a local move an edge, the agents it would make unhappy its blocking set, and Annamalai's
  layer signature (−|X₁|, |Y₁|, …, ∞) the termination measure. It never looks at values, so P1 does not apply.
- *Two obstructions to the literal translation*, both precise:
  1. **Traps** (§3.2, §3.4, `attempts/k4-haxell-single-swap-collapse.md`): AKS swaps one edge at a time and keeps
     every unit matched. The graph G₁ of partial EFX₀ allocations under single local moves has components without a
     complete allocation, the smallest at **n = 2, m = 5** (k = 4). There a blocker's repair is safe only *together
     with* its parent edge. From serial-dictatorship starts the literal tree also walks into dead ends of its own move
     catalogue (junk transfers, chains, re-bases), smallest D3 (n = 3, m = 6): stuck from 38 of 4,069 screen starts,
     30 with composite collapses.
  2. **Non-local blocking** (§3.6): in Santa Claus a collapse cannot hurt a lower edge, because blocking is resource
     overlap. In EFX₀ it can, through envy toward whole bundles, so the signature can rise. This happened 11,553
     times in 12,379 steps with generic moves, once in 2,721 with junk transfers and chains.
- *What survives: CONN₂* (§4). Every partial EFX₀ allocation reaches a complete one through partial EFX₀ allocations,
  each step a composite of at most two local moves, the pool never growing. It implies TARGET₄ (start from the empty
  allocation) and mentions no values. **No counterexample** in two independent implementations (Python and C, which
  agree on all 203 instances where both run): about 120 million partial EFX₀ states in the C census alone (screen,
  suite, special and 1,521 logged hard instances with n ≤ 5; random core profiles; random instances at k = 3, 4 and
  general k up to n = 5), plus the exhaustive n = 2 value grids (2 million instances).
- *CONN₁ (single moves) fails at every k ≥ 3*: at k = 4 from n = 2, at k = 3 from n = 4 (g834, n = 4, m = 7; REFUTED,
  §4). On the data, k = 3 traps are much rarer: none with n ≤ 3 (472,860 n = 2 grid instances, 18,600 random n = 3
  ones), against traps at n = 2 for k = 4. At k = 4 every trap found has an agent with four relevant goods holding at
  least two goods.
- *Lemma CI* (§4, written proof): for agent- and good-disjoint, holding-monotone edges a collapse never gives a lower
  edge a new victim, so the signature falls as in Santa Claus. But such trees are value-monotone, and P1 forbids that.
  The invariant that makes Haxell's termination free is exactly the monotonicity P1 rules out.
- *One-shot augmentation is not local* (§3.5, `attempts/k4-haxell-bounded-augmentation.md`): some states need three
  local moves at once before the pool can shrink (already at n = 2, k = 3), and some need four (n = 3, k = 4). So the
  augmentation must be a *sequence* of steps kept inside 𝒫, which is the job of an alternating tree, and no bounded
  one-step augmentation lemma can replace it.
- *From serial-dictatorship starts* (§3.1): a sequence of victim-free moves (junk transfers, chains) reaches a
  complete EFX₀ allocation from **every** start tested: 4,069 screen, 4,327 suite, 174 special, 21,374 logged hard
  profiles, 19,200 random core profiles (n = 4, 5), at most 5 moves.
- *Open, and where k ≤ 4 must enter*: a never-stuck lemma for a tree with radius-2 edges (the analogue of Haxell's
  cover count), plus the collapse invariant for non-monotone edges (obstruction 2; Lemma CI covers only monotone
  ones). Neither has a candidate inequality yet (§4).
- *Next*: CONN₂ at n = 2 (smallest case; true on the whole grid) as a written proof; the structure of the k = 4 traps;
  a signature that also counts collapse-created victims, tested on the data; CONN₂ on the H_t gadgets (too large for
  the census: needs a reachability search from the serial-dictatorship start instead).

## 1. Literature (what was read, at which level)

Quotes are short; formulas are re-typed. "Read in full" means the arXiv HTML rendering of the stated version was read
end to end in this session (by a fetch agent whose report is the source here); nothing below is from memory.

**Haxell 1995** (P. E. Haxell, "A condition for matchability in hypergraphs", Graphs and Combinatorics 11 (1995)
245–248). *Not accessed* (publisher login). The statement below is as Annamalai and Wikipedia state it.
- *Theorem (Haxell's condition)*, as stated by Annamalai (arXiv 1509.07007v2, Theorem 1.1): for an r-uniform bipartite
  hypergraph H = (A, B, E) (every edge has exactly one vertex in A and r − 1 in B), if τ(E_S) > (2r − 3)(|S| − 1) for
  every S ⊆ A, then H has an A-perfect matching. Here E_S = {e ∈ E : |e ∩ S| = 1} and τ(F) is the least number of
  B-vertices meeting every edge of F. The strict inequality is needed. For r = 2 it is Hall's condition.
- Wikipedia ("Hall-type theorems for hypergraphs", §4, read verbatim for that section) states it for edges of size at
  most r, as τ(N_H(Y₀)) ≥ (2r − 3)(|Y₀| − 1) + 1, and says "Haxell's proof is not constructive".
- Davies–Rothvoss–Zhang (Theorem 1, background) state the dichotomy form: either a left-perfect matching, or C ⊆ X and
  U ⊆ W with |U| ≤ (2r − 3)(|C| − 1) such that every hyperedge meeting C also meets U.

**Annamalai, "Finding perfect matchings in bipartite hypergraphs"** (arXiv 1509.07007v2, read in full; the venue was
not verified).
- *Theorem 1.3*: for fixed ε > 0 and r ≥ 2, a polynomial-time algorithm finds a perfect matching when
  τ(E_S) > (2r − 3 + ε)(|S| − 1) for all S. Theorem 5.4: it returns either a perfect matching or a violating S.
- *Blocking* (Def. 2.2): the blocking set of an edge e is {f ∈ M : f ∩ e ∩ B ≠ ∅}; e is *immediately addable* if it
  has no blocking edge.
- *Layer* (Def. 2.3): a pair (X, Y), X ⊆ E ∖ M pairwise B-disjoint, Y ⊆ M exactly the blocking edges of X, and each
  edge of Y meets exactly one edge of X.
- *Alternating tree* (Def. 2.4): T = (L₀, …, L_ℓ), L₀ = (∅, {a₀}) for an unmatched a₀; the A-vertices of X_i lie in
  A(Y_{i−1}); the sets B(X_i ∪ Y_i) are pairwise disjoint across layers.
- *Build* (§3.1): a tree vertex of A(Y_ℓ) gets an addable edge if it has fewer than U edges in X and some edge of it is
  B-disjoint from B(X_{≤ℓ} ∪ Y_{≤ℓ} ∪ X ∪ Y); such edges are added to X with their blocking edges in Y. *Collapse*
  (§3.2) runs while X_ℓ has more than μ|X_ℓ| immediately addable edges: swap them in, discard L_ℓ, rebuild L_{ℓ−1}.
- *Signature* (§5, eq. (4)): each layer contributes the pair (−⌊log_b(c_i |X_i|)⌋, ⌊log_b(c′_i |Y_i|)⌋) with explicit
  scale factors c_i, c′_i and b = 1/(1 − μ³); the vector is the concatenation, with ∞ appended. *Lemma 5.1*: its
  lexicographic value decreases at every iteration: a new layer replaces ∞ by finite entries; a collapse at the
  earliest layer t either matches a₀ or shrinks Y_{t−1} by a factor (so its second coordinate drops) or grows X_{t−1}
  by a factor 1 + μ (so its first coordinate drops). Lemma 5.3: polynomially many signature vectors.
- *Stuck case* (Lemma 4.4): if the build adds nothing, with S the tree's A-vertices (|S| = |Y_{≤ℓ}|), the tree's
  B-vertices cover E_S; each non-root A-vertex accounts for r − 1 B-vertices of its matching edge plus at most r − 2
  of the tree edge meeting it, so τ(E_S) ≤ (2r − 3)(|S| − 1), against the hypothesis. (At ε = 0 the same count is the
  covering bound of Haxell's theorem; this reading is ours, not stated in the paper.)

**Annamalai–Kalaitzis–Svensson, "Combinatorial algorithm for restricted max-min fair allocation"** (arXiv 1409.0607v2,
read in full; v1 not read).
- Setting: players, resources with v_ij ∈ {0, v_j}; configurations C(i, τ) = {C : v_i(C) ≥ τ}; the configuration LP
  CLP(τ). Fat resources v_j ≥ τ/β, thin otherwise; an *edge* (p, R) has p valuing every resource of R; a δ-edge has R
  inclusion-minimal with v_p(R) ≥ τ/δ. A *matching* is a set of β-edges, player- and resource-disjoint.
- Blocking (§3.5): (p, R) ∈ M blocks (p′, R′) if R ∩ R′ ≠ ∅. A layer is (A_i, B_i) (with an integer d_i in §4): A_i
  thin α-edges, pairwise disjoint and disjoint from earlier layers; B_i the matching edges blocking A_i; P_i the players
  of B_i.
- The paper does not use the words "alternating tree" for its structure (layers and alternating paths in the
  player–fat-resource graph); fat resources are rerouted along vertex-disjoint paths (DPM_M, a max-flow count).
- *Collapse*: while some t has |I_t| ≥ μ|P_t| (I_t: the immediately addable edges of layer t, those keeping τ/β of
  free value), collapse the smallest such t, discard layers above t.
- *Signature* (§3.6): s_i = ⌊log_{1/(1−μ)} |P_i|⌋, s = (s₀, …, s_ℓ, ∞); in §4.6, s_i = ⌊log_{1/(1−μ)}(|P_i|/δ^{i+1})⌋.
  *Lemma 3.8 / 4.10*: the lexicographic value decreases at every step (a new layer replaces ∞; a collapse of layer t
  gives |P′_t| < (1 − μ)|P_t|). Layers: O(log |𝒫|). Lemma 4.11: |𝒫|^{O(…)} signature vectors (Hardy–Ramanujan).
- The never-stuck step is an *expansion lemma* from LP feasibility (Lemma 3.6: |A_{i+1}| ≥ |P_{≤i}|/5; Lemma 4.6 via
  Menger and LP duality): if the tree stops growing, a dual solution with positive objective exists, so CLP(τ) is
  infeasible.

**Davies–Rothvoss–Zhang, "A tale of Santa Claus, hypergraphs and matroids"** (arXiv 1807.07189v4, read in full).
- Theorem 2 (matroid max-min allocation, (1/5 − ε)T − max p_w / 5); Theorem 3: Santa Claus (6 + ε)-approximation (the
  earlier claimed 4 + ε was withdrawn after an error, §4).
- Add edges A ⊆ E_{αT}, blocking edges B ⊆ E_{βT}; discovered nodes C = {i₀} ∪ B_X. The expansion lemma (Lemma 8)
  replaces Haxell's cover count by a matroid exchange argument.
- *Signature* (§2.4): s = (s₀, …, s_ℓ, ∞) with s_j = ⌊log_b |B_{≤j}|⌋; Lemma 13: it decreases lexicographically after
  each loop (a new layer adds a finite coordinate before ∞; a collapse deletes the coordinates above ℓ̃ and lowers
  s_ℓ̃ by Lemma 12). The fetch agent flagged an apparent typo in the proof of Lemma 12 (a chain of inequalities that
  is inconsistent as printed); not checked further.

**Asadpour–Feige–Saberi, "Santa Claus meets hypergraph matchings"** (APPROX 2008; TALG 2012). *Not accessed* (every
candidate URL failed). Secondhand from Davies et al. §1 only: AFS use Haxell's theorem to prove the hypergraph matching
statement of Bansal–Sviridenko; the conference version gives factor 5, the journal version 4. [unverified]

**What transfers, and what does not.**
- The pattern: keep every matched player matched; grow layers of (addable edges, blocking edges); swap an edge in
  only when it is unblocked; discard the layers above a collapse. Termination is by the layer-size signature, which
  never looks at values. A player's configuration may get worse when it is re-matched: the only requirement is that
  it stays a configuration.
- The never-stuck step is where the problem enters: a cover count (Haxell), or LP duality (AKS), or matroid exchange
  (DRZ). For EFX₀ we have no such inequality to start from; the experiments of §3 ask whether the tree ever gets
  stuck at all.
- Blocking in all three papers is *resource overlap*. In EFX₀ two bundles conflict also through envy, which is not a
  resource relation. §2 handles this by defining the blocking set of a move as the matched agents it would unmatch.

## 2. The translation

**States.** Two models (`k4/haxell/ht_lib.py`). Both label each good as *base* or *junk*, start from the
serial-dictatorship picks of an order (picks are bases, the other goods junk), and test EFX₀ by the raw definition.
- *Model A* (units = agents): the allocation is complete, all junk starting with an absorber (the last agent of the
  order); an agent is *matched* when it is happy (envies no bundle strongly); the root of a tree is an unhappy agent.
- *Model G* (units = goods): the junk starts unallocated, in a *pool*; every state is a partial EFX₀ allocation (all
  agents happy with respect to the allocated bundles); the root of a tree is a pool good, to be allocated. Nothing
  returns to the pool. This is AKS's shape: a matched unit stays matched, and each augmentation matches one more.

**Edges** (moves): T, a junk good moves to any agent (a pool good is placed); C, an improving chain of `k4/sdc.md` §29
(x₀ takes junk H₀, each x_i takes x_{i−1}'s base plus junk, the released goods go to any agent); D, a re-base (an
agent swaps its base for junk of its own, possibly losing value). Values can fall under T and D; only C raises them.

**Blocking.** The *victims* of a move are the agents happy before and unhappy after. An edge for a victim b of a tree
edge f is a move after which applying f no longer makes b unhappy. A move is addable if it touches no good touched
by a tree edge and its victims are new to the tree (Annamalai's B-disjointness). An edge without victims is
*immediately addable*. Dictionary: matched player ↦ happy agent (A) or allocated good (G); configuration ↦ move;
blocking edge ↦ victim; resource ↦ good.

**Signature.** Annamalai's (−|X₁|, |Y₁|, …, −|X_ℓ|, |Y_ℓ|, ∞) without the logarithmic scaling. A collapse at layer t
discards layers t, t + 1, … (as in his Lemma 5.1), so the first coordinate that changes is |Y_{t−1}|, which loses
the collapsed edge's player. A build replaces ∞ by finite entries. So the signature falls at every iteration
*provided a collapse creates no new victim for a lower edge*. In Santa Claus disjointness guarantees this. Here it
is checked at run time, and it happened once in ~2,700 iterations (`tree_screen_G.log`). The signature never looks
at values.

## 3. Experiments

All on every order of every instance (n ≤ 5 unless stated), logs in `results/k4_haxell/`. Evidence only.

### 3.1 Victim-free search (the upper bound for any tree)

A tree only ever applies victim-free moves, so the complete breadth-first search over sequences of victim-free
moves bounds what any tree can do (`ht_bfs.py`).
| model, moves | screen starts (n ≤ 5) | reach EFX₀ | stuck | log |
|---|---|---|---|---|
| A, T + C, strict | 4,069 | 4,066 (≤ 3 moves) | 3 (one instance, one absorber) | `bfs_screen_TC.log` |
| A, T + C, unhappy count never rises | 4,069 | 4,069 | 0 | `bfs_screen_A_count.log` |
| G, T + C, strict | 4,069 | 4,069 (≤ 5 moves) | 0 | `bfs_screen_G.log` |

Model G beyond the screen set (every order, `CAP=200000` states, never reached):
| data | starts | stuck | most moves | log |
|---|---|---|---|---|
| suite, n ≤ 5 | 4,327 | 0 | 5 | `bfs_suite_G.log` |
| special (T3, Q2, r4253, r3943) | 174 | 0 | 2 | `bfs_special_G.log` |
| the hard profiles logged in `results/k4_sdc/*.log`, n ≤ 4 | 21,374 | 0 | 4 | `bfs_logs_G.log` |
| 500 random k = 4 core profiles, n = 4 | 12,000 | 0 | 4 | `bfs_cores_n4_G.log` |
| 60 random k = 4 core profiles, n = 5 | 7,200 | 0 | 4 | `bfs_cores_n5_G.log` |

In Model A's stuck start (gap-ivmax-n5-m9, picks (4, 8, 5, 6, 7), absorber 2) only two states are reachable: every
move that protects agent 1 hurts agent 2 or 4. Any other absorber works.

### 3.2 The literal tree, and why it fails

`ht_tree.py` (Annamalai's layers, AKS's collapse-and-discard; one edge per player per layer, fewest victims first).
| model | stuck starts (of 4,069) | stuck at layer 0 / 1 / 2 | signature non-decreases | log |
|---|---|---|---|---|
| A | 101 | 7 / 23 / 1 trees | 0 of 1,187 | `tree_screen_TC.log` |
| G | 38 | 0 / 8 / 8 trees | 0 of 2,721 (1 lower edge gained a victim) | `tree_screen_G.log` |

Two causes, both traced:
- *A root that needs two moves* (Model A, A131, order (0, 3, 1, 2)): agent 1 becomes happy only after a parking
  transfer, a chain that trades its pick for a pair, and a dump of a worthless good on it. No single edge serves it.
- *A dead end entered by earlier augmentations* (Model G, C127, order (0, 1, 3, 2)): two victim-free placements reach
  ({2}, {4}, {0, 1, 5}, {6}) with good 3 pooled, where no move of the catalogue keeps EFX₀. Two transfers made
  together complete it (`attempts/k4-haxell-single-swap-collapse.md`).

Haxell's argument needs every reachable partial matching to be augmentable. The second cause shows that this fails
for single-move collapses, and §3.4 shows it fails already at n = 2.

### 3.3 Composite collapses

`ht_ctree.py`: the edges of a tree are pairwise good-disjoint, so they commute, and the whole tree is swapped in as
one composite move once the composite has no victim. Stuck from 30 of the 4,069 screen starts (`ctree_screen_G.log`);
every success needed at most two layers. The remaining failures are dead ends reached by the greedy choice of
earlier augmentations (one edge per player); the complete search of §3.1 avoids them.

### 3.4 Traps of the local-move graph G*

`ht_gstar.py` enumerates every partial EFX₀ allocation ((n + 1)^m assignments) and joins two of them when one generic
local move leads from the first to the second without enlarging the pool: move one good, swap two goods (the pool
counts as a holder), or trade two bundles. A *trap* reaches no complete EFX₀ allocation. A *radius-2 trap* is still
a trap when composites of two moves are allowed (the intermediate state need not be EFX₀).
| data | instances | with a trap | radius-2 traps | log |
|---|---|---|---|---|
| screen set, n ≤ 4, m ≤ 8 | 134 | 5 | 0 | `gstar_screen.log` |
| suite, n ≤ 4, m ≤ 8 | 119 | 5 | 0 | `gstar_suite.log` |
| special (T3, r4253, Q2) | 3 | 0 | 0 | `gstar_special.log` |
| random k = 4 core profiles, n ≤ 3 | 1,469 | 6 | 0 | `gstar_cores_n3.log` |
| random, n = 2, m = 5, k = 3 / 4 / 5 (= every good) | 3,000 each | 0 / 9 / 5 | 0 | `gstar_gen_n2m5k*.log` |
| random, n = 2, m = 6, k = 3 / 4 / 6 | 2,000 each | 0 / 1 / 4 | 0 | `gstar_gen_n2m6k*.log` |
| random, n = 3, m = 6, k = 3 / 4 / 6 | 800 each | 0 / 1 / 0 | 0 | `gstar_gen_n3m6k*.log` |
| random, n = 3, m = 7, k = 3 / 4 / 7 | 300 each | 0 / 1 / 0 | 0 | `gstar_gen_n3m7k*.log` |

**Second implementation** (`gstar.c`, driven by `gstar_run.py`; written separately from `ht_gstar.py`, sharing only
the definitions; reverse breadth-first search from the complete allocations). It agrees with the Python census on
every instance where both run: 109 screen and 94 suite instances, every count (states, complete, traps, radius-2
traps) equal (`gstarc_xcheck_*.log`). At larger sizes (up to (n + 1)^m ≤ 3·10⁶ assignments):
| data | instances | partial EFX₀ states | with a trap | radius-2 traps | log |
|---|---|---|---|---|---|
| screen, n ≤ 5, m ≤ 10 | 151 | 488,506 | 7 | 0 | `gstarc_screen.log` |
| suite, n ≤ 5, m ≤ 10 | 136 | 455,580 | 7 | 0 | `gstarc_suite.log` |
| logged hard profiles, n ≤ 5 | 1,521 | 4,711,834 | 6 (one with n = 5) | 0 | `gstarc_logs.log` |
| special | 4 | 18,298 | 0 | 0 | `gstarc_special.log` |
| random k = 4 core profiles, n = 4 | 279 | 1,385,536 | 0 | 0 | `gstarc_cores_n4.log` |
| random n = 4, m = 8, k = 3 / 4 / 8 | 300 / 300 / 200 | 4,602,714 | 0 / 0 / 0 | 0 | `gstarc_gen_n4m8k*.log` |
| random n = 5, m = 8, k = 3 / 4 | 150 / 150 | 6,551,264 | 0 / 1 | 0 | `gstarc_gen_n5m8k*.log` |
| random n = 3, m = 9, k = 3 / 4 | 600 / 600 | 12,671,868 | 0 / 1 | 0 | `gstarc_gen_n3m9k*.log` |
| random n = 2, m = 7, k = 4 / 7 | 20,000 each | 21,097,405 | 2 / 6 | 0 | `gstarc_gen_n2m7k*.log` |
| random n = 2, m = 8, k = 4 / 8 | 10,000 each | 31,066,107 | 0 / 1 | 0 | `gstarc_gen_n2m8k*.log` |
| random n = 3, m = 5–8, k = 3 | 18,000 | 17,375,331 | 0 | 0 | `gstarc_gen_n3m{5,6,7,8}k3.log` |
| random n = 3, m = 5–8, k = 4 | 18,000 | 14,870,106 | 43 | 0 | `gstarc_gen_n3m{5,6,7,8}k4.log` |
| random n = 4, m = 7, k = 3 / 4 | 1,000 each | 4,982,469 | **1** / 2 | 0 | `gstarc_gen_n4m7k*.log` |

The k = 3 trap (g834, n = 4, m = 7; agent 0 values goods 0, 5, 6 at 22, 9, 24; agent 1 values 2, 5, 6 at 9, 40, 29;
agent 2 values 0, 4, 5 at 6, 40, 28; agent 3 values 1, 3, 4 at 11, 20, 21) is the state ({0, 3}, {1, 2}, {5}, {4}) with
good 6 pooled. Both implementations find it, and `attempts/k4_haxell_trap.py` replays it from the raw definition.

**Exhaustive grids at n = 2** (`ht_n2k3.py` through `gstar.c`): every pair of relevant sets with every good relevant
to someone (agent 0's goods normalized to 0, …, k₀ − 1), and every value vector from a fixed grid.
| k | m | value grid | instances | with a trap | radius-2 traps | log |
|---|---|---|---|---|---|---|
| ≤ 3 | ≤ 6 | {1, 2, 3, 5, 8, 13} | 472,860 | **0** | 0 | `n2_grid_k3.log` |
| ≤ 4 | ≤ 8 | {1, 2, 4, 7} (ties allowed) | 1,540,944 | 3,366 | **0** | `n2_grid_k4.log` |

**Random samples at n = 2** (`ht_climb.py sample`, Python census; values 1–10 or 1–40): 20,000 instances for each
(m, k) with m = 4, 5, 6 and k ∈ {3, 4, m}: traps only at k ≥ 4 (up to 92 of 20,000), never at k = 3, no radius-2 trap
(`climb_sample_*.log`).

**Trap structure** (`ht_trapstat.py`): every trap found has exactly one pooled good, except three general-k instances
at n = 2, m = 6 with two. At k = 4, every trap has an agent with four relevant goods holding at least two goods (35
of 35 traps on 3,000 random n = 2 instances, 15 of 15 on the screen set). The pooled good need not be wanted: in 9 of
those 50 traps no agent values it above its whole holding. No
serial-dictatorship start is a trap. **The smallest trap** (c4x-n2m5-base-needs): both agents value the shared goods
2, 3, 4 at 3, 4, 8, and each its private good (0, resp. 1) at 2. The state ({0, 2}, {1, 3}), with good 4 pooled, is
partial EFX₀, but whoever receives 4 is envied, and no single other move helps. Moving 4 to agent 0 and 2 to agent 1
together gives ({0, 4}, {1, 2, 3}). P1's stuck state of GM4-E (`k4/sdc.md` §1) is not a trap: 2,448 partial EFX₀
allocations, 15 complete, no trap.

### 3.5 Augmentation radius: one-shot augmentation is not local

For a partial EFX₀ allocation s with a nonempty pool, the *augmentation radius* is the fewest local moves (move,
swap, trade; intermediate states arbitrary, the pool never growing) after which the state is partial EFX₀ with a
smaller pool. A tree that augments in one composite step of r moves needs radius ≤ r everywhere ("AUG_r"), which
would give EFX₀ by induction on the pool. `ht_aug.py` first computes the Hamming radius (goods whose holder changes;
an upper bound on the move radius, since each changed good is one move), and `ht_mrad.py` the move radius of every
state whose Hamming radius exceeds 2.
- *Hamming radius* (`aug_*.log`): up to 4 at n = 2, k = 3, and above 4 at n = 2, k = 4 (15 of ~200,000 states), at
  n = 3, k = 3 (5 states), and on 23 of 109 screen instances.
- *Move radius* (`mrad_*.log`): a bundle trade is one move, so most of those states have move radius 2 (trade, then
  place). But **AUG₂ is false**, already at n = 2 and k = 3: 198 states of 3,000 random instances (n = 2, m = 5) need 3
  moves; also 56 at k = 4, 11 with every good relevant, and 1,172 at n = 3, m = 6, k = 3 (800 instances). **AUG₃ is false
  at k = 4**: g372 (n = 3, m = 6: agent 0 values goods 1, 2, 3, 5 at 4, 35,
  16, 10; agent 1 values 0, 2, 3, 4 at 21, 18, 14, 9; agent 2 values 0, 2, 3, 5 at 39, 34, 18, 9), state
  ({1, 4, 5}, {0}, {3}) with good 2 pooled, needs 4 moves; on the screen set 7 states of three n = 3, m = 6 instances
  (c4min-tlam-n3-m6, c4x-n3m6-onefour-a, induct-pot-nash) need 4 (`mrad_screen_n3.log`).

So no bounded one-step augmentation lemma holds at these radii, while *multi-step* augmentation through radius-2
moves never fails (§3.4): g372's state is no trap of G₂. This is the division of labour in Haxell's proof, where the
augmenting structure is a sequence of swaps, each local, organized by the tree.

### 3.6 Trees on generic moves, and the signature invariant

`ht_tree.py MOVES=1` / `MOVES=2`: the tree of §3.2 (Model G) with the generic moves of G* as edges (radius 1), or their
composites of two (radius 2). Screen set, n ≤ 3, every order (397 starts):
| edges | stuck starts | signature non-decreases / checks | collapses that gave a lower edge new victims | log |
|---|---|---|---|---|
| generic, radius 1 | 76 | 11,553 / 12,379 | 11,553 | `tree_screen_G_generic1_n3.log` |
| generic, radius 2 | 17 | 398 / 1,118 | 398 | `tree_screen_G_generic2_n3.log` |

(For comparison, the T + C catalogue of §3.2 gave one such event in 2,721 checks.) This is a **second obstruction**,
independent of traps. AKS's signature falls because a collapse cannot hurt a lower edge: the lower edge's blockers
are resource overlaps, and the collapsed edge is resource-disjoint from it. In EFX₀ a victim's envy depends on whole
bundles, so a collapse that touches none of a lower edge's goods can still change who that edge would hurt; bundle
trades do it constantly. A Haxell-type proof has to supply this invariant separately, for instance by restricting
edges to moves whose effect on every other agent's envy is confined to the goods they touch (junk transfers and chains
nearly are), or by a signature that also counts such events.

(The first version of this run let a swap through the pool place the root good while pooling another, so an
augmentation could cycle; the root's purpose now requires the pool to shrink. The T + C runs of §3.2–§3.3 cannot pool
a good and were not affected.)

## 4. What survives, and what a proof would need

**Definitions.** Let 𝒫 be the set of partial EFX₀ allocations of an instance (every agent happy with respect to the
allocated bundles; the unallocated goods form the pool). A *local move* reassigns one good to another agent (a pooled
good may be placed, but nothing returns to the pool), swaps the holders of two goods (the pool counts as a holder), or
trades the bundles of two agents. G_r joins s, t ∈ 𝒫 when a composite of at most r local moves leads from s to t and
t has no more pooled goods than s (the intermediate states need not be in 𝒫). A *trap of G_r* is a state of 𝒫 from
which no complete EFX₀ allocation is reachable in G_r.

**Conjecture CONN₂ (proof/k4-haxell, CONJECTURE).** In every additive instance in which every agent values at most four
goods, G₂ has no trap.

**CONN₁ at k = 3 (REFUTED, proof/k4-haxell).** "If every agent values at most three goods, G₁ has no trap" is
false: g834 (n = 4, m = 7, §3.4). No k = 3 trap exists with n = 2 on the value grid, and none was found with n = 3, so
at k = 3 traps start at n = 4 and are rare (1 of 1,000 random instances there, against 43 of 18,000 at n = 3, k = 4).

**Facts (computational, each with its log).**
- G₁ has traps at k = 4 (smallest: n = 2, m = 5, `attempts/k4-haxell-single-swap-collapse.md`), and at general k.
- No trap of G₂ is known: §3.4, the C census below, and the climbs of `ht_climb.py`.
- G₁ traps at k = 3 need n ≥ 4 on the data: none with n = 2 on the grid (472,860 instances, `n2_grid_k3.log`), none in
  random samples with n = 3 (18,600), one in 1,000 random instances with n = 4. At k = 4 the n = 2 grid (values
  {1, 2, 4, 7}, m ≤ 8) has 3,366 instances with traps among 1,540,944, and none with a radius-2 trap.
- Some states of 𝒫 need three or four local moves at once before the pool can shrink (§3.5), so neither conjecture can
  be proved one augmentation at a time with a jump of two moves.

**Why CONN₂ is the right "Haxell condition".**
- *It implies TARGET₄.* The empty allocation lies in 𝒫, so a complete EFX₀ allocation is reachable from it.
- *It is hereditary in the right sense.* In Haxell's theorem the hypothesis holds for every subset S of players, so
  every partial matching can be augmented, whatever the earlier augmentations did. CONN₂ says the same of every
  partial EFX₀ allocation, which is what lets an alternating tree augment greedily without entering a dead end
  (the failure of §3.2).
- *It is value-free.* It speaks only of membership in 𝒫. P1's stuck state of GM4-E is in 𝒫 and is not a trap: the
  path out lowers some agent's value.
- *It is not implied by anything known.* For general additive instances it would imply EFX₀ existence (the empty
  allocation again), so its general-k form is at least as hard as the EFX conjecture. The k = 4 proof must use k ≤ 4.
  At general k the census also found no G₂ trap (n ≤ 3), so it does not by itself locate where k ≤ 4 enters.

**Lemma CI (collapse invariant; written proof below, checked on 5,927 random pairs, `lemma_ci_screen.log`).** Let S
be a partial EFX₀ allocation, and e, f local moves (or composites) such that
- the sets A_e, A_f of agents whose bundles they change are disjoint, and so are the goods they touch;
- neither lowers the value of any agent it touches (*holding-monotone*);
- e(S) is a partial EFX₀ allocation.

Then every agent that f makes unhappy from e(S) is one that f makes unhappy from S.

*Proof.* Since e and f touch disjoint agents and goods, f changes the same bundles in the same way from S and from e(S).
Let i be happy in e(S) and unhappy in f(e(S)), strongly envying a bundle Z of f(e(S)).
- *Z belongs to an agent of A_e.* Then Z is that agent's bundle in e(S). If i ∉ A_f, i's holding is the same in e(S)
  and f(e(S)), and i was happy in e(S): contradiction. If i ∈ A_f, then i ∉ A_e, so i's holding in e(S) equals that in
  S, and in f(e(S)) it equals that in f(S), which is at least that in S by monotonicity of f: again no envy.
- *Z belongs to an agent outside A_e.* Then Z is also that agent's bundle in f(S). i's holding in f(e(S)) is at least
  its holding in f(S): equal if i ∉ A_e, and if i ∈ A_e (so i ∉ A_f) it is i's holding in e(S), at least that in S by
  monotonicity of e, which equals that in f(S). Strong envy only weakens as the holding grows, so i strongly envies Z
  in f(S).

So i is unhappy in f(S); and i is happy in S because S is a partial EFX₀ allocation. ∎

*Consequence.* For trees whose edges are pairwise agent- and good-disjoint and holding-monotone, a victim-free collapse
never gives a lower edge a new victim, and Annamalai's signature falls at every iteration, as in Santa Claus. But every
collapse of such a tree weakly raises every value and keeps the allocation partial EFX₀. By K4.SDC.P1, from GM4-E's
state X no partial EFX₀ allocation is weakly better for everyone and either better for someone or more complete, so
such a tree cannot augment X. **The invariant that makes the signature argument free forces the value-monotonicity
that P1 forbids.** Without monotonicity the invariant fails often (677 of 6,324 random non-monotone pairs; §3.6). A
Haxell-type proof must therefore use non-monotone edges and prove the collapse invariant for them by another argument.

**What a Haxell-type proof of CONN₂ needs.**
1. *Edges of radius 2.* A tree whose collapses are composites of at most two local moves (`ht_tree.py MOVES=2`,
   §3.6). The signature argument is unchanged: a collapse at layer t discards the layers from t up and lowers |Y_{t−1}|,
   provided the collapsed composite creates no victim for a lower edge (the invariant AKS get from disjointness, here
   to be proved or enforced).
2. *A never-stuck lemma.* When no tree player has an addable edge, the tree's goods and victims must give a
   contradiction. Haxell's version is a cover count, τ(E_S) ≤ (2r − 3)(|S| − 1). The EFX₀ analogue would bound the goods
   that the blocked placements of the root good and the victims' repairs can touch, using |R_i| ≤ 4. No candidate
   inequality is known. CONN₁ fails at k = 3 as well (n = 4), so the radius-2 edges are needed for every k ≥ 3, and the
   difference between k = 3 and k = 4 is one of frequency (traps from n = 2 at k = 4, from n = 4 at k = 3).
4. *The collapse invariant for non-monotone edges* (Lemma CI covers only monotone ones, which P1 rules out).
3. *A start.* The serial-dictatorship picks are never traps, and from every one of them on the screen set a sequence
   of victim-free moves completes (§3.1). The empty allocation works for CONN₂ itself.

## 5. CONN₂ beyond k = 4, and on the counterexamples to OC/OC₁ (burst 2)

Requested by the coordinator: does CONN₂ hold where OC₁^max fails, and at k ≥ 5? Instances are copied verbatim from
their sources into `k4/haxell/ext_instances.py` (PW5, PW4, RD5, RD4 from `k4/ksens/` on `claude/k4-ksens`; KG8, KG7 from
`attempts/kgen-n4-oc1.md` on `claude/kgen-n3`; the 39 TTC cores and B<, B> from `claude/kind-lamport-y8fdme`), and each
was checked against its source's stated picks.

**Full census** (`gstar.c`; every partial EFX₀ allocation of the instance):
| instances | n, m, k | partial EFX₀ states | G₁ traps | G₂ traps | log |
|---|---|---|---|---|---|
| PW5, PW4, RD5, RD4, KG8, KG7 | n = 4, 5; m = 7–9; k = 4, 5 | 81,635 | 0 | 0 | `gstarc_ext.log` |
| the 39 k = 4 core counterexamples to OC/OC₁ (TTC list) | n = 5, m = 9, k = 4 | 2,217,110 | 0 | 0 | `gstarc_ttc.log` |
| B<, B> (strict perturbations of TTC 36) | n = 6, m = 10, k = 4 | 1,420,558 | 0 | 0 | `gstarc_bcore.log` |

So every instance where OC, OC₁ or OC₁^max fails is free even of *single-move* traps: what fails there is the
serial-dictatorship-plus-one-chain shape, not the local connectivity of partial EFX₀ allocations.

**Start-based probes** (`gstar_probe.c`, `gstar_probe_run.py`), for instances too large for the census: from the
picks of every order (n ≤ 6) or of 30 sampled orders, and from states visited by random EFX₀-preserving walks, a
best-first search through partial EFX₀ allocations in steps of at most two moves. A probe whose search space is
exhausted without a complete allocation is a trap. The tool was validated against the census: with single moves
only it reports the known traps (n = 2 trap, g834) and none elsewhere.
- PW5, PW4, RD5, RD4, KG8, KG7: 1,118 probes, all reach a complete allocation (`probe_ext.log`).
- The clean PW(f, W, r) grid of `k4/ksens/fam_ladder.clean`, f ≤ 5, W ≤ 4, r ≤ 8 (n ≤ 9, m ≤ 17, k = max(r + 1, f + 1)
  ≤ 9): see `probe_pwgrid.log` (no trap among the cells finished so far; the status block gives the final count).

**Full census at k ≥ 5 on random instances** (`gstar_run.py gen:…`; values 1–40; `gstarc_gen_n*k*.log`, finished):
17 cells with n ≤ 5 and k = 5–10 (n = 2: k = 7, 8; n = 3: m = 8, 10; n = 4: m = 8, 9; n = 5: m = 8). That is 43,050
instances and 135,083,927 partial EFX₀ states, with **no G₂ trap (radius 2)** and 251 traps for single moves. The cell
n = 3, m = 8, k = 5 was re-run after a crash (a permission error while the binary was rebuilt). Earlier: no G₂ trap at
k = 5–8 for n ≤ 4 (§3.4).

**The PW grid, finished.** The full census covers the 45 cells with n ≤ 6 and (n + 1)^m ≤ 3·10⁸ (`gstarc_pwgrid.log`):
6,347,959 partial EFX₀ states, **no G₂ trap**, and 12 single-move traps, three in each PW(f, 1, 4) cell. Conjecture W
(two single moves with rotations, `measure_rot2_pwgrid.log`) on the 26 cells with n ≤ 5: no stuck state for welfare or
leximin. Pool-shrinking alone fails in 24 of the 26.

## 6. The one-step lemma: candidate measures, and what decides them

CONN₂ is a reachability statement. A proof by local search needs a measure μ and a one-step lemma: from every partial
EFX₀ allocation with a nonempty pool, some step of a fixed move class leads to a partial EFX₀ allocation with smaller
μ. With μ = (|pool|, φ) compared lexicographically, this gives CONN by well-foundedness. P1 rules out φ that never lets
an individual agent lose; it does not rule out welfare-type φ, which can lower some agents.

`gstar_measure.c` (driven by `gstar_measure_run.py`) enumerates every partial EFX₀ allocation and counts the *stuck*
states for each candidate φ: states with a nonempty pool from which no step lowers (|pool|, φ). Candidates: φ0 none
(pure augmentation, AUG); φ1 −welfare Σᵢ vᵢ(Xᵢ); φ2 leximin; φ3/φ4 ± Σ|X_j|²; φ5 the number of envy pairs vᵢ(X_j) > vᵢ(Xᵢ);
φ6/φ9 the number of allocated goods held by an agent that values them (complementary forms); φ7 the number of
victim-free placements of pooled goods; φ8 the blockedness of placements; φ10–φ18 welfare or leximin with tie-breakers.

**Steps of at most two local moves (move, swap, trade).** Every candidate has stuck states. Welfare has 3 (on the
screen set, e.g. induct-v-r3, a plateau of 7 equal-welfare neighbours), the best tie-breaks 1 (`measure_screen.log`).

**Steps of at most three local moves** (`measure3_*.log`): welfare, leximin and the envy count have **no stuck state**
on any dataset. That covers the screen set, the suite, random k = 4 cores (n ≤ 3), PW5/RD5/KG, random instances with
n = 2–4 at k = 3, 4, 5 and 7, and the 39 TTC cores: about 5.6 million partial EFX₀ states. AUG₃ and the relevance count
fail.

**No fixed radius works for welfare, leximin or the relevance count: the family CYC_n** (k = 3). Agent i values its
own good gᵢ at 10, the next agent's good g_{i+1} at 11, and a pooled good p at 1. In the state where every agent
holds its own good, p cannot be placed: the predecessor of its receiver strongly envies. A partial rotation along a
path of r agents changes welfare by r − 10. So welfare and leximin rise only with the full rotation, which needs
n − 1 trades. `gstar_measure` confirms it: CYC₅ is stuck at radius 3 for welfare, leximin and every tie-break, and
CYC₄ is not. The envy count is not stuck on CYC₄–CYC₆, even at radius 2.

**Rotations as moves.** Let a move also rotate the bundles along any cycle of agents. That is the classical
envy-cycle operation, generalized to any cycle, so it also performs closed chains (the family CHAINₜ below completes
by one rotation and one placement). With steps of at most two such moves (`measure_rot2_*.log`):
| data | instances | partial EFX₀ states | stuck: AUG | welfare | leximin | envy count | relevance |
|---|---|---|---|---|---|---|---|
| screen (n ≤ 4, m ≤ 7) | 109 | 111,591 | 1,660 | **0** | **0** | 212 | 112 |
| suite (n ≤ 4, m ≤ 7) | 94 | 78,665 | 1,180 | **0** | **0** | 142 | 77 |
| random k = 4 cores, n ≤ 3 | 538 | 200,436 | 375 | **0** | **0** | 42 | 71 |
| PW5, PW4, RD5, RD4, KG8, KG7 | 6 | 81,635 | 1,034 | **0** | **0** | 27 | 11 |
| the 39 TTC cores (n = 5, m = 9) | 39 | 2,217,110 | 10,030 | **0** | **0** | 0 | 14 |
| the hard profiles logged in `results/k4_sdc/*.log`, n ≤ 5 | 1,520 | 4,668,436 | 26,454 | **0** | **0** | 761 | |
| B<, B> (n = 6, m = 10; welfare and leximin only, `gstar_measure` with its single-measure option) | 2 | 1,420,558 | 4,366 | **0** | **0** | | |
| random n = 2, m = 5, every good relevant | 3,000 | 231,398 | 11 | **0** | **0** | 5 | 11 |
| random n = 3, m = 6, k = 3 / 4 | 800 / 800 | 593,535 | 269 / 741 | **0** | **0** | 158 / 100 | 15 / 53 |
| random n = 3, m = 7, k = 5 | 600 | 509,542 | 556 | **0** | **0** | 66 | 54 |
| random n = 4, m = 7, k = 4 / 7 | 300 / 300 | 1,453,133 | 4,151 / 5,116 | **0** | **0** | 108 / 6 | 91 / 5,116 |

*Constructions tried against W* (`ht_families.py`, `families.log`: census and stuck states at radius 2 and 3 without
rotations, and radius 2 with rotations):
- CYC_n (above): passes with rotations, up to n = 6.
- CHAINₜ, a wanting path closed by the pooled good: agent 0 values g at 12 and b₀ at 10, agent i values bᵢ₋₁ at 11 and bᵢ
  at 10, i = 1, …, t. Passes for t = 3, 4, 5, with or without rotations. One rotation and one placement complete it;
  without rotations, welfare-raising steps lead there.
- OPENₜ, the same path ending at an absorber z that holds a good only it values (the last agent also values g at 12):
  passes for t = 2, 3, 4 (n ≤ 6), although the intended completion takes three moves.

*Two moves are needed.* With single moves (rotations included), welfare is stuck on 185 screen states and on the two
trap states of the n = 2 trap of §3.4 (`gstar_measure.c` with RADIUS = 1), so the radius 2 in W cannot be lowered.

*Ties.* Strict increase is what plateaus could break, so W was also run with ties:
- every n = 2 instance with k ≤ 3, m ≤ 6 and values in {1, 2, 3, 5, 8, 13}: 472,860 instances, 31,887,837 partial EFX₀
  states, no stuck state for welfare or leximin (`n2w_grid_k3.log`);
- the k ≤ 4 grid: `n2w_grid_k4.log`;
- 4,400 random instances with n = 3, 4, k = 3, 4 and values drawn with replacement from 1–3 or 1–4: 4,190,328 states,
  no stuck state (`measure_rot2_gent_*.log`).

An independent Python implementation (`ht_lemma_w.py`: its own move generator, rotations included, raw EFX₀ test)
agrees: no stuck state for welfare on 56 screen instances (11,753 states, `lemma_w_py_screen.log`), and exactly the
one stuck state of CYC₅ when rotations are limited to trades. Further Python runs (`lemma_w_py_*.log`): 200 random k = 4
core profiles with n ≤ 3, 300 random n = 3, m = 6, k = 4, 150 random n = 3, m = 7, k = 5, and 1,000 random n = 2, m = 5
with every good relevant. In all, 1,706 instances and 397,633 partial EFX₀ states, no stuck state.

**Conjecture W (one-step welfare lemma) — REFUTED at n = 2, k = 4** (`attempts/k4-haxell-conjecture-w.md`; the n = 2
grid with k ≤ 4, `n2w_grid_k4.log`, found 576 instances where it fails; smallest: m = 7, strict values). Statement, kept
for reference: let X be a partial EFX₀ allocation with a nonempty pool. Then
a composite of at most two moves leads to a partial EFX₀ allocation X′ with |pool(X′)| < |pool(X)|, or with
|pool(X′)| = |pool(X)| and Σᵢ vᵢ(X′ᵢ) > Σᵢ vᵢ(Xᵢ). A move is one of: give one good to another agent (a pooled good may be
placed, nothing returns to the pool); swap the holders of two goods (the pool counts as a holder); rotate the bundles
along a cycle of agents.

*Why it fails, and what survives.* An agent may have to give away all its other goods at once. In the counterexample
both agents value a pooled good g above everything else they could hold, so g's receiver must hold g alone and
dump its three other goods. That takes three single moves, of which one swap through the pool counts once. At k = 5
the same construction defeats three moves (W5), so with single-good moves the radius has to grow with k, about
k − 1. That is a place where k really enters. Two repaired forms:
- **W₃ (three moves; candidate for k ≤ 4).** No stuck state where W had none. **On the whole n = 2 grid with k ≤ 4
  (470,500,040 states) it has no stuck state, for welfare or leximin** (`n2w_grid_k4_r3.log`). Pool-shrinking within
  three single moves fails at 5,076 states of 576 instances, exactly the instances where W fails. It fails at k = 5
  (W5).
- **W^sub (two moves, giving a set of goods to one agent counting as one move).** With welfare it is **REFUTED at
  n = 4, k = 4** (burst 3, `attempts/k4-haxell-wsub-welfare.md`). With leximin (L^sub, below) it survives. It contains
  W's moves, so it holds wherever W held. It repairs W4 and W5. **On the whole n = 2 grid with k ≤ 4 and values
  {1, 2, 4, 7} (1,540,944 instances, 470,500,040 partial EFX₀ states) it has no stuck state, for welfare or for
  leximin** (`n2w_grid_k4_sub.log`). Pool-shrinking alone (φ0) fails at 48 states of 36 instances: the welfare
  steps are needed.

*Skewed random instances* (`genskew`, one or two goods valued 30–90 by several agents, the rest 1–15: the shape of
the counterexample; `measure_*genskew*.log`, welfare / leximin stuck states):
| data | partial EFX₀ states | W | W₃ | W^sub |
|---|---|---|---|---|
| n = 2, m = 7, k = 4 (3,000 instances) | 1,422,857 | 1,264 / 1,264 | 0 / 0 | 0 / 0 |
| n = 3, m = 7, k = 4 (3,000) | 2,842,370 | 0 / 0 | | |
| n = 3, m = 8, k = 4 (1,500) | 3,853,984 | **188 / 168** | 0 / 0 | 0 / 0 |
| n = 4, m = 7, k = 4 (300) | 824,660 | 0 / 0 | | |

| n = 2, m = 9, k = 5 (3,000) | 11,497,172 | 933 / 933 | | 0 / 0 |
| n = 3, m = 8, k = 5 (800) | 1,853,763 | 149 / 125 | | 0 / 0 |
| n = 3, m = 9, k = 6 (400) | 2,474,674 | 125 / 117 | | 0 / 0 |

So W fails at n = 3 and at k = 5 as well. W₃ survives wherever it was run at k = 4, and W^sub survives wherever W
fails, at k = 4, 5 and 6. (W₃ is not run at k ≥ 5, where W5 already refutes it.)

**W^sub stated precisely (the target for formalization).** The model is `EFX.Inst` of `lean/EFX/Model.lean`
(n agents, m goods, values `v i g : Nat`), with a partial allocation as an owner map into `Option`.
- *State.* `X : Fin m → Option (Fin n)`. The bundle of i is Xᵢ = {g : X g = some i}, the pool is P(X) =
  {g : X g = none}. *Partial EFX₀*: for all i ≠ j and every g with X g = some j,
  vᵢ(Xⱼ ∖ {g}) ≤ vᵢ(Xᵢ). This is `Inst.EFX0` with the pool ignored; h ranges over all of Xⱼ, zero-valued goods
  included. *Welfare*: W(X) = Σ_g [X g = some i] · vᵢ(g).
- *Moves.* X′ is a **move** of X if it is one of the following.
  - (T) **Set transfer**: a holder h : Option (Fin n), a nonempty set S ⊆ {g : X g = h} and an agent b with
    some b ≠ h; X′ g = some b for g ∈ S, X′ g = X g otherwise. A single-good move is the case |S| = 1. A
    placement of pooled goods is the case h = none.
  - (S) **Swap**: goods g ≠ g′ with X g ≠ X g′; X′ g = X g′, X′ g′ = X g, all else unchanged. A swap with a pooled
    good is the only way a good enters the pool, and it sends exactly one out.
  - (R) **Rotation**: L ≥ 2 distinct agents a₀, …, a_{L−1}. X′ g = some a_{(t+1) mod L} if X g = some a_t, and
    X′ g = X g otherwise (the pool is untouched). L = 2 is the trade of two bundles.
  
  No move enlarges the pool: (T) from the pool shrinks it by |S|, and every other move keeps its size.
- *Lemma W^sub (REFUTED at n = 4, k = 4 with welfare: `attempts/k4-haxell-wsub-welfare.md`).* Let X be partial
  EFX₀ with P(X) ≠ ∅. Then there are X₁ and X₂ such that X₁ is X or a move of X, X₂ is X₁ or a move of X₁, X₂ is
  partial EFX₀, and either |P(X₂)| < |P(X)|, or |P(X₂)| = |P(X)| and W(X₂) > W(X). X₁ need not be EFX₀.
- *Lemma L^sub (REFUTED at n = 4, k = 4: `attempts/k4-haxell-lsub-leximin.md`).* The same, with the
  **leximin** order in place of welfare. Let λ(X) be the vector of the values vᵢ(Xᵢ) sorted increasingly. The
  last condition becomes |P(X₂)| = |P(X)| and λ(X₂) > λ(X) lexicographically. This is φ2 of `gstar_measure`. It has
  a step at all 36 states where W^sub fails, and had no stuck state wherever it was run before (the n = 2 grid, the
  skewed sets).
- *W₃* (welfare, three single-good moves, no set transfers) also has a step at all 36. It fails at k = 5 (W5).
- *Lemma P^sub (Pareto; REFUTED at n = 4).* The same moves, but the measure step must be a **Pareto improvement**:
  the pool size kept, no agent worse, some agent strictly better. A Pareto improvement raises welfare and leximin, so
  P^sub implies both W^sub and L^sub, and fails wherever either fails.
  - It is **ordinal**: whether Y is a Pareto improvement of X compares, for each agent, two sets of its goods
    (vᵢ(Yᵢ) > vᵢ(Xᵢ) iff vᵢ(Yᵢ ∖ Xᵢ) > vᵢ(Xᵢ ∖ Yᵢ)). So with strict values it depends only on the type profile, and
    exhaustive checks over types are complete for it.
  - `gstar_measure` measure 19.
- *Where P^sub holds (exhaustive over strict types).*
  - **n = 2** (Theorem N2 below, with its Pareto strengthening): k ≤ 4, with up to two goods valued by nobody.
  - **n = 3, k ≤ 3 (computer-verified, two implementations)**: every strict type profile of every shape (14,100
    classes up to Lemma OR, all m ≤ 9, 3,756,992 partial EFX₀ states) has no P^sub stuck state (`ht_n3types.py`, C;
    `n3types_k3_m7.log`, `n3types_k3_m89.log`). The independent Python checker `ht_n3types_check.py` re-ran every
    class with the same state counts and no stuck state (`n3types_k3_pycheck_full.log`). Completeness is by Lemmas
    TD and OR. Pool-shrinking alone fails at 7,129 of those states.
  - So two moves suffice for n ≤ 3 (k ≤ 3 at n = 3). Every known failure has n = 4 and an agent with four goods;
    n = 4 with k ≤ 3, and n = 3 with k = 4 exhaustively, are not settled.
  - *k = 3 climbs (evidence).* Two-move Pareto climbs with k = 3 found no failure at n = 4 (m = 7, 8) or n = 5
    (m = 7); the hardest states kept 2 to 8 escapes (`p2climb_*.log`). This suggests a place where k enters:
    **P^sub may hold for k ≤ 3 at every n, while k = 4 needs a third move.** That is a CONJECTURE (P^sub for k ≤ 3).
  - *Three-move Pareto climbs (evidence).* No P^sub₃ failure: seeded from 4 of the n = 4 failures, and random at
    n = 4, m = 8 and n = 5, m = 7, 8 (`p3climb_*.log`).
  - **The n = 5 test** (`run_n5climb.sh`, `n5climb_*.log`; m = 8, k ≤ 4). Each seed is an n = 4 two-move failure
    plus a fifth agent holding a private good, and the climber mutates the fifth agent too.
    - Adding the fifth agent removes every seed's two-move failure: it gives the goods an outlet.
    - *Two moves* (4 seeds × welfare, leximin, Pareto; 500 steps × 2 climbers each): one failure, Pareto from seed 4.
      At that instance welfare and leximin still have two-move steps, and **three moves give a step for every
      measure**, single-good moves included. There were no welfare or leximin failures. In the other runs the hardest
      states kept 2–4 (Pareto), 4–16 (welfare) and 2–10 (leximin) escapes.
    - *Three moves* (the same 4 seeds × 3 measures; 400 steps × 2 climbers each; 3,357 s): **no failure**.
      - The climbs rarely even reached a state that needs three moves. That happened once, under Pareto, and that state
        had a three-move step. In the other runs every state without a single-move step still had 2–14 two-move
        escapes.
      - So at n = 5 the radius did not grow past three, and the two-move failures of n = 4 do not survive a fifth
      agent without help from the climber. This is evidence (climbs), not exhaustion.
  - **Sampled core profiles** (`run_p3cores.sh`; `n4core_p2_sample_cert.log`, `n4core_p3_sample_cert.log`). The
    sample takes 200 random certificate-domain type profiles of each of the 780 n = 4, k = 4 cores with 4 ≤ m ≤ 8:
    156,000 instances and 499,517,909 partial EFX₀ states. P^sub is ordinal, so each sampled profile is checked
    exactly; only the sampling makes this evidence.
    - *Two moves*: 3 stuck states, one in each of 3 profiles. All three cores have m = 7, three agents with four goods
      and one with three (`k4_certs_4_n4_3`, idx 4, 70, 72; the instance lines are the `STUCK` lines of the log).
      At all three, welfare and leximin do have two-move steps (`gstar_measure 2 1 1 1` and `2 1 2 1`), so these
      failures are Pareto-only. That is consistent with P^sub being strictly stronger than W^sub and L^sub.
    - *Three moves* (`gstar_measure 3 1 19 1`): **no stuck state in any of the 156,000 profiles.** At the three
      two-move failures, three single-good moves also suffice (`3 1 19 0`).
    - So two-move Pareto failures are rare on cores (3 in 156,000 profiles), and three moves covered every sampled
      profile. Exhausting every profile is out of reach (up to 288³ · 6 per core, before symmetry; see "Why every
      profile cannot be covered" below).
    - The same with every strict type allowed (unbalanced ones too, `DOMAIN=strict`; 100 profiles per core):
      `run_p3cores_strict.sh`, `n4core_p{2,3}_sample_strict.log`.
  - **Anatomy of the three-move steps** (`ht_rescue.py`, pure Python from the raw definition, no code shared with the
    C checker; `rescue_anatomy.log`). The input is all 44 known two-move failures:
    - the 36 welfare states and the 4 leximin states at n = 4;
    - the n = 5 Pareto failure;
    - the 3 core-sample failures.
    
    The script re-checks that each state has no step within two moves, then lists every three-move composite that
    reaches a smaller pool or a Pareto improvement.
    - **Every failure has a three-move composite that shrinks the pool** (36 to 330 per failure). So the failures are
      not plateaus of the measure: the pool can shrink, it just takes three moves. Pool-shrinking alone is still not
      enough in general. In the core sample, no three moves shrink the pool at 60 states (in 32 profiles; φ0 of
      `n4core_p3_sample_cert.log`), and each of those states has a two-move Pareto step.
    - Every failure has a rescuing composite whose two intermediate states are partial EFX₀ (2 to 26 per failure):
      three EFX₀ moves, of which the first two do not improve.
    - 43 of the 44 have a rescue that is a Haxell-type alternating path. First, pooled goods go to an agent a₁ (a
      transfer from the pool, or a swap of a pooled good with one of a₁'s goods). Then a set or a swap goes from a₁
      to a₂, then from a₂ to a₃. The exception is the first core failure (`k4_certs_4_n4_3`, m = 7, idx 4), which
      has no such rescue.
    - The commonest rescue (at 41 of the 44) has three moves: agent A gives a good to B; A swaps one of its goods for
      a pooled good; then A, B and C rotate their bundles. Its net flow is P → B, A → B, A → P, B → C, C → A.
  - **Measure Q** (`gstar_measure` measure 20). From every partial EFX₀ allocation with a nonempty pool, either two moves
    give a Pareto improvement (with the pool kept), or three moves shrink the pool.
    - Q implies P^sub₃, and the anatomy suggests it. On the data so far the two failure sets are disjoint:
      - two moves fail (P^sub) only where three moves shrink the pool;
      - three moves fail to shrink the pool only where two moves give a Pareto step.
    - So **Q holds on everything checked**:
      - the 44 failures (`gstar_measure 3 1 20 1`, and also with single-good moves only, `3 1 20 0`);
      - the 156,000 sampled core profiles. This follows from the two logs: the sample's 3 P^sub stuck states each have
        a pool-shrinking three-move composite.
      - At n ≤ 3 it follows from Theorem N2 and K4.HX.PN3.
    - Q splits the work: Pareto steps stay local (two moves), and only augmentations get a longer reach, as in an
      augmenting-path argument.
    - Climbs that try to break Q: `run_qclimb.sh`, `qclimb_*.log`.
- *Lemma P^sub₃ (CONJECTURE for every |Rᵢ| ≤ 4).* P^sub with **three** moves. It has a step at all 40 known two-move
  failures: the 36 for welfare and the 4 found by the leximin climbs (`gstar_measure 3 1 19 1`; with single-good moves
  only, `3 1 19 0`, also none stuck). It implies W^sub₃ and L^sub₃ and TARGET₄, and it is the cleanest candidate for
  verification by types and for a proof.
- *Lemma W^sub₃ / L^sub₃ (CONJECTURE for every |Rᵢ| ≤ 4).* The same with **three** moves, with welfare or leximin
  as the measure. At n = 4 neither two-move form holds: W^sub fails at WS4 and L^sub at LS4, at different states.
  Three moves give a step at all 37 known failures, for both measures (`attempts/k4_haxell_wsub.py`). Radius-3
  climbs are in `r3climb_*.log`. That the radius grew from two to three at n = 4 is a warning that it may grow with
  n.
- *Consequence (elementary).* The all-pool allocation is partial EFX₀. Each step decreases (|P|, −W), or
  (|P|, λ) for L^sub, lexicographically, and the states are finite. So the lemma for an instance gives a complete
  EFX₀ allocation of it, and the lemma for all k = 4 instances gives TARGET₄. Formally this is well-founded induction
  on |P| and then on W, or on λ among the finitely many value vectors.
- *What the checker runs.* `gstar_measure 2 1 1 1` (RADIUS 2, ROT 1, ONLY 1 = welfare, SUB 1) implements exactly
  these moves: single moves to an agent, swaps, trades, rotations of length ≥ 3, and transfers of ≥ 2 goods from one
  holder to one agent. Its stuck count for φ1 counts the states violating the lemma. φ0 counts the states with no
  step that shrinks the pool (AUG within two such moves). φ0 is reported but not needed.

A Lean rendering of the definitions (a sketch: not compiled, and no `lean/` file is added in this burst):
```lean
namespace EFX.Inst
variable (I : Inst)
abbrev PAlloc := Fin I.m → Option (Fin I.n)
def pval (X : I.PAlloc) (i : Fin I.n) (j : Fin I.n) (ex : Option (Fin I.m)) : Nat :=
  finSum I.m (fun g => if X g = some j ∧ ex ≠ some g then I.v i g else 0)
def PEFX0 (X : I.PAlloc) : Prop :=
  ∀ i j : Fin I.n, i ≠ j → ∀ g, X g = some j → I.pval X i j (some g) ≤ I.pval X i i none
def poolSize (X : I.PAlloc) : Nat := finSum I.m (fun g => if X g = none then 1 else 0)
def welfare (X : I.PAlloc) : Nat := finSum I.m (fun g => match X g with | some i => I.v i g | none => 0)
inductive Move (X : I.PAlloc) : I.PAlloc → Prop
  | transfer (h : Option (Fin I.n)) (S : Fin I.m → Bool) (b : Fin I.n)
      (hS : ∀ g, S g = true → X g = h) (hne : ∃ g, S g = true) (hb : some b ≠ h) :
      Move X (fun g => if S g = true then some b else X g)
  | swap (g g' : Fin I.m) (hne : X g ≠ X g') :
      Move X (fun x => if x = g then X g' else if x = g' then X g else X x)
  | rotate (σ τ : Fin I.n → Fin I.n) (h1 : ∀ a, τ (σ a) = a) (h2 : ∀ a, σ (τ a) = a) :
      Move X (fun g => (X g).map σ)                -- σ: any permutation of the agents (τ its inverse)
def WsubStep (X Y : I.PAlloc) : Prop :=
  I.PEFX0 Y ∧ (∃ Z, (Z = X ∨ I.Move X Z) ∧ (Y = Z ∨ I.Move Z Y)) ∧
  (I.poolSize Y < I.poolSize X ∨ (I.poolSize Y = I.poolSize X ∧ I.welfare X < I.welfare Y))
end EFX.Inst
```
In the sketch, `rotate` takes any permutation σ of the agents, given with its inverse τ since core Lean has no
`Equiv`. That is more than (R), which rotates one cycle: a product of disjoint rotations counts as one move there.
More moves make the lemma weaker, so the checked form (single cycles) implies the sketch's form. The sketch's form
is the convenient one for a proof.

**W^sub on the coordinator's test sets (burst 3; welfare, the form later refuted at n = 4; `gstar_measure 2 1 1 1`, every partial EFX₀ state with a
nonempty pool of every instance):**
| test set | instances | partial EFX₀ states | W^sub stuck | log |
|---|---|---|---|---|
| n = 2, every relevant-set pair with k ≤ 4, values {1, 2, 4, 7} (ties included) | 1,540,944 | 470,500,040 | **0** (leximin 0) | `n2w_grid_k4_sub.log` |
| n = 3, every shape with k ≤ 3, values {1, 2, 4, 7, 12}, m ≤ 7 (up to isomorphism; welfare and leximin; m = 8, 9 queued) | 8,155,420 | 2,571,087,783 | **0** (leximin 0) | `n3grid_k3_v12.log` (welfare, m ≤ 5), `n3grid_wl_k3_v12.log` (both, m ≤ 6) |
| n = 4, k = 4 cores with one 4-good agent, m ≤ 5 (20 cores): **every** strict balanced type profile of the certificate domain, up to automorphism | 451,824 | 223,522,208 | **0** (leximin 0 too: `n4core_wl_all_m5.log`) | `n4core_all_m5.log` |
| n = 4, k = 4 cores with m = 4 and at most two 4-good agents (5 cores, the two n4_2 cores included): every profile, up to automorphism | 552,048 | 115,378,032 | **0** (leximin 0 too: `n4core_wl_all_m4.log`) | `n4core_all_m4.log` |

The n = 3 instances are counted after the symmetry reduction: goods of one pattern are interchangeable, and agent
permutations that fix the shape are factored out. `ht_n3grid_check.py` checks the reduction against the full product
on a small grid. On the cores, a type profile fixes the ordinal type of each agent, realized by the type's integer
representative from `k4/order_types.json`; welfare is cardinal, so other realizations are sampled separately (below).
`ht_n4core_check.py` checks the automorphism reduction. Pool-shrinking alone (φ0) fails in 419,736 of the 451,824
core instances: on cores the welfare steps do most of the work.

**Why every profile cannot be covered.** A core with a agents of four goods and b of three has up to 288ᵃ · 6ᵇ
profiles: 2.2·10⁴ to 7·10⁹ per core before symmetry, and 0.5 ms (m = 4) to 0.5 s (m = 9) per instance. Only the
cores with one 4-good agent and m ≤ 5, plus the two n4_2 cores with m = 4, fit (both done, table above). Every other
core is sampled: 200 random certificate-domain profiles per core with m ≤ 8; 100 random profiles per core with every
strict type allowed and random per-agent scaling 1–4 of the representatives (so cross-agent welfare comparisons
vary); and 20 per core with m = 9.

**Which move kinds W^sub needs (ablation).** Each kind of move was switched off in turn (`gstar_measure` OFF
bitmask), and the adversarial climb (`ht_wclimb.py`, below) searched for a state with no step (`wablate_off*.log`;
n = 2 and n = 3, m = 7, k = 4, 3 climbers × 1,500 instances each). Every failure was re-checked by the independent Python
checker `ht_wexplain.py`, which reports no step with the kind off and 6–16 steps with all moves
(`wablate_recheck.log`).
| kind switched off | failure found | smallest witness (values; state; pool) |
|---|---|---|
| swaps through the pool | yes, n = 3 | v₀ = {0: 36, 3: 44, 5: 45}, v₁ = {1: 38, 2: 44, 3: 60, 6: 1}, v₂ = {1: 9, 4: 8, 5: 49}; ({0, 2, 6}, {3}, {1, 4}); {5} |
| trades of two bundles | yes, n = 3 | v₀ = {1: 59, 3: 35, 4: 54, 5: 11}, v₁ = {0: 15, 4: 41, 5: 6}, v₂ = {1: 50, 2: 18, 3: 17, 6: 18}; ({0, 2, 3, 5}, {4}, {1}); {6} |
| rotations of ≥ 3 agents | yes, n = 3 | v₀ = {0: 47, 2: 45, 4: 19, 6: 2}, v₁ = {0: 46, 1: 32, 5: 12, 6: 8}, v₂ = {2: 60, 3: 38, 6: 6}; ({2}, {0}, {3, 4, 5, 6}); {1} |
| transfers of ≥ 2 goods between agents | yes, n = 2 | v₀ = {2: 59, 3: 15, 4: 8, 5: 31}, v₁ = {0: 14, 1: 27, 2: 51, 6: 4}; ({3, 4, 5}, {0, 1, 6}); {2} (W4's mechanism) |
| single-good transfers between agents | yes, n = 3 | v₀ = {0: 35, 1: 54, 4: 17, 6: 8}, v₁ = {1: 47, 2: 11, 3: 35, 5: 5}, v₂ = {0: 41, 3: 30, 5: 14, 6: 38}; ({0, 4}, {2, 3}, {5, 6}); {1} |
| swaps of two agents' goods | yes, **n = 4** (none at n = 2, 3) | v₀ = {4: 17, 5: 56, 6: 42}, v₁ = {1: 19, 2: 6, 4: 12, 5: 29}, v₂ = {0: 37, 1: 36, 3: 18}, v₃ = {0: 58, 4: 38, 6: 40}; ({5}, {2, 3, 4}, {1}, {0}); {6} |
| transfers of ≥ 2 pooled goods | none (hardest state: 2 steps; also none with agent swaps off at n ≤ 3) | |

So the move class of W^sub is close to minimal: of its seven kinds, six are each needed. The n = 4 witness for agent
swaps was found by the climb with both unneeded-looking kinds off (OFF = 9, `wablate_off9_n4m7k4.log`). The Python
re-check (`wablate_off9_recheck.log`) shows that switching off the agent swaps alone already leaves no step. With all
moves the state has **exactly one W^sub step**: place good 6 with agent 0 and swap agent 0's good 5 for agent 1's
good 4. That gives the complete EFX₀ allocation ({4, 6}, {2, 3, 5}, {1}, {0}), welfare 188 > 168. This is the
tightest state found for W^sub: one escape.
- Why it is tight: every placement of good 6 alone is blocked, each time by strong envy (τ against own value).
  - At agent 0, by agent 1 (29 > 18: it wants good 5).
  - At agent 1, by agents 0 and 3 (59 > 56, 78 > 58).
  - At agent 2, by agent 1 (19 > 18).
  - At agent 3, by agent 2 (37 > 36).
- The step repairs the first block. Agent 1 receives good 5 (worth 29 to it) for good 4 (12), and agent 0 keeps 6
  and 4 (59 ≥ 56, the most it can claim from agent 1's new bundle).

Only transfers of two or more pooled goods remain without a witness. With up to four relevant goods per agent and
one good pooled at every hard state found, that kind may simply never be used at these sizes.

**Pool-shrinking alone is not enough, even with set moves.** At n = 3, m = 5 with strict values (v₀ = {0: 945},
v₁ = {2: 897, 3: 696, 4: 83}, v₂ = {0: 679, 1: 534, 3: 556}) the state ({2}, {3}, {1, 4}) with good 0 pooled has
no composite of two moves that shrinks the pool. Its W^sub step is a welfare step, the swap of good 0 (worth 945 to
agent 0) for good 2 (worth 0 to agent 0) through the pool (`wexplain_aug_n3m5.log`). Agent 0 must hold good 0
alone. Good 2 can go nowhere: agent 2 strongly envies {3, 2}, and agent 1 strongly envies {1, 4, 2}. So the welfare
part of the measure is used, not only as a tie-breaker.

The rest of this paragraph and the evidence above apply to both forms.

*Consequences.* (|pool|, −welfare) strictly decreases and takes finitely many values. So from the empty allocation a
complete EFX₀ allocation is reached, in at most (m + 1)·w steps, w the number of distinct welfare values. W for k ≤ 4 implies TARGET₄. W
for all additive instances implies EFX₀ existence, so its general form is at least as hard as the EFX conjecture.
The data above include k = 5 and 7 and every-good-relevant instances with no failure, so they do not show where
k ≤ 4 would enter. The same holds with leximin in place of welfare.

*What the measure is and is not.* Welfare is a value measure, but the lemma is not value-monotone: the step may lower
any agent, and P1's stuck state is escaped this way. The pool comes first, so the potential can fall in welfare when
a good is placed. Envy-cycle rotations alone raise welfare, so a welfare-stuck state has an envy graph without cycles.
- *[unverified] link to the literature:* Chaudhury–Kavitha–Mehlhorn–Sgouritsa's "little charity" algorithm also
  combines allocation steps, envy-cycle rotations and a lexicographic potential, but lets goods return to the pool.
  This is recalled, not read in this session.

*Where a proof would start.*
1. At a welfare-stuck state, rotations along envy cycles are welfare-improving, so the envy graph is acyclic and has
   a source s.
2. Placing a pooled good g at s fails only if some agent i strongly envies X_s + g by dropping a good h ≠ g with
   vᵢ(h) < vᵢ(g).
3. The second move must then repair i: hand i the good g, or move h, or rotate i's bundle into a cycle. The data say
   one of these always works within two moves. The case analysis of which, using |R_i| ≤ 4, is the open step.
4. W is exhaustively checked up to n = 6 (B<, B>, `measure_rot2_bcore_phi*.log`). Beyond that only sampled states
   are checked (§7).

*The smallest case, n = 2, is already not a one-liner.* Write τᵢ(Z) = vᵢ(Z) − min_{z∈Z} vᵢ(z) for |Z| ≥ 2 (0 otherwise),
so EFX₀ reads v_A(X_A) ≥ τ_A(X_B) and v_B(X_B) ≥ τ_B(X_A). For a pooled g the four obvious one- or two-move
completions are: g to A; g to B; trade and then g to the new holder of X_B; trade and then g to the new holder of X_A.
They fail together exactly when τ_B(X_A + g) > v_B(X_B), τ_A(X_B + g) > v_A(X_A), τ_B(X_B + g) > v_B(X_A) and
τ_A(X_A + g) > v_A(X_B). All four inequalities hold at the n = 2 trap ({0, 2}, {1, 3}), g = 4: 11 > 6, 12 > 5, 12 > 3,
11 > 4. Its repair is of a fifth kind: g goes to A while A's good 2 goes to B. A proof of W at n = 2 therefore needs
the moves that take a good from the receiver of g, and the case analysis of when they keep EFX₀. That is the first
open case.

**The n = 2 case (burst 3, toward a proof).** W^sub and L^sub have no stuck state on the n = 2 grid. Both two-move
failures need n = 4, so n = 2 is still a fair, bounded target.
- *With ties the measure is needed.* On the grid, 48 states (in 36 instances) have no pool-shrinking composite of two
  moves (`n2aug_grid_k4.log`, which lists 12). In the smallest, m = 5: v_A = (2, 4, 7, 2, 0), v_B = (4, 2, 7, 0, 2), the
  state is ({1, 4}, {0, 3}) and good 2 (worth 7 to both) is pooled. Each agent holds a good it values at 0 that the
  other wants, and the step is the welfare swap of goods 3 and 4.
- *With strict values, pure augmentation looked enough* (**Claim A2**: some composite of at most two moves shrinks the
  pool). There was no failure on 1,067,080 random partial EFX₀ states with real values (`ht_n2claim.py`;
  `n2claim_m9.log`: m ≤ 9 and any k; `n2claim_m10k4.log`: m ≤ 10 and k ≤ 4). **But Claim A2 is false**
  (`attempts/k4-haxell-n2-pure-augmentation.md`); the exhaustive check below finds the rare types the samples missed.
  - How the augmentations are made, counting the first augmenting composite in the enumeration order (so these
    shares describe the steps found, not which kinds are required): a single placement in 91% of the states.
  - Otherwise, one of:
    - give one good, then place: 6.6%;
    - place, then swap two agents' goods: 1.4%;
    - place, then trade: 0.15%;
    - place, then swap with the pool: 0.12%;
    - a transfer of two or more goods (between agents, or from the pool) with a placement: 0.6% (the W4 mechanism);
    - two placements.
  - An earlier version of the script tested only the families "B's bundle grows", "A's bundle grows" and "trade,
    then place". It reported failures that the exact checkers rejected: "swap two agents' goods, then place" was
    missing. So a proof of Claim A2 must include that family.
- **Theorem N2 (computer-verified; k ≤ 4, strict values).** Let n = 2, let every agent value between one and four
  goods, let every good be valued by someone, and let each agent's values be strict (no two distinct sets of its valued
  goods have equal value). Then from every partial EFX₀ allocation with a nonempty pool, at least one of these holds:
  - a composite of at most two moves of §6 reaches a partial EFX₀ allocation with a smaller pool;
  - a single swap of a good of A's with a good of B's gives a partial EFX₀ allocation in which **both** agents are
    strictly better off.

  Hence W^sub and L^sub hold for these instances, and so does the lemma with any measure that rises when both agents
  gain.
  - *Pareto strengthening, with junk goods.* Add up to two goods valued by nobody (`ht_n2types.py JUNK=1, 2`). Then
    pool-shrinking fails at 180 and 240 states, and the misplaced swap covers only 36 and 64 of them. But **every**
    such state has a *Pareto composite* of at most two moves: the pool kept, EFX₀, one agent strictly better and
    neither worse. That is type-determined (`n2types_k4_pareto_junk{0,1,2}.log`).
  - So **P^sub holds at n = 2** for strict k ≤ 4 instances with at most two junk goods. For junk goods, only the C
    checker has re-run every class; the Pareto composites are witnesses found in Python.
  - *Why the check is complete: two lemmas (PROVED, written here).*
    - **Lemma TD (type-determinedness).** Let v and w be valuations with the same relevant sets Rᵢ, zero outside
      them, and for each agent the same strict type on Rᵢ: for disjoint nonempty S, T ⊆ Rᵢ, vᵢ(S) > vᵢ(T) iff
      wᵢ(S) > wᵢ(T), and never equality. Then for all partial allocations X and Y:
      - (a) X is partial EFX₀ under v iff under w;
      - (b) vᵢ(Yᵢ) > vᵢ(Xᵢ) iff wᵢ(Yᵢ) > wᵢ(Xᵢ), and the same for ≥.

      *Proof.* (a) The condition vᵢ(Xⱼ ∖ {h}) ≤ vᵢ(Xᵢ) compares A = (Xⱼ ∖ {h}) ∩ Rᵢ with B = Xᵢ ∩ Rᵢ, which are
      disjoint. If A = ∅ it holds for both. If A ≠ ∅ = B it fails for both, since values on Rᵢ are positive. If both
      are nonempty, the type decides it. (b) vᵢ(Yᵢ) − vᵢ(Xᵢ) = vᵢ((Yᵢ ∖ Xᵢ) ∩ Rᵢ) − vᵢ((Xᵢ ∖ Yᵢ) ∩ Rᵢ), a comparison
      of disjoint sets, with the same three cases. ∎

      So whether a state has a pool-shrinking composite, or a Pareto composite, is the same for every realization of
      the type profile. Moves do not depend on values.
    - **Lemma OR (orbit reduction).** Call goods valued by the same set of agents a class. Relabeling goods within
      their classes maps an instance to an isomorphic one, and every statement here is invariant under relabeling.
      Give each class a designated agent who values it. Under a strict type, that agent's values on the class are
      distinct, so exactly one relabeling within each class makes them increase.

      Every orbit of type profiles therefore has exactly one profile in which each designated agent's values increase
      along its class (A for the A-only and the shared goods, B for the B-only goods). Also, every pair of relevant
      sets is isomorphic to one with A-only goods first, then shared, then B-only. ∎ For n = 3 (`ht_n3types.py`) the
      designated agent of a class is the first agent valuing it, and the shapes are all multisets of patterns up to
      agent permutation (`ht_n3grid.py`).
    - The types themselves come from `k4/order_types.json` (K4.OT, CERTIFIED). For one and two goods the strict types
      are 1 and 2, written out in the script.
    With these, `ht_n2types.py` runs every strict type profile once up to Lemma OR (45,999 classes;
    `n2types_k4_theorem.log`) through `gstar_measure` (C). Every class has its partial EFX₀ states (6,639,927 in all)
    checked.
  - *The cases.* Pool-shrinking fails at exactly 20 states, one per class, all of the shape of the attempts file: each
    agent holds a misplaced good, and the swap of the two misplaced goods is the second alternative. **Two implementations agree.** The
    independent Python checker of `ht_n2claim.py` re-ran all 45,999 classes (6,208,383 partial EFX₀ states with a
    nonempty pool; `n2types_k4_fullcheck.log`) and found exactly the same 20 failing instances.
    - The second alternative at the 20 states is a witness (the swap), checked in Python against the raw definition.
      `attempts/k4_haxell_n2aug.py` replays one of them with no shared code.
  - *Not covered.* Ties (the n = 2 value grid with ties has no W^sub or L^sub stuck state, but it is a grid, not every
    weak type). Goods valued by nobody: there pure augmentation fails even with strict values. Example: m = 7,
    v_A = (0, 680, 0, 3218, 0, 2915, 400), v_B = (0, 5170, 0, 9035, 147, 3445, 1810), state ({3}, {0, 1, 2, 4, 6})
    with good 5 pooled; goods 0 and 2 are worthless to both (`wexplain_aug_n2_junk.log`). Agent B values five
    goods there, so this example has k = 5; whether junk goods break pure augmentation at k ≤ 4 is not settled. W^sub
    and L^sub still have steps there: swap good 5 for one of B's goods through the pool, then trade. k ≥ 5 in
    general.
- *So the n = 2 proof splits.*
  - For strict values and k ≤ 4: Theorem N2 (computer-verified). A written proof would exhibit the families "g to one
    agent, then a transfer, a swap or a trade" from the six blocking inequalities (the four obvious completions and
    "g alone"), plus the misplaced swap. By `ht_n2rules.py`, six rules each sometimes needed alone cover every hard
    strict state found: trade then place; g to one agent then one good or a set back; swap then place.
  - For ties: use the measure, or perturb. A perturbation argument needs care, since a step for perturbed values need
    not be one for the tied values.
  - Neither part is written.


## 7. W on large instances: the stranded welfare maxima, the S′ family, and n = 6–8 (burst 2, continued)

For instances too large to enumerate, W is checked at given states by `ht_wlocal.py`. Its augmenting search is
exact. A placement plus one rotation leaves the old bundles, one of them enlarged by g, permuted along a cycle, and
agent i's EFX₀ condition then depends only on the bundle i receives: vᵢ(b) ≥ max over the other bundles b′ of
τᵢ(b′). So the EFX₀ re-assignments are the perfect matchings of an agent–bundle compatibility graph, and "a placement
and one rotation" is a directed cycle through every agent that cannot keep its own bundle (depth-first search). The
welfare-raising search covers one or two good moves and one rotation, not rotation plus a move, so a state with no
step found would still need an exhaustive check (none occurred).
- `ht_wwalk.py` repeats W steps from a state to a complete allocation, re-checking each step (EFX₀, strict decrease
  of (|pool|, −welfare)).
- `ht_wsample.py` samples states on random instances: the empty allocation, the serial-dictatorship picks, and
  random EFX₀-preserving walks from them. It checks W at each and walks to completion.

**The stranded welfare maxima of CH-F** (kgen-charity, `kgen/charity.md` §6; instances copied verbatim into
`ext_instances.py`). In both instances the maximum welfare over partial EFX₀ allocations (198 at k = 4, n = 9, m = 14;
484 at k = 3, n = 12, m = 17) is attained only with goods 6 and 7 unallocated. W cannot raise welfare there, so it
must shrink the pool within two moves. It does (`wlocal_chf.log`): source s₀ gives its good 1 (worth 1 to it) to
source s₁, which values it at 0, and takes g₀ = 6, which it values at 0. That leaves one good out at welfare 197
(resp. 483), exactly the maxima with at most one good out. Both W-walks then complete in one more step
(`wwalk_chf.log`). The step lowers s₀'s value, which is the kind of move P1 requires.

**The families S(σ, k), S′(σ, k)** (built by `ext_sprime.py`, copied from `kgen/charity/stuck_family.py`; their
stranded states are CKMS stopping states with σ − 1 goods out, default values): for σ = 2–5 and k = 3, 4 (n ≤ 40,
m ≤ 49), every W-walk from the stranded state completes, one augmentation per step (`wwalk_sprime.log`).

**Random instances with n = 6–8** (`ht_wsample.py`, `wsample_*.log`; 8 start states per instance: the empty
allocation, serial-dictatorship picks, and random EFX₀-preserving walks from them, up to 30 moves):
| n, m, k, values | instances | states checked | W step found: placement / + move / + rotation / welfare | walks completed |
|---|---|---|---|---|
| 6, 10, 4 | 400 | 3,074 | 2,090 / 765 / 210 / 9 | 3,074 |
| 6, 11, 5 | 400 | 3,104 | 2,212 / 680 / 210 / 2 | 3,104 |
| 7, 12, 4 | 300 | 2,359 | 1,756 / 501 / 98 / 4 | 2,359 |
| 7, 13, 5 | 300 | 2,349 | 1,786 / 457 / 103 / 3 | 2,349 |
| 8, 14, 4 | 200 | 1,585 | 1,264 / 280 / 41 / 0 | 1,585 |
| 8, 15, 5 | 200 | 1,588 | 1,267 / 267 / 54 / 0 | 1,588 |
| 6, 10, 4, values 1–4 (ties) | 300 | 2,281 | 1,674 / 511 / 95 / 1 | 2,281 |
| 7, 12, 5, values 1–4 (ties) | 300 | 2,347 | 1,790 / 430 / 127 / 0 | 2,347 |

In all, 18,687 states: every one has a W step, and every walk reaches a complete EFX₀ allocation. These are
sampled states, so this is weaker evidence than the exhaustive checks of §6. Random states rarely need more than a
placement and one other move.
