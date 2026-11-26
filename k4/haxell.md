# Haxell-type alternating trees for k = 4 (workstream proof/k4-haxell)

Branch `claude/k4-haxell`. Angle (k4/attack_log.md): SD-C and OC₁ say that *some* serial-dictatorship order works, but
no simple rule or local move selects it, and no value-based potential can work (K4.SDC.P1). In restricted Santa Claus,
Haxell's hypergraph Hall theorem is made algorithmic by alternating trees whose termination is a lexicographic
signature of the tree's layers, not agents' values. This note records (1) exactly what those papers say, at the level
read; (2) a translation to EFX₀ states; (3) what the resulting searches do on the project's data. Evidence below is
evidence only (PROMPT.md §5 rule 3).

## Status

(Updated at the end of each burst.)

**Burst 1 (2026-11-26).** Evidence only; nothing here changes a ledger row.
- *Literature* (§1): Annamalai (Haxell's condition made algorithmic), AKS and Davies–Rothvoss–Zhang read in full;
  Haxell 1995 and Asadpour–Feige–Saberi not accessed.
- *The literal translation fails, at n = 2* (§3.2, `attempts/k4-haxell-single-swap-collapse.md`). A tree whose
  collapses are single local moves keeps every partial EFX₀ allocation EFX₀, as AKS keeps every player matched. But
  the graph G* of partial EFX₀ allocations under single local moves has **traps**: components without a complete
  allocation. The smallest has n = 2, m = 5. Envy blocking is not resource overlap: a blocker's repair is often safe
  only *together with* the parent edge.
- *Two moves at once suffice on every instance tested* (§3.4). No partial EFX₀ allocation of ~17,000 instances
  (k = 3, k = 4 and general k; n ≤ 4, m ≤ 8; screen, suite, random cores, random instances) is a trap once composite
  moves of two local moves are allowed. Single-move traps occur at k = 4 and at general k, **never at k = 3** (6,100
  random k = 3 instances). No serial-dictatorship start is a trap, and P1's stuck state of GM4-E is not one either:
  value-lowering moves lead out of it.
- *One-shot augmentation is not local* (§3.5): some partial EFX₀ allocations need more than four goods to change
  holder before a pool good can be placed (n = 2 at k = 4; n = 3 at k = 3; 23 of 109 screen instances). So the
  augmentation must be a *sequence* of moves, which is what an alternating tree supplies.
- *Trees* (§3.3): from every serial-dictatorship start on the screen set (n ≤ 5, 4,069 starts), a sequence of
  victim-free moves reaches a complete EFX₀ allocation (complete search, Model G: 0 stuck). The AKS-style trees
  find one from all but 38 (single-move collapses) or 30 (composite collapses) starts. The signature decreased at
  every one of the ~2,700 steps checked.
- *Candidate statement for a proof* (§4): **CONN₂**, every partial EFX₀ allocation reaches a complete one through
  partial EFX₀ allocations, each step reassigning at most two goods or trading two bundles, with the pool never
  growing. It implies TARGET₄ (start from the empty allocation) and mentions no values. Its k = 3 form with single
  moves (CONN₁) has no counterexample.
- *Next*: a tree that is complete on the data (alternatives per layer, composite collapse of a branch), run on the
  suite, the logged profiles and n = 6–9; an adversarial climb for a radius-2 trap; a proof of CONN₁ for n = 2 and of
  the composite collapse invariant.

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

Every trap found has one pooled good (three general-k instances at n = 2, m = 6 have traps with two). No
serial-dictatorship start is a trap. **The smallest trap** (c4x-n2m5-base-needs): both agents value the shared goods
2, 3, 4 at 3, 4, 8, and each its private good (0, resp. 1) at 2. The state ({0, 2}, {1, 3}), with good 4 pooled, is
partial EFX₀, but whoever receives 4 is envied, and no single other move helps. Moving 4 to agent 0 and 2 to agent 1
together gives ({0, 4}, {1, 2, 3}). P1's stuck state of GM4-E (`k4/sdc.md` §1) is not a trap: 2,448 partial EFX₀
allocations, 15 complete, no trap.

### 3.5 Augmentation radius

`ht_aug.py`: for every partial EFX₀ allocation with a nonempty pool, the fewest goods whose holder must change to
reach a partial EFX₀ allocation with a smaller pool (all reassignments of d goods, d ≤ 4).
| data | instances | states with radius 1 / 2 / 3 / 4 / > 4 | log |
|---|---|---|---|
| random n = 2, m = 5, k = 3 | 3,000 | 183,336 / 26,201 / 3,478 / 162 / 0 | `aug_gen_n2m5k3.log` |
| random n = 2, m = 5, k = 4 | 3,000 | 166,419 / 32,459 / 3,627 / 117 / 15 | `aug_gen_n2m5k4.log` |
| random n = 2, m = 5, k = 5 | 3,000 | 169,046 / 39,265 / 4,024 / 40 / 2 | `aug_gen_n2m5k5.log` |
| random n = 2, m = 6, k = 6 | 2,000 | 296,244 / 59,766 / 3,942 / 9 / 0 | `aug_gen_n2m6k6.log` |
| random n = 3, m = 6, k = 3 | 800 | 219,625 / 38,257 / 31,326 / 442 / 5 | `aug_gen_n3m6k3.log` |
| random n = 3, m = 6, k = 4 | 800 | 195,824 / 42,130 / 33,819 / 761 / 23 | `aug_gen_n3m6k4.log` |
| random k = 4 core profiles, n ≤ 3, m ≤ 7 | 1,346 | 376,918 / 63,369 / 46,905 / 960 / 12 | `aug_cores_n3.log` |
| screen, n ≤ 4, m ≤ 7 | 109 | 80,997 / 12,744 / 15,221 / 1,326 / 131 | `aug_screen.log` |

So no bounded-radius *one-step* augmentation lemma holds ("AUG_r" is false for r ≤ 4, even at k = 3), while
*multi-step* augmentation through radius-2 moves never fails (§3.4). This is the division of labour in Haxell's
proof: the augmenting structure is a sequence of swaps, each local, organized by the tree.
