# Haxell-type alternating trees for k = 4 (workstream proof/k4-haxell)

Branch `claude/k4-haxell`. Angle (k4/attack_log.md): SD-C and OC₁ say that *some* serial-dictatorship order works, but
no simple rule or local move selects it, and no value-based potential can work (K4.SDC.P1). In restricted Santa Claus,
Haxell's hypergraph Hall theorem is made algorithmic by alternating trees whose termination is a lexicographic
signature of the tree's layers, not agents' values. This note records (1) exactly what those papers say, at the level
read; (2) a translation to EFX₀ states; (3) what the resulting searches do on the project's data. Evidence below is
evidence only (PROMPT.md §5 rule 3).

## Status

(Updated at the end of each burst.)

- Burst 1: literature read (§1); model and code in progress.

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
