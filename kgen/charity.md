# Bounded charity in terms of relevant goods (CH(k))

Workstream `proof/kgen-charity` (branch `claude/kgen-charity`, draft PR #105). Scripts: `kgen/charity/`; logs:
`results/kgen_charity/`. Everything called evidence below is evidence only (PROMPT.md §5 rule 3). No ledger row is
changed here; the coordinator integrates.

## Status (end of burst 1)

| item | statement | status | artifact |
|---|---|---|---|
| CH-A | every additive instance with ≤ k relevant goods per agent has a partial EFX₀ allocation with strong charity and \|P\|(\|P\| − 1) ≤ e(k − 2)n, i.e. \|P\| ≤ 1 + √(e(k−2)n); \|P\| = 0 for k ≤ 2 | PROVED (written proof, §3; lemmas checked on every stopping state computed) | §3, `chlib.py`, `ch_screen.log` |
| CH-B | if every good is valued by at most d agents (any k), the same with \|P\| < e·d, independent of n and k | PROVED (written proof, §3) | §3 |
| CH-C | at every CKMS stopping state, \|P\| < σ ≤ (k − 2) · min_{g∈P} \|V(g)\| (σ = number of sources, V(g) = valuers of g) | PROVED | §2, Lemma CH4 |
| CH-D | for every σ ≥ 2 there is an instance with k = 3 and a state with σ − 1 unallocated goods at which no CKMS rule applies under any choice of champion (n ≈ 1.5σ²) | PROVED (construction checked by the raw definitions for σ ≤ 7, k = 3, 4) | §4, `stuck_family.py`, `stuck_family_k*.log` |
| consequence | CKMS's rules (and so the rainbow-cycle reduction) cannot give charity independent of n, even at k = 3, where complete EFX₀ is a theorem: CH-A is tight up to a constant factor for the method | PROVED (from CH-D) | §4 |
| PM(k) | every Pareto maximum (P1's hypothesis) leaves at most f(k) goods out; PM(k) ⇒ CH(k) | CONJECTURE (f(4) ≥ 1 by GM4-E) | §5, `pm_*.log` |
| least charity | 0 on every instance tested, k = 3..8 | EVIDENCE (this is TARGET_k on random data) | §1, `least_*.log` |

So route (b) of the brief is settled in both directions: the rainbow-cycle method works with genuine zeros and gives
exact EFX₀ with O(√(kn)) charity, but no better, because its stopping states can leave Θ(√n) goods out at k = 3. An
n-independent f(k) needs moves outside CKMS's U0/U1/U2: for instance a global potential (Pareto maxima, §5), which
the data do not refute.

## 0. Statement and conventions

Additive valuations v_i ≥ 0, R_i = {g : v_i(g) > 0}, |R_i| ≤ k; V(g) = {i : v_i(g) > 0}, the valuers of g. A *state*
is a partial allocation X = (X_1, …, X_n) with pool P = M ∖ ∪X_i.
- *EFX₀*: v_i(X_i) ≥ v_i(X_j ∖ h) for all i ≠ j and h ∈ X_j. Agent i *strongly envies* a set B if
  v_i(B ∖ h) > v_i(X_i) for some h ∈ B.
- *Strong charity*: v_i(P) ≤ v_i(X_i) for every i (Chaudhury–Kavitha–Mehlhorn–Sgouritsa, "CKMS"). *Weak charity*:
  v_i(g) ≤ v_i(X_i) for every i and g ∈ P.
- *Envy graph* G_X: i → j iff v_i(X_j) > v_i(X_i). Sources: in-degree 0; S = the set of sources, σ = |S|; C(s) = the
  agents reachable from s (s included).

**CH(k).** There is f(k) such that every additive instance with |R_i| ≤ k for all i has an EFX₀ state with strong
charity and |P| ≤ f(k). f(2) = 0 (serial dictatorship, L2), f(3) = 0 (LEDGER row T); TARGET₄ is f(4) = 0.

**Literature used** (read for this note; the agent-side survey `research_notes/EFX literature from the agent side/
agent_count_side.md` §4 covers the rest):
- CKMS, arXiv 1907.04596v3, §2 (pp. 8–12) read: Algorithm 1–3, Lemma 2 (cycle rotation), Definition 3 (most envious
  agent), Lemmas 4–7 (rules U0, U1, U2), Theorem 8 (EFX, strong charity, |P| < number of sources). Their EFX is the
  all-goods form, which for nonnegative additive values is EFX₀; nothing in §2 assumes positive values.
- Chaudhury–Garg–Mehlhorn–Mehta–Misra, arXiv 2103.01628, §4 (pp. 11–14) read: the group champion graph and the
  reduction from charity to the rainbow cycle number R(d), for (1 − ε)-EFX.
- Sivashankar, arXiv 2607.27455v1, §1–3 and §5 (pp. 1–7) read: Theorem 3, the packing inequality
  (k − 1)! Σ|V_i| ≤ Π|V_i| for k-partite digraphs with the in-neighbour condition and no rainbow cycle, hence
  R(d) < ed. Its proof (an injection from (permutation, terminal vertex) pairs to transversals) was re-derived here.
- BCFF (n − 2, additive), Mahara (n − 2, monotone), Ghosal et al. (t types: t − 2): as recorded in the survey, not
  re-read. The survey found no charity bound in terms of relevant goods per agent or valuers per good.

## 1. Kill-or-confirm data

- **Least charity** (`ch_least.py`, SAT with a cardinality bound on the pool; encoding checked against the raw
  definitions on 36,000 fixed assignments, `enc_check.log`, 0 mismatches): 0 on every instance, see the table in the
  status block. This is the expected answer (EFX₀ is believed to exist), not information about CH(k).
- **Where CKMS's rules stop** (`ch_ckms.py`, `ch_screen.py`; exact rules U0/U1/U2 from the empty allocation and from
  serial-dictatorship picks, random tie-breaks; a nonzero stop is then continued with *every* champion choice, the
  "robust" stop):
  - random instances, k = 3, 4, 6, 8, n ≤ 6: essentially always 0 (one robust stop with one good out in 4,000 runs);
  - the 168 curated k = 4 instances (the DE4 screen set): robust stops with one good out on 28 instances (GM4, ls-*,
    hall-bt4, …, including n = 2 and n = 3 instances), never two (`ch_screen.log`, 6,720 runs).
  - So CKMS's own potential (welfare) already strands goods at k = 4, which is P1's phenomenon (K4.SDC.P1).
- **Structure of the stops** (checked on every stop by `chlib.stuck_report`): every source holds ≥ 2 goods, every
  champion values the pool good and a good of the source's bundle, and is not reachable from that source
  (Lemmas CH1–CH4 below). The pool goods are the ones every source's champions reach from elsewhere.

## 2. Lemmas on stopping states

A *champion option* of a set B is a pair (Z, t): Z ⊆ B is an inclusion-wise minimal envied subset (some agent envies
Z, nobody envies Z ∖ h for any h ∈ Z) and t envies Z. CKMS's "most envious agent" picks one option by a tie-break.
A *stopping state* (for a fixed champion selection c(s, g)) is an EFX₀ state with acyclic G_X to which none of U0
(add a pool good to some bundle keeping EFX₀), U1 (someone envies P) and U2 (a cycle as in CKMS Algorithm 2, with the
selected champions) applies. A *robust stopping state* is one where U2 applies for no selection.

**Lemma CH0 (envied bundles cannot grow).** If w envies X_i, then w strongly envies X_i ∪ {g} for every good g.
*Proof.* Let h be w's least valued good of X_i ∪ {g}. If h = g, then (X_i ∪ g) ∖ h = X_i, which w envies. Otherwise
v_w(h) < v_w(g) — or v_w(h) = v_w(g) and we may take h = g — and v_w((X_i ∪ g) ∖ h) ≥ v_w(X_i) > v_w(X_w). ∎
So U0 can only add to sources.

**Lemma CH1 (locality of U0).** Let X be EFX₀ with weak charity, s a source, g ∈ P.
1. If t strongly envies X_s ∪ g, then t ≠ s, v_t(g) > 0, t values a good of X_s, and |X_s| ≥ 2.
2. For every champion option (Z, t) of X_s ∪ g: g ∈ Z, every good of Z is in R_t, and ∅ ≠ Z ∖ g ⊆ X_s.

*Proof.* (1) Strong envy gives h ∈ X_s ∪ g with v_t((X_s ∪ g) ∖ h) > v_t(X_t). h ≠ g, since v_t(X_s) ≤ v_t(X_t) (s is
a source). So v_t(X_s ∖ h) + v_t(g) > v_t(X_t) ≥ max(v_t(X_s), v_t(g)), the last by weak charity. Hence
v_t(g) > v_t(h) ≥ 0, and v_t(X_s ∖ h) > 0: t values a good of X_s other than h, so |X_s| ≥ 2. (2) If g ∉ Z then
Z ⊆ X_s is envied by t, against v_t(X_s) ≤ v_t(X_t). A good of Z worth 0 to t could be removed with t still envying,
against minimality. Z = {g} is not envied, by weak charity. ∎

So a pool good can be blocked at a source only by its own valuers, and only through goods they value in that source's
bundle. This is the "local" structure of route (a). With CKMS Lemma 4(b), |Z| ≤ |X_s| when U0 fails at (s, g).

**Lemma CH2 (sources of a stopping state).** At a stopping state with P ≠ ∅, every source holds at least two goods,
and for every g ∈ P its bundle contains a good valued by some valuer of g other than s.
*Proof.* U1 fails, so strong charity, hence weak charity, holds. U0 fails at (s, g), so someone strongly envies
X_s ∪ g; apply Lemma CH1(1). ∎

**Lemma CH3 (champions of a stopping state).** At a stopping state, for every s ∈ S and g ∈ P, the selected champion
t = c(s, g) satisfies: t ∈ V(g); t ≠ s and t ∉ C(s); R_t meets X_s, X_t and P.
*Proof.* X_s ∪ g is strongly envied (U0 fails), hence envied, so an option exists. CH1(2) gives t ∈ V(g) and
R_t ∩ X_s ≠ ∅. If t ∈ C(s), the one-term cycle (s_0, g_0) = (s, g), t_1 = t ∈ C(s_0) satisfies U2's precondition.
v_t(X_t) ≥ v_t(g) > 0 by weak charity, so R_t meets X_t. ∎

**Lemma CH4 (counting).** At a stopping state with P ≠ ∅, for every g ∈ P,
σ ≤ Σ_{t ∈ V(g)} μ_t, where μ_t = |{s ∈ S ∖ {t} : R_t ∩ X_s ≠ ∅}| ≤ |R_t| − 2.
Hence σ ≤ (k − 2)|V(g)|, and with CKMS Theorem 8, |P| ≤ σ − 1 ≤ (k − 2) · min_{g ∈ P} |V(g)| − 1.
*Proof.* s ↦ c(s, g) maps S into V(g), and c(s, g) ≠ s values a good of X_s (CH3), so t receives at most μ_t
sources. R_t contains g ∈ P, a good of X_t, and one good of each bundle X_s counted in μ_t; these bundles are
pairwise disjoint, differ from X_t (s ≠ t) and from P. So |R_t| ≥ 2 + μ_t. ∎

**Corollary CH4′.** k ≤ 2: every stopping state is complete, so CKMS's algorithm alone proves f(2) = 0. k = 3: a
stopping state leaves fewer goods out than any pool good has valuers; if some pool good has a single valuer, it is
complete.

**Lemma CH5 (shortest rainbow cycles are executable).** Let D be the *source digraph*: vertices S, and an edge
s →_g s′ (colour g ∈ P) whenever some champion option (Z, t) of X_s ∪ g has t ∈ C(s′). A cycle of D is *rainbow* if
its vertices and its colours are distinct. If D has a rainbow cycle, take a shortest one,
(s_0, g_0), …, (s_{ℓ−1}, g_{ℓ−1}) with options (Z_i, t_{i+1}), t_{i+1} ∈ C(s_{i+1}). Then the agents t_1, …, t_ℓ are
distinct and any envy paths π_i from s_i to t_i are pairwise vertex-disjoint; so U2 applies along it and gives an
EFX₀ state in which every agent on the paths strictly gains (CKMS Lemma 7).
*Proof.* If π_a and π_b (a ≠ b) share a vertex u, then t_b is reachable from u, hence t_b ∈ C(s_a). The option
(Z_{b−1}, t_b) of X_{s_{b−1}} ∪ g_{b−1} then gives an edge s_{b−1} → s_a, and s_a → s_{a+1} → ⋯ → s_{b−1} → s_a is a
rainbow cycle of length (b − a) mod ℓ ∈ [1, ℓ − 1], shorter. Equal t's are a special case (they share t). ∎

CKMS's Lemma 6 produces such a cycle with disjoint paths by construction, and CKMS's Lemma 7 uses disjointness
implicitly; CH5 says that any rainbow cycle of D can be shortened to an executable one, which is what the
rainbow-cycle reduction needs. (Implemented: `chlib.shortest_rainbow`, `chlib.apply_u2`, which asserts disjointness.)

**Lemma CH6 (Pareto maxima are robust stopping states).** If X is EFX₀, no EFX₀ state Y has v_i(Y_i) ≥ v_i(X_i) for
all i with strict inequality for some i, and none with the same values allocates more goods, then X is a robust
stopping state; in particular it has strong charity.
*Proof.* A cycle rotation (CKMS Lemma 2), U1 (Lemma 5) and U2 (Lemma 7, with CH5 for any option) each give an EFX₀
state that is weakly better for all and strictly better for some; U0 gives one with values ≥ and one more good. ∎
The same holds for a welfare maximum with the fewest unallocated goods.

## 3. Exact charity from the rainbow cycle number (Theorems CH-A, CH-B)

**Proposition CH-R.** At a stopping state, fix for each agent a an assigned source σ(a) with a ∈ C(σ(a)) (any
choice). Let Q_g = {c(s, g) : s ∈ S} and build the |P|-partite digraph Γ with parts V_g = {g} × σ(Q_g) and an edge
(g, s₁) → (h, s₂) iff σ(c(s₂, g)) = s₁. Then every vertex of V_h has an in-neighbour in V_g for every g ≠ h, and Γ has
no rainbow cycle. So by Sivashankar's Theorem 3, with p = |P| and n_g = |V_g| ≤ |Q_g| ≤ |V(g)|,

    (p − 1)! · Σ_g n_g ≤ Π_g n_g.

*Proof.* (h, s₂) has the in-neighbour (g, σ(c(s₂, g))) ∈ V_g: the champion exists because U0 fails at (s₂, g).
A rainbow cycle (g_1, s_1) → (g_2, s_2) → ⋯ → (g_ℓ, s_ℓ) → (g_1, s_1) (distinct g's) means
c(s_{i+1}, g_i) ∈ C(s_i), i.e. edges s_{i+1} →_{g_i} s_i of D, so a closed walk in D with distinct colours. Its
vertices may repeat; a shortest closed sub-walk between two visits of the same vertex is a rainbow cycle of D, and by
CH5 U2 applies, contradicting stopping. (This is CGMMM's Lemma 14 with ε = 0: "valuable" becomes "positively
valued", which is what keeps the parts small.) ∎

**Theorem CH-B (charity bounded by valuers per good).** If every good is valued by at most d agents, every stopping
state — so the output of CKMS's algorithm from the empty allocation — has |P| < e·d (|P| ≤ R(d)), whatever n and k.
*Proof.* n_g ≤ d for every part, and Sivashankar's Theorem 3 gives p! ≤ d^{p−1}, hence p < ed. ∎
For d = 2 this gives |P| ≤ 2, weaker than the known complete EFX₀ on multigraphs; for d ≥ 3 it is, as far as the
survey found, new. In (p, q) language (`proofs/pq_bounded.md`) it is a charity bound for (d, ∞)-bounded instances.

**Theorem CH-A (charity bounded by relevant goods per agent).** If every agent values at most k goods, every
stopping state has p(p − 1) ≤ e(k − 2)n, so |P| ≤ 1/2 + √(e(k − 2)n + 1/4) = O(√(kn)); and |P| = 0 when k ≤ 2.
*Proof.* A champion t ∈ Q_g values g, a good of X_t and a good of X_s for a source s ≠ t (CH3), so it values at most
k − 2 pool goods and lies in at most k − 2 sets Q_g. Hence Σ_g n_g ≤ Σ_g |Q_g| ≤ (k − 2)n. By AM–GM,
Π n_g ≤ (Σ n_g / p)^p, so the packing inequality gives (p − 1)! p^p ≤ (Σ n_g)^{p−1}; with (p − 1)! ≥ ((p − 1)/e)^{p−1},
Σ n_g ≥ ((p − 1)/e) p^{p/(p−1)} ≥ p(p − 1)/e. For k ≤ 2 use CH4′. ∎

Together with CKMS: |P| ≤ min{σ − 1, (k − 2) min_g |V(g)| − 1, 1/2 + √(e(k − 2)n + 1/4), R(max_g |V(g)|)}.
For exact EFX the best general charity is n − 2 (BCFF, Mahara, as recorded in the survey); CH-A is sublinear for
k = o(n), and CH-B is n-independent. Neither statement was found in the surveyed literature; the
rainbow-cycle line states its results for (1 − ε)-EFX only, because without sparsity "valuable" needs ε > 0.

## 4. The method cannot do better: stopping states with Θ(√n) goods out at k = 3 (Proposition CH-D)

**Construction S(σ, k)** (σ ≥ 2, k ≥ 3; `stuck_family.py`). Pool goods g_1, …, g_{σ−1}.
- Source s_j (j ∈ Z_σ) holds {x_j, x′_j}, values x′_j at 1 and its children (below) at 2.
- For every pool good g and every j, a champion c(g, j) holds {y_{g,j}} and values y_{g,j} at 10, x_j at 6, g at 6.
- The champions c(·, j − 1) hang below s_j in a tree: each internal node is a relay holding one good that its parent
  values at 2; a relay values its children's goods at 2 and nothing else; the source has ≤ k − 1 children, a relay ≤ k.

Every agent values at most k goods (champions 3), every good is valued, n = σ + σ(σ − 1) + (number of relays)
≤ 1.5σ² + O(σ) at k = 3.

**Proposition CH-D.** The state of S(σ, k) is EFX₀ with strong charity, leaves σ − 1 goods out, and is a robust
stopping state.
*Proof.*
1. *Envy graph.* Champions envy nobody (v(X_{s_j}) = 6 ≤ 10); relays and sources envy exactly their children. So G_X
   is the forest of trees, acyclic, its sources are s_0, …, s_{σ−1}, and C(s_j) is s_j's tree, which contains the
   champions c(·, j − 1) and no other champion.
2. *EFX₀ and charity.* The only bundles with two goods are {x_j, x′_j}; their valuers other than s_j are the
   champions c(·, j), who see 6 ≤ 10. Pool goods are valued only by champions, each valuing one pool good at 6 ≤ 10.
3. *U0, U1.* By CH0 only sources can take a good. X_{s_j} ∪ g is strongly envied by c(g, j): removing x′_j, worth 0 to
   it, leaves 12 > 10. U1 fails by 2.
4. *U2, every option.* An envier of a subset of {x_j, x′_j, g} values one of these goods: s_j (values only x′_j, at
   its own value 1), c(g′, j) (only x_j, 6 ≤ 10, when g′ ≠ g), c(g, j″) (only g, when j″ ≠ j), or c(g, j). So the
   only option is ({x_j, g}, c(g, j)), and c(g, j) ∈ C(s_{j+1}) only. The source digraph D has edges s_j →_g s_{j+1}
   for all g and no others; its only cycle has length σ and needs σ distinct colours, but there are σ − 1. ∎

Checked for σ = 2..7 at k = 3 and σ = 2..6 at k = 4 by the raw definitions, `chlib.u0_moves`, the U2 search over all
options, and a run of CKMS with all options that makes no move (`stuck_family_k3.log`, `stuck_family_k4.log`).

**Consequences.**
- At every fixed k ≥ 3 the bound of CH-A is tight up to a constant factor *for stopping states*: σ − 1 ≥ √(n/1.5) − 2
  against CH-A's √(e(k − 2)n) + 1. Analysing the stopping states of U0/U1/U2 (with any tie-break, and with the
  rainbow-cycle number in any form) cannot prove CH(k), not even CH(3).
- The states are not Pareto maxima: one SAT improvement completes each of S(2..4, 3) (`chlib.improve`, recorded in
  §5). So the obstruction is to the *local* rule set, not to value-monotone methods as such.
- Route (a) (charge the charity to the valuers of the unallocated good) is exactly Lemma CH4, and S(σ, 3) shows that
  charge is tight: there each pool good has σ valuers, one per source, and σ ≤ (k − 2)|V(g)| holds with equality.
  (`attempts/kgen-charity-local-rules.md`.)

## 5. Global potential: Pareto maxima (Question PM)

**Conjecture PM(k).** Every Pareto maximum (an EFX₀ state that no EFX₀ state Pareto-dominates and that allocates the
most goods for its value vector; the hypothesis of K4.SDC.P1) leaves at most f(k) goods out.

PM(k) implies CH(k) with the same f (a Pareto maximum exists and has strong charity by CH6). P1 is PM with f = 0;
it is refuted at k = 4 (GM4-E), so f(4) ≥ 1 if PM(4) holds.

Data (`pm_search.py`, exact per instance: `chlib.pm_with_pool` runs a CEGAR over Pareto maxima; it agrees with the
P1 replay on GM4-E: five Pareto maxima, one leaves one good out, none leaves two):
- the 168 curated k = 4 instances: 20 have a Pareto maximum leaving one good out (`pm_screen_1.log`), none has one
  leaving two (`pm_screen_2.log`);
- random instances with k = 3, n ≤ 5 (600, `pm_rand_k3.log`, `pm_core_k3.log`): no Pareto maximum leaves a good out;
- the families S(2..4, 3) of §4: (see `pm_family_1.log`).

## 6. Open

1. PM(4) with f(4) = 1, or a Pareto maximum leaving two goods out at k = 4. The structure lemmas CH1–CH5 apply
   (CH6); the data say the global condition kills the S(σ, k) states. Which Pareto improvement kills them is the
   first thing to understand.
2. P1 at k = 3 (PM(3) with f = 0): no counterexample in the data. It would be a value-monotone proof of TARGET.
3. Combine CH-B with relevant goods: high-degree pool goods are the only obstacle to an n-independent bound in CH-A.
