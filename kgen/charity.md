# Bounded charity in terms of relevant goods (CH(k))

Workstream `proof/kgen-charity` (branch `claude/kgen-charity`, draft PR #105). Scripts: `kgen/charity/`; logs:
`results/kgen_charity/`. Everything called evidence below is evidence only (PROMPT.md §5 rule 3). No ledger row is
changed here; the coordinator integrates.

## Status (end of burst 3)

| item | statement | status | artifact |
|---|---|---|---|
| CH-A | every additive instance with ≤ k relevant goods per agent has a partial EFX₀ allocation with strong charity and \|P\|(\|P\| − 1) ≤ e(k − 2)n, so \|P\| ≤ 1 + √(e(k − 2)n); \|P\| = 0 for k ≤ 2 | PROVED (written proof, §3; lemmas asserted on every stopping state computed) | §2–§3, `chlib.py` |
| CH-B | if every good is valued by at most d agents (any k, any n), the same with \|P\| < e·d | PROVED (written proof, §3) | §3 |
| CH-M | CH-A (with k − 1 for k − 2) and CH-B for monotone valuations, R_i the support of v_i | PROVED (written proof only) | §3, Remark CH-M |
| CH-C | at every CKMS stopping state, \|P\| < σ ≤ (k − 2) · min_{g∈P} \|V(g)\| | PROVED | §2, Lemma CH4 |
| CH-D | for every σ ≥ 2: a k = 3 instance and a state leaving σ − 1 goods out at which no CKMS rule applies under any champion choice (n ≈ 1.5σ²) | PROVED (written proof; checked for σ ≤ 7, k = 3, 4) | §4, `stuck_family.py`, `stuck_family_k*.log` |
| CH-E | for every σ ≥ 2 and k ≥ 3: a Pareto maximum (P1's hypothesis) leaving σ − 1 goods out, n = O(σ²) | PROVED (written proof; exhaustive check without SAT for σ ≤ 4, SAT for σ ≤ 7) | §5, `refute_pm.py`, `refute_pm_k*.log`, `pm_family_sat.log` |
| P1 threshold | P1 (K4.SDC.P1: Pareto maxima are complete) holds for k ≤ 2 and fails at k = 3 (n = 4, m = 7, every agent values exactly 3 goods) | PROVED for k ≤ 2 (CH6 + CH4′); REFUTED at k = 3 (CH-E with σ = 2; brute force over all 5⁷ partial allocations) | §5, `refute_pm_k3.log` |
| PM(k) | Pareto maxima leave ≤ f(k) goods out | REFUTED for every k ≥ 3 and every f (CH-E) | §5 |
| W(k, f) | the welfare maximum, among those with the fewest unallocated goods, leaves ≤ f goods out (§6 for the exact statement); W(k, f) ⇒ CH(k) | f = 0 REFUTED at k = 3 (n = 4, m = 7) and k = 4 (GM4-G); **f = 1 REFUTED at k = 3 and k = 4** (CH-F: n = 12, m = 17 and n = 9, m = 14, integer values; each verified by SAT and by MILP); f ≥ 2: §6 | §6, `w_brute.log`, `w_counterexample*.log`, `attempts/kgen-charity-welfare-maxima.md` |
| W small n | no welfare maximum strands a good for n = 3, k = 3; none strands two for n = 3, k = 3, 4 and n = 4, k = 3 | exhaustive by one implementation (z3 CEGAR over real values, all m ≤ nk + n by Lemma W0) | §6, `w_synth_n*.log` |
| DU | an instance whose incidence graph has ≥ 2 components with agents has a complete EFX₀ allocation | PROVED (written proof; recipe checked on 2,000 random unions and on copies of the stranded instances) | §3, Prop. DU, `union_dump.log` |
| CH-B′ | k = 4 and every good valued by ≤ d agents: ≤ 2, 4, 6 goods out for d = 2, 3, 4 (3, 4 if R(3) = 3, R(4) = 4 [unverified]) | PROVED (from CH-B, CH-C, the packing inequality) | §7 |
| least charity | 0 on every instance tested, k = 3..8, n ≤ 9 | EVIDENCE (this is TARGET_k on random data) | §1, `least_*.log` |

**Conclusion so far.** The rainbow-cycle method works with genuine zeros and gives *exact* EFX₀ with O(√(kn))
charity (CH-A), and charity < e·d when goods have ≤ d valuers (CH-B, independent of n and k); both look new and extend
to monotone valuations (CH-M). Disconnected instances never need charity (DU). But an n-independent f(k) cannot come
from CKMS's rules (CH-D), from Pareto-maximality (CH-E), or — for f ≤ 1 — from welfare maximality (CH-F): each can
strand goods at k = 3, where complete EFX₀ is a theorem, and the first two strand Θ(√n). Value-monotone methods work
exactly up to k = 2 (CH-E′). A proof of CH(k), k ≥ 3, must lower some agent's value at some step, as LB⁺ does at
k = 3. At k = 4 the only n-independent bounds proved are for instances whose goods have few valuers (CH-B′); the open
case is connected instances whose unallocated goods all have many valuers, which is the shape of S, S′ and CH-F.

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

- **Least charity** (`ch_least.py`: SAT with a cardinality bound on the pool; the encoding is checked against the raw
  definitions on 36,000 fixed assignments, `enc_check.log`, 0 mismatches; every witness is re-checked by the raw
  definitions). 2,800 random instances, least charity 0 on every one:

  | log | instances | n | relevant goods per agent | values |
  |---|---|---|---|---|
  | `least_k4.log`, `least_k4_small.log` | 600 + 600 | 3–9 | 3–4 | 1..100; 1..6 (ties) |
  | `least_k4_hot.log` | 400 | 3–9 | 2–4, a few goods valued by many agents | 1..100 |
  | `least_k6.log`, `least_k6_small.log` | 400 + 400 | 3–8 | 3–6 | 1..100; 1..6 |
  | `least_k8.log`, `least_k8_hot.log` | 200 + 200 | 3–7 | 4–8; 2–8 with hot goods | 1..100 |

  This is the expected answer (EFX₀ is believed to exist), not information about CH(k): the least charity is 0
  exactly when a complete EFX₀ allocation exists.
- **Where CKMS's rules stop** (`ch_ckms.py`, `ch_screen.py`): the exact rules U0/U1/U2, from the empty allocation and
  from random serial-dictatorship picks, random tie-breaks; a nonzero stop is then continued with *every* champion
  option (the "robust" stop).
  - Random instances (`ckms_rand_k{3,4,6,8}.log`, `ckms_hot_k4.log`; 2,000 instances, n = 2–7, 10 runs each):
    20,000 runs, 13 stop with one good out under their tie-break, 1 under every option (k = 8, n = 5). Every
    instance with a nonzero stop has least charity 0.
  - The 168 curated k = 4 instances (the DE4 screen set, `ch_screen.log`, 40 runs each): 101 runs on 28 instances stop
    with one good out, 68 of them robustly (GM4-*, ls-*, hall-bt4, …, down to n = 2); never two.
  - So CKMS's own potential (welfare, increased locally) strands goods on hard k = 4 instances, which is P1's
    phenomenon. §4 and §5 show that this is not a small-n accident: both the local rules and Pareto maxima can
    strand Θ(√n) goods at k = 3.
- **Structure of the stops** (asserted on every stop by `chlib.stuck_report`): every source holds ≥ 2 goods, every
  champion values the pool good and a good of the source's bundle and is not reachable from that source, and
  σ ≤ Σ_{t∈V(g)} μ_t (Lemmas CH1–CH4 below).

## 2. Lemmas on stopping states

A *champion option* of a set B is a pair (Z, t): Z ⊆ B is an inclusion-wise minimal envied subset (some agent envies
Z, nobody envies Z ∖ h for any h ∈ Z) and t envies Z. CKMS's "most envious agent" picks one option by a tie-break.
A *stopping state* (for a fixed champion selection c(s, g)) is an EFX₀ state with acyclic G_X to which none of U0
(add a pool good to some bundle keeping EFX₀), U1 (someone envies P) and U2 (a cycle as in CKMS Algorithm 2, with the
selected champions) applies. A *robust stopping state* is one where U2 applies for no selection.

**Lemma CH0 (envied bundles cannot grow).** If w envies X_i, then w strongly envies X_i ∪ {g} for every good g.
*Proof.* Removing g from X_i ∪ {g} leaves X_i, which w envies. ∎
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
choice). Let Q_g = {c(s, g) : s ∈ S} and build the |P|-partite digraph Γ with parts V_g = {g} × σ(Q_g) and, for
g ≠ h, an edge (g, s₁) → (h, s₂) iff σ(c(s₂, g)) = s₁. Then every vertex of V_h has an in-neighbour in V_g for every g ≠ h, and Γ has
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

**Remark CH-M (monotone valuations; written proof, not machine-checked).** CKMS's rules and Theorem 8 are stated for
normalized monotone valuations. Call R_i the *support* of v_i if v_i(S) = v_i(S ∩ R_i) for every S, and read
"t values h" as h ∈ R_t. Then CH0–CH2, CH5, CH6, CH-R and CH-B hold verbatim with V(g) = {i : g ∈ R_i}; CH3 holds
without its clause "R_t meets X_t"; and CH4, CH-A and CH-C hold with k − 1 in place of k − 2 (and "complete for
k ≤ 1"). In CH1, a good outside R_t changes no value of t, which replaces "v_t(g) > 0"; weak charity
v_t({g}) ≤ v_t(P) ≤ v_t(X_t) follows from strong charity by monotonicity. The only step that uses additivity is
"t values a good of its own bundle" in CH3: with complements v_t({g}) can be 0, so a champion may hold nothing it
values, which costs one in the count μ_t ≤ |R_t| − 1.

**Algorithmic remark.** CH-A and CH-B are existence statements about every stopping state. CKMS's algorithm reaches
a stopping state in pseudo-polynomial time if U2 is applied whenever *some* rainbow cycle exists; finding one is a
colourful-cycle problem, and CKMS's own Lemma 6 only guarantees one when |P| ≥ σ. For CH-B, Sivashankar's Lemma 4
finds a rainbow cycle in expected O(p²) time once p > e·d, which gives a randomized pseudo-polynomial algorithm with
charity ⌈ed⌉; for CH-A, whose parts have unequal sizes, the running time is not analysed here.

**Proposition DU (disjoint unions are always completable; written proof, checked).** If the incidence graph
(agents and goods, an edge i–g when g ∈ R_i) has at least two connected components that contain agents, the instance
has a complete EFX₀ allocation. (Additive valuations; also monotone ones with R_i the support, as in CH-M.)
*Proof.* Let I_1, …, I_c (c ≥ 2) be the components with agents and J the goods valued by nobody. In each I_r take a
CKMS stopping state X^r: EFX₀ inside I_r, strong charity v_a(P_r) ≤ v_a(X^r_a), an acyclic envy graph and so a
source s_r. Give P_r to s_{r+1} (indices mod c) and J to s_1. Let a ∈ I_r look at the bundle B of agent b.
- b ∈ I_r: B = X^r_b ∪ E with E worthless to a, and E ≠ ∅ only if b is a source of I_r. Removing h ∈ E leaves
  v_a(X^r_b) ≤ v_a(X^r_a) (b unenvied); removing h ∈ X^r_b leaves v_a(X^r_b ∖ h) ≤ v_a(X^r_a) (EFX₀ in I_r).
- b ∉ I_r: a values at most the goods of P_r in B, and v_a(P_r) ≤ v_a(X^r_a) by strong charity.
Received goods are worthless to their receiver, so no agent's own value changes. ∎

So a counterexample to EFX₀ — and any family of instances that needs many unallocated goods in CH(k) — must be
connected: unenvied pools of different components absorb each other. With CH1 this is the global form of the
local fact that a pool good conflicts only with sources whose bundles hold a good valued by one of its valuers.
`union_dump.py` builds the allocation of the proof and checks it with the raw definition on 2,000 random unions of
2–4 instances and on 2–3 copies of GM4-E, GM4-G, S(3, 3), S′(3, 3) taken with their stranded states
(`union_dump.log`). Two copies of GM4-G, whose welfare maximum strands a good, have a complete welfare maximum
(`w_union.log`). Not found in the surveyed literature.

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

## 5. Global potential: Pareto maxima strand Θ(√n) goods too (Proposition CH-E); P1 fails at k = 3

A *Pareto maximum* is an EFX₀ state that no EFX₀ state Pareto-dominates and that allocates the most goods among the
states with its value vector (the hypothesis of K4.SDC.P1). By CH6 it is a robust stopping state with strong
charity, so CH1–CH5 apply; Pareto maxima exist in every instance. **PM(k)**: every Pareto maximum leaves at most f(k)
goods out (it would imply CH(k)); P1 is PM with f = 0.

**Lemma PM1 (holders pay).** At a Pareto maximum, let (Z, t) be a champion option of X_a ∪ P′ for any agent a ≠ t and
any P′ ⊆ P, i.e. t envies Z, nobody envies Z ∖ h. Then a values some good of Z ∩ X_a, unless Z ⊆ P.
*Proof.* Otherwise let t take Z, let a keep X_a ∖ Z, and return X_t to the pool. t strictly gains, a loses nothing
(Z ∩ X_a is worth 0 to it), the others keep their bundles. Nobody envies Z ∖ h for any h, so nobody strongly envies
Z; a's bundle only shrank; every value is at least what it was. So the new state is EFX₀ and Pareto-dominates X. ∎
This is what kills the stalls S(σ, k) of §4, where the champion of X_{s_j} ∪ g uses x_j, worth 0 to s_j.

**Construction S′(σ, k)** (σ ≥ 2, k ≥ 3): S(σ, k) with every agent valuing its own bundle. Source s_j holds
{x_j, x′_j}, values each at 2 and its ≤ k − 2 children at 5; a relay holds {z}, values z at 4 and its ≤ k − 1
children at 5; champion c(g, j) holds {y_{g,j}} and values y_{g,j} at 10, x_j at 6 and g at 6; the champions
c(·, j − 1) are the leaves of s_j's tree; the pool is g_1, …, g_{σ−1}. Every agent values at most k goods.

**Proposition CH-E.** The state X of S′(σ, k) is EFX₀ with strong charity, leaves σ − 1 goods out, and is a Pareto
maximum.
*Proof.* EFX₀ and charity as in CH-D (the only two-good bundles are the sources'; champions see 6 ≤ 10 there; parents
envy only singletons). Let Y be EFX₀ with v_a(Y_a) ≥ v_a(X_a) =: u_a for all a. Call a *displaced* if it does not
hold its own goods (y for a champion, z for a relay, both x_j and x′_j for a source).
1. *A displaced relay or source holds a child's good.* Its own goods are worth ≤ 4 and it loses part of them, so it
   needs a good worth 5, and the only ones it values are its children's. That child is then displaced.
2. *A displaced champion c(g, i) holds x_i and g* (10 needs 6 + 6), so s_i is displaced.
3. Following 1 down s_i's tree from a displaced s_i reaches a displaced leaf, a champion c(g, i − 1), which by 2
   holds a pool good and displaces s_{i−1}. If anyone is displaced, then some source is (from a displaced relay go
   down its tree by 1 to a displaced champion c(g, i), and use 2). By 3 the set of displaced sources is closed under
   i ↦ i − 1, so all σ sources are displaced, and the σ leaves c(·, i − 1) reached are distinct champions holding
   σ distinct pool goods. There are σ − 1.
So nobody is displaced, every agent holds its own goods, and every good it values that is not its own is either
someone else's own good or (champions only) a pool good g. A champion c(g, j) holding g as well: its parent values
y_{g,j} at 5, holds its own goods worth 4 and nothing else it values, and sees {y_{g,j}, g} minus g worth 5 > 4. So
v(Y) = u. Finally no pool good can be added at equal values: to a source, c(g, j) sees x_j and g (12 > 10 after
removing x′_j); to a relay or champion a, a's parent sees a's own good, worth 5 > 4, after removing g. ∎

So **PM(k) fails for every k ≥ 3 and every f**: with n = O(σ²) agents a Pareto maximum leaves σ − 1 = Ω(√n) goods
out. With σ = 2 it is a **refutation of P1 at k = 3** (n = 4, m = 7, every agent values exactly three goods; the table
is in `attempts/kgen-charity-pareto-maxima.md`): no partial EFX₀ allocation dominates it (brute force over all 5⁷),
and each of its 58 complete EFX₀ allocations leaves some agent worse off. K4.SDC.P1's moral ("a value-monotone
procedure can stop with goods left over") therefore holds at k = 3 as well; LB⁺ is not value-monotone, so there is
no conflict with TARGET.

**Corollary CH-E′ (the threshold is k = 3).** P1 holds when every agent values at most two goods: a Pareto maximum
is a robust stopping state (CH6), and stopping states are complete for k ≤ 2 (CH4′). With CH-E: Pareto maxima are
always complete for k ≤ 2, and for k ≥ 3 they can leave Ω(√n) goods out. The same dichotomy holds for CKMS's
stopping states (CH4′, CH-D).

Checks: `refute_pm.py` (standalone, no SAT: rebuilds S′ from this description, raw EFX₀, enumerates every
value-feasible family of relevant parts and every placement of the remaining goods; σ ≤ 4 at k = 3, 4) and the SAT
test `chlib.improve` for σ ≤ 7 (`pm_family_sat.log`). On S′(2, 3) the welfare maximum and the leximin maximum over
partial EFX₀ allocations are complete (§6, Question W).

Data on curated and random instances (`pm_search.py`, exact per instance by a CEGAR over Pareto maxima, which agrees
with the P1 replay on GM4-E: five Pareto maxima, one leaving one good out):
- the 168 curated k = 4 instances: 20 have a Pareto maximum leaving one good out, none leaving two
  (`pm_screen_1.log`, `pm_screen_2.log`);
- 20,600 random instances with k = 3, n ≤ 5 (`pm_rand_k3.log`, `pm_core_k3.log`, `pm_core_k3_20000.log`): no Pareto
  maximum leaves a good out. S′(2, 3) is a structured instance that random sampling does not produce.

## 6. The welfare maximum (Question W)

**Definition.** For an instance I let w*(I) be the largest total value Σ_i v_i(X_i) over partial EFX₀ allocations
X (no charity condition), and p*(I) the fewest unallocated goods among the partial EFX₀ allocations with total
w*(I). For f ≥ 0:

> **W(k, f).** Every additive instance in which every agent values at most k goods has p*(I) ≤ f.

**W(k)** says W(k, f) holds for some f independent of n. A welfare maximum with p*(I) unallocated goods is a robust
stopping state (CH6), so it has strong charity and CH-A/B/C apply; W(k, f) implies CH(k) with the same f. W is
scale-sensitive across agents: rescaling one agent (v_i ↦ λ_i v_i) changes neither EFX₀ nor the Pareto order but
changes w*, so W over all instances also covers every weighted welfare Σ λ_i v_i.

**Lemma W0 (what a smallest counterexample looks like).** If some instance with n agents has p*(I) ≥ p, then some
instance with the same n and k has p*(I) ≥ p and a welfare maximum X leaving p*(I) goods out in which (i) every
unallocated good is valued by some agent, and (ii) every bundle holds at most one good valued by nobody. In particular
m ≤ nk + n, and the values can be taken in {0} ∪ [1, ∞).
*Proof.* (i) holds for every such X: a pool good valued by nobody can be added to a source (CH0: a source exists
since a welfare maximum has an acyclic envy graph), keeping EFX₀ and the total, which leaves fewer goods out.
(ii) Let X_j hold two goods h, h′ valued by nobody, and delete h′ from the instance. Removing h′ from any EFX₀
allocation keeps it EFX₀ and keeps its total and (or lowers) its number of unallocated goods; conversely an EFX₀
allocation Y′ of the smaller instance, after rotating envy cycles (which raises the total), has a source, which can
take h′. So the largest totals with at most p − 1 goods unallocated agree in the two instances, and X ∖ h′ keeps the
total w* with p*(I) ≥ p goods out. Repeat. Each agent values at most k goods, so at most nk goods are valued; scaling
all values by one constant gives the last clause. ∎

### Results

**W(k, 0) is false at k = 3 and k = 4.** On GM4-G the largest total (32) is attained only with one good unallocated,
complete EFX₀ allocations reach 31; the same holds for GM4-G cut to three goods per agent, a k = 3 instance with the
hypergraph of S′(2, 3) (`w_brute.py`, no SAT, `w_brute.log`). On GM4-E, which K4.SDC.P1 lists as total-value-stuck,
the largest total is tied with complete allocations.

**Proposition CH-F (W(3, 1) and W(4, 1) are false).** S′(3, 4)'s hypergraph (n = 9, m = 14, every agent valuing at
most four goods) with integer values ≤ 40, and S′(3, 3)'s hypergraph (with relays: n = 12, m = 17, every agent valuing
at most three goods) with integer values ≤ 60, each have their stranded state (two goods out; totals 198 and 484) as
their only welfare maxima: every EFX₀ allocation leaving at most one good out has total ≤ 197, resp. ≤ 483. Values
and tables: `w_counterexample.py` (`k4`, `k3`), `attempts/kgen-charity-welfare-maxima.md`. *Checks:* the states by
the raw definitions; the two maxima (overall, and with ≤ 1 out) by the SAT welfare maximiser `chlib.welfare_max` and
by a separately written MILP (scipy, HiGHS), which agree (`w_counterexample.log`, `w_counterexample_k3.log`); the
values were found by the exact z3 search `w_synth_family.py` (real values first, then bounded integers). So W(k)
needs f ≥ 2 at k = 3 and k = 4: welfare maxima strand two goods even where complete EFX₀ is a theorem.

**Exact search for small n** (`w_synth.py`, z3 CEGAR over *real* values: an outer problem chooses valuations that make
a stranded state of given bundle sizes EFX₀ with strong charity, a robust stopping state (CH6: no good can be added,
≥ q + 1 sources, sources hold ≥ 2 goods) and strictly heavier than every allocation found so far that leaves fewer
than p goods out; an inner problem looks for a new such allocation; UNSAT of the outer problem rules the sizes out).
By Lemma W0 the sizes with m ≤ nk + n cover every instance, and since a welfare maximum leaves fewer goods out than it
has sources, stranded counts q = p, …, n − 1 cover every welfare maximum leaving ≥ p out. Single implementation;
the FOUND cases are re-checked by brute force or, for CH-F, by SAT and MILP.

| n | k | strands ≥ p | stranded counts q searched | result | log |
|---|---|---|---|---|---|
| 3 | 3 | 1 | 1, 2 | none (UNSAT for every size vector) | `w_synth_n3_k3_p1.log`, `w_synth_n3_k3_p1_q2.log` |
| 3 | 3 | 2 | 2 | none | `w_synth_n3_k3_p2.log` |
| 3 | 4 | 2 | 2 | none | `w_synth_n3_k4_p2.log` |
| 3 | 4 | 1 | 1 | (running) | `w_synth_n3_k4_p1.log` |
| 4 | 3 | 1 | — | exists (the cut of GM4-G) | `w_brute.log` |
| 4 | 3 | 2 | 2, 3 | none | `w_synth_n4_k3_p2.log`, `w_synth_n4_k3_p2_q3.log` |
| 4 | 4 | 2 | 2 | partial (slow: about 80 s per size vector) | `w_synth_n4_k4_p2.log` |

So the smallest welfare maximum stranding a good at k = 3 has n = 4; the smallest stranding two has 5 ≤ n ≤ 12 at
k = 3 and 4 ≤ n ≤ 9 at k = 4 (n = 4 pending).

**Why the values must be asymmetric.** With uniform values (every champion y = 2A, x = A, g = A + 1; every
parent valuing its children equally) the S′ state is the welfare maximum for σ = 2 but not for σ = 3. There a
champion takes y, x_j, x′_j and g at once (2A + 2A + 1 against 2A) while its parent takes the sibling champion's good,
and the parent, valuing both children equally, does not strongly envy the bundle that now holds its old favourite.
In the z3 solutions each parent values one child about twice the other (s₂: 8 and 4), which turns this into strong
envy. A proof for general σ would have to organise such asymmetries along the relay trees.

**Larger σ.** Whether S′(σ, k) carries values making its σ − 1 stranded goods a welfare maximum for every σ (which
would refute W(k) for every f, with Θ(√n) goods) is being tested by the same exact search; σ = 3 succeeds at k = 3 and k = 4 (CH-F), σ = 4 at k = 4
(three goods stranded, n = 20) is running (`w_synth_family_s4k4.log`).

**Earlier data, kept:** the welfare maximum is complete on 166 of the 168 curated k = 4 instances (GM4-G and its copy
are the exceptions, `w_screen.log`), on 8,400 random instances (`w_rand_*.log`), on the S and S′ families with their
default values (`w_family.log`) and with GM4-G's values for σ ≥ 3 (`w_family_vals.log`); on the coordinator's n = 6
core B< (OC₁ fails there) the welfare maximum is complete, 164 against 158 with one good out, and no Pareto maximum
strands a good (`w_Bless.log`); two disjoint copies of GM4-G have a complete welfare maximum (Proposition DU,
`w_union.log`); value hill-climbs stall at ties (`w_climb*.log`); S′(2, 3)'s default stranded state is not a
supported point, so no rescaling of it is a counterexample (`welfare_support.log`).

## 7. What can be proved at k = 4 without n (the weakest form)

The weakest open form of CH(k) asks only for a partial EFX₀ allocation with at most f(k) goods unallocated (no
condition on the pool), f independent of n. CH-D, CH-E and CH-F show that no argument that only uses a stopping state
of CKMS's rules, a Pareto maximum, or (for f ≤ 1) a welfare maximum can give it at k = 3 or k = 4. What the lemmas do
give, n-independently, and already in the strong form (nobody envies the pool):

**Corollary CH-B′ (k = 4, few valuers per good).** Let every agent value at most four goods and every good be valued
by at most d agents. Then some partial EFX₀ allocation with strong charity leaves at most
- 2 goods out if d = 2 (R(2) = 2, CGMMM §1, read; also < (k − 2)d = 4 by CH-C),
- 4 goods out if d = 3 (the packing inequality: p! ≤ 3^{p−1} fails at p = 5; CH-C gives ≤ 5), and 3 if R(3) = 3,
  which Sivashankar attributes to Kirchweger–Szeider [unverified],
- 6 goods out if d = 4 (p! ≤ 4^{p−1} fails at p = 7), and 4 if R(4) = 4 [unverified, same source].
In general p ≤ min{R(d), (k − 2)d − 1} with R(d) < ed.

**Corollary CH-C′.** For every k and every instance, CKMS's stopping states leave fewer than
(k − 2) · min_{g ∈ P} |V(g)| goods out: the charity is small as soon as one unallocated good has few valuers.

**Proposition DU** (§3): if the incidence graph is disconnected (two components with agents), nothing need be left
out. So an instance needing charity must be connected, and in CH(k) the obstruction is global, as in S and S′.

So the open case at k = 4 is exactly: connected instances whose unallocated goods all have many valuers. In every
construction above (S, S′, CH-F) every pool good has σ valuers, one per source, and the stranding comes from the
cyclic order of the sources. A proof must break that cycle by a move that lowers some agent's value (LB⁺'s rotation
at k = 3), and the families of §4–§6 are the test cases for any candidate move.

## 8. Open

1. **Non-monotone moves.** CH-D and CH-E show that a proof of CH(k), k ≥ 3, must sometimes lower an agent's value.
   The two known mechanisms are LB⁺'s rotation (k = 3) and Kaviani–Seddighin–Shahrezaei's virtual values
   (`proofs/pq_bounded.md` §2.1, their rule that may lower actual utilities). A charity version of either, with the
   S′ family as the test case, is the next step.
2. **Combine CH-B with relevant goods.** In CH-A the only obstacle to an n-independent bound is pool goods with many
   valuers; in S and S′ every pool good has σ valuers.
3. **Route (c)** (serial-dictatorship picks plus one absorber, `k4/sdc.md` §29–§30) was not pursued beyond the
   observation that from SD picks every unfrozen agent can take one junk good for free (a two-good bundle {y_a, j}
   with y_a unwanted is strongly envied by nobody, because every agent values j at most its own pick); CKMS runs from
   SD picks behave like runs from the empty allocation (`ch_screen.log`, `ch_ckms.py`).
