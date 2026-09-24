# Conjecture D for β = 2 (connected cores with m = 2n − 1)

Workstream `proof/beta2`, plan Step 3.1, ledger open item 4 (second half). Ledger rows D2, D2.O, D2.C, T2.

**Theorem D2.** Every connected core with n ≥ 2 agents and m = 2n − 1 goods (cyclomatic number β = 2) has an EFX₀
allocation in which at most one bundle has more than two goods.

The proof is constructive and self-contained. It uses only the definitions (EFX₀, core) and re-derives the counting
identity (L4) and the safety conditions it needs (the "if" directions of L5 and L8, with ties allowed), so it does not
depend on the ordinal model or on any computation. It did not follow the suggested route (shortening long paths):
a potential-function argument on an orientation problem ("collector theorem", §4) handles every core without
branch agents at once, and the cores with branch agents reduce to it or to a matching lemma (§3).

Computational cross-check (evidence for the proof, not part of it): `src/beta2.py` runs the construction of this
proof step by step and asserts every intermediate claim; `src/verify_beta2.py` runs it on every connected β = 2 core
(1, 3, 8, 15, 25, 37, 52 cores for n = 2, …, 8, from nauty genbg) and every ranking profile, 98,991,756 pairs in all,
and checks each output against the raw EFX₀ definition and the one-large-bundle condition: 0 failures, every case of
§5 exercised (`results/verify_beta2.log`, about 12 minutes on 4 CPUs). The distinct allocations it produced, saved
as `results/certs_beta2_{2..8}.json.gz`, cover every profile according to the SAT-free checker `tools/check_certs.py`
(`results/check_certs_beta2.log`). `src/test_collector.py` tests the collector theorem in its general form on random
multigraphs with pins, beyond β = 2 cores: 164,861 instances, 0 failures (`results/test_collector.log`).

## 0. Conventions

A core (PROMPT.md §3) is an instance in which every agent i values exactly three goods, R_i = {g : v_i(g) > 0}, every
good is valued by some agent, every agent has at most one private good (a good valued by no other agent), and every
agent is balanced. For each agent fix an order R_i = {a_i, b_i, c_i} with v_i(a_i) ≥ v_i(b_i) ≥ v_i(c_i), breaking
ties arbitrarily; balanced means v_i(a_i) < v_i(b_i) + v_i(c_i). The ranking profile is this choice of orders.
Nothing below assumes the values are distinct.

G is the agent–good incidence graph (bipartite, connected). An allocation X = (X_i) is a partition of all goods.
A good g is *alone* in X if its bundle is exactly {g}. Agent i is *safe* in X if v_i(X_i) ≥ v_i(X_j ∖ {h}) for every
j ≠ i and every h ∈ X_j; X is EFX₀ iff every agent is safe. "i holds g" means g ∈ X_i.

Agents with a private good are *P-agents*; for a P-agent e write p_e for its private good. The other agents are
*Q-agents*. A good valued by at least two agents is *shared*; deg(g) is the number of agents valuing g. H is G with
the private goods deleted: its vertices are the agents and the shared goods; a P-agent has H-degree 2, a Q-agent
H-degree 3, a shared good H-degree deg(g) ≥ 2. H is connected, because private goods are leaves of G.
π denotes the number of P-agents.

## 1. Sufficient conditions for safety

**Lemma 1.** Agent i is safe in X if one of the following holds.
- (S1) X_i contains at least two goods of R_i.
- (S2) i holds a_i, and no bundle with at least three goods contains both b_i and c_i.
- (S3) i holds b_i, and a_i is alone.
- (S4) i holds c_i, and a_i and b_i are alone.

*Proof.* Write A = v_i(a_i), B = v_i(b_i), C = v_i(c_i), so A ≥ B ≥ C > 0 and A < B + C. Fix j ≠ i, h ∈ X_j and
Y = X_j ∖ {h}; then v_i(Y) is the sum of the values of the goods of R_i in Y. If X_j is a singleton, Y = ∅.
- (S1) v_i(X_i) ≥ B + C > A. At most one good of R_i lies outside X_i, so v_i(Y) ≤ A.
- (S2) a_i ∉ Y. If Y contained both b_i and c_i, then X_j ⊇ {b_i, c_i, h} would be a bundle of at least three
  goods containing both, which is excluded. So v_i(Y) ≤ B ≤ A ≤ v_i(X_i).
- (S3) b_i ∉ Y, and a_i ∉ Y (if a_i ∈ X_j then X_j = {a_i} and Y = ∅). So v_i(Y) ≤ C ≤ B ≤ v_i(X_i).
- (S4) As in (S3), Y contains no good of R_i, so v_i(Y) = 0. ∎

(These are the "if" directions of L8 and of cases T, B, C of L5, re-derived with ties allowed.)

## 2. Structure of cores with m = 2n − 1

**Lemma 2 (counting).** In a core with m = 2n − 1, π = n − 2 + Σ_{g shared} (deg(g) − 2). Hence there are at most two
Q-agents. If there are two, every shared good has degree 2. If there is exactly one, exactly one shared good has
degree 3 (call it o) and every other shared good has degree 2.

*Proof.* Counting the 3n edges of G at the goods: 3n = π + Σ_{g shared} deg(g) = π + 2(m − π) + Σ_{g shared}
(deg(g) − 2) = 4n − 2 − π + Σ (deg(g) − 2). So n − π = 2 − Σ (deg(g) − 2), where every term of the sum is ≥ 0. ∎

**Lemma 3 (shapes).** Suppose there is at least one Q-agent. Then H has exactly two vertices of degree 3 (the two
Q-agents, or the Q-agent and o), called the branch vertices s and t, and every other vertex of H has degree 2.
Moreover H is either
- a *theta*: three paths from s to t, pairwise sharing only s and t; or
- a *dumbbell*: two vertex-disjoint cycles C_s ∋ s and C_t ∋ t, and a path P from s to t whose interior avoids
  C_s ∪ C_t.

In a theta, H − s is a tree. In a dumbbell, C_s − s is a connected component of H − s; it is a path whose two end
vertices are the two neighbours of s on C_s, and the third neighbour of s lies on P.

*Proof.* The degrees follow from Lemma 2. G has 3n edges and n + m = 3n − 1 vertices and is connected, so its
cyclomatic number is 3n − (3n − 1) + 1 = 2; deleting the leaves (private goods) does not change it, so β(H) = 2.
Call a path of H whose interior vertices all have degree 2 and whose ends are branch vertices a *thread*. A cycle of
H through degree-2 vertices only would be a whole component of H, which is impossible since H is connected and has
a branch vertex; so the edges of H split into threads, three at s and three at t (counting a thread from s to s
twice). Let k threads join s to t and let ℓ_s, ℓ_t threads return to s, t; then k + 2ℓ_s = k + 2ℓ_t = 3, so either
k = 3 (a theta) or k = 1 and ℓ_s = ℓ_t = 1 (a dumbbell). In a theta, H − s is the union of three paths ending at t that
pairwise share only t, hence a tree. In a dumbbell, every vertex of C_s other than s has degree 2 and both its
neighbours on C_s, so C_s − s is a component of H − s, and it is a path between the two neighbours of s on C_s. ∎

## 3. Lemma O: a Q-agent holds its top good alone

**Lemma 4 (Lemma O).** Let z be a Q-agent and g ∈ R_z, and suppose that the connected component of g in G − z is a
tree. Then there is an allocation X with X_z = {g} in which every other agent i holds exactly two goods, both in R_i.
If g = a_z, this allocation is EFX₀ and all its bundles have at most two goods.

*Proof.* First, every connected component of G − z has cyclomatic number at most 1. Indeed G − z has 3n − 3 edges
and 3n − 2 vertices; if it has c components then β(G − z) = c − 1. Each component K is joined to z by at least one
of z's three edges. If K is joined to z by exactly one edge, at the good g_K, then K contains a cycle: the part K_H of
K in H (K minus its private goods) is connected, every vertex of K_H other than g_K has all its H-neighbours in K_H
(agents are not adjacent to z, and g_K is the only good of K adjacent to z) and so K_H-degree at least 2, and g_K has K_H-degree deg(g_K) − 1 ≥ 1; a tree with at least two vertices has two
leaves, and a single vertex g_K would have H-degree 1; so K_H is not a tree. If c = 3, each component is joined to z
by exactly one edge and contains a cycle, so β(G − z) ≥ 3 > c − 1: impossible. Hence c ≤ 2 and β(G − z) ≤ 1.

We look for an assignment of the m − 1 = 2(n − 1) goods other than g to the n − 1 agents other than z, each good to
an agent that values it, each agent receiving exactly two goods. By Hall's theorem (applied after splitting every
agent into two copies), it exists iff |N(A) ∖ {g}| ≥ 2|A| for every set A of agents other than z, where N(A) is the
set of goods valued by some agent of A. Let G_A be the subgraph of G formed by A, N(A) and the 3|A| edges at A; it
lies in G − z. For a component K of G_A with agent set A_K, it has 3|A_K| edges and |A_K| + |N(A_K)| vertices, so
|N(A_K)| = 2|A_K| + 1 − β(K). Since K is a connected subgraph of G − z, β(K) ≤ 1, so |N(A_K)| ≥ 2|A_K|; and if
g ∈ N(A_K), then K lies in the component of g in G − z, which is a tree, so β(K) = 0 and |N(A_K) ∖ {g}| = 2|A_K|.
The sets N(A_K) are disjoint, and g lies in at most one of them; summing over the components gives Hall's
condition. Since the goods other than g number exactly 2(n − 1), every good is assigned.

If g = a_z: every agent other than z holds two of its own goods and is safe by (S1); no bundle has three goods, so z
is safe by (S2). ∎

## 4. The collector theorem

**Setting.** V is a finite set of goods (the *vertices*) and E a finite set of agents. Every e ∈ E values exactly
three goods, R_e = {p_e, x_e, y_e}, where x_e ≠ y_e lie in V (the *endpoints* of e) and p_e ∉ V is valued by no other
agent of the instance; the p_e are distinct. Each e ∈ E is balanced, with order (a_e, b_e, c_e) as in §0. Some
vertices are *pinned*: for each pinned vertex π ∈ Π ⊆ V there is an agent outside E whose bundle is exactly {π}.
Z is a finite set of goods, disjoint from V and from the p_e, containing no good valued by an agent of E. The rest
of the instance (other agents and goods, allocated arbitrarily) contains no good valued by an agent of E. Finally,

  |E| + |Π| = |V| + 1.   (★)

A *cover state* is a pair (w, h) of an agent w ∈ E (the *collector*) and a map h : E ∖ {w} → V such that
h(e) ∈ {x_e, y_e} for every e and h is a bijection onto V ∖ Π. Think of h(e) as the head of the edge e = x_e y_e of
the multigraph K = (V, E); t(e) denotes the other endpoint (the tail). Every vertex v is then *covered* exactly once:
by its pin if v ∈ Π, otherwise by the agent h⁻¹(v).

For a cover state and a set J ⊆ E ∖ {w}, the allocation X = X(w, h, J) of V ∪ {p_e : e ∈ E} ∪ Z is
- X_e = {h(e)} for e ∈ J,
- X_e = {p_e, h(e)} for e ∈ E ∖ ({w} ∪ J),
- X_w = {p_w} ∪ {p_e : e ∈ J} ∪ Z,

with the pin holders' bundles {π} and the rest of the instance as given. Only X_w can have more than two goods.

**Theorem 5 (collector theorem).** If a cover state exists, then there are a cover state (w, h) and a set J such that
every agent of E is safe in X(w, h, J).

*Proof.* Fix a cover state (w, h). Call an agent e ∈ E ∖ {w}
- *happy* if h(e) = a_e;
- *transparent* if h(e) = b_e and t(e) = a_e (so a_e, b_e are the endpoints of e and p_e = c_e);
- *bad* otherwise.

*Walks.* The walk from a vertex v is the sequence v₀ = v, e₁, v₁, e₂, v₂, … built as follows: if v_i ∈ Π the walk
stops; otherwise e_{i+1} = h⁻¹(v_i), and if e_{i+1} is transparent the walk continues with v_{i+1} = t(e_{i+1}),
while if e_{i+1} is happy or bad it stops. So the walk is finite and stops at a pin, a happy agent or a bad agent,
or it is infinite and passes through transparent agents only. It *succeeds* if it contains no bad agent. Put

  J = {e ∈ E ∖ {w} : the walk from h(e) succeeds}.

The walk from h(e) begins with e, so bad agents are not in J; and for a transparent e the walk from h(e) is e followed
by the walk from t(e).

(a) *If the walk from v succeeds, v is alone in X.* If v ∈ Π, its bundle is {v}. Otherwise e = h⁻¹(v) is the first
agent of the walk from v, which is the walk from h(e); it succeeds, so e ∈ J and X_e = {v}.

(b) *Every e ∈ E ∖ {w} is safe.* If e ∉ J, then X_e = {p_e, h(e)} and (S1) applies. If e ∈ J is happy, e holds a_e,
and {b_e, c_e} = {p_e, t(e)}; p_e ∈ X_w while t(e) ∈ V and X_w ∩ V = ∅, so b_e and c_e are in different bundles
and (S2) applies. If e ∈ J is transparent, e holds b_e = h(e), and the walk from t(e) = a_e succeeds (it is the rest
of the walk from h(e)), so a_e is alone by (a) and (S3) applies.

(c) *The collector.* Let D(w) = ∅ if p_w = a_w, D(w) = {a_w} if p_w = b_w, and D(w) = {a_w, b_w} if p_w = c_w; in
each case D(w) ⊆ {x_w, y_w}. If the walk from every x ∈ D(w) succeeds, w is safe: if p_w = a_w, w holds a_w, and
b_w, c_w ∈ V are in different bundles (every bundle contains at most one vertex: the pin holders and the agents of
E ∖ {w} hold one each, X_w none, and the rest of the instance none), so (S2) applies; if p_w = b_w, w holds b_w and
a_w is alone by (a), (S3); if p_w = c_w, w holds c_w and a_w, b_w are alone by (a), (S4).

(d) *Switching.* Suppose that the walk from some x ∈ D(w) fails: v₀ = x, e₁, v₁, …, e_{k−1}, v_{k−1}, e_k, with
e₁, …, e_{k−1} transparent and e_k bad (k ≥ 1; in particular x ∉ Π). The vertices v₀, …, v_{k−1} are distinct: the
walk is generated by the map v ↦ t(h⁻¹(v)), so if v_j = v_i with i < j ≤ k − 1, the walk would be periodic from v_i
on, and e_k = h⁻¹(v_{k−1}) would equal an earlier, transparent, agent. Hence e₁, …, e_k are distinct as well, and
none of them is w. Define a new cover state (w′, h′) by

  w′ = e_k,  h′(w) = x,  h′(e_i) = v_i = t(e_i) for 1 ≤ i ≤ k − 1,  h′(e) = h(e) for every other e ∈ E ∖ {w, w′}.

Before, e₁, …, e_k covered v₀, …, v_{k−1}; now w, e₁, …, e_{k−1} cover the same vertices, and nothing else changes,
so h′ is a bijection onto V ∖ Π, and h′(e) ∈ {x_e, y_e} for every e. Compare the numbers of bad agents: e_k was bad
and is now the collector; each e_i (i < k) was transparent, so t(e_i) = a_{e_i}, and is now happy; w now has head x,
which is a_w (happy) or, when p_w = c_w, x = b_w with tail a_w (transparent); no other agent changes. So the number
of bad agents drops by exactly one.

Start from any cover state and apply (d) as long as some walk from D(w) fails. The number of bad agents is a
non-negative integer that drops at each step, so this stops, at a cover state in which every walk from D(w)
succeeds. With J as defined, every agent of E is safe by (b) and (c). ∎

Remarks. (1) The collector's bundle has 1 + |J| + |Z| goods; it is the only bundle that may have more than two.
(2) Theorem 5 does not use β = 2 or connectivity, only (★) and the existence of a cover state; `src/test_collector.py`
tests it in this generality.

**Lemma 6 (cover states in a connected multigraph).** Let K = (V, E) be a connected multigraph without loops in which
every vertex has degree at least 2 and |E| = |V| + 1. Then for every w ∈ E there is a cover state (w, h) with Π = ∅.

*Proof.* K − w has |V| vertices and |V| edges and at most two components. If it is connected, it has exactly one
cycle. Otherwise w is a bridge, and each side C of it contains a cycle: all vertices of C have K-degree at least 2
and all their edges in C, except the endpoint u of w, which has C-degree at least 1; a tree with at least two
vertices has two leaves, and C = {u} would give u degree 1 in K (there are no loops). The cyclomatic number of K − w
is |V| − |V| + 2 = 2, so each side has exactly one cycle. In each component with exactly one cycle, orient the cycle
cyclically and every other edge away from the cycle; every vertex then has exactly one incoming edge, and h(e) = the
head of e is a cover state. ∎

## 5. Proof of Theorem D2

Let C be a connected core with n ≥ 2 agents and m = 2n − 1 goods, with any balanced valuations and a fixed order
(a_i, b_i, c_i) for every agent. By Lemma 2 there are at most two Q-agents.

**Case 1: no Q-agent (π = n).** Let K be the multigraph whose vertices are the shared goods and whose edges are the
agents, agent e joining its two shared goods (distinct, so K has no loops). There are m − n = n − 1 shared goods, so
|E| = n = |V| + 1; K is connected because H, which is K with every edge subdivided by its agent, is connected; every
vertex has degree deg(g) ≥ 2. By Lemma 6 a cover state exists (Π = ∅), and Theorem 5 (with Z = ∅ and no other
agents) gives an EFX₀ allocation of all goods in which only the collector's bundle can have more than two goods.

**Case 2: some Q-agent z such that the component of a_z in G − z is a tree.** Lemma 4 with g = a_z gives an EFX₀
allocation with all bundles of at most two goods. By Lemma 3 this covers every theta (if z is a branch vertex of a
theta, H − z is a tree, and G − z adds only leaves) and every dumbbell in which some Q-agent z has a_z on its cycle
C_z (the component of a_z in G − z is the path C_z − z with private goods attached, a tree).

**Case 3: otherwise.** Then there is a Q-agent, H is a dumbbell (Case 2 covers the thetas), and every Q-agent z is a
branch vertex whose top good a_z is its neighbour on the bridge path P, which we call z_P. Two facts used below:

(L) *The loop at a Q-agent z.* By Lemma 3, C_z − z is a path h₀, f₁, h₁, f₂, …, f_ℓ, h_ℓ with ℓ ≥ 1, where h₀ and h_ℓ
are the two neighbours of z on C_z (the goods b_z and c_z) and each f_i is an agent valuing h_{i−1} and h_i; the f_i
have H-degree 2, so they are P-agents. Giving f_i the bundle {p_{f_i}, h_i} for i = 1, …, ℓ allocates every good of
the path except h₀, the *spare good* s_z = h₀, and each f_i is safe by (S1) whatever the other bundles are.

(B) *Safety of a Q-agent z holding exactly {a_z}.* If at most one of b_z, c_z lies in a bundle of at least three
goods (for instance: only the spare good h₀ of its loop does, the other goods of the loop being in two-good bundles
by (L)), then z is safe by (S2).

*Case 3a: one Q-agent q (π = n − 1).* The branch vertices are q and the degree-3 good o, and a_q = q_P (possibly
q_P = o, when P is the single edge q o). Let D be the component of H − q containing q_P: the path P without q,
together with the cycle C_o. All agents in D are P-agents (q is the only Q-agent), and each has both its shared goods
in D. Let V be the set of goods of D, E the set of agents of D, and Π = {q_P}, pinned by q with X_q = {q_P}. D is
connected with exactly one cycle (C_o), and it has 2|E| edges (two per agent) and |E| + |V| vertices, so
2|E| − |E| − |V| + 1 = 1, i.e. |E| = |V| and (★) holds. A cover state: let w₀ be an agent on C_o; the multigraph
(V, E ∖ {w₀}) is a tree (it is connected, D minus an edge of its cycle, and has |V| − 1 edges); orient every edge away
from q_P. Every vertex other than q_P then has exactly one incoming edge, and q_P is pinned.
Allocate the loop at q by (L), with spare good s_q, and apply Theorem 5 to (V, E, Π) with Z = {s_q}. The goods valued
by agents of E are their private goods and V; outside E they are held only by q (the pin, bundle {q_P}), so the
setting of Theorem 5 holds, and every agent of E is safe. The loop agents are safe by (L). The agent q holds a_q, and
b_q, c_q are h₀ = s_q (in the collector's bundle) and h_ℓ (in the bundle {p_{f_ℓ}, h_ℓ}), so q is safe by (B). All
goods are allocated: the goods of C_q − q by (L) and Z, the goods of D by the cover state and the pin, all private
goods to their owners or the collector. Only the collector's bundle can have more than two goods.

*Case 3b: two Q-agents u, v (π = n − 2), and P has at least one agent.* All shared goods have degree 2. Write P as
u, g₀, e₁, g₁, …, e_k, g_k, v with k ≥ 1, so a_u = u_P = g₀ and a_v = v_P = g_k ≠ g₀. The agents e_i are P-agents
(H-degree 2) valuing g_{i−1} and g_i. Let V = {g₀, …, g_k}, E = {e₁, …, e_k}, Π = {g₀, g_k}, pinned by u and v with
X_u = {g₀}, X_v = {g_k}. Then |E| + |Π| = k + 2 = |V| + 1, and w₀ = e₁ with h(e_i) = g_{i−1} for 2 ≤ i ≤ k is a
cover state. Allocate the loops at u and at v by (L), with spare goods s_u and s_v, and apply Theorem 5 with
Z = {s_u, s_v}. As in Case 3a, the goods valued by the e_i are their private goods and V, held outside E only by the
pin holders u and v; so every e_i is safe; the loop agents are safe by (L); u and v are safe by (B). All goods are
allocated: the goods of the two loops by (L) and Z, the goods of P by the cover state and the pins, all private goods
to their owners or the collector. Only the collector's bundle can have more than two goods.

*Case 3c: two Q-agents u, v, and P is the single good g (u, g, v).* Then a_u = a_v = g, and b_v, c_v are the two
neighbours of v on C_v. Let X_u = {g} and allocate the loop at u by (L), with spare good s_u. Allocate the loop at v by
(L), numbering its path so that h₀ = b_v (the spare good of the loop at v is then b_v), and let X_v = {b_v, s_u}.
Every bundle has at most two goods. The agent u holds a_u and no bundle has three goods: (S2). The agent v holds b_v
and a_v = g is alone: (S3). The loop agents: (L).

The cases are exhaustive: with no Q-agent, Case 1; with a Q-agent, Case 2 unless H is a dumbbell in which every
Q-agent's top good is its neighbour on P; then Case 3a (one Q-agent) or 3b/3c (two Q-agents, P with or without
agents). In every case the allocation is EFX₀ and has at most one bundle with more than two goods. ∎

## 6. Consequences, and what is not covered

- **D holds for every β = 2 core, for all n ≥ 2.** Before this, D at β = 2 was certified only for n = 5, 6, 7
  (R1, R2); n = 2, 3, 4 were not checked, since `frontier.py` starts at m = n + 4.
- **Large bundle.** In Case 1 and Cases 3a/3b the large bundle is the collector's, made of private goods (its own and
  those of the agents in J) plus at most two spare goods; in Cases 2 and 3c all bundles have at most two goods. The
  large bundle can have up to n goods (Case 1, all other agents in J); `results/verify_beta2.log` records the largest
  size per case.
- **Corollary T2.** Combined with the reduction to cores (L2, L3), components (L6) and β = 1 (L8): if the core
  obtained from an instance with |R_i| ≤ 3 has only connected components with β ≤ 2 (m_C ≥ 2n_C − 1), the
  instance has an EFX₀ allocation. This inherits the status of L2, L3, L6 and L8 (proof sketches in
  `proofs/lemmas.md`).
- **Not covered: β ≥ 3.** The collector theorem needs (★), one deficit unit; a β = 3 core without Q-agents has
  |E| = |V| + 2. Whether one collector can absorb two deficit units (conjecture D for β = 3) is open; Theorem 5 applies
  verbatim to any core component where (★) and a cover state can be arranged.
- **The failed intermediate schemes** (collector restricted to P-agents; every shared good held by an agent that
  values it) are recorded in `attempts/beta2-pc-scheme.md` and `attempts/beta2-gpc-scheme.md`, with their smallest
  failing configurations; they are why Lemma O and Case 3c are needed.
