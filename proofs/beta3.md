# Conjecture D for β = 3 (connected cores with m = 2n − 2)

Workstream `proof/beta3`, plan Step 3.2, ledger open item 7. Ledger rows D3.M, D3.P, D3.0, D3.2, D3.S, D3.Q, D3, T4.

**Theorem D3.** Every connected core with n agents and m = 2n − 2 goods (cyclomatic number β = 3) has an EFX₀
allocation in which at most one bundle has more than two goods.

**What is proved by hand and what is computed.** The proof has two halves.
- A general part, proved here by hand for every β: the collector theorem of `proofs/beta2.md` (D2.C) extended to
  any number of collectors (Theorem 2), and a reduction (Theorem 5): a core satisfies D under every ranking profile as
  soon as the rankings of its *Q-agents* (agents without a private good) admit a *Q-plan*, a combinatorial object
  defined in §3 that ignores the P-agents' rankings. Two consequences are proved by hand:
  - **Corollary 3.** D holds for every connected core in which every agent has a private good, for every β.
  - **Theorem D3 for q ≤ 2.** D holds for every β = 3 core with at most two Q-agents (Lemma 6).
- A finite part, Lemma 7: every β = 3 core has a Q-plan for every ranking of its Q-agents. Lemma 8 (proved)
  shows that it suffices to check the *reduced* β = 3 cores, those in which every thread (path of degree-2 vertices
  between branch vertices) carries at most one P-agent, or at most two if it is a loop at a good (§5), and Lemma 9 (proved) shows that reduced β = 3 cores with a Q-agent have at most 10 agents. The
  finite check was done by computer: all connected β = 3 cores with 3 ≤ n ≤ 10 were enumerated with nauty (list
  certified complete by orbit counting, `tools/check_enum.py`), and every reduced one has a Q-plan for each of the
  6^q rankings of its Q-agents. An independent checker (`tools/check_qplans.py`, written without the search code)
  re-derives reducedness and re-checks every plan (`results/qplans_beta3.log`, `results/check_qplans.log`).

So Theorem D3 is PROVED for cores with q ≤ 2 and, for all β = 3 cores, it rests on one finite computation
(Lemma 7 for q = 3, 4): CERTIFIED in the ledger's sense (an exhaustive check over a finite set that a proved lemma
shows is enough, with independently checked certificates). A hand proof of Lemma 7 for q = 3, 4 is open; §6 says
what those cases need. (Among the β = 3 cores with n = 6, 143 of 211 have q ≤ 2; with n = 7, 370 of 541.)

**Cross-check of the whole construction** (evidence, not part of the proof): `src/beta3.py` runs the construction
step by step (Q-plan, orientations, multi-collector switching) and asserts every intermediate claim;
`src/verify_beta3.py` runs it on every connected β = 3 core with n = 3, …, 7 (2, 16, 62, 211, 541 cores) and every
ranking profile, 161,793,072 core–profile pairs, and checks each output against the raw EFX₀ definition and the
one-large-bundle condition: 0 failures, no claim of the proof violated (`results/verify_beta3.log`, 27 minutes on
4 CPUs). The distinct allocations are saved as `results/certs_beta3_{3..7}.json.gz` and accepted
by the SAT-free checker `tools/check_certs.py --require-d` (`results/check_certs_beta3.log`).

## 0. Conventions

As in `proofs/beta2.md` §0. A core is an instance in which every agent i values exactly three goods,
R_i = {g : v_i(g) > 0}, every good is valued by some agent, every agent has at most one private good (a good valued by
no other agent), and every agent is balanced. For each agent fix an order R_i = {a_i, b_i, c_i} with
v_i(a_i) ≥ v_i(b_i) ≥ v_i(c_i), ties broken arbitrarily; balanced means v_i(a_i) < v_i(b_i) + v_i(c_i). Values need
not be distinct. G is the agent–good incidence graph; *connected core* means G is connected. An allocation X = (X_i)
is a partition of all goods; a good g is *alone* if its bundle is {g}; agent i is *safe* if
v_i(X_i) ≥ v_i(X_j ∖ {h}) for all j ≠ i and h ∈ X_j; X is EFX₀ iff every agent is safe. The cyclomatic number of a
connected core is β = 3n − (n + m) + 1 = 2n − m + 1.

*P-agents* have a private good (p_e for P-agent e), *Q-agents* have none; π and q = n − π count them. A good valued by
at least two agents is *shared*; V denotes the set of shared goods. Every good of degree 1 is private, and each
P-agent has exactly one, so |V| = m − π. H is G with the private goods deleted (connected, since private goods are
leaves of G). A P-agent e values exactly two shared goods, its *endpoints* x_e ≠ y_e.

**The multigraph K.** K has vertex set V and one edge per P-agent e, joining x_e and y_e (no loops; parallel edges
allowed). Q-agents are not edges of K. For a connected component C of K write V(C), E(C) (its P-agents) and
**base(C) = |E(C)| − |V(C)|**; base(C) ≥ −1, with equality iff C is a tree. Since every edge of K is a P-agent,
K is H with the Q-agents deleted and each P-agent replaced by an edge.

## 1. Sufficient conditions for safety

**Lemma 1.** Agent i is safe in X if one of the following holds.
- (S1) X_i contains at least two goods of R_i.
- (S2) i holds a_i, and no bundle with at least three goods contains both b_i and c_i.
- (S3) i holds b_i, and a_i is alone.
- (S4) i holds c_i, and a_i and b_i are alone.

*Proof.* Write A = v_i(a_i), B = v_i(b_i), C = v_i(c_i), so A ≥ B ≥ C > 0 and A < B + C. Fix j ≠ i, h ∈ X_j and
Y = X_j ∖ {h}; v_i(Y) is the sum of the values of the goods of R_i in Y, and Y = ∅ if X_j is a singleton.
- (S1) v_i(X_i) ≥ B + C > A, and at most one good of R_i lies outside X_i, so v_i(Y) ≤ A.
- (S2) a_i ∉ Y. If Y contained b_i and c_i, then X_j ⊇ {b_i, c_i, h} would be a bundle of at least three goods
  containing both. So v_i(Y) ≤ B ≤ A ≤ v_i(X_i).
- (S3) b_i ∉ Y, and a_i ∉ Y (if a_i ∈ X_j then X_j = {a_i} and Y = ∅). So v_i(Y) ≤ C ≤ B ≤ v_i(X_i).
- (S4) As in (S3), Y contains no good of R_i, so v_i(Y) = 0. ∎

Conditions (S1)–(S4) only concern the goods of R_i in X_i and the other bundles. So they stay true when goods that i
does not value are added to X_i, and (S1) stays true when any goods are added.

**Lemma 2 (counting).** In a connected core, Σ_C base(C) = β − 1 − 2q, the sum over the components C of K. For
β = 3: Σ_C base(C) = 2 − 2q, and q ≤ 4.

*Proof.* K has π edges and m − π vertices, so Σ base(C) = π − (m − π) = 2(n − q) − (2n + 1 − β). For the bound on q,
count the 3n edges of G at the goods: 3n = π + Σ_{g ∈ V} deg(g) ≥ π + 2(m − π) = 2m − π, and with m = 2n − 2,
π = n − q this reads 3n ≥ 3n − 4 + q. ∎

For β = 3 the same count gives Σ_{g ∈ V} (deg(g) − 2) = 4 − q.

## 2. The multi-collector theorem

**Setting.** Some agents already have bundles; a set E of P-agents is still to be served. V′ is a set of shared goods
with {x_e, y_e} ⊆ V′ for every e ∈ E. Π ⊆ V′ is a set of *pinned* goods: each is the whole bundle {π} of an agent
outside E. Z is a set of goods containing no good of V′ and no good valued by an agent of E. Every other bundle already
fixed contains no good of V′ and no good valued by an agent of E (the goods valued by agents of E are V′ and their
private goods). Let

  k = |E| + |Π| − |V′| ≥ 1.   (★k)

A *cover state* is a pair (W, h): a set W ⊆ E of k *collectors* and a bijection h : E ∖ W → V′ ∖ Π with
h(e) ∈ {x_e, y_e}; h(e) is the *head* of e and t(e) the other endpoint, its *tail*. For J ⊆ E ∖ W and a collector
w* ∈ W (the *main collector*), the allocation X = X(W, h, J, w*) gives
- X_e = {h(e)} for e ∈ J, and X_e = {p_e, h(e)} for e ∈ E ∖ (W ∪ J),
- X_{w*} = {p_{w*}} ∪ {p_e : e ∈ J} ∪ Z, and X_w = {p_w} for every other collector w,

and keeps the bundles fixed before. Among the agents of E only w* can hold more than two goods. With k = 1 this is the
collector theorem of `proofs/beta2.md` (Theorem 5 there).

**Theorem 2 (multi-collector theorem).** If a cover state exists, then there are a cover state (W, h) and a set
J ⊆ E ∖ W such that, whichever w* ∈ W is chosen, every agent of E is safe in X(W, h, J, w*).

*Proof.* The proof of `proofs/beta2.md` Theorem 5 goes through with a set of collectors; we repeat it. Fix a cover
state. Every good v ∈ V′ is held by exactly one agent: its pin holder if v ∈ Π, otherwise h⁻¹(v). An agent
e ∈ E ∖ W is *happy* if h(e) = a_e, *transparent* if h(e) = b_e and t(e) = a_e (then p_e = c_e), *bad* otherwise.

*Walks.* The walk from v ∈ V′ is v₀ = v, e₁, v₁, e₂, … : if v_i ∈ Π it stops; otherwise e_{i+1} = h⁻¹(v_i), and if
e_{i+1} is transparent the walk continues with v_{i+1} = t(e_{i+1}), while if it is happy or bad the walk stops. It
*succeeds* if it contains no bad agent (in particular if it is infinite). Collectors hold no good of V′, so they never
occur on walks. Put J = {e ∈ E ∖ W : the walk from h(e) succeeds}; the walk from h(e) starts with e, so J contains no
bad agent, and for transparent e it is e followed by the walk from t(e).

(a) *If the walk from v succeeds, v is alone.* If v ∈ Π its bundle is {v}. Otherwise e = h⁻¹(v) starts the walk from
v = h(e), so e ∈ J and X_e = {v}.

(b) *Every e ∈ E ∖ W is safe.* If e ∉ J, X_e = {p_e, h(e)}: (S1). If e ∈ J is happy, it holds a_e and
{b_e, c_e} = {p_e, t(e)}; p_e ∈ X_{w*}, which contains no good of V′, while t(e) ∈ V′: (S2). If e ∈ J is transparent,
it holds b_e and the walk from t(e) = a_e succeeds, so a_e is alone by (a): (S3).

(c) *Collectors.* For w ∈ W let D(w) = ∅, {a_w} or {a_w, b_w} according as p_w = a_w, b_w or c_w; D(w) ⊆ {x_w, y_w}.
If the walk from every x ∈ D(w) succeeds, w is safe, whether or not it is the main collector: it holds p_w and goods
it does not value (private goods of others, and Z). If p_w = a_w, then b_w, c_w ∈ V′ lie in different bundles, since
every bundle contains at most one good of V′ (pin holders and agents of E ∖ W one each, collectors and the bundles
fixed before none): (S2). If p_w = b_w, a_w is alone by (a): (S3). If p_w = c_w, a_w and b_w are alone: (S4).

(d) *Switching.* Suppose the walk from some x ∈ D(w), w ∈ W, fails: v₀ = x, e₁, v₁, …, e_{k′−1}, v_{k′−1}, e_{k′} with
e₁, …, e_{k′−1} transparent and e_{k′} bad. As in `proofs/beta2.md` the v_i are distinct (the walk is generated by
v ↦ t(h⁻¹(v)); a repetition would make it periodic and e_{k′} transparent), hence so are the e_i, and none is a
collector. Define W′ = (W ∖ {w}) ∪ {e_{k′}}, h′(w) = x, h′(e_i) = v_i for 1 ≤ i < k′, h′ = h elsewhere. Before,
e₁, …, e_{k′} held v₀, …, v_{k′−1}; now w, e₁, …, e_{k′−1} do, so (W′, h′) is a cover state. The number of bad agents
drops by exactly one: e_{k′} was bad and is now a collector; each e_i (i < k′) moves to its tail, which is its top, and
becomes happy; w gets head x, which is a_w (happy) or, when p_w = c_w, b_w with tail a_w (transparent).

Apply (d) as long as some collector has a failing walk from D(w). The number of bad agents drops each time, so this
stops at a cover state in which every walk from every D(w) succeeds; with J as defined, (b) and (c) apply. ∎

**Lemma 4 (orientations).** Let C be a connected multigraph without loops, M ⊆ V(C), and k = |E(C)| − |V(C)| + |M| ≥ 0.
Then there are a set W ⊆ E(C) of k edges and a bijection h : E(C) ∖ W → V(C) ∖ M with h(e) an endpoint of e.

*Proof.* If M ≠ ∅, root a spanning tree T at some r ∈ M and let h map the edge from each vertex v ∉ M to its parent
onto v; these |V(C)| − |M| edges are distinct. If M = ∅, then |E(C)| ≥ |V(C)|, so C is not a tree; let f be an edge
on a cycle, with endpoints r and s, root a spanning tree T of C − f (connected) at r, map the parent edge of every
v ≠ r onto v, and map f onto r. In both cases W is the set of the remaining k edges. ∎

## 3. Q-plans

Fix the orders (a_z, b_z, c_z) of the Q-agents. A *role* of a Q-agent z is one of the sets
{a_z} (*a-pin*), {b_z} (*b-pin*), {a_z, b_z}, {a_z, c_z}, {b_z, c_z} (*2-holder*); a-pins and b-pins are *1-holders*.

A **Q-plan** is a triple (Y, Z, T): a role Y_z for every Q-agent, pairwise disjoint; a set Z ⊆ V of *spares* disjoint
from ⋃Y := ⋃_z Y_z; and a *dump target* T ⊆ V, such that the following hold, where for a component C of K

  ε(C) = base(C) + |V(C) ∩ (⋃Y ∪ Z)|,

and C is *active* if ε(C) ≥ 1, *balanced* if ε(C) = 0.
- (Q0) If Y_z = {b_z}, then {a_z} = Y_{z′} for some 1-holder z′ ≠ z.
- (P1) ε(C) ≥ 0 for every component C of K.
- (P2) An active component contains no good of Y_z for a 2-holder z, and no spare. (Other goods of R_z may lie in
  it.)
- (P3) If Z ≠ ∅ and no component is active, then T = Y_z for a 2-holder z, or T = {v} for a good v ∈ V ∖ (⋃Y ∪ Z).
  Otherwise T = ∅. Let L = Z ∪ T.
- (P4) If Y_z = {a_z}, then b_z and c_z are not both in L.

A Q-plan depends only on the core and on the orders of the Q-agents. Examples: a core without Q-agents has the Q-plan
(∅, ∅, ∅) iff base(K) ≥ 0 (Corollary 3); the Q-agents of D2's Case 3 are a-pins, and the spare goods of the loops
there are spares.

**Theorem 5 (Q-plans suffice).** Let C be a connected core (any β) and fix orders for all agents. If the orders of the
Q-agents admit a Q-plan, then C has an EFX₀ allocation in which at most one bundle has more than two goods.

*Proof.* Let (Y, Z, T) be a Q-plan and call the goods of ⋃Y ∪ Z *marked*.
1. *Q-agents.* Each Q-agent z gets X_z = Y_z.
2. *Balanced components.* For a balanced C, Lemma 4 with M = the marked goods of C and k = ε(C) = 0 gives a
   bijection h from E(C) onto the unmarked goods of C with h(e) ∈ {x_e, y_e}; every e ∈ E(C) gets {p_e, h(e)}.
3. *Active components.* Let E be the P-agents of all active components, V′ their goods, and Π the marked goods among
   them. By (P2), each good of Π is the only good of a 1-holder, so X_z = {π}: it is pinned. In each active C, Lemma 4
   with M = V(C) ∩ Π gives ε(C) collectors and a head map covering the other goods of C; together they form a cover
   state for (E, V′, Π) with k = Σ_{C active} ε(C) = |E| + |Π| − |V′| ≥ 1. Take the spares Z as the set Z of the
   setting. The setting of Theorem 2 holds: agents of E value only V′ and their private goods; Z ∩ V′ = ∅ by (P2), and
   spares are shared goods outside V′, so not valued by agents of E; apart from the pins, the bundles of steps 1–2
   contain only private goods of agents outside E and shared goods outside V′ (the goods Y_z of 2-holders and the goods of
   balanced components lie outside V′ by (P2)), so no good of V′ and no good valued by an agent of E. Theorem 2 gives
   a cover state and J; allocate X(W, h, J, w*) for any w* ∈ W.
4. *No active component.* Then no agent is served in step 3. If Z ≠ ∅, add Z to the bundle of the owner of T: the
   2-holder z with Y_z = T, or the P-agent e with h(e) = v when T = {v} (v is unmarked, so it lies in a balanced
   component and is some e's head by step 2).

*Everything is allocated.* Marked goods: Y to the Q-agents, Z to w* (step 3) or to T's owner (step 4). Unmarked shared
goods: in balanced components by step 2, in active ones by the cover state (V′ ∖ Π). Private goods: to their owners,
or to w* for the agents of J.

*At most one large bundle.* Q-agents hold one or two goods, P-agents of balanced components two, agents of E one or
two, except w* (step 3) or T's owner (step 4); call that bundle the *large bundle* (if Z = ∅ and there is no active
component, every bundle has at most two goods). The shared goods in the large bundle are exactly those of L: Z in
step 3 (w*'s other goods are private), Z ∪ T in step 4.

*Everyone is safe.* Agents of E: Theorem 2. P-agents of balanced components (including T's owner): (S1). 2-holders
(including T's owner): (S1). An a-pin z holds a_z, and b_z, c_z are not both in the large bundle by (P4), the only
bundle with more than two goods: (S2). A b-pin z holds b_z, and a_z is the whole bundle of a 1-holder by (Q0): (S3). ∎

**Corollary 3 (no Q-agents).** Every connected core in which every agent has a private good has an EFX₀ allocation
with at most one bundle of more than two goods, whatever β is.

*Proof.* With q = 0, K is H with every agent replaced by an edge, hence connected, and by Lemma 2
base(K) = β − 1 ≥ 0 (β ≥ 1 because m ≤ 2n: 3n = π + Σ_{g ∈ V} deg(g) ≥ π + 2(m − π) = 2m − π ≥ 2m − n). So (∅, ∅, ∅) is a Q-plan: (P1) holds and (P2)–(P4) are
empty. Apply Theorem 5. (For β = 1 this is L8; for β = 2 it is Case 1 of `proofs/beta2.md`; for β ≥ 2 the large bundle
belongs to one of the β − 1 collectors.) ∎

## 4. Q-plans for β = 3 with at most two Q-agents (by hand)

For a component D of K let r(D) be the number of pairs (z, g) with z a Q-agent and g ∈ R_z ∩ V(D), and
S(D) = Σ_{g ∈ V(D)} (deg(g) − 2) ≥ 0. Counting the edges of H at the goods of D (each P-agent of D contributes two,
each pair (z, g) one) gives Σ_{g ∈ V(D)} deg(g) = 2|E(D)| + r(D), so

  base(D) = (S(D) − r(D)) / 2.   (†)

If q ≥ 1, every component D has r(D) ≥ 1: K is H minus the Q-agents, with each P-agent replaced by an edge, and H is
connected. Summing, Σ_D r(D) = 3q and Σ_D S(D) = 4 − q (§1). Since base(D) ≥ −1, (†) gives r(D) ≤ S(D) + 2, and
r(D) ≡ S(D) (mod 2). A component with S(D) = 0 therefore has r(D) = 2 and base −1; call it a *thread component*
(it is a path of degree-2 goods and P-agents between two goods of Q-agents, or a single good valued by two Q-agents).

In the plans below, a component with ε(C) = −1 before spares are added is *needy*; each needy component receives
exactly one spare, which makes it balanced. If all Q-agents are 1-holders, Σ_C ε(C) = Σ base + q = 2 − q before the
spares (Lemma 2), so for q = 2 the needy components are exactly balanced by the active ones:
#needy = Σ_{C active} ε(C). Hence (P3) holds with T = ∅ (spares come with an active component), (P2) holds (the
marked goods of active components are 1-holders' goods, and spares go to needy components), and (P4) can only fail if two spares
are the goods b_z, c_z of one a-pin z.

**Lemma 6.** Let C be a connected core with β = 3 and q ≤ 2. Every order of its Q-agents admits a Q-plan.

*Proof.* **q = 0**: Corollary 3.

**q = 1**, Q = {z}: Σ S = 3, Σ r = 3, Σ base = 0. By (†) a component with r(D) = 1 has S(D) odd, so base(D) ≥ 0,
and a component with r(D) = 2 has base ≥ −1. Take Y_z = {a_z}.
- If z's three goods lie in one component, or in three, all bases are 0 (they are ≥ 0 and sum to 0): the component of
  a_z is active, the others balanced; Z = ∅.
- If they lie in two components D₂ (two goods) and D₁ (one good), then (base(D₂), base(D₁)) is (0, 0) or (−1, 1). In
  the first case, or if a_z ∈ D₂, no component is needy; Z = ∅. Otherwise D₂ is needy and contains b_z and c_z:
  take Z = {b_z}. Then L = {b_z} and (P4) holds.

**q = 2**, Q = {u, v}: Σ S = 2, Σ r = 6, Σ base = −2. By (†), a component has (S, r, base) equal to (0, 2, −1) (a
thread component), (1, 1, 0), (1, 3, −1), (2, 2, 0) or (2, 4, −1); in particular every base is 0 or −1.

*(i) a_u ≠ a_v.* Take Y_u = {a_u}, Y_v = {a_v}, and one spare in each needy component. By the remark above, only (P4)
needs checking, and only when there are two needy components. Then Σ_{C active} ε(C) = 2. An active component has
ε(C) = base(C) + (number of the goods a_u, a_v in C), and base(C) ≤ 0, so both tops lie in active components of base
0: either in one, which by (†) has S = r ≥ 2, hence S = r = 2, so it contains no pair (z, g) other than (u, a_u) and
(v, a_v); or in two, each with S = r ≥ 1, hence S = r = 1. Either way all of Σ S = 2 is used up, so every other component is a
thread component, and the four remaining pairs (u, b_u), (u, c_u), (v, b_v), (v, c_v) lie in exactly two thread components T₁, T₂ (the two needy ones).
- If b_u and c_u lie in different thread components, change the plan to Y_u = {b_u, c_u} (a 2-holder),
  Y_v = {a_v}, Z = ∅: T₁ and T₂ get one good of u each and are balanced; the component of a_v gets excess 1 and contains
  neither b_u nor c_u (the goods in Y_u; it may contain a_u), so it is active and satisfies (P2); the component of a_u, if different, has base 0 and no marked good.
  All components are balanced or active, Z = ∅, and (P3), (P4) are empty.
- Otherwise b_u, c_u ∈ T₁, so b_v, c_v ∈ T₂ (each thread component has r = 2). The two spares, one in T₁ and one in T₂,
  are never both goods of u or both goods of v: (P4) holds.

*(ii) a_u = a_v = g.* Take Y_u = {g} and Y_v = {b_v} (a b-pin: g is the only good of the 1-holder u, so (Q0) holds),
and one spare in each needy component. As in (i), two needy components would force the goods g and b_v into active
components of base 0, where S = r by (†). The component of g has r ≥ 2 (u and v both value g), so r ≥ 3 if it also
contains b_v, and otherwise the two components have S ≥ 2 and S ≥ 1: either way Σ S ≥ 3 > 2. So at most one
component is needy, at most one spare is used, and (P4) holds. ∎

With Theorem 5, **D holds for every connected β = 3 core with at most two Q-agents**, by hand. The q = 1 case with a
spare is Case 3a of `proofs/beta2.md` one level up (the collector theorem now needs two collectors when
base(D₁) = 1). `src/dg_beta3.py --hand` builds exactly these plans and checks them with both plan checkers on every
β = 3 core with q ∈ {1, 2} and 3 ≤ n ≤ 10 (`results/hand_plans_beta3.log`; evidence only).

## 5. Q-plans for β = 3 in general: reduction to finitely many cores

**Lemma 7.** Let C be a connected core with β = 3. Every choice of orders of its Q-agents admits a Q-plan.

The proof reduces Lemma 7 to finitely many cores (Lemmas 8 and 9) and checks those by computer.

*Threads.* A vertex of H is a *branch vertex* if its H-degree is at least 3: the Q-agents and the goods of degree
≥ 3. P-agents and goods of degree 2 have H-degree 2. If H had no branch vertex it would be a cycle and β = 1, so for
β = 3 every edge of H lies on exactly one *thread*: a path of H between branch vertices (possibly the same one) whose
interior vertices have H-degree 2. A thread that starts and ends at the same good is a *good-loop*. A β = 3 core is
*reduced* if every thread has at most one P-agent in its interior, and every good-loop at most two.

**Lemma 8 (shortening).** Let C be a connected β = 3 core with a thread t that has at least two P-agents in its
interior, or at least three if t is a good-loop. Then there is a connected β = 3 core C′ with one agent fewer, the same
Q-agents with the same goods, such that every Q-plan of C′ (for some orders of the Q-agents) is a Q-plan of C (for
the same orders). Consequently, if every reduced β = 3 core has a Q-plan for every order of its Q-agents, Lemma 7
holds.

*Proof.* Along t, agents and goods alternate. Take two consecutive P-agents f, f′ in the interior of t and the good g
between them; g has H-degree 2, so it is valued by exactly f and f′. Let g″ be the other shared good of f and g‴ that
of f′. Then g‴ ≠ g″: otherwise f, g, f′, g″ would form a cycle of H in which g, f, f′ have degree 2, so either g″ has
degree 2 as well and the cycle is all of H (impossible), or t is a good-loop at g″ with exactly the two P-agents
f, f′ (excluded). Build C′ by deleting f, its private good p_f and g, and replacing g by g″ in R_{f′} (with any
balanced values for f′; Q-plans do not depend on values). Then f′ values
p_{f′}, g″, g‴ (distinct), g″ keeps its degree (f′ replaces f), all other goods and agents are unchanged, so C′ is a
core, connected (H′ is H with the path g″ f g f′ replaced by the edge g″ f′), with n′ = n − 1, m′ = m − 2, hence
β′ = β = 3. The Q-agents and their goods are unchanged (g was valued only by P-agents).
K′ is K with the two edges f = g″g and f′ = g g‴ replaced by the single edge f′ = g″g‴: the components correspond,
with the same base and the same vertices except g. A Q-plan (Y, Z, T) of C′ uses only goods of Q-agents and goods of
V ∖ {g}; in C every component has the same ε, so (P1) and (P2) hold, the dump target T = {v} (if any) is still a good
of V outside ⋃Y ∪ Z, and (Q0), (P4) only involve the Q-agents' goods. So (Y, Z, T) is a Q-plan of C.
Each step removes an agent, so repeating it ends at a reduced core, from which Q-plans lift back step by step. ∎

**Lemma 9 (reduced cores are small).** A reduced β = 3 core with at least one Q-agent has at most 10 agents.

*Proof.* Let B be the set of branch vertices of H and Γ the multigraph on B with one edge per thread (L11). Γ has the
cyclomatic number of H, 3, so |E(Γ)| = |B| + 2, and every vertex of Γ has degree ≥ 3, so 3|B| ≤ 2|B| + 4: |B| ≤ 4
and Γ has at most 6 threads. Every P-agent lies in the interior of exactly one thread, so the number of P-agents is at
most the number of threads plus the number of good-loops. A good o with ℓ good-loops has degree ≥ 2ℓ + 1 (it is also
joined to the rest of H, which contains a Q-agent), so deg(o) − 2 ≥ ℓ, and the number of good-loops is at most
Σ_{g ∈ V} (deg(g) − 2) = 4 − q (§1). Hence n = q + π ≤ q + 6 + (4 − q) = 10. ∎

*The finite check.* A connected β = 3 core has n ≥ 3 (m = 2n − 2 ≥ 3). `src/dg_beta3.py` enumerates all connected
cores with m = 2n − 2 and 3 ≤ n ≤ 10 (nauty genbg, `src/cores_nauty.py`): 2, 16, 62, 211, 541, 1,232, 2,477 and
4,619 cores. It marks the reduced ones and stores, for each reduced core and each of the 6^q orders of its Q-agents, a
Q-plan found by exhaustive search (`beta3.find_plan`); no order lacks one. Reduced cores (all q, including q = 0):
2, 15, 45, 96, 108, 81, 36 and 11 for n = 3, …, 10, with 110,259 Q-plans in all (`results/qplans_beta3.json.gz`,
`results/qplans_beta3.log`, under 3 minutes on 2 CPUs). Two independent checks (`results/check_qplans.log`, under
a minute):
- `tools/check_enum.py` certifies, by orbit counting and independently of nauty, that the list is complete up to
  isomorphism for every n;
- `tools/check_qplans.py`, written without the search code, re-derives which cores are reduced (with a different
  algorithm: components of H minus its branch vertices) and checks every stored plan against the definition of §3.

By Lemmas 8 and 9 every β = 3 core with a Q-agent shortens to a reduced core with at most 10 agents, which is
isomorphic to one on the list. Q-plans are invariant under isomorphism (a relabelling of agents and goods carries
orders, components and conditions (Q0)–(P4) along), and the check covers every order of the listed core's Q-agents.
Cores without Q-agents are covered by Corollary 3. This proves Lemma 7.

*Proof of Theorem D3.* Lemma 7 and Theorem 5. ∎

## 6. What the construction does (data from `results/verify_beta3.log`)

- **The large bundle.** It is the main collector's (its private good, the private goods of the agents of J, which
  hold their top (case T of L5) or their b with their top alone (case B), and the spares), or a dump target's
  (a P-agent holding its private good and one shared good, or a 2-holder, plus the spares), or there is none.
  Spares are shared goods, valued only by agents that are safe regardless (P-agents of balanced components, 2-holders,
  a-pins for which (P4) holds, and b-pins, whose top is held by a 1-holder and so is never a spare). This is close to, but not the same as, the canonical shape of conjecture S2.K
  (`proofs/construction.md` §5.2: owner in case C, bundle = its c plus private goods of agents in cases T or B):
  here the main collector may be in case T, B or C, and spares are shared goods. D3 is proved directly; it does not
  go through construction LB (S2.LB) or S2.K.
- **Which tools each q needs** (over every β = 3 core with n ≤ 7 and every order of its Q-agents; `src/dg_beta3.py`
  searches roles in the order a-pin, b-pin, 2-holder, and spares before dump targets): q = 0 and q = 1 need only
  a-pins, spares and collectors; q = 2 also needs b-pins and 2-holders; q = 3 and 4 need all tools, including dump
  targets (smallest example: n = 4, agents (0,1,5), (0,1,4), (2,3,4), (2,3,4), with orders a–b–c equal to (0,1,5),
  (4,0,1), (2,4,3), (2,4,3): Q-plan Y = {0}, {2}, {4} for agents 1, 2, 3 (a b-pin, an a-pin, a b-pin whose top 2 is
  held by agent 2), spare 3, no active component, dump target {1}, the head of agent 0: allocation {1, 3, 5}, {0},
  {2}, {4}).
- **How much the pieces are used** (n = 7, all 151,445,376 core–profile pairs): the large bundle is the main
  collector's in 58% of them, a dump target's in 22% (a Q-agent's in 0.4%), and in 20% every bundle has at most two
  goods. The largest bundle has 6 goods (a collector's; dump targets: at most 4). The multi-collector switching
  needs up to 5 switches; 81% of the pairs need none. Per-q tallies are in `results/verify_beta3.log`.

## 7. Scope and what is open

- **Proved by hand:** Theorem 2 and Theorem 5 for every β; Corollary 3 (D for every connected core in which every
  agent has a private good, any β); D for β = 3 cores with q ≤ 2 (Lemma 6).
- **Certified (finite computation behind a proved reduction):** Lemma 7 for q = 3, 4, hence Theorem D3 for all
  β = 3 cores.
- **Open:** a hand proof of Lemma 7 for q = 3, 4 (§6 lists which roles these need; in particular dump targets).
  Beyond β = 3: Theorem 5 holds for every β, and so do Lemma 8 (its proof only uses that H is not a cycle) and the proof of Lemma 9, which
  in general gives n ≤ q + (3β − 3) + (2β − 2 − q) = 5(β − 1) for reduced cores with a Q-agent (Γ has at most
  3β − 3 threads, and Σ_{g ∈ V} (deg(g) − 2) = 2β − 2 − q). So D for any fixed β reduces to Q-plans for finitely
  many reduced cores. For β = 4 that means n ≤ 15, too far for enumerating all cores with genbg; generating the
  reduced cores directly from their kernels Γ would be needed. Whether every core has a Q-plan for every order of
  its Q-agents is open for β ≥ 4.
- Disconnected cores (ledger open item 5) are not addressed.
