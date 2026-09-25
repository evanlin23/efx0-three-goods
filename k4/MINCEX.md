# k = 4: structure of a minimal counterexample

Workstream `proof/k4-mincex`. The minimal-counterexample route of `proofs/min_counterexample.md` (rows MC1–MC6),
carried to TARGET₄: every instance with nonnegative additive valuations and |R_i| ≤ 4 for every agent has a complete
EFX₀ allocation. Ledger rows `K4.MC0`–`K4.MC7`. None of them has been reviewed yet. The rows record the status each
proposes (PROVED or CERTIFIED), with its artifacts, pending the coordinator's review.

**Results.**
- *Soundness of local reductions at k = 4* (K4.MC0, K4.MC1). The inductive statement is plain EFX₀ existence, as at
  k = 3. A minimal counterexample is a connected k = 4 core with strict types, and Lemmas M1 and M1(b) hold verbatim,
  with gadget agents of up to 4 goods. Proof in §1–§2.
- *Local reductions*, certified by `k4/reduce4.py` (type-aware, all profiles of a configuration at once) and re-checked by
  the independent `k4/check_reductions4.py` (with a sensitivity test). In a minimal counterexample:
  - **K4.MC2**: no agent has two private goods (a one-agent gadget with one private good fewer handles all 144 types);
  - **K4.MC3**: no good of degree 2 is shared by two P3 agents (M3 carried to k = 4);
  - **K4.MC5**: if a P3 agent f shares a good g of degree 2 with a Q3 or P4 agent e, then e does not value f's other
    good, f ranks g last and its other shared good first, and e ranks g first (plus a weaker restriction for Q4).
- *Bounds* (K4.MC4, proved from the above by counting). A minimal counterexample (or one within 𝒞_β) has
  **n ≤ 3(β − 1)** agents. From K4.MC2 and K4.MC3 alone: n ≤ 5(β − 1) − t − 2n_{Q4}.
- ***TARGET₄ for β ≤ 3*** (K4.MC6). Every instance with |R_i| ≤ 4 whose incidence-graph components have cyclomatic
  number ≤ 3 has an EFX₀ allocation, and hence every instance whose k = 4 core components have β ≤ 3. β ≤ 2 follows
  from the bound and K4.R3. β = 3 leaves exactly **9 cores** (n = 5, 6, with restricted type domains, 21.7 million
  profiles). All 9 are certified, even in the shape D2, and re-checked by an independent enumeration (82,782 cores).
- *What remains* (§7). At β = 4 the bound gives n ≤ 9, and 5,558 candidate cores remain, with up to 5.7·10¹⁴
  restricted profiles. The Q4 configurations and the goods of degree ≥ 3 need reductions.

Notation as in `proofs/min_counterexample.md`. θ_i(B) = v_i(B) − min_{g ∈ B} v_i(g) (0 if |B| ≤ 1); agent i is *safe*
in X iff v_i(X_i) ≥ θ_i(X_j) for all j ≠ i. In a k = 4 core (`k4/SCOUT.md` §2, K4.CORE) an agent has 3 or 4 goods and
at most d − 2 private goods. The four kinds that survive K4.MC2 are named by that count:
**P3** (3 goods, one private), **Q3** (3 goods, none), **P4** (4 goods, one private), **Q4** (4 goods, none); **PP4**
has 4 goods, two private (then p + q < s + t). A *type* is a strict balanced order type (K4.OT: 6 for 3 goods, 288 for
4). Γ′ is the incidence graph without the private goods. It is connected and has the same cyclomatic number
β = Σ_i d_i − n − m + 1. In Γ′ an agent has degree d − (number of private goods): P3 and PP4 have degree 2 (*thread
agents*), Q3 and P4 have 3 (*E3 agents*), Q4 has 4.

## 1. The inductive statement (K4.MC0)

A *counterexample* is an additive instance with |R_i| ≤ 4 for every agent and no EFX₀ allocation. A *minimal*
counterexample has the fewest agents n and, among those, the fewest goods m. For β ≥ 1, 𝒞_β is the class of such
instances whose incidence graph has only components of cyclomatic number ≤ β. A *minimal counterexample within 𝒞_β*
is minimal among the counterexamples in 𝒞_β. Deleting agents or goods never raises a component's cyclomatic number, so
𝒞_β is closed under the CORE reductions and under taking components.

**Lemma K4.MC0.** Let H be a minimal counterexample (or one within 𝒞_β). Then:
- (a) every instance with |R_i| ≤ 4 (in 𝒞_β) and fewer agents, or with n agents and fewer goods, has an EFX₀
  allocation;
- (b) H is a connected k = 4 core;
- (c) we may assume that every agent's valuation is strict (a strict balanced type), and only the types matter;
- (d) some agent has 4 goods, and n ≥ 5; if n = 5, at least three agents have 4 goods.

*Proof.* (a) is minimality. (b) If H is not a core, one step of the K4.CORE reduction (R1, R2 or L3; `k4/SCOUT.md` §2)
applies. It gives an instance with fewer agents, or fewer goods, that lies in 𝒞_β when H does. That instance has an
EFX₀ allocation by (a), and the step extends it to H. If H is a core but not connected, each component has fewer agents
(by K4.L's L6: every component has at least 2 agents) and lies in 𝒞_β. So each has an EFX₀ allocation, and L6 combines
them. (c) K4.TIE's perturbation (supported on each R_i) moves every agent into a strict chamber C_i without changing the
hypergraph. If the strict profile (C_i) had an EFX₀ allocation X, then X would be EFX₀ for H by the closure argument
of K4.TIE. So the strict profile is a counterexample with the same n and m, and hence a minimal one. For a fixed
allocation, an agent's safety depends only on its type (its behavior on disjoint subsets, K4.OT). (d) If every agent
has ≤ 3 goods, TARGET (proved, `proofs/lb_last_step.md`) applies. Every connected k = 4 core with n ≤ 4 is covered by
K4.R3 and K4.R4, and with n = 5 and at most two 4-good agents by K4.R5 (all certified, strict profiles). ∎

(d) uses computation (K4.R3–K4.R5). The literature (Mahara; Afshinmehr et al., as in T3) would add m ≥ n + 4 and a good
of degree ≥ 3; nothing below uses it.

## 2. Local reductions are sound (K4.MC1)

The definitions of `proofs/min_counterexample.md` §2 are used verbatim. A *configuration* (S, I) is a set S of agents
and a set I of goods that no agent outside S values; ∂ is the set of *boundary goods*, the other goods valued by S. A
*reduction* replaces (S, I) by a gadget (S′, I′): agents S′ valuing only goods of I′ ∪ ∂, **each with at most 4
relevant goods** (the only change from k = 3), and goods I′ that no outside agent values. Then come local states,
extensions, U(B), "inner" and "dominated".

**Lemma K4.MC1 (M1 and M1(b) at k = 4).** Let H be a minimal counterexample (or one within 𝒞_β), and let H′ be the
result of a reduction. Suppose H′ is smaller (|S′| < |S|, or |S′| = |S| and |I′| < |I|), and lies in 𝒞_β whenever H
does. Suppose also that every admissible local state of an EFX₀ allocation of H′ has an extension in which every agent of S
is safe and every new or modified bundle is dominated (M1), or, with the unenvied bundle, the relaxed condition of
M1(b). Then H has an EFX₀ allocation. So a minimal counterexample contains no such configuration (with its agents'
types).

*Proof.* H′ has an EFX₀ allocation Y by K4.MC0(a). It is an instance with |R_i| ≤ 4, arbitrary additive valuations, no
core condition needed. The proofs of M1 and M1(b) in `proofs/min_counterexample.md` §2 never use the number of goods
per agent:
- agents of S are judged by the extension directly;
- outside agents only need "they value nothing in I ∪ I′" and the monotonicity of θ;
- M1(b) needs only F2 (rotating envy cycles keeps EFX₀; any additive valuations).

They carry over word for word. ∎

Three remarks, each used by the certificates below:
- *The gadget may depend on the profile.* H is fixed, and so is its profile, so it suffices that, for H's profile,
  some reduction satisfies the lemma. The certificates therefore cover each configuration's profiles by a union of
  reductions, and a gadget agent's valuation may copy an agent of S (as the contractions do) or be any fixed valuation.
- *A boundary good need not have an outside valuer.* The proof uses only that outside agents value nothing in I ∪ I′.
  So a configuration certified with a good in ∂ also covers the case where no outside agent values that good.
- *One representative per type suffices.* An agent's safety in X depends only on its type (K4.MC0(c)), so the
  checkers judge each type through one integer representative. The generator and the checker use different
  representatives.

## 3. The tools

**`k4/reduce4.py`** (the reducer). It generalizes `src/reduce.py` to 3- and 4-good agents with types, and decides a
reduction for every profile of the configuration at once:
1. For every local state, it computes the admissible profiles: gadget agents safe (and not envying the unenvied bundle),
   as a boolean array over the types of the agent a gadget copies.
2. It enumerates every extension allowed by M1/M1(b) (moved items and interior goods placed, every changed bundle
   dominated).
3. It keeps, per state, the extensions with non-dominated "views", each with the boolean mask of the types under which
   each agent of S is safe (raw EFX₀ definition, the type's integer representative from `k4/order_types.json`).
4. A profile is reduced when every state admissible for it is covered by the outer product of some extension's masks.

**Gadget search.** For one-agent gadgets h on ∂ (plus one gadget good z′ when |∂| < 4), the state coverages do not
depend on h's valuation, so they are computed once. Admissibility is then evaluated for a whole menu of valuations at
once: one valuation per behavior class of 3 or 4 goods with values 0..10 (43 and 1,665 classes, zeros allowed). A
greedy choice of reductions covers every reduced profile, and each chosen one is re-run directly and written to the
certificate. For every admissible state it stores a few extensions whose masks cover the reduced profiles.

**`k4/check_reductions4.py`** (the independent checker; no shared code):
- its own type enumeration (the grid [1, 16]^d, each type represented by its *last* grid point);
- its own state enumeration (label maps in restricted-growth form, canonicalized);
- the raw definition as v(own) ≥ v(B) − v(g);
- its own gadget-legality check: smaller, ≤ 4 goods per gadget agent, all in I′ ∪ ∂, and H′ ∈ 𝒞_β for every way the rest
  can connect the boundary goods;
- its own check of every stored extension against M1/M1(b): goods conserved, outside bundles keep their goods outside
  I′, moved items only to S or to outside bundles of gadget goods, every changed bundle dominated.

It re-derives the covered profiles and unites them per configuration. With `--expect` it fails on any count
mismatch. It writes the profiles *not* covered (`results/k4_min_cex_px_fail.json`), which §5–§6 use.
- Certificate: `results/k4_min_cex_reductions.json.gz` (177 records, 93,552 states); log
  `results/k4_min_cex_reductions.log`.
- Check: `results/k4_check_min_cex_reductions.log`. All counts agree and there are 0 problems. The same log has the
  *sensitivity test*. Each of these corruptions is rejected: a deleted state, a good dropped from an extension, an extra
  gadget agent, the unenvied bundle dropped, a gadget agent with 5 goods, an undeclared gadget good, an interior good
  moved into an outside bundle (breaking domination), a gadget that is not smaller, and a gadget that closes a new cycle.
- Regression: `src/reduce.py`'s k = 3 counts are reproduced exactly (pair: DEL 23, CON-e 26, CON-f 26; loop: DEL 23,
  GAD 23; `python3 k4/mincex4.py pair P3 P3`).

## 4. The reductions

**K4.MC2 (no agent with two private goods).** A minimal counterexample (or one within 𝒞_β) has no PP4 agent.

*Configuration* single-PP4: S = {e}, R_e = {s, t, p, q}, I = {p, q} (private), ∂ = {s, t}; 144 types (p + q < s + t).
*Reductions*: a gadget agent e′ on {s, t, z′} with one gadget good z′, so H′ has the same agents and one good fewer.
Five valuations of e′ cover all 144 types, for example s = t = 2, z′ = 3 (72 types) and s = 2, t = 4, z′ = 3 (26). (Intuition, not used: e′
is an agent with one private good z′ standing for p and q. Where e′ holds z′, e can take p and q, and wherever Y
threatens e′ through s and t together, e′'s safety forces the constraint e needs.) In the incidence graph two
pendant leaves become one, so H′ ∈ 𝒞_β. CERTIFIED (both implementations: 144 of 144).

**K4.MC3 (M3 at k = 4).** In a minimal counterexample (or one within 𝒞_β) no good of degree 2 is shared by two P3
agents. *Configurations* pair and loop of `proofs/min_counterexample.md` §4 (36 rankings each). The reductions are
DEL, CON-e, CON-f and GAD. The certificate of M3 is valid at k = 4 as it stands: M1 holds at k = 4 (K4.MC1), and a 3-good
agent's type is its ranking. The new tools re-certify it (pair 36/36, loop 36/36, with the k = 3 counts per
reduction). With K4.MC2, a thread agent is a P3 agent, so every thread carries at most one agent (§5). CERTIFIED.

**K4.MC5 (a P3 agent next to an E3 or Q4 agent).** Let f be a P3 agent with shared goods g, y and private good p_f, and let
g have degree 2, shared with an agent e of kind Q3, P4 or Q4. *Configuration* px (*closed* if e also values y, *open*
otherwise). S = {e, f}, I = {g, p_f} (+ p_e for P4). The reductions are DEL and every one-agent gadget h on ∂ (+ z′), from
the menu. Coverage (both implementations):

| e | open | closed |
|---|---|---|
| Q3 | 34 of 36 | **36 of 36** |
| P4 | 1,718 of 1,728 | **1,728 of 1,728** |
| Q4 | 648 of 1,728 | 1,656 of 1,728 |

So in a minimal counterexample:
- (i) if e is Q3 or P4 (an *E3 agent*), the configuration is open;
- (ii) f ranks y > p_f > g (its shared-with-e good last, its other shared good first);
- (iii) e ranks g first.

For Q3 the two profiles left are e: g > a > b or g > b > a with f: y > p_f > g. For P4 they are 10 types of e, all with g on
top, with the same f. For Q4 the profiles left are recorded in `results/k4_min_cex_px_fail.json`; §6 uses them, but
the bound of §5 does not. CERTIFIED. The failed part is in `attempts/k4-mincex-px-open.md`.

A typical gadget: h valuing a = b = 2 and z′ = 3, ignoring y. It reduces 6 of the 36 Q3 profiles and 800 of the 1,728 P4
ones. It is safe when holding z′ unless a, b sit together in a bundle of ≥ 3 goods; this is the same gadget that
drives K4.MC2.

## 5. Bounds (K4.MC4)

Let H be a minimal counterexample (or one within 𝒞_β). Let n₀, n₁, n₂ be the numbers of P3, E3 (Q3 or P4) and Q4
agents (no PP4 by K4.MC2), and t = Σ (deg g − 2) over the shared goods of degree ≥ 3.

**Theorem K4.MC4.** n ≤ 3(β − 1). Also, from K4.MC2 and K4.MC3 alone, n ≤ 5(β − 1) − t − 2n₂.

*Proof.* In Γ′ every agent has degree 2 (P3), 3 (E3) or 4 (Q4), and every shared good has degree ≥ 2.
Σ_v (deg_Γ′ v − 2) = 2|E(Γ′)| − 2|V(Γ′)| = 2(β − 1), so
  (1) n₁ + 2n₂ + t = 2(β − 1).
Count the incidences of P3 agents with shared goods: 2n₀ = A + B + C. Here A counts incidences at goods of degree ≥ 3.
B counts those at goods of degree 2 whose other valuer is an E3 agent, and C those whose other valuer is a Q4 agent.
By K4.MC3 the other valuer is never P3.
- A ≤ Σ_{deg g ≥ 3} deg g ≤ 3t, since deg ≤ 3(deg − 2) when deg ≥ 3.
- C ≤ 4n₂.
- B ≤ n₁. By K4.MC5(iii), an E3 agent e ranks first every good of degree 2 it shares with a P3 agent. Its type is strict,
  so there is at most one such good per E3 agent, and each such good carries one P3 incidence.

So 2n₀ ≤ 3t + n₁ + 4n₂, and n = n₀ + n₁ + n₂ ≤ (3t + 3n₁ + 6n₂)/2 = 3(β − 1) by (1).

For the second bound, replace B + C by the number of goods of degree 2, which is at most 3n₁ + 4n₂ (each is valued by a
non-P3 agent, K4.MC3). Then 2n₀ ≤ 3t + 3n₁ + 4n₂, and n ≤ (3t + 5n₁ + 6n₂)/2 = 5(β − 1) − t − 2n₂. ∎

K4.MC5(ii) adds that a P3 agent has at most one good of degree 2 shared with an E3 agent: it would rank both last. The
proof above does not need this, but the shape generator uses it. `k4/mincex_shapes.py` checks the bound computationally
too: it lists Γ′ for β = 3 up to n = 5(β − 1) = 10 and finds nothing left above n = 6
(`results/k4_min_cex_shapes_3.log`).

The k = 3 analogue (MC4) was n ≤ 5(β − 1) − t. Here K4.MC5 improves it to 3(β − 1). Whether K4.MC5's Q3 case holds at
k = 3 was not checked: there, gadget agents may have only 3 goods.

## 6. TARGET₄ for β ≤ 3 (K4.MC6)

**Theorem K4.MC6.** Every instance with |R_i| ≤ 4 in 𝒞₃ has an EFX₀ allocation. Hence TARGET₄ holds for every instance
whose k = 4 core (from any sequence of the K4.CORE reductions) has only connected components with cyclomatic number
≤ 3.

*Proof.* Let H be a minimal counterexample within 𝒞₃: a connected k = 4 core with strict types and β ≤ 3 (K4.MC0).
- β = 1: orientation (K4.L).
- β = 2: n ≤ 3 by K4.MC4, but n ≥ 5 by K4.MC0(d).
- β = 3: 5 ≤ n ≤ 6. Take H′s graph Γ′ and kinds. Every agent is P3, Q3, P4 or Q4 (K4.MC2), no good of degree 2 is shared
  by two P3 agents (K4.MC3), and at least one agent has 4 goods, three if n = 5 (K4.MC0(d)). The profile, restricted to
  every pair (e, f) of configuration px in H, is one that K4.MC5's certificate does not cover. The list of such cores,
  with each agent's type domain cut to the projections of the uncovered sets, is computed in two independent ways
  (below). It has exactly 9 cores, and each of them has an EFX₀ allocation for every profile in the product of its
  domains. By K4.MC0(c) only H's types matter, so H has an EFX₀ allocation, a contradiction.

The second sentence: each K4.CORE step extends EFX₀ allocations, and components combine (L6). ∎

*The 9 cores* (n, m, kinds; profiles in the product of the restricted domains; allocations in the certificate):

| n | m | kinds | profiles | allocations |
|---|---|---|---|---|
| 5 | 11 | P4 P4 P3 P4 P3 | 28,800 | 4 |
| 5 | 11 | P4 P4 P3 Q4 P3 | 28,800 | 2 |
| 6 | 11 | Q4 P3 P3 P3 P3 P3 | 442,368 | 39 |
| 6 | 11 | P4 Q3 P3 P3 P3 P3 | 720 | 1 |
| 6 | 11 | P4 Q3 Q3 P3 P3 P3 | 40 | 1 |
| 6 | 12 | P4 P4 P3 P3 P3 P3 | 3,600 | 1 |
| 6 | 12 | Q4 P3 P3 P3 Q4 P3 | 21,233,664 | 22 |
| 6 | 12 | P4 P4 Q3 P3 P3 P3 | 200 | 1 |
| 6 | 13 | P4 P4 P4 P3 P3 P3 | 1,000 | 1 |

Every allocation in the certificate has at most one bundle of more than 2 goods, so these 9 also satisfy K4.D (D2) on
their restricted domains. This says nothing about K4.D for β ≤ 3 in general: D is not the inductive statement.

*Generation* (`k4/mincex_shapes.py`, log `results/k4_min_cex_shapes_3.log`):
1. It lists Γ′ with nauty's genbg: bipartite, connected, agents of degree 2–4, shared goods of degree ≥ 2, cyclomatic
   number 3.
2. It drops Γ′ that K4.MC3 or the Q3/P4 part of K4.MC5 excludes whatever the kinds.
3. It makes each degree-3 agent Q3 or P4, and keeps the cores with the right number of 4-good agents.
4. It cuts the domains by the px profiles left (for Q3, P4 and Q4, intersected over the labelings of e's symmetric goods).
5. It merges isomorphic cores.

This gives 407 cores with n ≤ 6 before the restrictions and 9 after. *Certification* (`k4/mincex_cert.py`,
`results/k4_min_cex_cores_3.json.gz`, `results/k4_min_cex_cores_3.log`) uses `k4/search4.py`'s CEGAR with the
restricted domains, model D2; no profile needed more.

*Independent check* (`k4/check_mincex_cores.py`, log `results/k4_check_min_cex_cores_3.log`):
- it lists every connected k = 4 core with 5 ≤ n ≤ 6 and β = 3 with genbg at the level of the full incidence graph (82,782
  cores; a different genbg class from the Γ′ list);
- it re-implements the filters;
- it cuts the domains with the uncovered px profiles as re-derived by `check_reductions4.py`, judging types by signature
  on its own type enumeration;
- it matches every survivor to a certified core up to isomorphism, and checks coverage of the full product of its
  domains with the raw definition.

Result: 407 cores pass the filters, the same 9 remain with the same profile counts, all covered. *Sensitivity test*
(`k4/test_check_mincex_cores.py`, `results/k4_test_check_mincex_cores.log`): it rejects a deleted allocation, a deleted
core, an allocation replaced by a bad one, and an enlarged px failing set.

Trust points:
- nauty's genbg. The two enumerations are different classes of graphs; neither is checked by orbit counting.
- K4.R3–K4.R5 and TARGET (existing rows).
- The hand proofs of K4.MC0, K4.MC1 and K4.MC4.

## 7. What remains

- **β = 4.** K4.MC4 gives n ≤ 9. Listing Γ′ for β = 4, n ≤ 9 with the same filters leaves 5,558 cores up to
  isomorphism (346, 2,183, 2,110, 835 and 84 for n = 5, …, 9), with restricted profile spaces of up to 5.7·10¹⁴
  (`results/k4_min_cex_shapes_4.log`, `results/k4_min_cex_shapes_4.json.gz`; generated, not certified). The n = 5 part
  (346 cores) overlaps compute/k4-frontier's targets (n = 5 with three or four 4-good agents). The
  largest spaces come from Q4 agents and 4-good E3 agents, whose K4.MC5 restrictions are weak or absent. Needed:
  reductions at Q4 agents (px-Q4 open reduces only 648 of 1,728; a one-agent gadget has no room for a gadget good there),
  reductions at goods of degree ≥ 3, and a two-agent gadget search (two agents on ∂ with fewer goods).
- **General β.** n ≤ 3(β − 1) holds for every β, so for each β only finitely many cores remain. Unavoidability (every
  core contains a reducible configuration) is open.
- The joint (e, f) restrictions of K4.MC5 are used only through per-agent projections. Using them jointly would shrink the
  profile spaces further, as would a CEGAR that accepts joint constraints.

## Reproduce

```
python3 k4/mincex4.py all --write=results/k4_min_cex_reductions.json.gz          # ~2 min on 4 CPUs
python3 k4/check_reductions4.py results/k4_min_cex_reductions.json.gz --fail-out=results/k4_min_cex_px_fail.json \
    --expect=single-PP4:144 --expect=pair-P3-P3:36 --expect=loop-P3-P3:36 --expect=px-Q3:34 --expect=px-Q3-closed:36 \
    --expect=px-P4:1718 --expect=px-P4-closed:1728 --expect=px-Q4:648 --expect=px-Q4-closed:1656   # ~30 s
python3 k4/check_reductions4.py results/k4_min_cex_reductions.json.gz --selftest
(cd k4 && python3 mincex_shapes.py 3 --write=../results/k4_min_cex_shapes_3.json.gz)            # ~10 s
(cd k4 && python3 mincex_cert.py ../results/k4_min_cex_shapes_3.json.gz ../results/k4_min_cex_cores_3.json.gz)
(cd k4 && python3 check_mincex_cores.py 3 ../results/k4_min_cex_cores_3.json.gz ../results/k4_min_cex_px_fail.json)  # ~50 s
(cd k4 && python3 test_check_mincex_cores.py)                                    # ~5 min
(cd k4 && python3 mincex_shapes.py 4 --nmax=9 --write=../results/k4_min_cex_shapes_4.json.gz)  # beta = 4 list, ~10 min
(cd k4 && python3 mincex_attempts.py drop-private; python3 mincex_attempts.py px-open)         # failed reductions
```
