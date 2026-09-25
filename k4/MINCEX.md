# k = 4: structure of a minimal counterexample

Workstream `proof/k4-mincex`. The minimal-counterexample route of `proofs/min_counterexample.md` (rows MC1–MC6),
carried to TARGET₄: every instance with nonnegative additive valuations and |R_i| ≤ 4 for every agent has a complete
EFX₀ allocation. Ledger rows `K4.MC0`–`K4.MC7`. §1–§7 reviewed by the coordinator (two independent reviews of PR #23,
one of them a brute-force referee check of the stored extensions and a re-derivation of the bound, the other an exact
computational re-run with its own generator); §8 (K4.MC7) reviewed (two independent reviews of PR #28, a mathematical referee report and a computational re-run).

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
- ***TARGET₄ for β ≤ 4*** (K4.MC7, §8): 5,558 candidates; 5,552 certified (D2) and re-checked; 6 graphical all-P4
  cores (n = 6, m = 15) by the multigraph theorem of Afshinmehr et al.

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

(a)–(c) are proved; (d) rests on the certified rows K4.R3–K4.R5 (and TARGET), so the lemma as a whole is CERTIFIED. The literature (Mahara; Afshinmehr et al., as in T3) would add m ≥ n + 4 and a good
of degree ≥ 3; §1–§7 do not use it; §8 (K4.MC7) uses Afshinmehr et al. only for 6 graphical cores.

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
mismatch. Every record must declare one of the 9 configurations exactly as hard-coded in the checker (agents with
their goods in order, I, ∂), or it is rejected before coverage is united. It writes the profiles *not* covered
(`results/k4_min_cex_px_uncovered.json`, compact JSON) and records its SHA-256 in its log, which §6's checker verifies.
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

So in a minimal counterexample (or one within 𝒞_β) **with strict types**, chosen by K4.MC0(c) (statements (ii) and (iii)
are about types):
- (i) if e is Q3 or P4 (an *E3 agent*), the configuration is open;
- (ii) f ranks y > p_f > g (its shared-with-e good last, its other shared good first);
- (iii) e ranks g first.

For Q3 the two profiles left are e: g > a > b or g > b > a with f: y > p_f > g. For P4 they are 10 types of e, all with g on
top, with the same f. For Q4 the profile of (e, f) lies, under every labeling of e's other goods,
in the set recorded in `results/k4_min_cex_px_uncovered.json` (profiles no reduction covers, not EFX₀ failures); §6
uses it, but the bound of §5 does not. CERTIFIED. The failed part is in `attempts/k4-mincex-px-open.md`.

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
- β = 0 is impossible: Γ′ is connected with minimum degree ≥ 2 (K4.L's L11), so it contains a cycle.
- β = 1: orientation (K4.L).
- β = 2: n ≤ 3 by K4.MC4, but n ≥ 5 by K4.MC0(d).
- β = 3: 5 ≤ n ≤ 6. Take H's graph Γ′ and kinds. Every agent is P3, Q3, P4 or Q4 (K4.MC2), no good of degree 2 is shared
  by two P3 agents (K4.MC3), and at least one agent has 4 goods, three if n = 5 (K4.MC0(d)). The profile, restricted to
  every pair (e, f) of configuration px in H, is one that K4.MC5's certificate does not cover. The list of such cores,
  with each agent's type domain cut to the projections of the uncovered sets, is computed in two independent ways
  (below). It has exactly 9 cores, and each of them has an EFX₀ allocation for every profile in the product of its
  domains. By K4.MC0(c) only H's types matter, so H has an EFX₀ allocation, a contradiction.

The second sentence: each K4.CORE step extends EFX₀ allocations, and components combine (L6). ∎

*Dependencies:* K4.CORE, K4.TIE and K4.L (PROVED); K4.MC0–K4.MC5; K4.R3–K4.R5 (CERTIFIED); TARGET (PROVED). No
published theorem.

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

Its log lists 21 cores with n ≤ 6 after the structural prune of step 2 (407 before it, as the independent check
counts), and 9 after the restrictions. *Certification* (`k4/mincex_cert.py`,
`results/k4_min_cex_cores_3.json.gz`, `results/k4_min_cex_cores_3.log`) uses `k4/search4.py`'s CEGAR with the
restricted domains, model D2; no profile needed more.

*Independent check* (`k4/check_mincex_cores.py`, log `results/k4_check_min_cex_cores_3.log`):
- it lists every connected incidence graph with 5 ≤ n ≤ 6 agents of degree 3–4 and β = 3 with genbg at the level of the
  full incidence graph (82,782 graphs; a different genbg class from the Γ′ list);
- completeness by orbit counting: for every (n, m), the listed graphs that are k = 4 cores give Σ n! m!/|Aut| (group
  sizes from nauty's countg) equal to the number of labeled connected k = 4 cores with β = 3, from `k4/check4.py`'s DP
  (self-tested there against brute force); all 13 (n, m) groups agree (for example (6, 10): 211, the k = 3 count);
- it re-implements the filters;
- it cuts the domains with the uncovered px profiles as re-derived by `check_reductions4.py`, judging types by signature
  on its own type enumeration;
- it verifies the SHA-256 of the uncovered-profile file against the value `check_reductions4.py` recorded;
- it matches every survivor to a certified core up to isomorphism, checks coverage of the full product of its
  domains with the raw definition, and checks that every certified allocation is D2.
Any failure makes its exit status nonzero.

Result: 407 cores pass the filters, the same 9 remain with the same profile counts, all covered. *Sensitivity test*
(`k4/test_check_mincex_cores.py`, `results/k4_test_check_mincex_cores.log`): it rejects a deleted allocation, a deleted
core, an allocation replaced by a bad one, an added non-D2 allocation, an enlarged px uncovered set, and a truncated
uncovered file (SHA-256 mismatch).

Trust points:
- nauty's genbg and countg. The independent list is complete by orbit counting against `k4/check4.py`'s DP
  (`results/k4_check_min_cex_cores_3.log`); the coordinator's reviewer re-derived the same list with a pure-Python
  generator, also checked by orbit counting.
- K4.CORE, K4.TIE, K4.L (PROVED), K4.R3–K4.R5 (CERTIFIED) and TARGET (existing rows).
- The hand proofs of K4.MC0, K4.MC1 and K4.MC4.

## 7. What remains

- **β = 4**: see §8 (round 2).
- **General β.** n ≤ 3(β − 1) holds for every β, so for each β only finitely many cores remain. Unavoidability (every
  core contains a reducible configuration) is open.
- The joint (e, f) restrictions of K4.MC5 are used only through per-agent projections. Using them jointly would shrink the
  profile spaces further, as would a CEGAR that accepts joint constraints.

## 8. β = 4 (round 2)

**Theorem K4.MC7.** Every instance with |R_i| ≤ 4 in 𝒞₄ has an EFX₀ allocation, provided each of the 6 cores below has
an EFX₀ allocation under every strict profile. They are graphical (every good valued by at most two agents), so the
multigraph theorem of Afshinmehr et al. (arXiv 2606.18665, read in full, `proofs/citations.md` item 4, as used by T3)
gives them EFX₀ under every additive valuation. So TARGET₄ holds for every instance whose k = 4 core components have
β ≤ 4 (from any sequence of K4.CORE reductions; each step extends EFX₀ allocations and L6 combines components, as in
K4.MC6), using that published theorem for these 6 cores and nothing else external.

The 6 cores (n = 6, m = 15, six P4 agents; agent i's goods, goods 9–14 private, every other good of degree 2), in the
order of `results/k4_check_min_cex_cores_4.log`:
1. [[0, 1, 2, 9], [0, 4, 8, 10], [1, 5, 7, 11], [2, 6, 8, 12], [3, 4, 6, 13], [3, 5, 7, 14]]; double edges (agents sharing two goods): (2,5)
2. [[0, 1, 2, 9], [0, 2, 8, 10], [1, 4, 7, 11], [3, 5, 6, 12], [3, 6, 8, 13], [4, 5, 7, 14]]; double edges (agents sharing two goods): (0,1), (2,5), (3,4)
3. [[0, 1, 6, 9], [0, 4, 7, 10], [1, 4, 7, 11], [2, 3, 6, 12], [2, 5, 8, 13], [3, 5, 8, 14]]; double edges (agents sharing two goods): (1,2), (4,5)
4. [[0, 1, 6, 9], [0, 4, 7, 10], [1, 5, 7, 11], [2, 3, 6, 12], [2, 4, 8, 13], [3, 5, 8, 14]] (agent multigraph: the prism)
5. [[0, 1, 6, 9], [0, 4, 8, 10], [1, 5, 7, 11], [2, 3, 6, 12], [2, 4, 7, 13], [3, 5, 8, 14]] (agent multigraph: K₃,₃)
6. [[0, 1, 6, 9], [0, 4, 6, 10], [1, 5, 7, 11], [2, 3, 8, 12], [2, 4, 7, 13], [3, 5, 8, 14]]; double edges (agents sharing two goods): (0,1), (3,5)


*Proof.* Let H be a minimal counterexample within 𝒞₄, with strict types (K4.MC0(c)). H is connected, so β(H) ≤ 4; if
β(H) ≤ 3 then H ∈ 𝒞₃ has an EFX₀ allocation by K4.MC6. So β = 4 and 5 ≤ n ≤ 9 (K4.MC0(d), K4.MC4). Its Γ′ is one of
the graphs listed by genbg (bipartite, connected, agents of degree 2–4, shared goods of degree ≥ 2, cyclomatic number
4). Its agents are P3 (Γ′-degree 2), Q3 or P4 (degree 3) and Q4 (degree 4) by K4.MC2. K4.MC3 holds, at least one agent
has 4 goods (three if n = 5), and its profile avoids every covered px profile (K4.MC5). These cores, with the cut domains, are 5,558 up to
isomorphism. Each has an EFX₀ allocation for every profile of its domains: 5,552 by the certificate below, and the 6
graphical ones by the multigraph theorem. By K4.MC0(c) only H's types matter, a contradiction. ∎

*The 5,558 cores* (`results/k4_min_cex_shapes_4.log`): 346, 2,183, 2,110, 835 and 84 for n = 5, …, 9, with restricted
profile spaces of up to 5.7·10¹⁴ (the 6 graphical all-P4 cores with n = 6, m = 15). The Γ′ lists are complete by
orbit counting (`k4/gamma_orbits.py`, `results/k4_gamma_orbits_4.log`: 111,078 graphs for 5 ≤ n ≤ 9, every (n, m′)
equal to the labeled count from check4.py's column-filling DP). The equality implies completeness only for a list
of valid, pairwise non-isomorphic graphs, so the script also checks every graph (sides, degrees, edges, connectivity)
and that no two have the same canonical form (nauty's labelg on the side-marked graphs). The checker below imports
this module for its orbit counting, so the two orbit logs come from one implementation.

*Certification* (`k4/mincex_cert.py`, certificate `results/k4_min_cex_cores_4.json.gz`, logs
`results/k4_min_cex_cores_4.log`). search4.py's CEGAR on the restricted domains, model D2, in three passes: a 30 s
limit per core (search4's scanner), then 120 s and 3,600 s with compute/k4-frontier's subsumption scanner
(`k4/frontier/search.py` and `scan2.c` of draft PR #26, commit 152afae, used unmodified from a scratch copy; the
certificate does not depend on the scanner, since the checker re-checks coverage). Regenerating the certificate needs
`k4/frontier/search.py` and `scan2.c` from PR #26 (under review, not yet on main); checking it does not. Result: 5,552 cores certified, every
one in the D2 shape; no profile without an EFX₀ allocation was found. The slowest certified ones, the ten
n = 6, m = 14 cores with five P4 agents and a Q3 (1.2·10¹³ profiles, 577–668 allocations), took 8–40 min each. Not certified: the 6 all-P4 cores
(n = 6, m = 15; 288⁶ ≈ 5.7·10¹⁴ profiles each; one ran for an hour without finishing).

*Independent check* (`k4/check_mincex_cores4.py`, log `results/k4_check_min_cex_cores_4.log`): written separately
from the generator. It lists Γ′ with genbg and checks completeness by orbit counting (every (n, m′), 5 ≤ n ≤ 9). It
re-implements the expansion (degree-2 agents P3, degree-4 Q4, degree-3 Q3 or P4), the filters (K4.MC3 on Γ′,
4-good agents, n = 5), and the domain cuts from the uncovered px profiles (SHA-256 verified against
`results/k4_check_min_cex_reductions.log`), with its own type representatives. It merges isomorphic cores and matches
every survivor to a certified core up to isomorphism. It checks coverage of the full product of the survivor's domains
with check4.py's pruned C search on each agent's inclusion-minimal safety rows (raw definition, vectorized), and D2.
It format-checks the certificate records first (check4.py's well_formed), and `--expect`, `--expect-n` and
`--expect-graphical` make its exit status depend on the number of cores left (5,558), their split by n (346, 2,183,
2,110, 835, 84) and the number of graphical cores accepted (6). On the β = 3 certificate it reproduces §6 (9 cores, 21,739,192 profiles; the summary lines of that run are in
`results/k4_test_check_mincex_cores4.log`). Its sensitivity test there rejects a deleted allocation, a deleted core, a
non-D2 allocation, a truncated uncovered file, a non-graphical core without allocations under --allow-graphical, an
enlarged uncovered set with a matching SHA-256, an allocation list that is EFX but not EFX₀, and a malformed record,
each for its expected reason (the message it prints).

*Reductions tried at β = 4* (not needed for the result):
- two 4-good agents sharing a good of degree 2 (configuration xy, `attempts/k4-mincex-xy-pairs.md`): for an open
  P4–P4 pair, one-agent gadgets reduce none (no room for a gadget good) and DEL 12%; for a closed pair, gadgets
  reduce 73,548 of 82,944 (89%);
- two P3 agents valuing the same two shared goods ("twins", `attempts/k4-mincex-twins.md`): 26 of 36 profiles.

**The general-β picture.**
- *Bound.* n ≤ 3(β − 1) for every β (K4.MC4). The candidate lists grow quickly: 0 cores at β = 2 (by the bound alone:
  n ≤ 3 < 5), 9 at β = 3, 5,558 at β = 4. Direct certification of β = 4 took about 10 CPU-hours, timeouts included.
- *What persists.* Call an agent's *excess* its Γ′-degree minus 2 (P3: 0; Q3, P4: 1; Q4: 2); an agent with excess ≥ 1
  has a *spare incidence*, beyond the two a thread agent has. Configurations the reductions never touch:
  - agents with a spare incidence (Q3, P4, Q4) adjacent to one another;
  - P3 agents between goods of degree ≥ 3;
  - P3 agents next to a single E3 agent, where f's ranking is forced (f ranks g last) and e ranks g first (2 of 6 Q3
    types, 10 of 288 P4 types);
  - Q4 agents, whose px restriction is weak.
- *Hard cores.* The 6 uncertified cores and the slowest certified ones (the ten n = 6, m = 14 cores with five P4
  agents and a Q3) have n = 6 and no P3 agent. So by (1) of §5 every agent has Γ′-degree 3 and n_Q4 = t = 0: they are
  graphical, and the multigraph theorem applies. (Non-graphical cores can be slow too: n = 9 with one Q4 and eight P3
  agents, t = 4, up to 23 min.) In the two simple ones (agent multigraph the prism or K₃,₃) every adjacent pair is an
  open P4–P4 pair, where the one-agent gadgets of the menu reduce nothing. The other four have a double edge (closed
  P4–P4 pair), where they reduce 73,548 of 82,944 pair profiles (not certified).
- *What could extend.* (i) Two-agent gadgets. Their state spaces (~3·10⁵ local states) need a C reducer. (ii) A k = 4
  proof of the multigraph theorem for cores (as `proofs/multigraph_extension.md` did for k = 3, ledger T5), which
  would remove the literature dependency at every β. (iii) A counting argument that bounds the number of 4-good agents,
  which dominate the profile spaces.

## Reproduce

```
python3 k4/mincex4.py all --write=results/k4_min_cex_reductions.json.gz          # ~2 min on 4 CPUs
python3 k4/check_reductions4.py results/k4_min_cex_reductions.json.gz --uncovered-out=results/k4_min_cex_px_uncovered.json \
    --expect=single-PP4:144 --expect=pair-P3-P3:36 --expect=loop-P3-P3:36 --expect=px-Q3:34 --expect=px-Q3-closed:36 \
    --expect=px-P4:1718 --expect=px-P4-closed:1728 --expect=px-Q4:648 --expect=px-Q4-closed:1656   # ~30 s
python3 k4/check_reductions4.py results/k4_min_cex_reductions.json.gz --selftest
(cd k4 && python3 mincex_shapes.py 3 --write=../results/k4_min_cex_shapes_3.json.gz)            # ~10 s
(cd k4 && python3 mincex_cert.py ../results/k4_min_cex_shapes_3.json.gz ../results/k4_min_cex_cores_3.json.gz)
(cd k4 && python3 check_mincex_cores.py 3 ../results/k4_min_cex_cores_3.json.gz ../results/k4_min_cex_px_uncovered.json)  # ~50 s
(cd k4 && python3 test_check_mincex_cores.py)                                    # ~6 min
(cd k4 && python3 mincex_shapes.py 4 --nmax=9 --write=../results/k4_min_cex_shapes_4.json.gz)  # beta = 4 list, ~45 s
(cd k4 && python3 mincex_attempts.py drop-private; python3 mincex_attempts.py px-open)         # failed reductions
# beta = 4 (section 8)
(cd k4 && python3 gamma_orbits.py 4 5 9)                                         # G' completeness, ~2 min
(cd k4 && python3 mincex_cert.py ../results/k4_min_cex_shapes_4.json.gz OUT.json.gz --jobs=4 --timeout=3600 \
    --scanner=frontier:DIR)   # DIR = compute/k4-frontier's k4/frontier (scan2.c, search.py); ~10 CPU-hours; resumable
(cd k4 && python3 mincex_ckpt.py ../results/k4_min_cex_shapes_4.json.gz OUT.json.gz.ckpt.jsonl ../results/k4_min_cex_cores_4.json.gz)
(cd k4 && python3 check_mincex_cores4.py 4 ../results/k4_min_cex_cores_4.json.gz ../results/k4_min_cex_px_uncovered.json \
    --jobs=3 --allow-graphical --expect=5558 --expect-n=5:346,6:2183,7:2110,8:835,9:84 --expect-graphical=6)  # ~25 min
(cd k4 && python3 test_check_mincex_cores4.py)                                   # ~30 s
(cd k4 && python3 mincex_attempts.py xy; python3 mincex_attempts.py twins)      # the failed xy and twins reductions, ~1 min
```
