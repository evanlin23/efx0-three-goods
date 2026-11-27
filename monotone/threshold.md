# The monotone threshold: the smallest k at which EFX₀ can fail

Workstream `proof/monotone-k` (side angle of the k = 4 campaign, `k4/attack_log.md`).

**Question.** Normalized monotone valuations, k-limited: v_i(S) = v_i(S ∩ R_i) with |R_i| ≤ k (R_i = the goods
that change i's value). EFX₀ in the raw all-goods form. Let k* be the smallest k for which some k-limited
monotone instance has no complete EFX₀ allocation.

## 1. What is known

| statement | status | artifact |
|---|---|---|
| k* ≤ 8. The instance of Akrami et al. (arXiv 2604.18216v4, §3.1, read) has 3 agents and 8 goods, every agent values all 8 goods (every singleton has value 1), and there is no EFX₀ allocation. Deleting any good or merging any two goods gives an instance that has one, as Theorem 1.2 of the paper predicts for m ≤ 7 | CERTIFIED (brute force, raw definition) | `monotone/amm_check.py` |
| The paper's extension to n ≥ 3, m ≥ n + 5 (Lemma 3.5) keeps 8 relevant goods for the base agents and gives each copy of the chosen agent 8 + (n − 3) relevant goods; dummy goods are relevant to nobody. It never lowers relevance | read (§3.2.1) | — |
| **k* ≥ 4 (Theorem M3):** monotone EFX₀ exists whenever every agent has ≤ 3 relevant goods, for every n and m | PROVED | `monotone/k3.md`, `monotone/k3_check.py` |
| k ≤ 2: serial dictatorship is EFX₀ for monotone valuations (the proof of L2c uses only monotonicity; also machine-checked as `MRDMono` in evanlin23/mrd-efx, see `proofs/citations.md`) | PROVED | `proofs/lemmas.md` (L2c), `monotone/k3.md` Remark 2 |

## 2. Reductions valid for monotone valuations (used to prune the search)

Call a monotone instance with |R_i| ≤ k and no EFX₀ allocation a *k-counterexample*. A k-counterexample with the
fewest agents, and among those the fewest goods, is *minimal*. A minimal k-counterexample satisfies:

1. **No junk.** Every good is relevant to some agent. Otherwise remove the junk J: the smaller instance has an EFX₀
   allocation by minimality, and L3 (rotate envy cycles, give J to an envy-graph source) extends it. L3's proof
   uses only monotonicity (`monotone/k3.md`, Remark 2).
2. **Connected** agent–good incidence graph (L6). Each component has fewer agents, or is the whole instance. Bundles
   from another component meet R_i in ∅, so v_i(X_j ∖ {g}) = 0.
3. **|R_i| ≥ 3 for every agent.** If |R_i| ≤ 2, rule R1 peels i whatever its valuation. It takes a favourite
   good, or nothing if R_i = ∅, and the rest has fewer agents.
4. **Every agent shares ≥ 2 of its goods with other agents.** Let Q be the goods of R_i that other agents also
   value, P = R_i ∖ Q, and suppose |Q| ≤ 1. If v_i(P) ≥ v_i(Q), peel i with bundle P: condition (i) of L2's
   general step holds, and (ii) holds because P is worthless to everyone else. Otherwise v_i(Q) > v_i(P) ≥ 0,
   so Q = {q} with v_i({q}) > v_i(R_i ∖ {q}); peel i with {q} (|P| ≤ 1). Either way the rest has fewer agents.
5. **m ≥ n + 4** (Mahara, arXiv 2107.09901, Theorem 3, read in full, `proofs/citations.md`: m ≤ n + 3 has an EFX₀
   allocation for monotone valuations). For n = 3, **m ≥ 8** (arXiv 2604.18216v4, Theorem 1.2, read).
6. **Counting.** Items 3–4 give at most (k − 2)n private goods and at least 2n incidences on shared goods, so
   m = (#shared) + (#private) ≤ (kn + #private)/2 ≤ (k − 1)n.

7. **n ≥ 3.** Two agents always have an EFX₀ allocation for monotone valuations (Plaut–Roughgarden, arXiv
   1707.04769, read: Definition 2.3 is the all-goods EFX, §2 defines "general valuations" as normalized and
   monotone, and Theorem 4.3 is cut-and-choose on the leximin++ solution, pp. 16–17). One agent takes everything.

8. **No agent is peelable** (optional constraint, `--np`): for every agent i, v_i(P) < v_i(R_i ∖ P) whenever P is a
   single good of R_i or a nonempty set of goods valued by no other agent. Otherwise L2's general step peels i
   with bundle P, and the rest has fewer agents. Runs that use this constraint say so (`"np": true`), and then
   cover minimal counterexamples only. That suffices for every "no counterexample with ≤ n₀ agents" claim.

So if a k-counterexample with at most n₀ agents exists, a minimal one exists among the hypergraphs with
3 ≤ |R_i| ≤ k, items 1–6, 3 ≤ n ≤ n₀ and n + 4 ≤ m ≤ (k − 1)n, under some valuation profile. (For n = 2 the
search was also run for k ≤ 6, as a check of the tooling: every hypergraph is UNSAT, `results/monotone/n2_*`.)

## 3. Search method

For each hypergraph (up to isomorphism, `monotone/hypergraphs.py`; re-enumerated independently by
`monotone/check_enum.py` for n ≤ 4 and by `monotone/check_enum5.py` for every certified family, log
`results/monotone/check_enum5.log`), the question "is there a monotone profile with no EFX₀ allocation?" is a SAT problem.
Every allocation must contain a strict violation v_i(X_j ∖ {g}) > v_i(X_i), and both sides are disjoint subsets
of R_i (`monotone/synth.py`). We solve it by CEGAR over allocations. A solver proposes a profile, a backtracking
search finds an EFX₀ allocation for it, and that allocation's clause is added, until UNSAT or until a profile
without an EFX₀ allocation is found. On UNSAT, the collected allocations L form the certificate: *every monotone
profile on this hypergraph makes some allocation of L EFX₀.*

**Symmetry breaking** (always on, `"sb": true`). Call goods that are relevant to exactly the same agents a
*class*. Permuting the goods of a class maps the hypergraph to itself, and turns a profile without an EFX₀
allocation into another such profile: X is EFX₀ for v∘π iff π(X) is EFX₀ for v. For each class, pick the
permutation that sorts its goods by the singleton values of the class's least agent. Permutations of different
classes act on disjoint goods and commute. So if any counterexample exists, one exists in which, for every class,
its least agent's singleton values increase with the goods' indices (strictly, by nondegeneracy). The same
argument preserves minimality and item 8, so the constraints combine.

Trust chain for an UNSAT claim (PROMPT.md §5 rule 4: two independent implementations):
- The search (`run_search.py`): CEGAR with the `order` encoding of `synth.py`. Strict total orders on 2^{R_i} by
  pairwise variables, with inclusion and transitivity; exact for nondegenerate profiles, which suffice. Solver:
  CaDiCaL. The order encoding is re-run on the final L.
- Second encoding (`synth.py`, `rank`), run on L where the record has `"rank_on_cert_unsat": true`: integer values
  in order (unary) encoding with V = 2^|R_i| levels. A counterexample can be perturbed to a nondegenerate one, whose
  ranks lie in 0..2^|R_i| − 1, so this is exact too. Records with `null` skipped it to save time (k ≥ 7).
- **Independent checker** (`monotone/check_cert.py`, no shared code, run on every UNSAT record): order encoding.
  Its clauses come straight from the definition (every i ≠ j and g ∈ X_j, no reduction to maximal sets), with its
  own implementation of the symmetry breaking and of item 8. Solver: Glucose 4.
- Negative test (`monotone/validate.py --negative`): the independent checker rejects every certificate cut to its
  first half (30/30 on `n3_m8_k5.jsonl`), so its UNSAT answers are not vacuous.
- Validation (`monotone/validate.py`): with the known counterexample's values pinned (nondegenerate
  strictification), both encodings of synth.py are SAT on all 6,561 allocation clauses. Random monotone profiles
  (EVIDENCE) never escape a certificate.

## 4. Results

Every hypergraph listed is UNSAT under the search, and every certificate passed `monotone/check_cert.py`, unless
the row says otherwise. "Complete" means every admissible m (n + 4 ≤ m ≤ (k − 1)n; m ≥ 8 at n = 3) and every
hypergraph of §2 for that m.

| n | k | m | hypergraphs | result | files |
|---|---|---|---|---|---|
| 2 | any | any | — | EFX₀ exists (Plaut–Roughgarden, Theorem 4.3; also searched for k ≤ 6 as a tooling check) | `results/monotone/n2_*` |
| 3 | 4 | 8–9 (complete) | 6 | no counterexample | `n3_m{8,9}_k4.jsonl` |
| 4 | 4 | 8–12 (complete) | 503 | no counterexample | `n4_m{8..12}_k4.jsonl` |
| 3 | 5 | 8–12 (complete) | 113 | no counterexample | `n3_m{8..12}_k5.jsonl` |
| 3 | 6 | 8–15 (complete) | 604 | no counterexample | `n3_m{8..15}_k6.jsonl` |
| 5 | 4 | 9–15 (complete) | 18,829 | no counterexample | `n5_m{9..15}_k4.jsonl.gz` |
| 4 | 5 | 8–16 (complete) | 9,373 (8,870 with a 5-good agent) | no counterexample | `n4_m{8..16}_k5_only.jsonl(.gz)` |
| 3 | 7 | 8–18 | RUNNING | | `n3_m*_k7_only.jsonl` |

The modification experiments on the paper's instance (`attempts/monotone-lower-relevance-of-amm.md`) say the
following, for the restricted family with some agents fixed to the paper's valuations only. With two agents
fixed, the third cannot drop any good. With one agent fixed, the other two cannot each drop one good (17 cases).

## 5. What this says about the threshold

- Proved: 4 ≤ k* ≤ 8 (Theorem M3; the paper's instance).
- Certified: a monotone counterexample at k = 4 needs ≥ 6 agents, at k = 5 ≥ 5 agents, and at k = 6 ≥ 4 agents. So with three agents,
  the threshold is 7 or 8; it is 8 if no 3-agent counterexample has k = 7.
- Since monotone EFX₀ at k = 4 would imply TARGET₄ (Theorem M3, Remark 3), the k = 4 rows are also
  small-n evidence for TARGET₄. They are no stronger than the campaign's additive certificates there (rows K4.*),
  but they cover the strictly larger monotone class: 912 disjoint-comparison types per 4-good agent against
  ≥ 336 additive ones (`monotone/types4.py`).
- Open: the exact value of k*. Is there a counterexample with k ∈ {4, …, 7} and more agents? At n = 3, is 8 the
  threshold?
