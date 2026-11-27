# Referee report: Theorem CH-KD and Corollary CH-KD′ (`kgen/charity.md` §8, branch `claude/kgen-charity`)

Referee: `proof/k4-referee`, 2026-11-26.
- Read: §8 at `1e986c6`, and Corollary CH-KD′ added at `0c85d91`. The cited CKMS §2 and Sivashankar §1, §3 were read
  earlier (`k4/referee/charity.md`).
- Check: `k4/referee/chkd_ref.py`, log `results/k4_referee/chkd_ref.log`. The four rules are implemented from §8's
  text; no code is shared with `kgen/charity/`.

## Verdict: CORRECT

The theorem: if every agent values ≤ k goods and every good has ≤ d valuers, some EFX₀ state with strong charity has
- P = ∅ for k ≤ 2;
- |P| ≤ (k − 2)·min_{g∈P}|V(g)| − 1 ≤ (k − 2)d − 1;
- |P|! ≤ d^{|P|−1}, i.e. |P| ≤ R(d) < e·d.

All three hold at the same state: any state where no rule applies. The bound is independent of n.

## Step by step

- **Rules.** U2 is taken along a shortest rainbow cycle of the source digraph D over all champion options.
  - CKMS's own U2 (Algorithm 2) has no |P| ≥ n precondition (checked in the earlier report).
  - Executing U2 takes the envy paths π_{i+1} from s_{i+1} to t_{i+1}. Agents shift along them, t_{i+1} takes Z_i, and
    (X_{s_i} ∪ {g_i}) ∖ Z_i joins the pool. A path of length 0 (t_{i+1} = s_{i+1}) is allowed and handled.
- **Step 1.** Correct (= CH5 of the earlier report). A shared vertex of π_a and π_b gives the edge s_{b−1} → s_a of D
  with colour g_{b−1}, and with it a shorter rainbow cycle. Sources have in-degree 0, so they lie only on their own
  paths.
- **Step 2.** Correct, and slightly stronger than stated: *every* sequence of rules terminates.
  - (R), (U1) and (U2) raise the welfare strictly. (U0) keeps it weakly and shrinks the pool.
  - So (welfare, −|P|) rises lexicographically on a finite set.
  - EFX₀ is kept: CKMS Lemmas 2, 5 and 7, with Lemma 7's implicit path-disjointness supplied by Step 1.
- **Step 3.** Correct.
  - t ∉ C(s) is shown via the one-edge rainbow cycle s →_g s. That also gives t ≠ s, since s ∈ C(s).
  - g ∈ Z ⊆ R_t and Z ∖ {g} ⊆ X_s follow from s being a source, from minimality and from weak charity.
- **Step 4.** Correct.
  - t can champion at most |R_t| − 2 sources, since R_t contains g, a good of X_t and one good per such source, all in
    disjoint bundles distinct from X_t and P.
  - The walk argument for |P| ≤ σ − 1 is CKMS Lemma 6 made self-contained. Every vertex of D has an out-edge of every
    colour: U0 fails at every (s, g), and every agent is reachable from a source in an acyclic graph. After ≤ σ steps
    a vertex repeats, using ≤ σ ≤ |P| colours.
- **Step 5.** Correct (= CH-R).
  - Γ has the in-neighbour property, and its rainbow cycles map to rainbow closed walks of D.
  - |V_g| ≤ |V(g)| ≤ d.
  - Sivashankar's Theorem 3 gives (p − 1)! Σ|V_g| ≤ Π|V_g|, hence p! ≤ d^{p−1}, because Π/Σ is increasing in each part
    size.
- **Corollary CH-KD′.** Correct. The parts of the goods with ≤ d valuers induce a sub-digraph of Γ. It keeps the
  in-neighbour property between its parts (the in-neighbour of a vertex in each other part is still there) and has no
  rainbow cycle, so its number of parts is ≤ R(d).
- **The table.** Recomputed: max p with p! ≤ d^{p−1} is 1, 2, 4, 6, 9, 11, 14, 16, 19, 21 for d = 1–10. The k = 4 and
  k = 5 rows (min with 2d − 1 and 3d − 1) match. So do the text's figures 2, 4, 6, 9 (part 3) and 3, 5, 7, 9 (part 2)
  for d = 2–5.
- **Unverified items.** R(3) = 3 and R(4) = 4 are used only for the optional improvement, correctly marked
  [unverified], and no part of the theorem depends on them.

## Computation (evidence)

The rules were run with random rule choices from the empty allocation on 6,000 random instances (n ≤ 5, m ≤ 8,
k ≤ 4). They were also run from the S(σ, k) and S′(σ, k) states of §4–§5 (σ ≤ 4, k = 3, 4). Asserted:
- EFX₀ after every rule, and the lexicographic potential rising;
- Step 1 at every U2: distinct champions and vertex-disjoint envy paths;
- at every stop: an acyclic envy graph, strong charity, parts 1–3, and CH-KD′ for every d′ ≤ d.

| runs | rules applied | of which U2 | failures of any assertion |
|---|---|---|---|
| 2 seeds × 3,012 starts | 36,035 | 9,981 | 0 |

Random instances always end with an empty pool. The 12 stops with a pool (1–3 goods) are the S and S′ states: there
no rule applies, and the bounds hold.
