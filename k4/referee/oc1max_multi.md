# Referee report: Lemma D-red, Proposition T0, Lemma KEEP, Lemma SET (with Lemma OWN, Lemma RING-red and Finding NC in passing) (`k4/oc1max_multi.md` §2–§4, §6, branch `proof/k4-oc1max-multi`, PR #115)

Referee: `proof/k4-referee`, 2026-11-26.
- Read: `k4/oc1max_multi.md` at `6959fc9` (D-red, T0, Corollary TR, KEEP, KEEP-1, SET, OWN). Also its update `1ccbb94`,
  which adds Lemma RING-red to §6 and leaves §2–§4 unchanged. All of §0–§7 read.
- Also read: the parts of `k4/oc1_hall.md` the proofs call (Lemma 2\*'s non-movable definition, §6; §21) on
  `claude/k4-oc1-hall`, and `k4/sdc.md` §29 on `claude/kind-lamport-y8fdme`.
- Checks:
  - `k4/referee/multi_ref.py`, run by `multi_ref_runs.sh`, log `results/k4_referee/multi_ref.log`;
  - `k4/referee/ring_ref.py`, log `results/k4_referee/ring_ref.log`.

  Both are written from the text and the raw EFX₀ definition, reusing only my own helpers (`oc1hall_ref.py`). No code
  from `k4/oc1max_multi/` was run or imported.

## Verdict

| item | verdict |
|---|---|
| Lemma D-red (K4.MULTI.DRED) | **CORRECT** (wording: two steps should cite (U), see below) |
| Proposition T0 (K4.MULTI.T0) | **CORRECT** |
| Corollary TR | CORRECT (immediate from D-red 2) |
| Lemma KEEP (K4.MULTI.KEEP), with the u = z remark | **CORRECT** |
| Corollary KEEP-1 | CORRECT as a reduction; it uses Lemma D1-chain (Hall §21, refereed in `oc1_hall_d1.md`) |
| Lemma SET (K4.MULTI.SET) | **CORRECT** |
| Lemma OWN (K4.MULTI.OWN), in passing | **CORRECT** (the same wording point for q = k) |
| Lemma RING-red (K4.MULTI.RING, `1ccbb94`), in passing | **CORRECT** (notation: T3's head junk is H_t = H₂, written "H₁") |
| Finding NC (T3) | **CONFIRMED** by my enumeration |

The lemmas are reductions: a chain *with property X* repairs. The note says so itself ("Honest scope", §7). Chain
existence is not claimed, and nothing here proves OC₁^max.

## 1. Lemma D-red

Setting:
- a perfect start;
- k ∈ D, and a canonical chain P = (k, …, z): each x_i wants Y_{x_{i−1}}, and z is unfrozen at the picks;
- H₀ ⊆ Π ∩ R_k improving, with Π = J ∪ {Y_z};
- owner k, so W_k = Π.

Each step re-derived:
1. **(G1), (G2), "nobody but k wants a good of Π".**
   - For junk g: v_i(g) < p_i ≤ v_i(B′_i), by (I2).
   - For Y_z and i ≠ z: v_i(Y_z) ≤ p_i, by (U).
   - For z itself: p_z < v_z(Y_{x_{t−1}}).

   (G2) also needs k not to want a good of J′. That is true, since junk is worth less than p_k < v_k(H₀) and
   v_k(Y_z) ≤ p_k by (U), but it is said only in OWN's proof. Every agent other than k holds one good, so (G1) holds.
2. **Frozen agents at B′.**
   - An agent off P that is unfrozen at the picks stays unfrozen, since values only rose. x₁, …, x_{t−1} are frozen at
     the picks, because x_{i+1} wanted their picks. So the frozen agents at B′ are F ∖ {k} plus possibly z.
   - **Wording.** The text says "a set holding one good it values never threatens it". As a general statement that is
     false: with a worthless second good removed, the single valued good counts. The session notes this itself under
     OWN's check. What is true here: an agent q ∈ F ∖ D values at most Y_z in Π, and v_q(Y_z) ≤ p_q ≤ v_q(B′_q) by (U).
     So removing any good from a subset of Π leaves ≤ v_q(B′_q).
   - The same one-line justification fixes step 3's "values at most one good of Π and cannot be exposed".
   - For d ∈ D ∖ (Θ(z) ∪ {k}): Π does not threaten d at p_d. Threatening is monotone in the set and antitone in the
     value, so no subset of Π threatens it at any value ≥ p_d.
3. **Exposed holders.**
   - Agents of F ∖ D are excluded as in 2. Middle agents are in F, so an exposed middle agent lies in D.
   - So an exposed holder is z, or off P and unfrozen at the picks, or in D ∖ {k} and unfrozen at B′.
   - Non-movable (Lemma 2\*, `oc1_hall.md` §6: wants a good of B_o, or |B_o ∩ R_u| ≥ 2 with
     v_u(B_o ∩ R_u) > v_u(B_u)) with B_o = H₀ is exactly crowding, since nobody wants a good of H₀ by 1.
4. **Condition C(B′, k).** Lemma 2\*'s (H1) runs over the non-holders other than k. These are the frozen singletons of
   2, and only those in (D ∖ {k}) ∪ {z} can be threatened. So (H1) becomes (H1″).
   - With H = ∅ the conclusion follows when none of HEAD, CROWD or DEMAND occurs.
   - DEMAND's d lies in Θ(z), by 2.

Hardness is not used in D-red. It is in the setting only.

## 2. Proposition T0

Suppose Θ(z) = ∅. Lemma 2 at the picks with owner z and H = ∅ (refereed CORRECT in `oc1_hall.md`):
- (G1) and (G2) hold, and (G5′) holds because z is unfrozen;
- (H3) holds because |B_z| ≤ 1;
- (H1): an agent q ∈ F ∖ D meets W_z = B_z ∪ J only in Y_z, worth ≤ p_q since z is unfrozen; an agent of D is
  unthreatened, by Θ(z) = ∅;
- (H2) with H = ∅ reads "exposed holders ≤ |N₁|", which is trivially true.

So an S\* completion owned by z exists. It is one-absorber, a contradiction.

The second part: J ∪ B_z threatens k, so (J ∪ B_z) ∩ R_k is worth more than p_k. This holds for null z too (B_z = ∅).
Correct.

## 3. Lemma KEEP

Lemma 2\* at B′ with owner k and H = {Y_z} gives W_k ∖ H = J.
- (H1): the frozen agents at B′ other than k are F ∖ {k} and z.
  - F ∖ D values no junk.
  - D ∖ D_T is pick-dangerous: J does not threaten it at p_d, hence not at any larger value.
  - (D_T ∖ {k}) ∪ {z} is covered by (K3).
- (K1) is exactly Lemma 2\*'s admissibility of u for Y_z against X(H) = J.
- No non-movable holder: by D-red 1 and (K2).

Correct.

**The u = z remark.** R_z ⊇ {a, Y_z}, so R_z holds ≤ 2 junk goods, each worth < p_z. Hence
v_z(J ∩ R_z) < 2p_z < v_z(a) + p_z, which is (K1) for u = z when z is unfrozen at B′. Here k ≤ 4 enters. Correct.

**KEEP-1.** With D_T = {k}, (K3) is only about the head. Existence of a canonical chain is Lemma D1-chain. Its proof
needs only "k frozen", not |D| = 1, as I re-derived for Hall §21. An improving H₀ ⊆ J exists because J threatens k.
Correct.

## 4. Lemma SET (and OWN)

**SET.**
- (a) Removing a good of H₀ leaves one junk good, worth < p_i ≤ v_i(X_i) for every agent with a pick, and null agents
  value nothing.
- (b) R_k ⊆ {Y_k, g, g′, ℓ}, and Y_k sits in x₁'s bundle. The cases go through:
  - x₁'s bundle: removing its slot good leaves Y_k (p_k), and removing Y_k leaves a good of J′ (≤ p_k);
  - the owner's bundle meets R_k in ≤ ℓ, which is either B′_o (unwanted by k by hypothesis) or junk;
  - any other holder's bundle meets R_k in ≤ ℓ, which is either an unfrozen base or junk;
  - frozen singletons.
- So no EFX₀ pair involves k, and the reduction (delete k and H₀) is exact for completions with an allowed owner.
- "At most one good of J ∖ H₀" for d valuing g, g′ is immediate from |R_d| ≤ 4 and Y_d ∉ J. Citing Lemma PL(c) is
  fine but not needed.

Correct.

**OWN** (in passing). Lemma 2\* with owner o and H = {Y_z}:
- (G1): H₀ threatens nobody.
- (G2) as in D-red, and k wants no junk.
- (H1):
  - q = k: W ∩ R_k ⊆ {ℓ}, and ℓ ∉ B′_o by (W2), so ℓ is junk with v_k(ℓ) < p_k < v_k(H₀). The text's "a single good,
    which never threatens" needs this value bound, which holds.
  - q ∈ F ∖ D: W ∩ R_q = ∅.
  - q pick-dangerous: the two-case argument J ⊄ R_q / J ⊆ R_q, re-derived; it is right.
  - D_T ∖ {k}: by (W1). z: by (W3).
- No non-movable holder: o is unfrozen and |B′_o| ≤ 1.
- The (W1)-automatic remark again needs "that one good is junk, worth < p_d". True.

Correct.

## 5. RING-red and Finding NC (in passing)

- **RING-red** is Lemma 2\* with owner k and H = ∅: (R1) gives (G1), (I2) gives (G2), (R3) gives (H1), and (R2) and
  (R4) exclude non-movable holders. Correct.
  - The definition does not require the middle agents to be frozen; T3's middle agent 2 is unfrozen. My first ring
    enumerator wrongly required it and found no T3-like rings; fixed before the run below.
- **T3, verified:**
  - picks (0, 4, 1), J = {2, 3, 5}, F = D = {0, 1}, D_T = ∅, hard;
  - the only canonical chain with an improving H₀ from a dangerous agent is (1, 2) with H₀ = {1, 3}, and after it no
    owner has a one-absorber completion;
  - B′ = ({4, 2}, {1, 3}, {0}) satisfies (R1)–(R4), with an S\* completion owned by 0.

## 6. Computation (evidence)

My checks run on hard starts: SD picks of random strict instances (k ≤ 4, n = 3–5; random 4-sets, a shared-pool
design and sparse sets), kept when perfect and one-absorber-hard by raw brute force over every owner. On them:
- every canonical chain from every k ∈ D, with every improving H₀ (not only minimal ones);
- every owner;
- every H ⊆ J′ for D-red 4.

| claim checked | tests | failures |
|---|---|---|
| T0: Θ(z) ≠ ∅ for every unfrozen z, and the pool improving for each k ∈ Θ(z) | 75,625 | 0 |
| D-red 1, 2, 3 (each chain) | 172,394 chains | 0 |
| D-red 4: brute-force S\* owned by k ⟺ some H with (H1″) and an SDR covering the crowded exposed holders | 172,394 | 0 mismatches |
| D-red: no HEAD, CROWD, DEMAND ⟹ S\* owned by k | 105,538 | 0 |
| KEEP ((K1)–(K3) ⟹ S\* owned by k with u taking Y_z) | 96,681 | 0 |
| KEEP's remark ((K1) holds for u = z when z ends unfrozen) | 59,148 | 0 |
| SET: no EFX₀ violation involving k in any S\*-shaped allocation; S\*(B′, o) ⟺ S\*(reduced, o) | 118,544 owner tests | 0 |
| OWN ((W1)–(W3) ⟹ S\* owned by o with u taking Y_z) | 49,042 | 0 |
| RING-red ((R1)–(R4) ⟹ S\* owned by k), separate run | 8,984 rings | 0 |

These come from 800,000 instances, 1,743,494 perfect starts, 71,497 hard ones and 68,035 with |D| ≥ 2. Each lemma's
hypotheses are also needed. Dropping one (40,000 instances each) gives:

| dropped | failures |
|---|---|
| DEMAND | 865 / 9,552 |
| CROWD | 332 / 7,694 |
| HEAD | 79 / 6,838 |
| (K2) | 74 / 6,078 |
| (K3) | 399 / 6,139 |
| (W1) | 21 / 2,314 |

## 7. For the coordinator

- D-red, T0, KEEP, SET, and in passing OWN and RING-red: CORRECT. They can be recorded as PROVED, as reductions.
- Two wording fixes for the authors:
  - D-red steps 2 and 3: replace "a set holding one good it values never threatens it" with the (U) bound
    v_q(Y_z) ≤ p_q;
  - OWN, q = k: add v_k(ℓ) < p_k.
- T3 (Finding NC) is confirmed.

## 8. Addendum: Theorem U and Corollary U1 (`d31a8f1`, unchanged at `5371d9b`; coordinator's queue, 2026-11-27)

Read: `k4/oc1max_multi.md` §3 (Theorem U, Corollary U1, the paragraph on the Hall session's question). Check:
`k4/referee/theorem_u_ref.py`, run by `theorem_u_ref_runs.sh`, log `results/k4_referee/theorem_u_ref.log`. Own code,
raw EFX₀.

**Verdict: CORRECT.**

**The Hall session's question.** It asked whether |D| ≥ 2 needs the extra hypothesis "the other frozen dangerous
agents are unthreatened by J". It does not: that is implied by D_T = {k}.
- Every d ∈ D ∖ {k} is pick-dangerous: J does not threaten it at p_d.
- Since threats are antitone in the value, J does not threaten it at any value ≥ p_d.
- That covers frozen dangerous middle agents too, whose values only rose.
- The proof uses this in two places:
  - (H1), where the owner's bundle is exactly J;
  - "an exposed d ∈ D ∖ {k} unfrozen at B′ would lie in D_T".

  The note states it explicitly in the paragraph after the theorem.

**The proof, re-derived.**
- Step 0: the walk of D1-chain needs only "k frozen", and J threatening k gives an improving H₀ ⊆ J.
- Step 1, the holder for Y_z.
  - If z is unfrozen at B′, z itself, by KEEP's slot bound v_z(J ∩ R_z) < 2p_z < v_z(a) + p_z.
  - Otherwise a wanter w of a at B′ is off P and wanted a at the picks.
  - w is unfrozen at the picks: otherwise the walk from w would give a longer canonical chain, distinct by (π).
  - w holds a pick (wanting implies non-null), w ∉ E_J, and it is a holder at B′ with value p_w. So it is
    unexposed against J, hence admissible.
  - The hypothesis "z ∈ E_J ⟹ z unfrozen at B′" then makes a frozen z unthreatened by J at v_z(a) > p_z.
- Step 2, Lemma 2\* with owner k and H = {Y_z}, so W_k ∖ H = J.
  - (H1) holds: F ∖ D values no junk, D ∖ D_T is pick-dangerous, and z is covered by step 1.
  - No exposed holder other than u exists. Off-path unfrozen agents are exposed iff in E_J ⊆ {z}. Dangerous agents
    unfrozen at B′ would be in D_T. z is a holder only when it is u.
- Corollary U1: with one unfrozen pick holder z, every chain ends at z and E_J ⊆ {z}. Step 1 shows that a wanter of a
  at B′ would be a second unfrozen pick holder, so z is unfrozen at B′.

**Computation (evidence).**
- Starts: 300,000 instances (n = 3–5, k ≤ 4; the mutation runs are separate) and 34,795 one-absorber-hard starts, of which 8,466 have D_T = {k}
  (7,868 with |D| ≥ 2).
- Tested: every longest canonical chain from k and every improving H₀ ⊆ J meeting the hypotheses. The completion was
  checked by brute force, with Y_z forced to z or to an unfrozen second wanter.

| check | tests | failures |
|---|---|---|
| Theorem U | 12,135 (10,839 with \|D\| ≥ 2) | 0 |
| Corollary U1: the hypothesis holds at every one-holder start | 7,353 starts | 0 |
| mutation: any canonical chain, not only longest | 3,123 | **406** |
| mutation: drop E_J ⊆ {z} | 2,613 | **21** |

Both hypotheses are used.

## 9. Addendum: Lemma M^c, the compensated matching form (`k4/oc1max_multi.md` §9 at `3d157f3`; coordinator's queue, 2026-11-27)

Read: §9 in full. Check: `k4/referee/mc_ref.py`, run by `mc_ref_runs.sh`, log `results/k4_referee/mc_ref.log`. It is
my own code: the formula written from the text, compared with a raw brute force over every S^c-shaped allocation.

**Verdict: CORRECT.** The three points the coordinator asked about:

- **(G2)'s role.** It is used in the Claim, the per-allocation characterization, at one place. A two-good bundle
  {y_j, z_j} with z_j junk threatens i only through y_j, because v_i(z_j) ≤ b_i ≤ t_i. So the only new threats are:
  - frozen singles j ∈ F_s whose good i wants, giving the term v_i(y_j) of τ_i;
  - the unchanged multi-good bundles, giving the term max_h v_i(B_q ∖ h);
  - X itself.

  Without (G2), a wanted junk good z_j would need its own requirement, and the Claim would be false as stated.
- **The Claim.** EFX₀ ⟺ (t_i ≥ τ_i(F_s) for all i, and X threatens no i ≠ o at t_i). Re-derived bundle by bundle:
  - singletons;
  - X;
  - unchanged multi-good B_q, q ≠ o;
  - holders' {y_j, z_j} (y_j unwanted);
  - frozen singles' {y_j, z_j}.

  Correct.
- **(⇒) and (⇐), and the enumeration over F_s.**
  - (⇒): agents that receive nothing have t_i = b_i and so are not needy. That gives (C1), since only N₁ ∪ F_s
    receive. A needy receiver must value its good, else t_i = b_i, so its good is an edge. The goods received form the
    (C3) matching with ≥ |H| − d edges.
  - (⇐): an unmatched j ∈ F_s only removes terms from τ (τ(F_s′) ≤ τ(F_s)). So requiring the matching for the larger
    F_s is sound, and enumerating every F_s ⊆ F₁ is exactly right.
  - (C2) is the owner's requirement.
- **(C3) and the deficiency formula.** Mendelsohn–Dulmage, as in Lemma M: a matching covering the needy agents and a
  maximum matching combine into one that does both. Correct.
- **Special cases.**
  - With F_s = ∅ and (G1), every τ_i = b_i and the needy agents are the exposed holders, so this is Lemma M.
  - At single-good states, S^c is the one-absorber shape.

  Both correct.

**Computation (evidence).**
- States: SD picks of random instances (k ≤ 4, n = 3–5; half with random 4-sets in m = n + 2, n + 3), and states one
  or two random improving chains away, kept when (G2) holds.
- Every owner; d = 0 and 1.

| run | states with (G2) | with frozen singles / multi-good bundles | owner tests | mismatches |
|---|---|---|---|---|
| two seeds × 15,000 instances | 48,930 | 26,952 / 18,930 | 391,846 | **0** |
| mutation: F_s = ∅ only | 2,414 | 1,275 / 914 | 19,140 | **68** |
| mutation: τ without the frozen-slot term | 2,414 | | 19,140 | **576** |
| mutation: edges without the compensation bound b_i + v_i(h) ≥ τ_i | 2,414 | | 19,140 | **38** |

So the frozen-slot enumeration, the frozen-slot requirement and the compensation bound are each necessary.

## 10. Addendum: Theorem S, Lemma HS, HS-U1, and the SLOT residue (`k4/oc1max_multi.md` §10 at `b107719`; 2026-11-27)

**Read.** §10 in full, and the ledger rows K4.MULTI.S and K4.MULTI.SLOT2 at `b107719`. §3 (Theorem U, KEEP) and §9
are unchanged.

**Checks.** All my own code, raw EFX₀; nothing from `k4/oc1max_multi/` was run or imported.
- `k4/referee/theorem_s_ref.py`, run by `theorem_s_ref_runs.sh`, log `results/k4_referee/theorem_s_ref.log`.
- `k4/referee/slot2_ref.py`, log `results/k4_referee/slot2_ref.log`.
- The 8,383 starts of K4.MULTI.DATA (`results/k4_oc1max_multi/hard2_starts*.jsonl.gz` at `b107719`) are read as data.
  The picks are recomputed from each stored order.

**Verdict.**
- Theorem S (both forms, (S-d) and (S-d′)): **CORRECT**.
- Lemma HS and HS-U1: **CORRECT**.
- The coverage claims are reproduced exactly: 5,945 / 6,679 / 7,441 starts, and 2,880 for Theorem U alone.
- **Fix:** the log613 instance is printed with wrong values for agents 1 and 2, and with the printed values its
  narrative is false (details below). Two wording remarks follow as well.

**The proof, re-derived.**
- *Step 0, the move.*
  - k is frozen, so the walk of D1-chain gives a canonical chain from k, and a longest one exists.
  - (S-a) makes W ∩ R_k improving.
  - The chain is official: each x_i wants Y_{x_{i−1}} at the picks, and z wants a.
  - h ∉ W ⊇ H₀, so h ∈ J′, and k's final bundle H₀ ∪ (J′ ∖ {h}) is Π ∖ {h} = W.
  - H₀ may contain Y_z, as official chains allow (H₀ ⊆ Π).
- *Step 1, the receiver.*
  - The SD order strictly increases along P: x_i wants Y_{x_{i−1}} at the picks, so x_{i−1} picked first.
  - So no agent of P other than x_{t−1} and z can value a above its pick, and k never wants a at B′.
  - Hence whether z is frozen after P does not depend on H₀. This is what makes (S-d′) well defined at chain level.
  - If z is frozen after P, every wanter w of a at B′ is off P and wanted a at the picks. w is unfrozen at the picks:
    otherwise the walk up from w would give a strictly longer canonical chain, whose agents are distinct by the SD
    order.
  - w holds a pick (perfect start), and w is unfrozen at B′: a wanter of Y_w at B′ would have wanted it at the picks,
    since values only rise.
  - So w is a holder with value p_w, and *every* wanter works, not just some.
- *Step 3, EFX₀ of A.* A has only two bundles with two or more goods: W, and {B′_r, h}.
  - **{B′_r, h}** threatens i only if v_i(B′_r) > v_i(A_i) or v_i(h) > v_i(A_i).
    - The first is excluded because r is a holder at B′ and values only rise; for k, v_k(B′_r) ≤ v_k(H₀) ≤ v_k(W).
    - The second is excluded because h ∈ J was available at i's SD turn, so v_i(h) ≤ p_i (null agents value nothing).
    - With h = Y_z, v_i(Y_z) ≤ p_i because the head is unfrozen at the picks.
  - **W** is checked over a partition of the agents other than k:
    - z: by (S-d), W ∩ R_z ⊆ {Y_z} and v_z(W) ≤ p_z < v_z(a); (S-d′) assumes the conclusion;
    - D ∖ {k}: (S-b), since threats are antitone in the value;
    - unfrozen pick holders other than z, w among them: (S-c);
    - F ∖ D: W ∩ R_i ⊆ {Y_z}, worth at most p_i;
    - pickless agents: null.

    z is unfrozen at the picks, so it is not in D. The partition is exhaustive.
  - A is a partition of all goods.
  - Hardness is not used.
- *Lemma HS.* With z unfrozen at B′:
  - (S2) is exactly "W does not threaten z at v_z(a) + v_z(h)";
  - (S3) covers everyone else at unchanged values;
  - {a, h} threatens nobody, as above.

  Correct.
- *HS-U1.* With one unfrozen pick holder, step 1 shows that a wanter of a at B′ would be a second one. Correct.

**Wording remarks** (no change to any claim).
1. *"With h = Y_z … the relaxed form is Theorem U."* It *contains* Theorem U, and is slightly more general:
   - it needs no hardness;
   - (S-a) is v_k(J) > p_k instead of k ∈ D_T;
   - (S-d′) with a frozen head needs only that J does not threaten z at v_z(a), not z ∉ E_J.

   Theorem U's hypotheses imply (S-a)–(S-c) and (S-d′), as the three bullets of the note say.
2. *log613, k = 2: "Every improving pair leaves agent 1 frozen and threatened."* With the data's values, the only
   improving H₀ ⊆ Π ∩ R₂ is the triple {4, 5, 6} (9 > 8; every pair is worth ≤ 7). "Pair" must mean (chain, H₀). The
   conclusion is right: the only holder is 0, so |H| ≤ 1, and the owner's bundle contains a good worthless to agent 1.

**Fix (log613's values).**

| | §10 prints | K4.MULTI.DATA (`hard2_starts.jsonl.gz`) |
|---|---|---|
| R₁ | {2: 8, 4: 2, 5: 3, 6: 4} | {2: 8, 4: 4, 5: 2, 6: 3} |
| R₂ | {3: 7, 4: 3, 5: 5, 6: 6} | {3: 8, 4: 3, 5: 4, 6: 2} |

R₀ agrees. With the **data's** values, the narrative is right throughout:
- p = (4, 8, 8);
- for k = 1, the only improving H₀ is {4, 5, 6};
- with |H| = 1, X threatens 2 at 8 (9 > 8), and 2 values neither good of J′ = {0, 1}, so 2 is a needy holder with an
  empty neighbourhood;
- with H = {0, 1}, the allocation ({1, 2}, {4, 5, 6}, {0, 3}) is EFX₀.

With the **printed** values the same picks arise (order (1, 2, 0)), but X = {4, 5, 6} threatens agent 2 even with
H = {0, 1}: v₂({4, 5, 6}) minus its cheapest good is 11 > p₂ = 7. So the printed |H| = 2 allocation is *not* EFX₀.
Replace the two lists by the data's.

**Computation (evidence).**
- For every k ∈ D, every longest canonical chain from k, and every h ∈ J ∪ {Y_z} meeting the hypotheses, the test
  takes **every** improving H₀ ⊆ W (not only minimal ones).
- When the head is frozen, it uses **every** wanter of a.
- It checks step 1's claims about the wanter, that the move is official, that A is a partition, and that A is raw EFX₀.

| run | starts | Theorem S tests (S-d / S-d′ only / h = Y_z) | failures | Lemma HS | HS-U1 |
|---|---|---|---|---|---|
| K4.MULTI.DATA | 8,383 | 64,486 / 20,600 / 16,330 | **0** | 83,133, 0 failures | 129,701, 0 failures |
| random perfect starts, not necessarily hard, ties in 30% (n = 3–5, two seeds) | 135,028 | 59,924 / 17,528 / 26,766 | **0** | 65,707, 0 failures | 14,235, 0 failures |

Mutations: each hypothesis is used. The failures are allocations that are not EFX₀; for the first mutation, the
second number counts wanters that are not holders.

| mutation | data: tests / failures | random: tests / failures |
|---|---|---|
| any canonical chain, not only longest | 129,817 / **16,265** (and 22,406 step-1 wanters not holders) | 14,727 / **490** (651) |
| drop (S-b) | 330,645 / **223,529** | 15,207 / **1,254** |
| drop (S-c) | 136,410 / **34,994** | 16,444 / **2,543** |
| drop (S-d) and (S-d′) | 114,777 / **13,361** | 15,857 / **1,956** |

**Coverage, recomputed independently on K4.MULTI.DATA.**
- Some (k, longest P, h) meets the hypotheses at:
  - **5,945** starts with (S-d);
  - **6,679** with (S-d′), h ∈ J;
  - **7,441** with (S-d′), h ∈ J ∪ {Y_z}.
- Theorem U's hypotheses (D_T = {k}, E_J ⊆ {z}, and z ∈ E_J ⟹ z unfrozen after P, at some longest chain) hold at
  **2,880**.
- All four match §10. I did not recompute the per-regime split, since it depends on the session's regime classifier.

**The SLOT residue (K4.MULTI.SLOT2, a conjecture; spot check of the named instances).**
- At log720, log613 and n4_3#947.0 (matched by name and picks), no (k, longest P, h ∈ J ∪ {Y_z}) meets Theorem S.
- The least kept-out set over every S\* completion with owner k ∈ D, after every canonical chain from k and every
  improving H₀ ⊆ Π (brute force), is **1, 2 and 3** respectively, as the table says.
- Witnesses:
  - log720: chain (0, 2, 3), H₀ = {0, 2}, agent 2 takes 8;
  - log613: chain (1, 0), H₀ = {4, 5, 6}, agents 0 and 2 take 0 and 1;
  - n4_3#947.0: chain (4, 2, 3), H₀ = {5, 8}, three holders take one good each.

## 11. Addendum: Lemma SD-E and Theorem REC-S, with Lemma LIFT (`k4/oc1max_multi.md` §12 and §8; 2026-11-27)

**Read.** §12 in full at `6c3fd95`, and again at `10d3bdf8`, where the proofs are unchanged and only a data row was
added. Also §8 (Lemma LIFT, unchanged; refereed CORRECT as item 22) and the ledger rows K4.MULTI.SDE and
K4.MULTI.RECS.

**Checks.** All my own code, raw EFX₀; nothing from `k4/oc1max_multi/` was run or imported.
- `k4/referee/rec_s_ref.py`, run by `rec_s_ref_runs.sh`, log `results/k4_referee/rec_s_ref.log`.
- Data, read as data only:
  - the 12 known failures (`oc1max_cex12.jsonl`);
  - the 4,955 walk failures (`oc1_fail_walk.jsonl.gz`).

**Verdict.**
- Lemma SD-E: **CORRECT**. Strict values are needed (mutation). So is the earliest-wanter choice: an arbitrary
  canonical chain fails.
- Theorem REC-S: **CORRECT**. Remarks:
  1. Hypothesis **(L) is redundant.** It always holds under the theorem's other assumptions (strict values, perfect
     start, T ⊆ J ∪ {Y_z}):
     - an agent i with a pick values a junk good g at most p_i, since g was available at its turn, and strictly less
       by strictness;
     - it values Y_z below p_i if i ≠ z, since Y_z is unwanted at the picks (strict);
     - for z, v_z(Y_z) = p_z < v_z(a);
     - and i's value after E(k) is at least p_i.

     (L) never failed in my runs (128,679 improving pairs). It can be dropped, or kept as a remark.
  2. SD-E's "in particular it is a perfect start of I⁻" needs Y perfect, as everywhere in the note. If Y is not
     perfect, B₁⁻ is still the SD outcome of σ ∖ k, but a pickless non-null agent of Y can stay pickless and still
     value a good of I⁻.
     - Example: agents 0, 1, 2 with v₀ = {0: 9}, v₁ = {0: 5, 1: 4}, v₂ = {0: 1}, σ = (0, 1, 2), so Y = (0, 1, –).
     - E(0) = (0, 1), and T = ∅.
     - In I⁻, agent 2 values good 0, which agent 1 holds, and agent 2 gets nothing.

     REC-S assumes a perfect start, so nothing downstream is affected.
  3. (K) is a genuine hypothesis. It fails at 188 of 6,065 Theorem S cases in my random runs, and every allocation
     where it fails is not EFX₀ (81 of 81 under the mutation).

**Lemma SD-E, re-derived.**
- σ increases along E(k): a wanter of Y_j picked after j, so the agents are distinct and the walk ends.
- Run σ ∖ k in I⁻. By induction, every agent before a has taken its B₁ good, so b_a is still available.
- Suppose some available g had v_a(g) > v_a(b_a) ≥ p_a. Then:
  - g is not junk: junk was available at a's turn in I;
  - g is not Y_z:
    - for a ≠ z, nobody wants Y_z. **This is the coordinator's first point:** Y_z may be available in I⁻ to agents
      that picked before z in I, and strictness plus "unwanted" settle it;
    - for a = z, z's new good beats p_z;
  - so g = Y_j is a pick that a wants, and σ(j) < σ(a);
  - g's B₁-holder comes after a, so it is not j. So j = x_l and the holder is x_{l+1}, with
    σ(x_l) < σ(a) < σ(x_{l+1}). Then a is an earlier wanter of Y_{x_l}, a contradiction.
- Distinct values make b_a a's unique favourite.
- With ties the argument gives only v_a(g) ≤ v_a(b_a), and tie-breaking can then hand a the other good. The mutation
  finds such cases.

**Theorem REC-S, re-derived.**
- E(k) with T is an official move (§29): T ⊆ (J ∪ {Y_z}) ∩ R_k is improving, and each x_l gains.
- B₁⁻ = SD(σ ∖ k) is a perfect start of I⁻.
- Theorem S needs no hardness. Its (G2) and the SD-order facts it uses hold at an SD outcome. So it gives P′ and an
  EFX₀ S\* completion X⁻ of I⁻. S\* is a one-absorber form, with the owner as absorber.
- LIFT 1: the conditions of an official move compare one agent's values on the current bundles, together with the pool
  J ∪ B_{x_t}. No condition mentions frozenness, picks or other agents.
  - Since k holds T, J(I, B₁) = J(I⁻, B₁⁻), and every other bundle is the same in I and I⁻.
  - So the move transfers verbatim, also when P′'s owner or head is an agent of E(k), which simply holds its B₁ good.
    **This is the coordinator's second point.**
  - In the data, P′'s head is an agent of E(k) in all 9,943 cases, and its owner is one in 57.
- LIFT 2: pairs inside I⁻ are as in I⁻. T threatens i ≠ k only if a single good of T beats v_i(X_i) ≥ v_i(B₁_i),
  which (L) excludes. k's view is (K). k receives no junk, so the absorber count is unchanged. Correct.

**Computation (evidence).** Two kinds of test:
- *SD-E:* every frozen k, the chain E(k), and every T ⊆ J ∪ {Y_z}, including non-improving T.
- *REC-S:* every k ∈ D, every improving pair T, and every Theorem S case in I⁻:
  - every longest chain, h ∈ J⁻ ∪ {Y_{z′}}, every improving H₀′ ⊆ W′ ∩ R_{k′}, and every receiver;
  - each repair is validated in I by simulating both moves as §29 official moves with my certifier-referee code
    (`cert_ref.apply_move`), then checking that the completion has one absorber, is a partition, and is raw EFX₀.

| run | starts | SD-E tests / failures | REC-S: repairs validated / failures | starts repaired |
|---|---|---|---|---|
| 12 known failures | 12 | 752 / **0** | 33 / **0** | **12 of 12** |
| 4,955 walk failures | 4,955 | 324,224 / **0** | 9,910 / **0** | **4,955 of 4,955** |
| random strict perfect starts (n = 3–5) | 50,631 (SD-E), 504,183 (REC-S) | 882,284 / **0** | 5,877 / **0** | 2,744 |

| mutation | tests / failures |
|---|---|
| SD-E with any canonical chain from k instead of E(k) | 343,136 / **43,272** |
| SD-E with tied values (tie-break by lowest good index) | 230,612 / **12,894** |
| REC-S without (K) | 81 / **81** (random); (K) never fails on the 4,967 data starts |
| REC-S with any canonical P₁, B₁⁻ not required to be SD | 912 non-SD cases / **7** (random) |

The coverage claim of §12 (REC-S repairs all 12 and all 4,955, in the E(k)-only form) is reproduced. I did not re-run
the matching session's 23,943 n = 5 walk rows.

## 12. Addendum: K4.MULTI.RECS.N4, an audit of `check_recs.py` and an independent re-validation (`b8bdc69`; 2026-11-27)

**Read.**
- `k4/oc1max_multi/check_recs.py` (125 lines) line by line, against the definitions.
- §12's paragraph "Certified at n = 4", and the ledger row K4.MULTI.RECS.N4.

**Check.** `k4/referee/recs_n4_ref.py`, log `results/k4_referee/recs_n4_ref.log`.
- It is my own validator: the earliest-wanter chain, reduction and Theorem S enumeration come from my `rec_s_ref.py`;
  the §29 move simulation, SD and raw EFX₀ from my `cert_ref.py`.
- `check_recs.py` was read, not run.
- Data:
  - the witness file `recs_witnesses_n4.json.gz`;
  - the certifier's export `two_move_starts_n4.json.gz` (sha256 `6159e38d…`).

**Verdict: CONFIRMED** (CERTIFIED stands). Two remarks on the checker, neither affecting the result.

**Audit of `check_recs.py`.** Its nine checks match the definitions:
1. SD picks, with ties broken by good index;
2. k frozen and valuing junk;
3. E(k) by σ-earliest wanters, up to an unwanted head;
4. T is two goods of (J ∪ {Y_z}) ∩ R_k with v_k(T) > p_k, and move 1's chain agents strictly gain;
5. (L), strictly;
6. SD-E, by SD of σ ∖ k with T banned;
7. move 2:
   - its agents are distinct and avoid k;
   - k′ is frozen and dangerous in the reduced state;
   - the head is unwanted;
   - H₀′ ⊆ J₁ ∪ B₁(z′) is improving;
   - the receivers take single goods and gain;
8. the owner's bundle is W = (J₁ ∪ B₁(z′)) ∖ {h}, and h goes to one other agent;
9. the final allocation is a partition (sorted goods = range(m)) that extends move 2 by junk only, with at most one
   absorber and X_k = T, and is raw EFX₀ over every removed good, zero-valued ones included.

Remarks:
- **(a) Coverage is not checked by the checker.** It reads each start's sets, values and picks *from the witness file*,
  so it cannot see a witness file that misses a start of the export or alters one. My validator closes this:
  - the witness starts equal the export's starts *as a multiset*: 112,880 each, 0 export starts without a witness, 0
    witness starts outside the export.
  - It would be worth adding this comparison (and the export's hash) to `check_recs.py`.
- **(b)** Check 7 does not require H₀′ ⊆ R_{k′}, which §29 requires of H sets. No witness has a good worthless to k′ in
  H₀′ (0 of 112,880), so this does not matter.
- Check 8 tests the *shape* of Theorem S, not its hypotheses. That is enough for the OC₂ certificate, since the
  allocation is checked raw. My validator also shows that **every witness is a genuine Theorem S case**:
  - in the reduced instance at B₁⁻, (k′, P′, h) meets the relaxed hypotheses with P′ a *longest* canonical chain;
  - the witness allocation is the one Theorem S builds;
  - (K) holds.

  So REC-S *as stated* applies at every n = 4 start, not only its shape.

**Re-validation (own code, all 112,880 witnesses).** For each witness, independently of `check_recs.py`:
- the picks are the SD outcome of the witness order, and k ∈ D;
- P₁ = E(k), and T is improving inside (J ∪ {Y_z}) ∩ R_k;
- both moves are replayed as §29 official moves by my simulator (H sets inside the relevant goods and the current junk,
  strict gains);
- (L) and SD-E hold, and k′ ∈ D in I⁻;
- the completion is a partition extending move 2 by junk, with at most one absorber and X_k = T, and is raw EFX₀.

| | count |
|---|---|
| export starts / witness starts / matched as multisets | 112,880 / 112,880 / **112,880** (0 missing, 0 extra) |
| witnesses valid | **112,880** |
| witness is a Theorem S case of I⁻ (relaxed, longest chain) with (K) | **112,880** |
| H₀′ with a good worthless to k′ | 0 |

**Standing.** At n = 4, OC₂^max holds by REC-S's mechanism at every start of the export. Like item 34, the claim "at
every n = 4 start with no one-move repair" inherits the completeness of the certifier's export, which I checked by
sampling only (item 21).

*Follow-up (`3143a331`).* Both remarks are applied, and I checked the diff:
- `check_recs.py` takes the export as an optional second argument. It prints its sha256 and compares the starts as a
  multiset (112,880; 0 missing, 0 extra).
- Check 7 now requires H₀′ ⊆ R_{k′}. The result is still 112,880 ok, with 8,241 negative tests rejected.
- One small point: the coverage comparison prints its counts but does not change the exit status, so a reader must
  read the log line.
