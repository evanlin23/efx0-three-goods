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
- Starts: 360,000 instances (n = 3–5, k ≤ 4) and 34,795 one-absorber-hard starts, of which 8,466 have D_T = {k}
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
