# Referee report: k3-oc1's Lemmas 4–7 and kgen-n3's Lemma G5 / Corollary G5′ (the k = 3 statement (P))

Referee: `proof/k4-referee`, 2026-11-27, coordinator's queue (burst 5, item 1).
- Read:
  - `k4/k3_oc1.md` §11–§12 in full, on `claude/k4-k3-oc1` at `9719be2`, and §1–§3 again for the definitions (DE
    states, E_o, Lemmas 1–3, Theorem B\*);
  - `kgen/n3.md` §15.1–§15.6 in full, on `claude/kgen-n3` at `a319483`.
- Check: `k4/referee/k3lem_ref.py`, run by `k3lem_ref_runs.sh`, log `results/k4_referee/k3lem_ref.log`.
  - It is my own code, written from the texts. Raw EFX₀ and the one-absorber completion are brute force
    (`cert_ref.py`).
  - Nothing from `k4/k3oc1/` or `kgen/` was run or imported.

## Verdict

| item | verdict |
|---|---|
| Lemma 4 (shared pairs die together) | **CORRECT** |
| Lemma 5 (release count) | **CORRECT** (the state after the trade and the upgrades must be valid; DE trades and LB upgrades under (UT) keep validity) |
| Lemma 6 (hard ⟹ every terminal has a frozen exposed agent) | **CORRECT** (uses Lemma 3's general form; the base-of-owner hypothesis is automatic for a terminal owner) |
| Lemma 7 (the pointer walk) | **CORRECT**. "Direct" is exactly "has a valid Rule E rotation" |
| Lemma G5 (Rule E rotations keep the want graph acyclic, also after LB's upgrades) | **CORRECT**. Rule E is needed (mutation) |
| Corollary G5′ (\|J\| ≤ 2 ⟹ the Rule E rotation completes with no owner) | **CORRECT** |

## 1. Re-derivation

**Lemma 4.**
- Exposure of x for owner o needs {b_x, c_x} ⊆ J′ ∪ base(o).
- A good shared with k's pair lies in k's bundle. That bundle is neither junk nor o's base (o ≠ k).
- LB upgrades do not touch k's bundle. ∎

**Lemma 5.** Let the trade have q pair-takers, followed by u upgrades.
- *A chain* (k's pair ⊆ J): its start takes two junk goods, and its end releases its pick, so the net change is −1.
- *A ring:* each pair arrow t → k takes one junk good, since its pair is {Y_t, j}.
- *An upgrade* takes one junk good.

So |J′| = |J| − q − u.

With e = e′ = 0 (perfect, and no agent ends empty), Lemma 2 gives ω′ − ω = ν′ − ν = −r. Then
|T′| = |J′| − ω′ = |T| − q − u + r. The two corollaries are |J′| ≤ |T′| ⟺ r ≥ ω, and, with k's slot,
|J′| ≤ |T′| + 1 ⟺ r ≥ ω − 1.

Lemma 2 counts n = |U| + ν + |T|, which needs a valid state. DE trades keep validity (B\* (a)–(c)), and LB's upgrades
move only unwanted b's ((UT)). Correct.

**Lemma 6.**
- If E_t ∩ F = ∅, Lemma 3's general form for the terminal owner t asks h(∅) = 0 ≤ |T ∖ E_t| − 1. This holds since
  t ∉ E_t.
- Its hypothesis "no x ∈ E_t with {b_x, c_x} ⊆ base(t)" is automatic, since |base(t)| ≤ 1. This is the form the
  referee fix of Lemma 3 gave.
- Lemma 1 (b) then completes, contradicting hardness. ∎

**Lemma 7.** "Direct" means {b_k, c_k} ⊆ J, or end(k) = t for some t with k ∈ E_t. That is exactly a valid Rule E
rotation:
- {b_k, c_k} ⊆ J ∪ {Y_e} with e = end(k);
- if the pair is not inside J, it contains Y_e, so k ∈ E_e.

If no frozen exposed agent is direct, take k_t ∈ E_t ∩ F (Lemma 6). Then:
- {b_k, c_k} = {Y_t, j} with j ∈ J, and end(k_t) ≠ t. So f has no fixed point, and some cycle has length q ≥ 2.
- Rule E is deterministic, so chains that meet end at the same terminal.
- f is injective on a cycle, so the segments are disjoint. Their interior agents are frozen, so the only terminal in
  segment i is t_{i+1}.
- Every step is a want arrow or a pair arrow (b + c > a). With distinct junk partners, the ring is one §29 chain:
  - x₀ = k_{t₁} takes {Y_{t₁}, j₁} ⊆ J ∪ B_{x_t};
  - every other pair-taker takes Y_{t_i} plus j_i.

Correct.

**Lemma G5.** Every want arc u → w after the rotation goes forward in σ.
- *Into a receiver x_i.* x_i now wants only goods above Y_{x_{i−1}}, which it wanted before.
  - An unmoved good keeps its earlier holder, which precedes x_i.
  - A moved good Y_{x_{j−1}} with j > i would put x_{j−1} before x_i in the need DAG, against the chain's increase.
  - j = i is x_i's own good, so j < i.
  - A good in k's pair is unwanted, by validity.
- *Out of a receiver.* Other wanters of Y_{x_{i−1}} (non-chain agents, or chain agents whose wants only shrank) wanted
  it at the draft. So they are later than the σ-earliest wanter x_i.
- *Other cases.* Non-chain arcs are unchanged, and k wants nothing and is wanted by nobody.
- Upgrades only delete arcs.

The case split is exhaustive. ∎

**Corollary G5′.**
- |J′| = |J| − 1, as in Lemma 5 with q = 1. t holds a single good, so some agent is outside U′.
- The acyclic want graph on those agents has an agent nobody wants, a terminal, so |T′| ≥ 1 ≥ |J′| when |J| ≤ 2.
- Upgrades never raise ω. So Lemma 1 (a) completes, with no owner, and every bundle has at most two goods. ∎

## 2. Computation (evidence)

**Data.**
- Random instances of DE's core case: n = 3–6, three goods per agent, values (4, 3, 2), which are exact by L5; dead
  goods allowed.
- The drafts of up to 6 random orders each, kept if perfect.
- Each draft is tested as it is and after LB's maximal upgrades.
- Hard means the draft has no one-absorber completion (brute force).

| check | tests | failures |
|---|---|---|
| G5: valid state and acyclic want graph after every valid Rule E rotation, before and after upgrades | 360,518 rotations | **0** |
| Lemma 4, after every rotation | 360,518 | **0** |
| Lemma 5: \|J′\|, \|T′\| and ω′ counted directly against the formulas (q = 1, u upgrades) | 360,518 | **0** |
| G5′: \|J\| ≤ 2 ⟹ \|J′\| ≤ \|T′\| before and after upgrades, and a one-absorber completion exists | 149,978 | **0** |
| Lemma 6: every terminal of a hard state has a frozen exposed agent (17,568 hard draft states, with and without upgrades) | 35,496 terminals | **0** |
| Lemma 7 on the two crossed configurations (n = 6 of §12; n = 7 of §12.1): no valid Rule E rotation; f has no fixed point; the segments are disjoint; the ring is a §29 official move with a valid result, and it completes | 2 / 2 | **0** |
| *mutation:* any need chain instead of Rule E | 86,300 rotations | **2,678 cycles** |

The random drafts never produced a hard state without a direct k. That is the rare crossed configuration (64 of
338,916 drafts at n = 6 in the source). So Lemma 7 is tested on the named instances only.

## 3. For the coordinator

All six items are correct, and each can be cited as PROVED. They are tools: none of them is (P) itself. As both notes
say, (P) still needs the release-plus-owner count. The release bound (R) is false at n = 7, and T-ω is conjectural.
