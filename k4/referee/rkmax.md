# Referee check: Conjecture RKMAX at n = 4, and its two logical claims (`k4/sdc.md` §31 end)

Referee: `proof/k4-referee`, 2026-11-27.
- **Read:** `k4/sdc.md` §31 at `c1b2756b` on `claude/kind-lamport-y8fdme`: the paragraphs "Conjecture RKMAX", "Proof
  shape", "Evidence" and "RF and σ". Also:
  - Lemma MAXSD (§31) and Lemma SDPO (§28);
  - the ledger row K4.SDC.RKMAX;
  - `lean/EFX/OCVariants.lean` on main (`ConjOC1exmaxWith`, `conjOC1exmaxWith_of_conjOC1maxWith`);
  - the coordinator's logs `extremal_rank_check_n4.log` and `rm_path_check_n4.log`, read as data.
- **Check:** `k4/referee/rkmax_ref.py` (`rkmax_ref_runs.sh`), log `results/k4_referee/rkmax_ref_all.log`. The code is
  my own: SD, ν, raw EFX₀, the official moves and the one-absorber completion come from `k4/referee/cert_ref.py`,
  written for my earlier re-verification of the certifier. The move set is additions, chains (passed bases nonempty)
  and rings: the move set of the coordinator's `oc1_mc2_rand.Inst.check`, which I read but did not run. Nothing from
  `k4/sdc/` is run or imported.
- **Input:** the certifier's complete n = 4 export `results/k4_oc1max/two_move_starts_n4.json.gz`, byte-identical on
  `compute/k4-oc1max-cert` and on `c1b2756b`, read as data.

## Verdict

- **The n = 4 claim is CONFIRMED by a second implementation** (numbers in §2). Every σ-maximal maximum-matching vector
  satisfies OC₁ at all 111,600 profiles. With the certifier's complete export (CERTIFIED) and the type reduction, that
  makes RKMAX at n = 4 a two-implementation certificate.
- **"RKMAX ⟺ every failing start has a σ-larger maximum-matching SD vector": CORRECT** (§1).
- **"RKMAX ⟹ OC₁^∃max": CORRECT**, given Lemma MAXSD (§1).
- **n = 5** (§2b): every σ-optimum satisfies OC₁ at all 583,680 profiles of the complete lists of 5_pure #419, #447
  and #38. This is a second implementation of the coordinator's `e6227707` claim. A 1-in-200 sample of the partial
  lists also shows no failure.
- **Text remark** on the "RF and σ" counts (§3): "raises σ at 111,600 pairs" means 111,600 of the 112,880 pairs. At
  the other 1,280 pairs no listed rotation raises σ, although some other u-first maximum-matching order does.

## 1. The logic

Fix a strict connected k = 4 core and a strict profile. Let 𝓜 be the set of maximum-matching (MM) SD pick vectors over
all n! orders. OC₁ at Y is a property of the profile and the pick vector Y alone: completions and moves start from the
bases {Y_i}, not from the order.

- **𝓜 is finite and nonempty.** Finiteness holds because there are n! orders. Nonemptiness is Lemma MAXSD (§31), which
  I re-derived. Take a maximum matching M that is Pareto optimal among maximum matchings (one exists, since there are
  finitely many maximum matchings). A Pareto improvement of M cannot unmatch anyone, since a matched agent prefers any relevant good
  to none. It cannot match anyone new, since M is maximum. So it is again maximum, and M is Pareto optimal among all
  matchings. By SDPO (§28, whose (⊇) direction I re-read) M is an SD outcome. In Lean, MAXSD is
  `exists_order_maximum`, used by `conjOC1exmaxWith_of_conjOC1maxWith`.
- **The equivalence.** The lexicographic order on ℕ⁴ is total, so for Y ∈ 𝓜: "Y is σ-maximal" ⟺ "no Y′ ∈ 𝓜 has
  σ(Y′) > σ(Y)".
  - (⟸) If every OC₁-failing Y ∈ 𝓜 has a σ-larger Y′ ∈ 𝓜, then no σ-maximal Y fails OC₁, which is RKMAX.
  - (⟹) Under RKMAX, an OC₁-failing Y ∈ 𝓜 is not σ-maximal, so some Y′ ∈ 𝓜, for instance any σ-maximal one, has
    σ(Y′) > σ(Y).
  - Both sides quantify over the same 𝓜 of the same profile, so the equivalence holds profile by profile, and hence for
    the universal statements. Correct.
- **RKMAX ⟹ OC₁^∃max.** By MAXSD, 𝓜 ≠ ∅. A σ-maximal Y ∈ 𝓜 exists by finiteness. It comes from some order ord,
  which is a permutation of the agents with a maximum-matching pick vector. RKMAX gives OC₁ at Y, which is exactly the
  witness `ConjOC1exmaxWith` asks for. Correct.
  - The Lean frame needs a finite argmax over `List.permutations`, plus the identification of the move relation
    (`OneMove`) with the moves used in RKMAX's check (additions, chains, rings).
- **Side claims of the paragraph** (not needed for the above):
  - *Type invariance.* The set 𝓜 depends only on each agent's order of single goods, because SD with strict values is
    ordinal. σ depends only on those orders. OC₁ at Y depends only on each agent's order of subset sums. So RKMAX at a
    profile depends only on its type profile. Correct, and this is what lets the export's integer representatives
    stand for all strict profiles.
  - *A σ-maximal maximum matching is Pareto optimal.* A Pareto improvement M′ of a maximum matching M keeps the matched
    set (above). Each agent's rank then weakly falls and one rank strictly falls. So every cumulative count
    N_j = #{rank ≤ j} weakly rises and some N_j strictly rises. At the least such j, the counts n₁, …, n_{j−1} are
    unchanged and n_j rises, so σ(M′) > σ(M) lexicographically. Correct. So the maximum of σ over all maximum
    matchings is attained in 𝓜, and the remark is consistent with optimizing over SD vectors only. The citation to
    Irving–Kavitha–Mehlhorn–Michail–Paluch is [unverified] here too.

## 2. The n = 4 computation (`rkmax_ref.py all`; `rkmax_ref_all.log`)

For each of the 111,600 profiles (sets, vals) of the export, I ran all 24 orders and computed ν (augmenting paths),
the set 𝓜 of MM vectors, the ranks and σ, and OC₁ by my own search (one-absorber completion at the picks, or after one
addition, chain or ring).

| quantity | mine | coordinator (`extremal_rank_check_n4.log`) |
|---|---|---|
| profiles | 111,600 | 111,600 |
| MM vectors | 769,360 | 769,360 |
| MM vectors failing OC₁ | 112,880 | 112,880 |
| profiles where my failing set = the export's picks | **111,600 of 111,600** | – |
| σ: every optimum satisfies OC₁ | **111,600** | 111,600 |
| σ: some optimum satisfies OC₁ | 111,600 | 111,600 |
| LMR (leximin on ranks): every / some optimum | 111,600 / 111,600 | 111,600 / 111,600 |
| RS (minimum rank sum): every / some optimum | 111,600 / 111,600 | 111,600 / 111,600 |
| TOP (most rank-1 agents): every / some optimum | **23,280** / 111,600 | 23,280 / 111,600 |
| failing Y with a σ-larger MM vector | 112,880 of 112,880 | – |

Notes:
- **My OC₁ test agrees with the certifier's export exactly.** At every profile, the MM vectors that fail OC₁ in my
  search are precisely the picks the export lists for that profile, so the export is neither stale nor over-full here.
- **σ-maximal vectors are not unique.** There are 198,400 σ-optimal vectors over the 111,600 profiles, so "every
  σ-maximal vector" is the right reading, and it holds. Of the 198,400:
  - 187,560 complete at the picks;
  - 10,840 (5.5%) need one move.
  The coordinator's 1-in-100 sample had 127 of 1,982 needing one move; the full count confirms that the optimum is
  not OC₀.
- **The certificate at n = 4.** The export is the certifier's complete list of OC₁^max-failing (type profile, picks)
  pairs (CERTIFIED, re-verified by me earlier, `oc1cert.md`). A strict profile outside it has no failing MM vector,
  so RKMAX holds there trivially. Inside it, the table shows RKMAX at every profile. By type invariance (§1), the
  integer representatives stand for all strict profiles of their types. So RKMAX at n = 4 now rests on two
  implementations: the coordinator's and this one.

## 2b. n = 5 (`rkmax_ref.py sigma`; `rkmax_ref_n5_*.log`)

In sigma mode, OC₁ is checked only at the σ-optimal MM vectors. All 120 orders are run at each exported profile.

| export (`compute/k4-oc1max-cert`, `results/k4_oc1max/n5/`) | profiles | MM vectors | σ-optima | every σ-optimum OC₁ | optima completing at the picks / needing one move |
|---|---|---|---|---|---|
| `two_move_starts_n5_sel2.json.gz`: complete lists of 5_pure #419, #447, #38 | 583,680 | 5,466,240 | 1,004,160 | **583,680 of 583,680** | 1,004,160 / 0 |
| `two_move_starts_n5_partial6.json.gz`: partial lists, every 200th profile | 3,503 | 44,425 | 6,485 | 3,503 of 3,503 | 6,461 / 24 |

- **The complete lists.** This is a second implementation of the coordinator's n = 5 claim (`e6227707`,
  `extremal_rank_n5_sel2.log`: σ-optimal vectors satisfy OC₁ at all 583,680). The optimum-set sizes agree:
  163,200 × 1 + 420,480 × 2 = 1,004,160 σ-optima. My LMR count (1,004,160) and RS count
  (163,200 + 2 · 391,680 + 4 · 28,800 = 1,061,760) also agree; OC₁ at those optima was not re-run here. Since the
  lists are complete for these three cores, RKMAX on them now rests on two implementations. One caveat: I did not
  re-derive the completeness of the n = 5 lists, which is the certifier's claim.
- At these three cores every σ-optimum completes at the picks: no move is needed.
- The partial lists, sampled at 1 in 200, show no failure.

## 3. "RF and σ"

`rkmax_ref.py all` also recomputes the RF/σ counts. At each failing start Y (each has exactly one receiver u at
n = 4, 112,880 of 112,880), and each listed order o, I took Y′ = SD(u, o − u):

| quantity | mine | coordinator |
|---|---|---|
| failing pairs (Y, u) where some u-first MM order raises σ | 112,880 of 112,880 | 112,880 (`extremal_rank_check_n4.log`) |
| failing pairs where some *listed* rotation (u, o − u) raises σ | 111,600 of 112,880 | 111,600 True, 1,280 False (`rm_path_check_n4.log`) |
| rotations: MM and σ raised | 283,120 of 292,080 | 16,240 + 266,880 = 283,120 |
| rotations: MM, σ not raised | 8,960 | 8,960 |
| rotations: not MM | 0 | 0 |

All the numbers agree.

**Text remark.** In §31, "The rotation (u, o − u) of a listed order o raises σ at 111,600 pairs" should say "at
111,600 of the 112,880 pairs". At the other 1,280 pairs, no listed rotation raises σ, though some other u-first MM
order does. Also, "At the other 266,880 rotations that raise σ" leaves out the 8,960 rotations that are maximum
matchings but do not raise σ.

So the potential form of RF in the ledger row ("At every failing pair (Y, u) some u-first maximum-matching vector raises
σ, 112,880 of 112,880") is correct as stated. It concerns some u-first vector, not the rotation of a listed order.

## Addendum (07:20): the rkmax session's note (`k4/rkmax.md` on `proof/k4-rkmax` at `ebd17e7e`, draft PR #158)

**Read:** §1 (Observation W; Lemmas TC, COMP, PO, 2AG), §2 and §3, line by line. There is no lemma named "GAIN" at
this head; 2AG, the two-agent gain/loss lemma, is taken to be the one meant.
**Check:** `k4/referee/rkdom_ref.py`, log `results/k4_referee/rkdom_ref_n4.log`. The code is my own: it enumerates
all maximum matchings directly, and uses `rkmax_ref.oc1` for OC₁. Nothing from `k4/rkmax/` is run.

### Verdicts

- **Observation W: CORRECT FOR MATCHED AGENTS; a wording fix.**
  - At a Pareto-optimal matching every good i prefers to M_i is matched, since otherwise giving it to i improves on M.
    So for a matched agent, rank − 1 = #{goods preferred} = out-degree in W.
  - For an *unmatched* agent, rank = 5 by convention, while its out-degree is |R_i|: every valued good is matched and
    preferred. That is 3 for a three-good agent. So "rank_i − 1 is the out-degree" and "the rank sum is n + |W(Y)|"
    fail at a non-perfect start with an unmatched three-good agent.
  - Also, "the receivers are the agents of in-degree 0" counts pickless agents too, unless receivers are read in Lean's
    sense.
  - Fix: say "at a perfect start", or "for matched agents". The signature counts ranks 1–4 only, so σ as the
    out-degree distribution of the matched agents is correct.
- **Lemma TC: CORRECT.**
  - (a): the first nonzero Δσ_t is the first nonzero Δc_t.
  - (b): the standard equivalence for sorted vectors via counts. c₅ = n for both, so t = 1..4 suffices.
  - (c): σ by (a). The rank sum is Σ_{t=0}^{4} (n − c_t). Leximin follows from pointwise ≤ of the sorted vectors with
    inequality somewhere.
  - (d): an agent's rank depends on its own good only.
- **Lemma COMP: CORRECT.**
  - Y ⊕ Y′ for two maximum matchings has components that are even cycles and paths with equally many edges of each.
    A path with more Y′ edges would augment Y, and one with more Y edges would augment Y′.
  - The equal paths are chains (two good ends) or shifts (two agent ends), and each Y ⊕ C_j is maximum.
  - Δc is additive over components on disjoint agents, by TC(d), and the lexicographic order on ℤ⁴ is compatible with
    addition. So no σ-raising single component implies no σ-raising Y′. The converse is immediate.
- **Lemma PO: CORRECT.** A Pareto improvement of a maximum matching keeps the matched set, since it can neither lose
  nor, by maximality, add an agent. Ranks weakly fall and one strictly, which is rank dominance by TC(b). The
  "in particular" follows from TC(c) and SDPO (strict values).
- **Lemma 2AG: CORRECT.**
  - Δc_t = [r′_a ≤ t < r_a] − [r_b ≤ t < r′_b].
  - Rank dominance means the drop interval ⊆ the rise interval with the two different, i.e. r′_a ≤ r_b, r′_b ≤ r_a,
    not both equalities.
  - σ rises iff the first nonzero Δc_t is +1: r′_a < r_b, or r′_a = r_b with the drop ending first (r′_b < r_a).
    Equal intervals give Δc ≡ 0.

### Data (n = 4, the certifier's complete export; every profile)

| claim (§3) | rkmax session | mine |
|---|---|---|
| every failing start is rank-dominated | 112,880 of 112,880 | **112,880 of 112,880** |
| … least dominating change: 2 agents / 3 agents | 107,760 / 5,120 | 107,760 / 5,120 |
| undominated maximum matchings, all satisfying OC₁ | 213,120 | **213,120**, all SD outcomes, all OC₁ |
| σ-optimal vectors (§2): total; completing at the picks / after one move | 198,400; 187,560 / 10,840 | the same (§2 above) |
| RS / LMR optimal vectors | 213,120 / 197,120 | the same |

On every 20th profile (5,580 profiles, 571,236 maximum matchings), I also checked:
- **COMP** directly: at every σ-maximal maximum matching (9,624), no maximum matching differing on a single component
  of the symmetric difference has larger σ. At every non-maximal one (561,612), one does. No violation.
- **2AG's formula** against the direct comparison (dominance and σ) on all 6,918,828 two-agent changes between maximum
  matchings: equal at all.

So **Conjecture RKDOM at n = 4** now has a second implementation. Since the export lists every failing start, "every
failing start is rank-dominated" certifies RKDOM, hence RKMAX, RS and LMR, at n = 4, together with the certifier's
completeness and the type reduction.

**Not re-run:**
- the n = 5 RKDOM runs of the commit message (583,680 sel2 starts dominated by a 2-agent change);
- the n = 4 class census of §2 and the Theorem U/S census of `ebd17e7e`.
