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
