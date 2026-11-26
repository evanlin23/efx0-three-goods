# Conjecture L / PL: every Pareto-maximal partial EFX₀ orientation of a linear instance is completable

Workstream `proof/k4-girth` (`k4/girth.md` §4). **Approach:** in a linear hypergraph (two agents share at most one
good) take a partial EFX₀ orientation whose value vector is Pareto-maximal among all partial EFX₀ orientations. Facts
F1–F6 hold there (proved), and Lemmas PARK and SLACK complete it whenever every leftover good has a common safe vertex
or a one-good absorber. Conjecture L said this always happens; PL said only that some EFX₀ completion exists. Both
survived ~1.5·10⁵ Pareto-maxima of random linear instances (n ≤ 7, ≤ 10 goods; `results/k4_girth_linear_pm_*.log`).

**Result: both are false**, on a hand-built linear instance with n = 4, m = 7, every agent valuing three goods
(so even k = 3). Agents i = 0, j = 1, r = 2, s = 3; goods e = 0 {i, j}, x_i = 1 {i, r}, x_j = 2 {j, s}, f = 3 {r, j},
h = 4 {s, i}, g = 5 {r}, g′ = 6 {s}:

    i: {e: 6, x_i: 10, h: 6}    j: {e: 6, x_j: 10, f: 6}    r: {x_i: 10, f: 4, g: 4}    s: {x_j: 10, h: 4, g′: 4}

State: i ← {x_i}, j ← {x_j}, r ← {f, g}, s ← {h, g′}, e unallocated; values (10, 10, 8, 8). It is a partial EFX₀
orientation, Pareto-maximal among all of them (brute force), and **no** EFX₀ completion exists: e to i or j makes r or s
strongly envy (they envy x_i, x_j and e is worthless to them); e to r gives j the bundle {f, g, e} worth 12 > 10 with g
worthless to j; e to s, symmetrically, fails for i.

The configuration is CFKS's second scenario with *rich* sources: r (an envier of i) is dangerous for j, s (an envier of
j) is dangerous for i, and both hold two goods, so there is no slack absorber. The random runs never produced it because
a source holding two goods while envying a one-good holder needs a top-heavy agent (here r and s: 10 ≥ 4 + 4), or a
fourth good. It is not a k = 4 core: R1 peels r and s first, which is exactly a non-value-monotone step (r takes x_i).

**Consequence.** As at k = 4 with 2-cycles (P1, `k4/sdc.md` §1), no argument of the form "take a Pareto-maximal partial
EFX₀ orientation and complete it" proves EFX₀ for linear instances; the potential or the procedure must exclude such
states. LSS's own run avoids it on this instance: with the flexible sink every one of its 16 labelings ends EFX₀,
because FixProp3 hands out single goods first and r never holds {f, g}. **It also fails in a strict linear k = 4 core** (n = 5, m = 11, every agent with four goods, seven 3-cycles):
add an agent w and goods t = {r, w}, t′ = {s, w}, q_i = {i, w}, q_j = {j, w}, all held by w, so that w is dangerous
for both i and j and r, s become balanced:

    i: {e: 12, x_i: 20, h: 13, q_i: 9}    j: {e: 12, x_j: 20, f: 13, q_j: 9}
    r: {x_i: 20, f: 7, g: 6, t: 8}        s: {x_j: 20, h: 7, g′: 6, t′: 8}    w: {q_i: 10, q_j: 7, t: 4, t′: 2}

The state i ← {x_i}, j ← {x_j}, r ← {f, g}, s ← {h, g′}, w ← {t, t′, q_i, q_j}, e unallocated, values
(20, 20, 13, 13, 23), is Pareto-maximal among the partial EFX₀ orientations and has no EFX₀ completion; 33 of the 34
Pareto-maxima of this core do complete. Both instances are re-checked by an independent enumeration in the replay
script (fresh code: no dominating orientation, no EFX₀ completion; its sensitivity is tested on a dominated state).
On both instances the maxima of welfare, Nash welfare and "Pareto-maximal, then most non-envied" satisfy PARK; the
leximin maximum of the n = 4 instance is the bad state.

**Reproduce:** `python3 attempts/k4_girth_attempts.py` (part 4).
