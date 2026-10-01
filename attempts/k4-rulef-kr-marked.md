# Lemma KR's "the rotation is a `RotStep`" needs the marked agents' bases to avoid NA (k4/rulef.md §3, at 719c911)

Found while formalizing Lemma KR in Lean (`lean/EFX/RuleFK.lean`, `EFX.LB4R.lemmaKR`, workstream
`formal/k4-rulef-count`). Not an error in the counting: the deficit bound holds; what fails is one clause of the
conclusion for states that LB₄ʳ never reaches.

**Statement as written.** "Let P be a valid pre-allocation whose bases have at most two goods, … Then P′ is a valid
pre-allocation, the rotation is a `RotStep`, and (P′, owner k, K = ∅) has deficit at most δ − 1 − c_k + ε." The proof
of "`RotStep`" checks (V1), (V2) for k's new base O and says "the other two-good bases are unchanged and miss
NA ⊇ NA′".

**Where it breaks.** `EFX.LB4R.RotStep` ends with `RotChecks`, which asks (V2) of every *marked* agent, even one whose
base is a single good (`k4/lb4.md` §5, as in `lb4.c`). A valid pre-allocation in the sense of `k4/lb4.md` §1 (and a state
with `EFX.LB4R.Inv`) may have a marked agent off the chain whose one-good base is needed; that base is unchanged by the
rotation and still needed, so `RotChecks` fails and the rotation is not a `RotStep`.

**The fix.** Add the hypothesis "every marked agent's base avoids NA" (`EFX.LB4R.MarkedOK`). It holds in every state
LB₄ʳ reaches, so the lemma as used (for states of LB₄ʳ) stands: after Phase 1 and upgrades of any policy every marked
agent is upgraded and has a two-good base, so (V2) gives it (`EFX.LB4R.upRun_facts`), and after a rotation `RotChecks`
itself gives it (`EFX.LB4R.markedOK_of_rotStep`). `EFX.LB4R.lemmaKR` and `EFX.LB4R.lemmaKR_output` take it as the
hypothesis `hmk`.

**Smallest failing configuration** (n = 3, m = 4; a chain has two agents and the marked agent is a third; O needs two
goods, since a single good of W worth more to k than Y_k would be in N_k, against (V1) or o not frozen; plus Y_k and
the marked agent's good). Agents k = 0, o = 1, m = 2; goods y = 0, g = 1, j₁ = 2, j₂ = 3. Values: k (3, 0, 2, 2),
o (1, 2, 0, 0), m (0, 5, 0, 0). State: B_k = {y} (k's pick), B_o = ∅ (no pick), B_m = {g} with m marked, J = {j₁, j₂};
needs as `needsOf` gives: N_k = ∅, N_o = {y, g}, N_m = ∅. It satisfies `Inv` ((V1): J misses NA = {y, g}; no base has
two goods). Lemma KR's hypotheses hold: o is not frozen and |B_o| = 0; W = J threatens nobody, so E = ∅ and the empty
service has size 0 (κ = 0, δ = 0); the chain k → o (k frozen, y ∈ N_o); O = {j₁, j₂} ⊆ R_k ∩ W with
v_k(O) = 4 > 3; (i) is vacuous; after the rotation o holds y and is not frozen ((ii)) and not threatened (ε = 0); (iii)
holds (`Inv`). The deficit bound holds (E′ = ∅, κ′ = 1: deficit −1 ≤ δ − 1 − c_k + ε = −1). But after the rotation o
needs g (2 > 1), and m, marked, still holds {g}: `RotChecks` fails, so the rotation is not a `RotStep` (and LB₄ʳ does
not perform it). The state is not reachable by LB₄ʳ: every state LB₄ʳ reaches (Phase 1, upgrades, then rotations) is the result of
the upgrades or of a `RotStep`, and satisfies `MarkedOK` by the two lemmas above.

Reproduce: `python3 attempts/k4_rulef_kr_marked.py` (the Lean definitions written out for this instance; exit status 0
iff every check above holds).
