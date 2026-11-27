# Referee note: Lemma T5 (`k4/ttc.md` §13, branch `claude/k4-ttc` at `77bcab1`) and Lemma MAX

Referee: `proof/k4-referee`, 2026-11-26.

**Verdict: CORRECT. Lemma T5 is the same statement as Lemma MAX** (`k4/oc1_hall.md` §19, refereed in
`k4/referee/maxsd.md`), with the same augmenting-path proof.
- T5's "x reachable from u" (distinct agents x₁, …, x_t with Y_{x₁} ∈ R_u and Y_{x_{j+1}} ∈ R_{x_j}) is exactly MAX's
  set S of agents reached by alternating paths u, g₁, j₁, g₂, j₂, ….
- T5 (a), u values no junk, is the length-one augmenting path. MAX states it implicitly (u ∈ S).
- T5 (b) is MAX (1).
- T5's "In particular" (every agent whose pick u values values no junk, so it is not dangerous) is MAX (2). MAX
  additionally notes that want-chains above a dangerous agent end at an unfrozen pick holder.

The two sessions reached the same lemma independently. The ledger needs one row for it.
