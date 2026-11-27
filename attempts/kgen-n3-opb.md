# "One pick per bundle" (OPB): a pick-carrying invariant for OC₁ that fails

Workstream `proof/kgen-n3`; full account in `kgen/n3.md` §13–§14.

**The approach.**
- Look for an EFX₀ completion in which every bundle holds exactly one serial-dictatorship pick, and every agent that
  holds another agent's pick values its bundle above its own pick.
- The picks are then permuted, and each non-trivial cycle of the permutation is one ring of Lemma R. At n = 3 a
  permutation has at most one non-trivial cycle, so OPB would have explained why one move suffices at n = 3, and
  disjoint rings would have been the n = 4 picture.
- OPB was also the invariant for carrying the picks through the AACGMM three-agent EFX algorithm (§13–§14).

**Why it seemed right.** It held on all 2,880 random n = 3 starts (m ≤ 8; generic, near-identical and zero-heavy
values) and on 3,523 random n = 4 starts. On the two k ≥ 5 counterexamples to OC₁ at n = 4
(`attempts/kgen-n4-oc1.md`), the repairs are of type 2+2.

**Why it fails.** On strict balanced k = 4 cores, the OC₁ repair can need the receiving agent of a chain to keep its
own pick as its one good outside the base. Two picks then share a bundle.

**Smallest failing configurations** (`python3 kgen/opb_cex.py`, `results/kgen_n3/opb_cex.log`):
1. **n = 3, m = 5** (a k = 4 core).
   - Sets [[0,1,2,4],[1,3,4],[2,3,4]], values [[3,6,10,2],[4,2,3],[4,2,3]], order (1,2,0), picks (0,1,2).
   - There are 5 EFX₀ allocations, and four of them put two picks in one bundle.
   - The fifth, ({2},{1,3},{0,4}), has one pick per bundle, but agent 2 gets 3 < 4.
   - OC₁ holds there, e.g. ({0,1},{3,4},{2}): a chain 1 → 0 in which agent 0 keeps its pick 0 as an extra good.
2. **n = 4, m = 7** (the k = 4 counterexample to OC₁^max, `k4/oc1cert.md` on `compute/k4-oc1max-cert`).
   - There are 14 EFX₀ allocations, and 4 have one pick per bundle. In none does every moved agent gain.

**Exhaustive scope.** `kgen/opb3_cover.py` checks all 51 n = 3 cores at k = 4, for every strict balanced profile and
every order. Many cores have uncovered profiles, even without the absorber condition (`results/kgen_n3/opb3_cover.log`).

**What remains.** OC₁ itself still holds on all n = 3 data. Its repairs are chains x₀ → x₁ in which x₁ may keep y_{x₁}
as its single extra good, not permutations of the picks.
