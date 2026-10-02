# Dropping the upgrade step

Workstream `proof/k3-simplify` (`proofs/k3_simple.md` §4).

**Idea.** The rotation makes k* upgraded (it takes {b, c}). Maybe it can also cover the cases that K3ALG's upgrade
loop handles, so that the loop can go.

**Where it breaks.** Theorem B (e) shows that r cannot be exposed after the rotation, using (UT): if r holds its b,
its c is not junk. Without upgrades, r can hold b_r with c_r junk. After the rotation r then holds its top, and
{b_r, c_r} can be exactly k*'s new pair, so no junk good can protect r. When everything fits into slots no absorber
is needed and nothing goes wrong. With one more junk good than slots, the absorber k* hurts r.

**Smallest failing configuration**, at n = 2, m = 5. Both agents rank 0 ≻ 1 ≻ 2, and goods 3, 4 are worthless.
- The draft gives agent 0 good 0 and agent 1 good 1; the junk is {2, 3, 4}.
- r = 1 fails, because agent 0 is exposed and agent 0 is frozen.
- The rotation gives agent 1 good 0 and agent 0 the goods {1, 2}. Junk {3, 4} exceeds the one slot (agent 1's), so
  agent 0 absorbs at least one of them. Agent 1 now holds its top, and its b and c are in agent 0's bundle of at least
  three goods, so v₁(X₀ ∖ {junk}) = 5 > 4.
- With one worthless good (m = 4) the junk fits into agent 1's slot, and the run is EFX₀.
- With upgrades, agent 1 takes {1, 2} at once, and {0, 3, 4}, {1, 2} is EFX₀.

On cores (no worthless goods) the variant failed on no profile with n ≤ 5. It failed on 3 of 4,810,500 sampled
profiles at n = 6, the first with rankings (2, 6, 4), (2, 5, 7), (3, 8, 5), (3, 5, 9), (0, 1, 4), (0, 4, 1), m = 10
(`results/k3_simplify/variants_n6_sample.log`).

Reproduce:
- `python3 k3/simplify/exp_variants.py 4` (the rows with `up=N`)
- `python3 -c "import sys; sys.path.insert(0,'k3/simplify'); from exp_variants import run; print(run([(0,1,2),(0,1,2)], 5, up=False, take_all=False, klast=True))"`
