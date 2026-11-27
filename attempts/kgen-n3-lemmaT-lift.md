# Lifting the two-agent maximizer argument (Lemma T) to three agents (workstream `proof/kgen-n3`)

**Idea.** For two agents, Lemma T (`kgen/n3.md` §9; conjectured, 8,095 instances) says the following. Among
allocations that keep both picks (the agents' tops) and in which b does not strongly envy a, *every* maximizer of
v_a(X_a) is EFX₀. The natural three-agent lift fixes an order and an agent z, takes the OC₁-reachable allocations in
which the other two agents are EFX₀-satisfied, and asks whether every maximizer of v_z(X_z) is EFX₀.

**Where it breaks** (`kgen/lemmaT3.py`; Lemma R ported from `kgen/oc3.c` and equal to it on 360 starts).

- **z = the first picker.** It first fails at k = 4, n = 3, m = 6, with strict values:

  | agent | values of goods 0–5 |
  |---|---|
  | 0 | 0, 3, 0, 36, 97, 73 |
  | 1 | 42, 0, 22, 81, 64, 0 |
  | 2 | 0, 0, 38, 54, 87, 19 |

  - Order (2, 0, 1); the picks are 4, 5, 3. All agents get picks, so this is a maximum-matching start.
  - Over F, agent 2's value is at most 87. The maximizer ({0, 5}, {1, 2, 3}, {4}) is not EFX₀: agent 2 values
    {1, 2, 3} at 92 and good 1 at 0, so it must not envy that bundle, and it does.
  - The maximizer ({0, 1, 5}, {2, 3}, {4}) has the same value and is EFX₀.
- **z = the first picker, with a tie-break.** Among the maximizers, take those with the fewest goods that z values at
  0 in the others' bundles. This still fails at k = 5, m = 5:
  - values (38, 0, 66, 91, 0), (42, 26, 0, 38, 0), (65, 0, 0, 0, 23), order (1, 0, 2), picks 3, 0, 4;
  - the maximizer ({1, 2, 3}, {0}, {4}) is not EFX₀, while another maximizer is.
- **z = the last picker.** It fails already at k = 3 (31 of 576 starts).

**What survives.** "*Some* maximizer of v_z is EFX₀" (Conjecture T₃) holds on all 2,880 starts tested for each role,
covering k = 3, 4, 5, general values and zeros (`results/kgen_n3/lemmaT3b_2{1..4}_120_5_8.log`).

**Why it breaks.**
- With two agents, the other agent's EFX₀ constraint is a down-set in a's bundle, so any maximizer can be pushed until
  a is satisfied.
- With three agents, a maximizer can route a good that z values at 0 into another agent's bundle, which z must then
  not envy at all.

So an n = 3 proof must choose among maximizers. The tie-break by goods that z values at 0 is not enough.

Reproduce: `python3 kgen/lemmaT3.py 21 120 5 8 klim:3,klim:4,klim:5,general,zeros`. Its output lists "LIFT FAILS"
lines, and the summary shows "every maximizer EFX0" below 576 while "some maximizer EFX0" is 576. The k = 4 instance
also appears in `results/kgen_n3/lemmaT3_11_150_6_8_k45.log`.
