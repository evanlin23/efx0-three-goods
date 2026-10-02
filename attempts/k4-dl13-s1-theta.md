# DL₁₃ existence: "an S1 shape always gives the S1 repair"

Workstream `proof/k4-dl13` (`k4/dl13.md` §2, §5). Ledger row K4.DL13.X (REFUTED).

**Candidate.** If a T1-stuck state has an S1 shape (a best owner o needs the good g of a frozen x, and for an optimal
X some c ∈ J ∖ X is blocked by x alone), then for some such (o, X, c) the owner o holding g is not threatened by
X ∪ {c} (θ_o(X ∪ {c}) ≤ v_o(g)), so that Corollary 9.1 (o and x swap, x owns X ∪ {c}) lowers the deficit.
Lemma 10 says how it can fail: (θ-a) o has at most two goods in X ∪ {c} worth more than g, or (θ-b) o is big-top on g
with its three lower goods in X ∪ {c}. The candidate says neither happens at every S1 triple.

**Smallest failing configuration: `dl13-n3m7-theta`** (n = 3, m = 7; #53's n = 3 catalogue, core (m = 7, idx 5) of
`results/k4_certs_3.json.gz`, profile 20,146,100).
- agent 0: goods 0:2, 2:6, 5:3, 6:10 (big-top: 10 > 6 + 3; balanced: 10 < 11);
- agent 1: goods 1:6, 4:2, 5:3, 6:10 (big-top);
- agent 2: goods 3:4, 4:6, 5:5, 6:8 (not big-top).

P = ({0, 2}, {1, 4}, {6}), J = {3, 5}.
- Needs: N₀ = N₁ = {6} (each pair is worth 8 < 10), N₂ = ∅. Agent 2 is frozen on 6 with two needers; f = 1, σ = −1,
  ω = 2, S = 0.
- Owner 0 (W₀ = {0, 2, 3, 5}): {0, 2, 3} and {0, 2, 5} are safe; {0, 2, 3, 5} threatens agent 2 only (θ₂ = 4 + 5 = 9 >
  8; agent 1 values only 5 there). u = 0 (two needers). Val = 3.
- Owner 1 (W₁ = {1, 3, 4, 5}): {1, 4, 3} and {1, 4, 5} threaten agent 2 (θ₂ = 6 + 4 = 10, 6 + 5 = 11 > 8). Val = 2.
- V = 3, def(P) = ω + 2 − V = 1. T1-stuck (checked by both implementations).
- The S1 triples are (o, X, c) = (0, {0, 2, 3}, 5) and (0, {0, 2, 5}, 3); in both, X ∪ {c} = {0, 2, 3, 5} and
  θ₀({0, 2, 3, 5}) = v₀({0, 2, 5}) = 11 > 10 = v₀(6): agent 0 holding 6 would be threatened by its own three lower
  goods. This is (θ-b) of Lemma 10; no S1 triple is θ-ok, so Corollary 9.1 does not apply.

**DL₁₃ still holds there** (17 (T3) moves lower the deficit). E.g. P′ = ({0, 2}, {6}, {3, 4}): the other needer,
agent 1, takes 6; agent 2 takes {3, 4} (the junk good 3 that it blocked, and 4 from agent 1's old base: worth 10 > 8,
so agent 2 needs nothing); owner 0 keeps its base and owns {0, 1, 2, 5}, which threatens nobody (agent 2: θ = 5 ≤ 10;
agent 1 holding 6: θ = 6 + 3 = 9 ≤ 10), and its value 11 > 10 means agent 0 no longer needs 6, so agent 1 (frozen on
6, needed by nobody else) is counted: Val = 4 + 1 = 5, def(P′) = −1 (Lemma 11 with κ = 1).

**Frequency** (the T1-stuck state records of the runs of `k4/dl13.md` §1): 1,503, row A2 of
`results/k4_dl13_stuck/candidates_runs.log` (every one with two or more needers of the frozen good; almost all θ-b).

**Reproduce.** `python3 attempts/k4_dl13_attempts.py` (case 2, both implementations).
