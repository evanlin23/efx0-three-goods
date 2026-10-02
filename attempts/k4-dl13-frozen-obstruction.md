# DL₁₃ existence: "the obstruction of a T1-stuck state is a frozen agent"

Workstream `proof/k4-dl13` (`k4/dl13.md` §5). Ledger row K4.DL13.X (REFUTED).

**Candidate (three nested forms).** Let P be a T1-stuck state at f ≥ 1 (min-frozen, def(P) > 0, no (T1) move lowers
the deficit; `k4/dl13.md` §1). Then
1. (*S1 shape*) some best owner o needs the good g of a frozen agent x, and for some optimal bundle X of o some junk
   good c ∉ X is blocked by x alone (X ∪ {c} threatens x and no other agent); or at least
2. (*single frozen blocker*) some best owner o, optimal X and c ∈ J ∖ X have X ∪ {c} threatening exactly one agent,
   and it is frozen; or at least
3. (*frozen exposure*) some frozen agent is exposed w.r.t. some free agent o (W_o = B_o ∪ J threatens it).

1 ⟹ 2 ⟹ 3 (X ∪ {c} ⊆ W_o, and threats are monotone). The S1 shape is the hypothesis of the S1 repair (Corollary 9.1),
so form 1 would have reduced the existence step to the θ-dichotomy (Lemma 10). Form 3 fails, hence all three.

**Smallest failing configuration: `dl13-n3m6`** (n = 3, m = 6; #53's n = 3 catalogue, core (m = 6, idx 13) of
`results/k4_certs_3.json.gz`, profile 4,17,236; a connected k = 4 core).
- agent 0: goods 0:1, 2:8, 4:4, 5:6 (not big-top: 8 < 6 + 4);
- agent 1: goods 1:2, 3:4, 4:10, 5:7;
- agent 2: goods 2:8, 3:4, 4:6, 5:3.

P: B₀ = {2}, B₁ = {3, 5}, B₂ = {4}; J = {0, 1}.
- Needs: N₀ = ∅ (2 is agent 0's top), N₁ = ∅ (v₁({3,5}) = 11 > 10), N₂ = {2} (8 > 6). So 𝒩 = {2}, agent 0 is frozen,
  f = 1 (as recorded in the catalogue), σ = 2n − m = 0, ω = 1, S = 1 (agent 2), |J| = 2.
- Owner 1 (W₁ = {0, 1, 3, 5}): {3, 5} is safe (agent 2 values 3:4, 5:3, θ = 4 ≤ 6), but {0, 3, 5} and {1, 3, 5}
  threaten agent 2 (they are not inside R₂, so θ₂ = 4 + 3 = 7 > 6). u = 0 (agent 2 needs 2). Val = 2.
- Owner 2 (W₂ = {0, 1, 4}): {0, 4} and {1, 4} are safe (agent 1: θ₁ = 10 ≤ 11; agent 0: θ₀ ≤ 4 ≤ 8), {0, 1, 4}
  threatens agent 1 (θ₁ = 10 + 2 = 12 > 11). u = 0 (agent 2's needs from {0,4} still contain 2). Val = 2.
- So V = 2 and def(P) = ω + 2 − V = 1 (Lemma H1).
- T1-stuck: agent 1 can re-base only inside {1, 3, 5}, and only to a base worth more than 10 (it may need only good 2,
  which it does not value): {3, 5} itself. Agent 2 can re-base only inside {4}. So there is no (T1) move at all.
- The frozen agent 0 is exposed to nobody: θ₀(W₁) = v₀({0, 5}) = 7 ≤ 8, θ₀(W₂) = v₀({0, 4}) = 5 ≤ 8. Form 3 fails.
  The two free agents block each other: owner 1 is blocked by agent 2 only, owner 2 by agent 1 only (an exposure
  2-cycle among free agents, as in Theorem Z's rotations).

**DL₁₃ still holds there**: six (T3) moves lower the deficit, each a role swap with a helper, e.g. P′ = ({5}, {4}, {2}):
agent 2 takes the frozen good 2, agent 0 takes 5 from agent 1's base (needs only 2: admissible), and agent 1 (the
helper) takes 4, its top, from agent 2's old base. In P′ agent 2 is frozen (agent 0 needs 2), J′ = {0, 1, 3}, ω = 1,
and owner 0 has the safe bundle {0, 1, 5} (agent 1 holding 4: θ = 2 + 7 = 9 ≤ 10; agent 2 holding 2: θ = 3 ≤ 8):
def(P′) = 0. The move is a 3-cycle x → z → h → x of the exchange digraph of `k4/c4min.md` §4 (need edge 0 → 2, then
agent 1 takes from agent 2's old base, agent 0 from agent 1's).

**Frequency** (the 13,971 T1-stuck state records of the runs of `k4/dl13.md` §1, rows A1, A4, A3 of
`results/k4_dl13_stuck/candidates_runs.log`, which reads those runs' dumps only): 2,679 have no S1 shape, 170 have no
single frozen blocker at a best owner, 29 have no exposed frozen agent; DL₁₃ holds at all of them. (The log's
smallest instance for these rows is another profile of the same core, also n = 3, m = 6.)

**After the move to the target R_T4** (`k4/dl13.md` §2.3): every one of these 29 states has f = 1 and a (T2) move
(a rotation of the free agents inside the key) that lowers the deficit, and the weakest form, restricted to states
where no (T1), (T2) or (T4) move lowers the deficit, has no failure in the runs: that restricted form is Conjecture SX
(ledger K4.DL13.SX; the restricted row A3 of `candidates_runs.log` reads 0, and its last line counts the 29 states by
f and by the kind of move that lowers the deficit). The two stronger forms still fail there (rows A1, A4 of
`candidates_runs.log`, restricted lines: 918 and 70 states).

**Reproduce.** `python3 attempts/k4_dl13_attempts.py` (case 1: both implementations, `k4/dl13_lemmas.py` and main's
`k4/c4x_check.py` with separately written tests; the check that the instance is a strict core uses
`k4/suite/model.py`); the frequencies: rows A1, A3, A4 of `results/k4_dl13_stuck/candidates_runs.log`
(`python3 k4/dl13_lemmas.py --candidates results/k4_dl13_stuck/stuck_*.jsonl.gz`). `candidates.log` adds the T1-stuck
states of compute/k4-dl13's failing n = 4 profiles to the input, so its unrestricted row A1 is larger.
