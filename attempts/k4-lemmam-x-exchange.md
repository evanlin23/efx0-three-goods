# Lemma M by exchange between first agents: which partner a′ fails, and why no partner can work

Workstream `proof/k4-lemmam-x` (PR #77, `k4/lemmam_x.md` §2). Ledger rows K4.LMX.X (refuted partners) and K4.RF.M.

**The idea.** Lemma M of `k4/rulef.md` (PR #72): every strict profile of every k = 4 core has a first agent a in
class K0 or K1 of rule RK (Lemma K certifies the run of τ_a = (a, then index order) without rotation, or after one
rotation). Prove it by an exchange: if a is *bad* (in neither class), an agent a′ read off a's run is *good*. Four
partners were proposed (`k4/rulef.md` §6 Step 3): (x1) the exposed frozen 4-good agent, (x2) the leader of r's block,
(x3) the needer at the end of a need chain from an exposed frozen agent, (x4) r itself.

**Where it breaks.**
- *(x1) and (x2) never work on the data.* On every strict profile of every core with n ≤ 3 and n = 4 with at most two
  4-good agents (1.03·10⁹ profiles, `results/k4_lemmam_x/exh_n2_n3_n4_12.log`), 26,248 (profile, bad first agent)
  pairs: the exposed frozen 4-good agent, where it exists (25,448 pairs), is bad on every one; the leader of r's block
  is a itself on every one (every bad run there is a single block). Smallest failure (n = 3, m = 6): agents
  {0, 1, 4, 5}, {2, 3, 4, 5}, {2, 3, 4, 5} with values (1, 4, 6, 8), (2, 3, 4, 8), (2, 7, 8, 4) (the profile of
  `attempts/k4-rulef-least-count.md`). τ₀: 0 takes 5, 2 takes 4, 1 takes 3; agent 2 is the exposed frozen 4-good agent
  (1 needs 4; {2, 3} worth 9 > 8 is junk plus r's pick), r = 1 leads no block, the only block is led by 0. Agents 0 and
  2 are bad, 1 is good (K1: 2 → 0 rotation is a downgrade of 2 to {3}).
- *(x4) works up to n = 4 and on H₃ but fails on H₄ and H₅.* On the data above r is good for every bad a (r is the
  needer at the end there). On the cores H_t of `k4/c4.md` §7: on H₃ (n = 13) the two bad first agents (ℓ = 0 and 9)
  have r good; on H₄ (n = 17, m = 43) six first agents are bad (ℓ and 9, 13–16) and on H₅ (n = 21, m = 53) ten (ℓ and
  9, 13–20), and for each of them r (the y or an x of the last gadget its run reaches) is bad too
  (`results/k4_lemmam_x/H2_H5_classes.log`; R_MODEL_CHECK).
- *(x3) depends on which end, and survives where a good agent exists.* The ends chosen by most chains into them, or of
  least index, or of the exposed frozen agent of least index, are good on all 26,248 pairs above, on the suite and on
  H₃–H₅; the earliest-processed end fails on 2 of H₄'s 6 and 3 of H₅'s 10 bad agents but reaches a good agent when
  iterated.
- *But no partner can work in general: Lemma M is false.* On HH₃ (two copies of H₃ sharing ℓ's good u, n = 26,
  m = 65; `k4/lemmam_bt.md` §3, PR #83, Proposition HH) every first agent is bad, so an exchange has no good agent to
  reach (PR #83's written proof and its runs of `k4/rulef.c` and `k4/lemmam_bt.py`; not recomputed here: with the
  kept-out sets of `k4/rulef.md` §2 Remark 4 the 26 first agents exceed the time allowed per run).

**What survives** (`k4/lemmam_x.md`): the structure of bad runs (Lemmas 1–3: an exposed frozen agent, an exposed 4-good
agent or (G2), a Hall violator among the exposed frozen agents; for (G2), k*'s lower goods are goods of r), the
locality Lemma 4, and the repaired target, adaptive insertion (§7).

**Smallest failing configurations.** (x1), (x2): n = 3, m = 6 above. (x4): H₄, n = 17, m = 43, first agent ℓ = 0,
r = 16 (smallest found; on H₂, H₃ and at n ≤ 4 r is good). Every partner: HH₃, n = 26.

**A caveat on the verdicts "bad".** `k4/lemmam_x.c` inherits from `k4/rulef.c` the convention that an upgraded or
rotated agent has no slot, while LB₄ʳ and Lean's model give a rotated agent with a one-good base one slot; so its
"bad" is an upper bound (on 288 of the 26,248 weighted pairs at n = 4 PR #33's model certifies the agent with one
rotation, `k4/lemmam_x.md` §2). The failures of (x1) and (x2) above hold in the model too (`k4/lemmam_x_check.py`).

Reproduce: `python3 k4/lemmam_x_check.py '[[0,1,4,5],[2,3,4,5],[2,3,4,5]]' '[[1,4,6,8],[2,3,4,8],[2,7,8,4]]'`
(second implementation; the candidates line shows EF4_minidx = 2 bad), `python3 k4/lemmam_x_run.py
--profiles=FILE -A43 -r1 -Y1 -D43` on H₂–H₅ (`python3 k4/lemmam_x_inst.py H2 H3 H4 H5 > FILE`), and
`python3 k4/lemmam_x_check.py --profiles=FILE --agents=0,16` on H₄ (the model's classes of ℓ and r).
