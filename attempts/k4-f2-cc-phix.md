# From Theorem Z′'s state at f ≥ 2: "Lemma C⁺, or Lemma C′⁺ paid by φ(x)"

Workstream `proof/k4-f2` (`k4/f2.md` §5, §6). Ledger row K4.F2.X (REFUTED).

**Candidate.** At every maximum Q of (r′, Λ′) at a key κ with def*(κ) > 0 where Lemmas A⁺ and B⁺ of k4/sx.md (PR #80)
fail, Lemma C⁺ of `k4/f2.md` §5 (another free agent owns a full bundle of ω + 2 goods) applies, or Lemma C′⁺ applies
with the paying good q = φ(x), the good that the unfrozen agent x gives up. These are the two f = 1 mechanisms of
k4/sx.md, PR #80 (its Lemmas C and C′, and the ι of `k4/dl13.md` Lemma 9) transcribed to f ≥ 2.

**Smallest failing configuration** (n = 4, m = 10, f = 2, ω = 4; in PR #80's T1-stuck and catalogue inputs):
- sets [[0,2,4,8],[1,3,7,9],[4,5,6,7],[5,6,8,9]], values [[4,2,3,8],[3,4,8,2],[3,2,4,8],[2,3,8,4]];
- key κ: agent 0 frozen on 8, agent 1 on 7; def*(κ) = 1;
- the maximum Q = {2: {4,6}, 3: {5,9}}, L = {0,1,2,3}; P_Q = ({8}, {7}, {4,6}, {5,9}), def(P_Q) = 1;
- the leaves are 2 and 3. X₂ threatens only agent 0, whose good 8 only agent 3 needs; X₃ threatens only agent 1,
  whose good 7 only agent 2 needs. No need chain joins a leaf to the frozen agent it threatens (A⁺ fails), and no
  free agent threatens another, so B⁺ has no threat path.
- `k4/f2_cc.py` finds no instance of C⁺ and none of C′⁺ with q = φ(x) (every move, owner and bundle enumerated).

**The repair** (C′⁺ with q = φ(w) of the other frozen agent, `k4/f2.md` §5): τ = 3 takes 8, x = 0 takes {0}, and the
leaf o = 2 owns Y = {1,3,4,5,6} (ω + 1 goods): good 5 of τ's old base lifts v₂(Y) to 9 > 8 = v₂(7), so agent 2 stops
needing 7, which nobody else needs; it counts, and def(P′) = 0 for P′ = ({0}, {7}, {4,6}, {8}).

**Frequency.** 12 of PR #80's 174 uncovered maxima (`results/k4_f2/cc_*.log`, rows "covered by the family | C+ or
(C′+ with q = phi(x)) | False": 8 catalogue, 4 T1-stuck, 0 n5c); C⁺ and C′⁺ with every kind of q cover all 174.

**Reproduce.** `python3 attempts/k4_f2_attempts.py` (case "crossed maximum"; uses PR #80's `k4/sx_f2.py` and
`k4/sx_keygraph.py`, on main): implementation A is `k4/f2_cc.py` (PR #80's `k4/sx_f2.analyse_key` for A⁺/B⁺, then
every C⁺/C′⁺ instance); implementation B (main's k4/dl134_xcheck.py, its own 𝒫 and deficits and the owner table of the
script) confirms def(P_Q) = 1, def(P′) = 0, the owner 2 with {1,3,4,5,6} at value 6, and that x = 0 needs 8 at P′.
