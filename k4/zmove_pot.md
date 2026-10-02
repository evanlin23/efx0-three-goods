# Theorem ZMOVE by a potential argument (work in progress)

Workstream `proof/k4-zmove-pot` (draft PR #87). Notation of `k4/c4x.md` §1, `k4/c4min.md` §1, `k4/c4min_reduce.md`
§1–§2, `k4/sx.md` §1–§3 and §6, `k4/dl2.md` §3–§4 and `k4/dl13.md` §2.1. Nothing here changes K4.D or K4.T.

**Target (Theorem ZMOVE).** For every strict profile of every connected k = 4 core with f ≥ 1 and ω ≥ 1, and every key
κ with def*(κ) > 0: at some Z′-maximum Q of κ (a configuration at κ maximizing (r′, Λ′)), some single (T3⁺) move from
P_Q with at most one helper (the helper giving up a good of its base) reaches a state P′ with def(P′) ≤ 0, or κ has a
(T4) edge to a key with smaller def*.

**Status (draft; this file is being written).**
- **The potential (§2, EVIDENCE).** The one-move repair exists at *every* state of the key that maximizes the number
  r′ of robust free agents, with or without Λ′; it fails at states that are only Pareto-maximal or only locally
  optimal for each free agent (core 4515, f = 2), and at arbitrary states (core 4604, f = 1). The two known families
  of states where single-step DL fails (compute/k4-rc, cores 4604 and 4515) are exactly states where a move inside
  the key raises r′. So the potential is r′, and the exchange that a proof must exclude is a move that makes one more
  free agent robust.
- **Proved in writing (§3):** Z′-maximality is a property of the state P_Q, every arrangement of the junk into slots and
  pool gives a Z′-maximum (the "re-choice of Q"), and a robust free agent is never threatened by a bundle that misses
  its base and the needed set.
- **In progress (§4):** ZMOVE at f = 1 at every state whose free agents are all robust and locally optimal, by one
  plain (T3) move.

## 1. Setting

f ≥ 1, ω ≥ 1, κ = (𝒩, φ) a key with frozen set F and def*(κ) > 0. A *state* of κ is a min-frozen P with key κ. For a
free agent y, U_y := R_y ∖ 𝒩. On states:
- y is *robust* at P if v_y(B_y) ≥ v_y(U_y ∖ B_y); r′(P) is the number of robust free agents;
- Λ′(P) := Σ_{y free} ℓ_y(B_y), with ℓ_y(S) = #{T ⊆ R_y : v_y(T) < v_y(S)} (`k4/sx.md` §2).

For a configuration Q at κ these are r′ and Λ′ of `k4/sx.md` §2 evaluated at its state P_Q (Q_y ∩ R_y = H_y since
Q_y ⊆ M ∖ 𝒩), so Q is a Z′-maximum iff P_Q maximizes (r′, Λ′) among the states P_Q of configurations at κ (§3 shows that
this is the maximum over all states).

**ZMOVE at a state.** zm(P) holds if some (T3⁺) move from P with at most one helper (giving up a good of its base)
reaches a min-frozen P′ with def(P′) ≤ 0. ZMOVE asks for zm(P_Q) at some Z′-maximum Q, or a (T4) edge.

## 2. Which potential: the data (EVIDENCE)

For a class 𝒞 of states (defined key by key), the *every-form* "zm(P) for every P ∈ 𝒞 of every key with def* > 0" was
tested; a class that passes is a candidate potential. Classes (all relative to the states of one key):
- ALL: every state; U: every free agent locally optimal (no re-base inside B_y ∪ J raises v_y(B_y)); PARETO: no state
  of the key is at least as good for every free agent and better for one;
- R: r′-maximal; RU: r′-maximal and U; RPARETO: r′-maximal and Pareto among those;
- LAM: Λ′-maximal; RLAM: (r′, Λ′)-maximal (the Z′-maxima).

| input | keys (def* > 0) | ALL | U | PARETO | R | RU | RPARETO | LAM | RLAM |
|---|---|---|---|---|---|---|---|---|---|
| core 4515 of compute/k4-rc (n = 5, m = 12, f = 2), all 1,076 profiles | 2,152 | 4,304 | 42 | 42 | 0 | 0 | 0 | 0 | 0 |
| core 4604 of compute/k4-rc (n = 5, m = 13, f = 1), all 369 profiles, with PR #80's n = 4 hunts (f = 1), f ≥ 2 inputs, T1-stuck keys, compute/k4-cover's two COVER⁺ failures | 2,107 | 369 | 0 | 0 | · | · | 0 | 0 | 0 |

(Entries: states without a one-move repair; "·": class not in that run (R and RU were added later and pass on a
mixed sample of all inputs). Preliminary counts from a scratch evaluator built on compute/k4-cover's libraries; the
committed tool, with a second implementation, and its logs follow in the next commits.) In addition, at every Z′-maximum (every arrangement) of every key with def* > 0 of: PR #80's n = 4 and
n = 5 hunts (f = 1, 2,672 keys), compute/k4-cover's f = 1 hunts (1,807 keys) and f = 2 hunt on the crossed n = 4, m = 10
core (3,871 keys), core 4604 (41 keys) and core 4515 (108 keys), PR #80's f ≥ 2 inputs and T1-stuck keys (1,522 keys):
zm holds. compute/k4-zmove (coordinator, 3091066) and PR #88 (proof/k4-zmove-hall) report the same every-form on
their data, PR #88 also for r′ alone.

**Core 4515: why P_Q avoids the two-helper trap.** In each of the 1,076 profiles the states without a one-move repair
are exactly compute/k4-rc's four stuck states ({4}, {1,8}, {10,11}, B₃, {9}) (B₃ one of {5,6}, {5,7}, {6,7} and a
singleton). At each of them agent 1 is not robust (v₁({1,8}) < v₁({10,11})), agent 2 holds {10,11} and is robust,
and r′ = 2, while the key's states reach r′ = 3. The trade "agent 1 takes {1,10} or {1,11}, agent 2 takes {3},
{3,10} or {3,11}" keeps the key, keeps agent 2 robust and makes agent 1 robust: it raises r′ but lowers agent 2's value,
so the stuck states are Pareto-maximal and locally optimal but not r′-maximal. The two-helper repair of compute/k4-rc
(agent 1 {1,8} → {1,10}, agent 2 {10,11} → {3}, then agent 3 takes 4 and agent 0 takes {0}) is this trade followed by a
plain (T3) swap. Every r′-maximal state has already made the trade, and from there one plain swap suffices (the
coordinator's C′⁺ repair, `k4/f2.md` §7.2 on proof/k4-f2-zmove). At core 4604 (f = 1) the stuck state
({11}, {12}, {3,7}, {4,8}, {5,9}) has agent 1 non-robust on {12} with the junk good 1 available: a (T1) move to {1,12}
raises r′; again the extra helper of the nearest repair is that move.

So a proof by potential has to use exchanges that raise r′ and are not Pareto improvements; Pareto- or
local optimality alone is refuted (`attempts/k4-zmove-pot-pareto.md`, to be committed).

## 3. Re-choice of Q (written proofs)

(Being written.)

## 4. All free agents robust, f = 1 (in progress)

(Being written.)
