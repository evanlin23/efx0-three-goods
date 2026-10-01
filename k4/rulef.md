# Rule F made explicit: a first-agent rule for LB₄ʳ and the A₄⁺ᴺ counting gap

Workstream `proof/k4-rulef` (ledger rows K4.RF.*, open items 18 and 27; rank 2 of `k4/strategy.md`). Builds on
`k4/adaptive.md` (#44: rule F, Proposition H′, Theorem A₄⁺ᴺ), `k4/c4.md`, `k4/c4one.md`, `k4/lb4.md`, `k4/hall.md`
and `proofs/lb_last_step.md`. Notation as there. Nothing here changes K4.D or K4.T.

Tools: `k4/rulef.c` (`k4/adaptive.c` of #44 plus the modes `-A40`, every first agent with its counts and the explicit
rules, `-A41`, rule RK, and `-A42`, static rules), `k4/rulef_run.py` (driver, one worker, resumable), `k4/rulef_runs.sh`
(every log of this file), `k4/rulef_model.py` and `k4/rulef_check.py` (Lemma K written again from the text on PR #33's
independent model `k4/c4_verify_H/lb4r.py`, with the completion of its proof built and checked against `Output` of
`lean/EFX/LB4R.lean` and the raw EFX₀ definition), `k4/rulef_rot.py` (which rotations repair, Lemma KR),
`k4/rulef_features.py` and `k4/rulef_bigtop.py` (what the working first agent has in common), `k4/rulef_H.py` (H_t),
`k4/rulef_suite.py` (rule RK as predicates of the suite `k4/suite/`).

**Status** (nothing here is PROVED in the ledger's sense: the written proofs are not yet refereed; rows K4.RF.*).
- **Lemma K (§2)**, an owner count for any valid pre-allocation: an owner, a set K of goods it keeps (its needs taken
  from B_o ∪ K, which can unfreeze agents), and every threatened agent served either by a slot good of its own that
  protects it whatever else happens or by a set of goods kept out of the owner's bundle. It contains the counts of
  A₄⁺(o), A₄⁺ᴺ and LB⁺'s hitting set. **Lemma K′** (Remark 5): letting an agent take slot goods and keep goods out at
  once makes the count *exact* (deficit ≤ 0 iff LB₄ʳ's owner test succeeds with that owner), so the counting gap
  closes by construction. Lemma K itself, robust and the form the other lemmas use, leaves no gap at n ≤ 3 and 4, 720 and 35,028
  profiles at n = 4 with one, two, three 4-good agents (§5.1); the 4 and the 720 are runs that succeed only
  without upgrades, which Lemma K certifies under that policy (n = 4 with three: RK₃ is being run, see §5.1). Written proofs; a
  second implementation builds the completions and checks them against Lean's `Output` and the raw definition.
- **Lemma KR (§3)**, LB⁺'s Theorem B in Lemma K's count: rotating a frozen agent along a need chain to the owner
  lowers the deficit by one under two explicit conditions. **Lemma S (§6)**: free exposed agents never raise the
  deficit. **Proposition H″ (§4.1)**: on every relabeling of H_t a gadget-1 first agent is certified without rotation.
- **Rule RK (§4)**, an explicit first-agent rule whose every test is a certificate: the first agent whose run Lemma K
  certifies (class K0), else whose run Lemma K certifies after one rotation (K1), else whose run satisfies Corollary
  C₄⁰ (C40). It never runs LB₄ʳ's owner search. **It is correct exactly when Lemma M holds** (some first agent is in
  K0, K1 or C40), the one statement left open (§6 says which cases a proof attempt closes and which it does not).
- **Data (§5)**: Lemma M holds, with K0 and K1 alone, on every strict profile of every certified core with n ≤ 4 and at
  most three 4-good agents (3.6·10¹⁰ profiles, exhaustive), on random samples of n = 4 with four 4-good agents
  (4.4·10⁶ profiles) and of n = 5 (6.3·10⁶), on H_t and on all 150 cores of the suite. **What the working first agent has in
  common** (§5.2): it is the agent that needs its top most. If exactly one agent is *big-top* (four goods, top worth
  more than the next two together), that agent is in K0 or K1 on all these classes; with several big-top agents the
  first one can fail (n = 4, m = 8), and without one, index order fails (9,632 n = 3 profiles); there, of two agents
  sharing a top, the one with a private fallback fails. Every static or one-step rule tried fails somewhere (the best
  at n = 4, m = 7), and on H_t the agent must be found in gadget 1. Rule RK finds it by its certificate.
- **Lean (§7)**: `lean/EFX/RuleF.lean` states rule F's target (`TheoremRuleF`, `RuleFConn`, `RuleFOne`: some first agent
  a with LB₄ʳ([a]) succeeding with at most one rotation) and proves it gives C₄∃ and TARGET₄ (`lean/check.sh` passes);
  Lemma M with Lemma K would discharge `RuleFConn`.
- **Failed** (`attempts/k4-rulef-*.md`, §5.3): the least-deficit rules (every count, n = 3, m = 6), "no frozen agent ⟹ a
  valid owner" (n = 2, m = 5), static rules built on big-top agents ("the first big-top agent, else index order":
  n = 3, m = 6; "the first big-top agent" with two or more: n = 4, m = 8; with a shared-top fallback: n = 4, m = 7),
  and Lemma K with kept-out sets restricted to goods the agent values (n = 4, m = 8, a suite core).

## 1. Setting

A k = 4 core, a strict profile, LB₄ʳ (`k4/lb4.md` §5; in Lean `EFX.LB4R.Succeeds`). For an agent a, τ_a is the
insertion sequence "a first, then index order" (in Lean the list `[a]`, `lean/EFX/LB4R.lean` choice 2). Rule F
(`k4/adaptive.md` §1) runs LB₄ʳ(τ_a) for a = 0, 1, … and keeps the first that succeeds with the fewest rotations.
Its success with at most one rotation on every profile tested is K4.AD.F/K4.AD.E. A proof needs (strategy §3, rank 2):
1. a first-agent rule that can be stated without running LB₄ʳ;
2. the counting theorem that closes the gap A₄⁺ᴺ leaves (K4.AD.AN, K4.C4.GAP);
3. a rotation statement for what remains.

A state P is a valid pre-allocation in the sense of `k4/lb4.md` §1 (bases B_i, needs N_i containing every good of
R_i ∖ B_i worth more than B_i, (V1), (V2)); J is its junk, F its frozen agents (a one-good base in NA), and a free
agent x has cap(x) = 2 − |B_x| slot places. Every state LB₄ʳ reaches is one (`EFX.LB4R.Inv`, K4.C4.FRAME). For an
agent x, a bundle L and a holding H, *threatened(x, L, H)* means max_{h ∈ L} v_x(L ∖ h) > v_x(H); it is monotone
(`k4/c4.md` §1): it stays true when L grows or v_x(H) drops.

## 2. Lemma K: an owner count with kept goods and served agents

**Lemma K.** Let P be a valid pre-allocation and o an agent that is not frozen, such that every base other than B_o
has at most two goods. Put W_o := B_o ∪ J. Fix a set K ⊆ J of goods that will stay in the owner's bundle, and let
- N_o^K := {g ∈ N_o : v_o(g) > v_o(B_o ∪ K)}, NA^K := N_o^K ∪ ⋃_{i ≠ o} N_i;
- F^K := the agents other than o whose base is one good of NA^K (so F^K ⊆ F ∖ {o}), and
  κ^K := Σ_{x ≠ o, x ∉ F^K} (2 − |B_x|), the slot places of the agents other than o once o's needs are N_o^K;
- E := {x ≠ o : threatened(x, W_o, B_x)}, the agents some bundle of the owner could threaten.

A *K-service* chooses for every x ∈ E either
- (s) a *slot good* g_x ∈ J ∖ K, where x ∉ F^K, |B_x| ≤ 1 and not threatened(x, W_o ∖ {g_x}, B_x ∪ {g_x}); or
- (r) a *kept-out set* D_x ⊆ J ∖ K with not threatened(x, W_o ∖ D_x, B_x),

with the slot goods pairwise distinct. Its size is |G ∪ H|, G the slot goods, H the union of the kept-out sets. The
*deficit* of (o, K) is the least size of a K-service minus κ^K (+∞ if E has an agent with no option).

If some K-service has size at most κ^K, then P has a completion X with owner o, the owner's needs taken from its
bundle, that satisfies (OC₄), in which frozen agents hold exactly their bases and only X_o may have more than two
goods. So X is EFX₀ (Theorem 1′₄, K4.LB4.S), and if P is a state of LB₄ʳ(τ) with ω ≥ 1, X is an `Output` and
LB₄ʳ(τ) succeeds.

*Proof.* Let C := G ∪ H, so |C| ≤ κ^K and C ∩ K = ∅.
- *Placing C.* Put each slot good g_x into the slot of x (x ∉ F^K, |B_x| ≤ 1, so x has a place). The agents other
  than o outside F^K have κ^K places, |G| of them used, and |H ∖ G| ≤ κ^K − |G|; put the goods of H ∖ G into
  unused places, one each. Let X_o := B_o ∪ (J ∖ C), and X_x := B_x plus its placed goods for x ≠ o.
- *The owner's needs shrink to N_o^K or less.* X_o ⊇ B_o ∪ K, since K ∩ C = ∅. Let N_o^X := {g ∈ R_o ∖ X_o : v_o(g) >
  v_o(X_o)}. A good of N_o^X lies outside B_o and is worth more than v_o(X_o) ≥ v_o(B_o), so it is in N_o (the
  Definition), and it is worth more than v_o(B_o ∪ K), so it is in N_o^K. Hence NA^X := N_o^X ∪ ⋃_{i ≠ o} N_i ⊆ NA^K
  ⊆ NA, the agents frozen with these needs are among F^K, and (V1), (V2) still hold.
- *X is a completion.* Every good is in one bundle; bases are kept; an agent that received a good is outside F^K,
  hence free under NA^X, with at most 2 − |B_x| goods added; frozen agents (under NA^X) are in F^K and hold exactly
  their base; only X_o may exceed two goods (bases other than B_o have at most two). The owner is not frozen under
  NA^X: it was not frozen, and NA^X ⊆ NA.
- *(OC₄).* Let x ≠ o. If x ∉ E: X_o ⊆ W_o and v_x(X_x) ≥ v_x(B_x), so x is not threatened by X_o (monotonicity).
  If x is served by (s): X_x = B_x ∪ {g_x} and X_o ⊆ W_o ∖ {g_x}. If x is served by (r): X_o ⊆ W_o ∖ D_x and
  X_x ⊇ B_x. Either way monotonicity gives the claim.

Theorem 1′₄ (K4.LB4.S, machine-checked: `EFX.LB4.Valid.sound`, with the owner's needs from its bundle) makes X
EFX₀. For a state of LB₄ʳ with ω ≥ 1, `Output` asks exactly for such a completion with an owner (`EFX.LB4R.Output`:
`Completion` with `ownerNeeds`, `OC`, and an owner when ω ≥ 1). ∎

**Remarks.**
1. *What it contains.* With K = ∅ and every agent of E served by (r) with a set D_x of size ρ_o(x), and the agents
   with dem(x) = 1 served by (s), it is the count of Theorems A₄⁺(o) (K4.C4.AO) and A₄⁺ᴺ (K4.AD.AN), except that
   Lemma 2₄'s sequential choice "the ≻-best junk good not yet placed" is replaced by the *robust* condition (s); the
   (r) sets may overlap (one kept-out good serves several agents, as in LB⁺'s hitting set, `proofs/lb_last_step.md`
   Lemma 1); and the kept set K takes the owner's needs from its bundle into account (the unfreezing clause of
   Lemma H1, `k4/hall.md` §1, there for removal-only completions). On every leaf of the n = 2 classes the A₄⁺ᴺ,
   A₄⁺(o) and intermediate counts being ≤ 0 imply Lemma K's deficit ≤ 0 (334,752 checks, 0 exceptions).
2. *Not exact.* Lemma K is a sufficient condition. LB₄ʳ's owner test is exact for a given C (`k4/lb4.md` Lemma 3₄);
   it allows a slot good that protects x only together with other goods kept out (and, rarely, two slot goods for an
   agent with an empty base). Remark 5 adds exactly that and gets an exact count.
3. *Where it is used.* Any valid pre-allocation: the state after Phase 1 and upgrades of either policy, and the state
   after rotations (a `RotStep` result passes (V1), (V2) and has at most one base of three or more goods, which must
   then be the owner's).
4. *Kept-out sets may hold goods x does not value.* threatened(x, L, H) discounts the least good of L only when
   L ⊆ R_x: if L has a good outside R_x, dropping that good is the best removal and costs x nothing. So a kept-out set
   may have to contain every good of W_o ∖ R_x, to make W_o ∖ D_x ⊆ R_x; Lemma K allows it (D_x ⊆ J ∖ K is arbitrary,
   and the proof places the goods of H in slot places without looking at who values them). `k4/rulef.c` restricts
   kept-out sets to goods of R_x unless `-Y1` is given (then it also tries each subset of J ∩ R_x together with all
   goods of J ∖ K outside R_x, the only extension that can matter). The restricted deficit is at least the full one, so
   every certificate of the restricted search is one of Lemma K, and the logs of §5.1 (made restricted) stand. The
   difference shows on the suite instance `lb4-owner-needs-from-base-n4m8` (n = 4, m = 8, four big-top agents with
   values (2, 3, 8, 4)): no first agent is certified by the restricted search, every one with `-Y1` (owner 0 or 1), and
   `k4/rulef_model.py` with `XKEEP = True` builds that completion and checks it against `Output` and the raw
   definition. Rerun with `-Y1` on every exhaustive class of §5.1 (`results/k4_rulef/rk_*_y1.log`) and on a pure n = 4
   sample (`results/k4_rulef/rk_pure4_y1_sample.log`), Lemma K certifies 1,152 more n = 3 profiles without rotation
   (all of rule F's, §5.1) and 1,160 more at n = 4 with three 4-good agents; no violations.
5. *Lemma K′: the exact count.* Let a *K′-service* choose for every x ∈ E a kept-out set D_x ⊆ J ∖ K and, if x ∉ F^K
   and |B_x| ≤ 1, a set G_x ⊆ J ∖ (K ∪ D_x) of at most 2 − |B_x| slot goods (possibly empty), such that
   not threatened(x, W_o ∖ (D_x ∪ G_x), B_x ∪ G_x), the sets G_x pairwise disjoint; its size is |⋃ G_x ∪ ⋃ D_x|.
   ((s) is |G_x| = 1, D_x = ∅; (r) is G_x = ∅.) **Lemma K′.** P has a completion X with owner o and the owner's needs
   from its bundle (OC₄, frozen agents holding their bases, only X_o above two goods; for a state of LB₄ʳ with ω ≥ 1:
   an `Output` with owner o) **if and only if** some K ⊆ J and some K′-service have size at most κ^K.
   *Proof.* "If": the proof of Lemma K, word for word (put G_x into x's slot places; X_x ⊇ B_x ∪ G_x and X_o ⊆ W_o ∖
   (D_x ∪ G_x), then monotonicity). "Only if": let C := J ∖ X_o, K := J ∩ X_o, G_x := X_x ∖ B_x and D_x := C ∖ G_x.
   Then B_o ∪ K = X_o, and N_o^K equals the owner's needs from X_o: a good of N_o^K is worth more than v_o(X_o), so it
   is not in X_o; the converse is the second step of Lemma K's proof. So F^K is the set of agents frozen in X, every
   good of C fills a slot place of an agent outside F^K ∪ {o} (|C| ≤ κ^K), the G_x are disjoint, an agent of F^K holds
   B_x (G_x = ∅), and W_o ∖ (D_x ∪ G_x) = W_o ∖ C = X_o: (OC₄) is the service condition. ∎
   So Lemma K's deficit misses LB₄ʳ's owner test only through its separated options, and the class K0 of rule RK with
   Lemma K′ (K0′) holds exactly the runs that LB₄ʳ solves without rotation under those policies. Checked on the gap
   profiles of §5.1 (`k4/rulef_gap.py`, every first agent and all three policies, on PR #33's model): Lemma K′ and
   LB₄ʳ's exact owner test agree on every state, and every Lemma K′ completion passes `output_check` and the raw
   definition (`results/k4_rulef/gap_check_n4_n4_1.log`, `gap_check_n4_n4_2.log`: 2 and 100 gap leaves, 0
   disagreements, 0 failing completions).

*Second implementation.* `k4/rulef_model.py` computes the same deficit (without `k4/rulef.c`'s restriction of slot
goods outside R_x to one representative) on PR #33's model, builds the completion of the proof and checks it with
`lb4r.output_check` (the literal `Output` of `lean/EFX/LB4R.lean`) and the raw EFX₀ definition. On every leaf
representative of the n = 2 classes (27,896 profiles, both policies, every first agent): 108,056 completions built,
0 failures; the two implementations agree on the sign of the deficit everywhere (`k4/rulef_check.py`). On every 200th
n = 3 leaf where index order is not in K0 (9,012 profiles, 54,072 pairs of first agent and policy): 33,388 completions
built, 0 failures, no sign difference (`results/k4_rulef/check_lemmaK_n3.log`).

## 3. Lemma KR: one rotation, in count form

LB⁺'s Theorem B (`proofs/lb_last_step.md` §5) and its k = 4 forms (B₄, B₄ʷ of `k4/c4.md`, BT1 of `k4/hall_bt.md`)
rotate a frozen agent k along a need chain to the owner and make k the owner. In the language of Lemma K the gain is
explicit: k leaves the set of agents to serve, and the old owner becomes an ordinary agent with a slot.

**Lemma KR.** Let P be a valid pre-allocation whose bases have at most two goods, o an agent that is not frozen with
|B_o| ≤ 1, W := B_o ∪ J, E the agents other than o threatened by W with their base, and σ a ∅-service of E (Lemma K
with K = ∅) of size κ + δ, where κ is the number of slot places of the agents other than o. Let k be a frozen agent,
k = x₀, x₁, …, x_t = o a need chain (distinct agents, t ≥ 1, x₀, …, x_{t−1} frozen, Y_{x_i} ∈ N_{x_{i+1}}), and
O ⊆ R_k ∩ W with v_k(O) > v_k(Y_k). Let P′ be the rotation (`k4/lb4.md` §5; `EFX.LB4R.RotStep`): x_i takes
Y_{x_{i−1}} (1 ≤ i ≤ t), B_o returns to the junk, and k takes the base O (marked, value-based needs). Suppose
- (i) no good of O is used by σ for an agent other than k;
- (ii) o is not frozen in P′ (no agent other than o needs Y_{x_{t−1}} in P′).

Let c_k be the number of goods σ uses for k and for no other agent (c_k = 0 if k ∉ E), and ε := 1 if o is threatened by
W holding Y_{x_{t−1}} and has a slot good g_o ∈ J′ ∖ G that serves it ((s) of Lemma K; G the slot goods of σ), ε := 0
if o is not threatened, and ε := ∞ otherwise. Then P′ is a valid pre-allocation, the rotation is a `RotStep`, and
(P′, owner k, K = ∅) has deficit at most δ − 1 − c_k + ε. In particular, if δ ≤ 1 and either o is not threatened in
P′ or c_k ≥ 1 and ε = 1, LB₄ʳ succeeds after this one rotation, with owner k.

*Proof.* *Validity* (the proof of Lemma R(b) of `k4/c4.md` §4a, which uses nothing about the upgrade policy).
W ∩ NA = ∅: J by (V1), B_o since o is not frozen. Each x_i (i ≥ 1) now holds a pick it ranked above its old one, so
its needs (the goods ranked above its pick) shrink. k's new needs N′_k = {g ∈ R_k ∖ O : v_k(g) > v_k(O)} are worth
more than v_k(O) > v_k(Y_k), so they lie in N_k. Nobody else changes, so NA′ ⊆ NA. Then J′ = W ∖ O ⊆ W misses NA′
((V1)); O ⊆ W misses NA′ ((V2) for k, which `RotChecks` asks of every marked agent); the other two-good bases are
unchanged and miss NA ⊇ NA′. Only O may have three or more goods. The chain is a need chain of P whose last agent o is
not frozen, and O ⊆ R_k ∩ (J ∪ B_o): this is a `RotStep`.

*W does not change.* W′ := O ∪ J′ = O ∪ (W ∖ O) = W (Lemma R(a)).

*Who is threatened* (Lemma R(c)). Let x ≠ k be threatened by W with its base B′_x in P′. If x is not on the chain,
B′_x = B_x, so x ∈ E. If x = x_i with 1 ≤ i < t, v_x(B′_x) > v_x(B_x), so by monotonicity x was threatened by W
with B_x: x ∈ E. So E′ ⊆ (E ∖ {k}) ∪ {o}.

*Capacity.* An agent off the chain that is not frozen in P is not frozen in P′ (same base, NA′ ⊆ NA). In P, k and the
x_i with i < t are frozen (no slot) and o is excluded from κ; in P′, k is excluded and o holds one good and, by (ii),
is not frozen. So κ′ ≥ κ + 1.

*A service of E′.* For x ∈ E′ ∖ {o} ⊆ E ∖ {k} keep σ's choice. It is admissible in P′: by (i) its goods lie in
J ∖ O ⊆ J′; a kept-out set D_x keeps x safe since W is the same and x's base is worth at least as much (monotonicity);
a slot good g_x was chosen for an agent with a slot that is off the chain (chain agents other than o are frozen in P),
whose base and W are unchanged and which is still not frozen. Slot goods stay distinct. If o ∈ E′, add (s) with g_o.
The size is at most |σ| − c_k + ε. So the deficit of (P′, k, ∅) is at most (κ + δ − c_k + ε) − (κ + 1). ∎

At k = 3 in LB⁺'s bad case: o = r, k = k*, O = {b_k*, c_k*}; (i) is the disjointness of the sets π_x; (ii) and "r not
threatened" are Theorem B(e); δ = 1 is "one terminal short". Lemma KR is that argument with any frozen k, any O and the
counting of Lemma K.

## 4. Rule RK: a first-agent rule whose every test is a certificate

For an agent a and a policy pol (need-shrinking or envy-free upgrades), let P_a^pol be the state after Phase 1(τ_a)
and upgrades of pol to their fixpoint (LB₄ʳ's order: smallest-index eligible agent, best eligible good).

**Rule RK.** Scan a = 0, 1, …, n − 1 (index order) three times and take the first a found:
1. (K0) some pol and some owner o, kept set K have Lemma K deficit ≤ 0 at P_a^pol, or ω(P_a^pol) ≤ 0;
2. (K1) some pol and some single rotation of P_a^pol (any frozen k, need chain and base O, as LB₄ʳ's R(1)) reach a
   state with Lemma K deficit ≤ 0 for some owner (or ω ≤ 0 and no base of three goods);
3. (C40) the envy-free run of τ_a satisfies the hypothesis of Corollary C₄⁰ (no 4-good agent exposed w.r.t. r, and in
   LB⁺'s bad case r is not a 4-good agent exposed after LB⁺'s rotation);

and a = 0 if none applies (the *open* class). Run LB₄ʳ(τ_a).

*Variant RK₃* (`k4/rulef.c -N1`): pol also ranges over LB₄ʳ's third policy, no upgrades (P_a^none is the Phase 1
state; Lean's `Policy.none`). Every class keeps its proof (Lemma K applies to any valid pre-allocation), and RK₃'s K0 and
K1 contain RK's. The data of §5.1 are for RK unless they say RK₃.

RK never runs LB₄ʳ's owner search: it runs Phase 1, the two upgrade fixpoints, the rotations of R(1), and evaluates
Lemma K's count. Each class carries its own proof that LB₄ʳ(τ_a) succeeds: K0 with no rotation (Lemma K), K1 with at
most one (Lemma K at the rotated state, which is a valid pre-allocation reached by a `RotStep`), C40 with at most one
(Corollary C₄⁰, K4.C4.AB.L, machine-checked). So **rule RK is correct exactly when the open class is empty**, which is
the existence statement

**Lemma M (missing).** For every strict profile of every k = 4 core some first agent a is in class K0, K1 or C40.

What a proof of rule F still needs is Lemma M; §5 gives the data, §6 what is known about a proof.

*How strong Lemma M is.* Read with Lemma K′ (Remark 5 of §2, exact) in place of Lemma K and with all three policies
of LB₄ʳ (need-shrinking, envy-free, no upgrades: Lean's `Policy`), K0 is exactly "LB₄ʳ(τ_a) succeeds without
rotation" and K1 exactly "with one `RotStep`", so Lemma M is then *equivalent* to rule F with at most one rotation
(`EFX.LB4R.TheoremRuleF`, K4.AD.F): nothing is lost, and the open statement is put in counting form. With Lemma K's
robust options (and two policies) it is a stronger statement, which the data of §5 still support; that strength is
what makes it usable, since Lemmas S, KR and Proposition H″ are statements about Lemma K's count.

### 4.1 Rule RK on the cores H_t needs no rotation

**Proposition H″.** On every relabeling of the cores H_t of `k4/c4.md` §7, every agent a of gadget 1 is in class K0
(need-shrinking upgrades). Hence rule RK takes an agent of class K0 (the first in index order; it need not be in gadget
1) and LB₄ʳ(τ_a) succeeds without rotation.

*Proof.* Proposition H′ (`k4/adaptive.md` §3, K4.AD.H, PROVED), Steps 1–3, applies to the run of τ_a, since a, an
agent of gadget 1, is processed before ℓ: after need-shrinking upgrades no agent is frozen, every free x_{j,i} holds
a_{j,i}, every free y_j holds a_{j,1}, ℓ holds g_1, and the upgraded agents hold {b_{j,i}, c_{j,i}} (x) or
{a_{j,2}, e_j} (y). Let r be the last-processed agent that is not upgraded, W = B_r ∪ J. Serve E (Lemma K, K = ∅):
- a free x_{j,i} ≠ r by the slot good b_{j,i}: W ∖ {b} meets R_x in at most {c_{j,i}, g_j}, worth 4 + 3 < 8 + 6;
- ℓ ≠ r by u: W ∖ {u} meets R_ℓ in at most {z, u′}, worth 6 + 4 < 8 + 5;
- a free y_j ≠ r by e_j: its goods a_{j,2}, a_{j,3} are picks of other agents, at most one of them (r's) in W, so
  W ∖ {e_j} meets R_y in at most one good, worth less than a_{j,1};
- an upgraded x_{j,i} ({b, c}, worth 10): W meets R_x in at most {a_{j,i}, g_j}, and in a_{j,i} only if r holds it.
  It is threatened only if both are in W (8 + 3 > 10); then g_j is junk, so j ≥ 2 (g_1 is ℓ's pick) and y_{j−1} is
  free (an upgraded y_{j−1} holds e_{j−1} = g_j) and not r (r = y_j holds a_{j,1}); serve x by the kept-out set {g_j}.
  If y_{j−1} is served, g_j is its slot good e_{j−1} and costs nothing more; otherwise y_{j−1}'s slot place is unused
  and takes g_j. Only x_{j,1} can be in this case (a_{j,i} ∈ W needs r = y_j holding a_{j,i}, so i = 1), so distinct
  such agents use distinct places;
- an upgraded y_j ({a_{j,2}, e_j}, worth 9): its other goods a_{j,1}, a_{j,3} are picks, at most one in W: not
  threatened.

The slot goods b_{j,i}, u, e_j are distinct junk goods (b, u private; e_j is junk since y_j is free and nobody else
takes it, Step 3 of H′). Every good of the service is charged to a distinct slot place of a free agent other than r
(its own, or y_{j−1}'s), and free agents hold one good, so the service has size at most κ: the deficit of (r, ∅) is
≤ 0. ∎

So on H_t (where index order needs ⌈2t/3⌉ rotations, Proposition H) RK is certified without rotation, by a proof
that does not run LB₄ʳ.

## 5. Data

### 5.1 Rule RK, exhaustive (`k4/rulef.c -A41 -r1`, `results/k4_rulef/rk_*.log`)

Every strict profile of every certified core with n ≤ 4 and at most three 4-good agents (#44's exhaustive classes,
K4.AD.E; lazy type splitting as in `k4/lb4.c`, leaf weights adding up to every profile). For each profile RK's class,
then LB₄ʳ (all three policies, at most one rotation) on RK's sequence, its output checked against the raw EFX₀
definition; a *violation* is a class whose promise LB₄ʳ does not meet (K0 but a rotation needed, K1 or C40 but more
than one).

| class | profiles | K0 | K1: LB₄ʳ needs 0 / 1 rotation | C40 | open | violations | rule F (#44): 0 / 1 rotation |
|---|---|---|---|---|---|---|---|
| n = 2 | 189,216 | 189,216 | 0 / 0 | 0 | 0 | 0 | 189,216 / 0 |
| n = 3 | 299,837,376 | 299,572,888 | 1,152 / 263,336 | 0 | 0 | 0 | 299,574,040 / 263,336 |
| n = 4, one 4-good agent | 7,247,232 | 7,246,412 | 0 / 820 | 0 | 0 | 0 | 7,246,416 / 816 |
| n = 4, two | 724,847,616 | 724,640,016 | 32 / 207,568 | 0 | 0 | 0 | 724,640,736 / 206,880 |
| n = 4, three | 34,971,844,608 | 34,961,456,592 | 14,732 / 10,373,284 | 0 | 0 | 0 | 34,961,492,780 / 10,351,828 |

Findings (EVIDENCE: one implementation of the classes, `k4/rulef.c`; the outputs are checked by the raw definition,
and LB₄ʳ's exact owner search confirms every class on every profile):
- **Lemma M holds on all 3.6·10¹⁰ profiles, with K0 and K1 alone**: the class C40 is never reached, so Corollary C₄⁰
  is not needed by the data, and every profile is certified by Lemma K, before or after one rotation.
- **Lemma K closes almost all of the counting gap.** A profile is in the gap when some first agent needs no rotation
  (rule F) but no first agent is in K0: 0 (n = 2), 1,152 (n = 3), 4, 720 and 36,188 (n = 4 with one, two, three
  4-good agents) in the table, whose kept-out sets hold only goods the agent values. With the kept-out sets of
  Remark 4 (`-Y1`, `results/k4_rulef/rk_*_y1.log`: K0 grows to 299,574,040 at n = 3 and to 34,961,457,752 at n = 4
  with three 4-good agents, K1 shrinks accordingly, the other rows are unchanged, no violation) the gap is 0, 0, 4,
  720 and 35,028. **With RK₃ the gap vanishes** where it has been run (`-Y1 -N1`, `results/k4_rulef/rk_*_n1.log`):
  on n = 2, n = 3 and n = 4 with one and two 4-good agents RK₃'s K0 and K1 are exactly rule F's no-rotation and
  one-rotation profiles (189,216; 299,574,040 / 263,336; 7,246,416 / 816; 724,640,736 / 206,880), so RK₃ is as good
  as rule F there, without running LB₄ʳ's owner search (n = 4 with three 4-good agents: being run on a separate machine).
  #44's gap for A₄⁺ᴺ, over *every* insertion sequence (K4.AD.AN), was 1,020 (n = 2), 119,616 (n = 3)
  and 31,224 (n = 4, two 4-good agents) profiles that LB₄ʳ solves without rotation under some owner-needs convention.
  K1 covers the gap anyway: with one rotation and Lemma K every profile is certified. Lemma K′ (Remark 5 of §2) is
  exact, so it leaves no gap by construction. And Lemma K's own gap is a matter of policy, not of counting: at n = 4
  with one and two 4-good agents every gap profile (4 and 720) is a run that LB₄ʳ solves without rotation only
  without upgrades, and Lemma K certifies it under that policy (`k4/rulef_gap.py`,
  `results/k4_rulef/gap_check_n4_n4_1.log`, `gap_check_n4_n4_2.log`).
- **RK is not optimal, but never needs two rotations.** It uses a rotation where some first agent needs none on 0
  (n ≤ 3), 4, 688 and 21,456 profiles (n = 4 with one, two, three 4-good agents; 21,408 with `-Y1`): these are the
  profiles of the counting gap on which the first K1 agent in index order is not one of those that need no rotation.

**Beyond the exhaustive classes** (random strict profiles of every certified core, `-SN`: N per core; EVIDENCE only,
PROMPT.md §5 rule 3; `results/k4_rulef/rk_pure4_sample.log`, `rk_n5_*_sample.log`):

| class | profiles | K0 | K1: LB₄ʳ needs 0 / 1 rotation | C40 | open | violations |
|---|---|---|---|---|---|---|
| n = 4, four 4-good agents (219 cores × 20,000) | 4,380,000 | 4,378,166 | 9 / 1,825 | 0 | 0 | 0 |
| n = 5, one 4-good agent (1,735 × 200) | 347,000 | 346,997 | 0 / 3 | 0 | 0 | 0 |
| n = 5, two (5,468 × 200) | 1,093,600 | 1,093,583 | 0 / 17 | 0 | 0 | 0 |
| n = 5, three (9,861 × 200) | 1,972,200 | 1,972,140 | 0 / 60 | 0 | 0 | 0 |
| n = 5, four (9,846 × 200) | 1,969,200 | 1,969,042 | 2 / 156 | 0 | 0 | 0 |
| n = 5, five (4,674 × 200) | 934,800 | 934,634 | 0 / 166 | 0 | 0 | 0 |

On the cores H_t of `k4/c4.md` §7 (t = 1, …, 5, each with three random relabelings, `k4/rulef_H.py`,
`results/k4_rulef/rk_H.log`) rule RK's agent is in K0 every time and LB₄ʳ needs no rotation (Proposition H″). On the
counterexample suite (`k4/suite/`, 151 instances, 150 of them k = 4 cores; `k4/rulef_suite.py`,
`results/k4_rulef/suite_rk.log`) rule RK succeeds with at most one rotation on all 150: 143 in K0, 7 in K1. One of
them, `lb4-owner-needs-from-base-n4m8`, needs Remark 4 of §2 (kept-out sets holding goods outside R_x): without it no
first agent is certified (`attempts/k4-rulef-keptout-in-R.md`).

### 5.2 What the first agents of classes K0 and K1 have in common

`k4/rulef.c -A41 -E1 -D5` lists, for every n = 3 profile on which index order (agent 0 first) is not in class K0, the
classes of every first agent (1,802,206 leaves, `results/k4_rulef/rk_idx_n3.log`). `k4/rulef_features.py` tests on
every 20th of them (90,111 leaves, 507,228 profiles) rules that choose the first agent without computing Lemma K for
other agents (`results/k4_rulef/features_n3.log`; a rule *covers* a profile when its agent is in K0 or K1):

| rule | profiles not covered (of 507,228) |
|---|---|
| **the first big-top agent** (four goods, a > b + c), else agent 0 | **0** |
| index order, else the end of a need chain from agent 0 in the index run | 15 |
| the end of a need chain from the frozen agent processed last (index run) | 41 |
| the end of a need chain from a frozen 4-good agent (index run) | 354 |
| the last agent r of the index run; least contested top; top shared by most tops | 720 each |
| 3-good first; most private goods; 4-good first; top is the least good of fewest; index order | 730–735 |
| most contested top; top shared by fewest tops | 785 each |
| the successor or the end of a need chain from agent 0 | 19,952 |

(The static rules are those of #44 at the first insertion step, `attempts/k4-adaptive-local-features.md`, plus new
ones; the one-step rules read an agent off the index run, in the spirit of #37's Lemma X′. A sample: it happens to
contain none of the 9,632 profiles on which the first rule fails, found exhaustively below.)

**Big-top agents.** Exhaustively (`k4/rulef.c -A42`, `results/k4_rulef/btrk_*.log`, `bt*_n*.log`):
- *one big-top agent: it works*. "The first big-top agent if there is one, else rule RK" (`-Q2`) leaves no profile
  open on n ≤ 3 and on n = 4 with one or two 4-good agents. With three 4-good agents it leaves 1,096 profiles
  uncertified (on 480 of them LB₄ʳ needs two rotations on that sequence), and every one of them has two or three
  big-top agents. So on all the data: **if exactly one agent is big-top, that agent is in class K0 or K1**.
- *several big-top agents: not the first one*. On the smallest failure (n = 4, m = 8, three big-top agents) agents 0
  and 1 are big-top with the same top; agent 0, which has two private goods, fails, and agent 1, which has none, is in
  K0 (`attempts/k4-rulef-bigtop-first.md`).
- *no big-top agent: index order does not work*. "The first big-top agent, else agent 0" (`-Q0`) fails with one
  rotation on 9,632 profiles at n = 3, every one without a big-top agent. There the working first agent's top is also
  another agent's top, and of two agents sharing a top the one with two private goods fails (table:
  `results/k4_rulef/bigtop_fallback_n3.log`). The static rules built on that (`-Q3`: the first big-top agent, else a
  shared-top agent with the fewest private goods; `-Q4`: the big-top agent with the fewest private goods, else the
  same) survive n = 3 and n = 4 with one 4-good agent, and fail on 4 profiles with two (n = 4, m = 7: the rule picks a
  3-good agent without private goods whose top is also a 4-good agent's top; that 4-good agent is in K0;
  `results/k4_rulef/bt4_n34.log`).

So the working first agent is "the agent that needs its top most" — a big-top agent, and among agents sharing a top,
one without a private fallback — but no static rule tried captures it on all the data; rule RK does, by certificate.

Why a big-top agent. *Remark (a two-line proof).* In every state after Phase 1 and upgrades of either policy, a
big-top agent q that does not hold its top a_q still needs it, and the agent holding a_q is frozen. Indeed q's base is
then one good below a_q (or empty) or an upgraded pair {Y, g} with Y, g ∈ R_q ∖ {a_q}, worth at most b + c < a; so
a_q ∈ N_q. The holder of a_q holds it as a pick (an upgraded base avoids NA by (V2)), hence is frozen. So with q not
first, Phase 1 can leave a frozen agent that no upgrade removes and that only a rotation, or q's own large bundle as
owner, releases; inserted first, q holds its top and needs nothing. This explains why big-top agents matter; it is not
a proof that the first big-top agent is in K0 or K1. On the cores H_t (no big-top agent) the first agent must lie in gadget 1 (Propositions H′, H″), which no static
feature tried identifies on every relabeling; rule RK finds it by its certificate.

### 5.3 Candidates that fail (`attempts/`, replayed by `attempts/k4_rulef_attempts.py`)

- `attempts/k4-rulef-least-count.md`: the first agent with the least deficit of a count (A₄⁺ᴺ, A₄⁺(o), the refined
  counts, Lemma K, ω; ties by index, by frozen or by exposed 4-good agents), and "a 4-good agent first": n = 3, m = 6,
  where all three first agents have deficit 1 and only one of them is in K1.
- `attempts/k4-rulef-frozen-free-owner.md`: "after Phase 1 and need-shrinking upgrades with no frozen agent and ω ≥ 1
  some owner is valid without rotation" (the step of Proposition H′ that a general theorem would need): n = 2, m = 5.
- `attempts/k4-rulef-bigtop-first.md`: static rules built on big-top agents: "the first big-top agent, else index order"
  (n = 3, m = 6, no big-top agent); "the first big-top agent" when two or more are big-top (n = 4, m = 8); the
  refinements with a shared-top fallback and fewest private goods (n = 4, m = 7).
- `attempts/k4-rulef-keptout-in-R.md`: Lemma M for Lemma K with kept-out sets restricted to goods the agent values
  (the first implementation): a suite core with n = 4, m = 8 and four big-top agents is in no class; with Remark 4's
  kept-out sets every first agent is in K0.

Each smallest failure is confirmed in PR #33's independent model (`k4/c4_verify_H/lb4r.py`: least rotations 2 on the
rule's sequence under every policy and both owner-needs conventions; for the lemma, no output at the state; for the
restricted kept-out sets, deficit 1 at every first agent and policy and after every single `RotStep`, while LB₄ʳ
needs no rotation), and K4.D holds there by brute force.

## 6. Lemma M: a proof attempt, and the cases it does not close

Fix a first agent a and a policy, let P be the state, ω ≥ 1, r the last-processed agent that is not upgraded (it is
not frozen when the policy is envy-free, (A1) of `k4/c4.md` §1), W = B_r ∪ J and E the agents threatened by W with
their base ("exposed"). Lemma K with owner r and K = ∅ reduces K0 for a to a count. Three steps close most of it.

**Step 1 (no exposed 4-good agent; envy-free policy): K0, K1, or (G2).** By Lemma E(i) (K4.C4.AB.L, Lean
`EFX.LB4R.lemmaE_three`) every exposed agent is a 3-good block leader holding its top with W ∩ R_x = {b_x, c_x}. By
Theorem A₄ (`EFX.LB4R.theoremA4`), outside LB⁺'s bad case some H ⊆ J with |H| ≤ S − cap(r) = κ meets every
π_x = {b_x, c_x} ∩ J; serving each x by the kept-out set {h} (h ∈ H ∩ π_x; then W ∖ {h} meets R_x in one good, worth
less than a_x) is a ∅-service of size ≤ κ: a ∈ K0. In the bad case, Theorem B₄ (`EFX.LB4R.theoremB4`,
`EFX.LB4R.theoremB4c`) gives, after LB⁺'s rotation along a need chain k* → r (a `RotStep`), ω′ ≤ 0 or the completion
of B₄(c), whose hitting set H′ serves E′ the same way: a ∈ K1 — unless r has four goods and is exposed after the
rotation along every chain ((G2) of `k4/c4.md` §6). This is Corollary C₄⁰ read in Lemma K's terms, and it is why the
class C40 of rule RK is contained in K0 ∪ K1 except for profiles where C₄⁰ uses a chain that Lemma K's search does not.

**Step 2 (free exposed agents cost nothing).**

*Lemma S.* Let |B_o| ≤ 1 and let σ be a K-service of the exposed agents that are not free (frozen or upgraded), with
K = ∅. Then σ extends to a ∅-service of all of E whose size exceeds |σ| by at most the number of free exposed agents
that use their own slot place; the others leave their slot place unused. Hence
deficit(r, ∅) ≤ |σ| − κ₀, where κ₀ is the number of slot places of the free agents other than r that are not exposed.

*Proof.* Take the free exposed agents x one at a time; G is the set of goods used so far. W ∩ NA = ∅ (J by (V1),
B_o since o is not frozen), so the goods of R_x ranked above x's pick are not in W; a threat needs two goods of R_x in
W, both ranked below the pick; so x holds a pick Y_x, which is a_x (three goods) or a_x or b_x (four goods), and at
most one good of R_x ∩ W is the owner's (Lemma E's argument, `k4/c4.md` §2, which uses only W ∩ NA = ∅ and holds for
either upgrade policy).
- x holds a_x of three goods: W ∩ R_x ⊆ {b, c}. If one of them, g, is junk and not in G, take it as slot good:
  W ∖ {g} meets R_x in one good, worth less than a. Otherwise both junk goods of R_x ∩ W are in G (at least one is
  junk, since |B_o ∩ R_x| ≤ 1): serve x by the kept-out set of those goods, at no cost.
- x holds b_x of four goods: W ∩ R_x ⊆ {c, d}; the same argument (one remaining good is worth less than b).
- x holds a_x of four goods: W ∩ R_x ⊆ {b, c, d}. If b is junk and not in G: slot good b (a + b > c + d). Else if c
  is junk and not in G: slot good c (W ∖ {c} meets R_x in at most {b, d}, and a + c > b + d). Else the junk goods
  among b, c are in G; let D be them plus d if d is junk. Then W ∖ D meets R_x in at most one good (the one of B_o, if
  any), so D serves x, and it costs at most one new good (d), which x's own unused slot place can take.
Each x adds at most one good, and only if it uses its own place (as slot good, or for d). ∎

So the free exposed agents (the case A₄ᵀ of `k4/c4.md` treats one at a time) never raise Lemma K's deficit: what
counts is the set F_E of exposed agents that are frozen or upgraded, against the places of free unexposed agents.

**Step 3 (frozen and upgraded exposed agents; open).** With σ_F a least service of F_E,
deficit(r, ∅) ≤ |σ_F| − κ₀, and K0 holds for a when |σ_F| ≤ κ₀ (or when a kept set K unfreezes enough agents, or
another owner does better). At k = 3 this is LB⁺'s Theorem A: every exposed frozen agent is a block leader whose need
chain ends at a free agent of its own block, which is not exposed (it is not a leader), so the blocks give
|σ_F| ≤ κ₀ except in the last block (the bad case, then Step 1's rotation). At k = 4 the count breaks in three ways
(`k4/c4.md` §6.1, K4.C4.GAP): an exposed 4-good agent need not lead its block, so a block can hold several exposed
agents and one free terminal; a flat agent needs two goods kept out; and the free terminal of a block can itself be
exposed. Lemma KR is the rotation that repairs a deficit of 1 when a frozen agent k has a need chain to r (it removes
k from F_E and adds r's place to κ₀). **What is not proved** is that for *some first agent* one of these succeeds:
- (M1) |σ_F| ≤ κ₀ (K0), for some a and some policy;
- (M2) else deficit 1 and a rotation as in Lemma KR, or another single rotation after which Lemma K applies (K1);
- (M3) and (G2) of Step 1 does not block every first agent.
The first agent enters only through Phase 1: changing it changes which agents are frozen and exposed. No argument here
relates the runs of two first agents; the exchange lemmas of `k4/c4one.md` §6 (Lemmas Ω, Ψ, PROVED, K4.C4.OM,
K4.C4.PSI) do so for runs with P-steps in any order and one 4-good agent, and are the natural tool for M1–M3.

*What the data say about M1–M3* (n ≤ 4, at most three 4-good agents). M3 is never needed (class C40 is empty). Where
no first agent satisfies M1 (the class K1 of §5.1), Lemma KR itself, with o = r, gives M2 for some first agent and
policy on every profile of a sample at n = 3 (every 5th leaf: 53,638 profiles, `results/k4_rulef/rotations_n3.log`),
almost always with o unthreatened after the rotation, and the rotated agent is an exposed frozen 4-good agent with
O = R_k ∩ W (B₄ʷ's shape). For M1 the big-top agents point to the induction to try: a big-top agent that does not hold
its top keeps a frozen agent no upgrade removes (§5.2), and with exactly one big-top agent inserting it first gives K0
or K1 on all the data. A proof of M along these lines would show: (a) with exactly one big-top agent q, the run of
τ_q satisfies M1 or Lemma KR's hypotheses; (b) with several, some big-top agent does (not always the first); (c)
without one, some agent sharing its top does — and (c) must contain Proposition H″'s choice of gadget 1 on H_t.

## 7. How a proof plugs into Lean

The frame is `lean/EFX/LB4R.lean` (K4.C4.FRAME, PROVED) and `lean/EFX/K4One.lean` (K4.ONE.FRAME, PROVED).
`lean/EFX/RuleF.lean` (this workstream) adds the statement a proof of rule F (or of rule RK) has to deliver and its
consequences, machine-checked:
- `EFX.LB4R.SucceedsR d v agents goods τ`: LB₄ʳ(τ) succeeds with at most d rotations (`Succeeds` is d = 3), and
  `succeeds_of_succeedsR` (d ≤ 3, via `rotReach_mono`);
- `EFX.LB4R.TheoremRuleF`: every strict profile of every k = 4 core has an agent a with `SucceedsR 1 … [a]`; τ = [a]
  is "a first, then index order" (choice 2 of `LB4R.lean`); `RuleFConn` (connected cores with a 4-good agent) and
  `RuleFOne` (connected cores with at most one 4-good agent) are the weaker forms TARGET₄ needs;
- `C4exists_of_ruleF`, `C4existsConn_of_ruleFConn`, `C4existsOne_of_ruleFOne` (through `sound_of_succeeds`), and
  `target4_of_ruleF`, `target4_of_ruleFConn`, `target4one_of_ruleFOne`.

A proof of rule RK would discharge `RuleFConn` as follows; nothing of it is in Lean yet:
1. Lemma K as a Lean theorem: for a state s with `Inv` (`EFX.LB4R.Inv`, every reachable state), an owner o that is not
   `Frozen`, K and a K-service of size ≤ κ^K, there is X with `Output … s (some o) X` (the completion of §2; its
   validity part is `EFX.LB4.Valid.sound_ownerNeeds` once the completion is built); and `EFX.LB4.complete_none_exists`
   for ω ≤ 0. Then class K0 gives `SucceedsR 0 … [a]` (no rotation: `RotReach.refl`) and class K1 gives
   `SucceedsR 1 … [a]` (one `RotStep`, which `EFX.LB4R.rotStep_inv` keeps inside `Inv`). Lemma K′ (Remark 5) is the
   cleaner statement to formalize: an iff with `∃ X, Output … s (some o) X`, whose "only if" half unfolds `Output`.
2. Class C40 is nearly a Lean theorem: `EFX.LB4R.corollaryC40'` (K4.C4.AB.L) gives `Succeeds` on its hypotheses;
   its proof uses at most one `RotStep`, so restating its conclusion as `SucceedsR 1` is a small change. (On the data
   the class C40 is never needed, §5.)
3. Lemma M — the existence of a first agent in K0 ∪ K1 ∪ C40 — is the open statement; with 1–2 it is `RuleFConn`.
`EFX.LB4R.TheoremC4` (every τ) is false (K4.C4.C); `TheoremRuleF` asks for one τ per profile, of length one, and is
not affected by Proposition H (on H_t rule RK needs no rotation, §4.1).

## 8. Reproduce

```
bash k4/rulef_runs.sh rk            # rule RK on every strict profile, n <= 4, at most three 4-good agents (~35 min, one CPU)
bash k4/rulef_runs.sh featdump feat  # n = 3: classes of every first agent where index order is not K0; features; Lemma KR
bash k4/rulef_runs.sh btrk bigtop    # a big-top agent first (else RK; else index order) and the failures of the fallback
bash k4/rulef_runs.sh samp H suite  # pure n = 4 and n = 5 samples, H_t with relabelings, the suite
bash k4/rulef_runs.sh y1            # rule RK with kept-out sets holding goods outside R_x (Remark 4 of §2; ~35 min)
bash k4/rulef_runs.sh n1            # rule RK3 (also no upgrades) with -Y1 on every exhaustive class (~37 min)
bash k4/rulef_runs.sh gap           # the gap profiles of -Y1 at n = 4 (one, two 4-good agents) against Lemma K' (~2 h)
bash k4/rulef_runs.sh rules         # the explicit rules of -A40 on n = 2 and n = 3 with m <= 5 (none fails there)
bash k4/rulef_runs.sh check attempts      # Lemma K's second implementation; the failed candidates
python3 k4/rulef_run.py --profiles=FILE -A41 -r1        # rule RK on given profiles ({"sets", "vals"} per line)
python3 k4/suite/run.py --pred=k4/rulef_suite.py:rule_rk  # rule RK on the counterexample suite
```
`k4/rulef_run.py` compiles `k4/rulef.c` into the temporary directory under a name made from a hash of the source
(`RULEF_BIN` overrides); its result lines and every log start with the command and that hash. `k4/rulef.c`'s modes
`-A40` (every first agent, the explicit rules of `rulef_rules`, `-Q` selects the one whose sequence is run) and `-A41`
(rule RK), `-A42` (static rules), the dumps `-D1`…`-D7` and `-E1` are documented in its header and in
`k4/rulef_run.py`; everything else is `k4/adaptive.c` (#44) unchanged. The class logs of §5.1 were made with earlier
revisions of `k4/rulef.c` whose `-A41` code is the present one (later changes add dump options, `-A42`, `-Y1` and
`-N1`, which are off by default).
