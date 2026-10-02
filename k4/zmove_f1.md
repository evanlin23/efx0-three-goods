# ZMOVE at one frozen agent (f = 1): first steps toward S1c at every n

Workstream `proof/k4-zmove-f1` (PR #91, draft). Target: Theorem ZMOVE (`k4/f2.md` §7.2) at f = 1. Milestones: (1)
Conjecture S1c (K4.TB.S1C) at every n; (2) the open cases of K4.SX.COVER; (3) ZMOVE at f = 1. Nothing here changes
K4.D or K4.T. Written proofs here are CONJECTURE rows until refereed; data rows are EVIDENCE.

**Status (end of the first session).** No milestone is reached. What is here:

- **Written proofs, not yet refereed** (§2; ledger K4.ZF1.CNT, CONJECTURE): four tools at a Z′-maximum Q of an f = 1
  key κ = (g, x) whose frozen agent x is big-top on g.
  - *Lemma JO* (any x): pool-optimality extends to the fillers. No free agent has a pair inside its pair, the pool and
    the other agents' fillers that beats its pair.
  - *Lemma CNT* (the counting certificate): a configuration with a lower good of x outside the pool, two robust free
    agents, and at most one threatener per free agent is completable. This is Theorem Z′(i) with Lemma D(ii) of
    `k4/c4min_reduce.md`, stated for any configuration.
  - *Corollary R1*: if κ is non-completable, then r′(Q) ≥ 2 forces the shape (I): every lower good of x in the pool, no
    free agent holding a filler, every terminal robust. Otherwise (shape (II)) *every* configuration at κ has at most
    one robust free agent.
  - *Lemma ABS*: in shape (I), no free agent can hold one of its own goods together with a lower good of x as a robust
    pair.
- **Consequences for the exception (E) of Lemma P** (§3; the only place S1c is needed for K4.SX.COVER at n ≥ 4): in (E)
  both terminals are "non-steep", and every free agent that values a lower good of x has exactly four goods, does not
  value g, values exactly one lower good ℓ of x, and has the shape v(h₁) + v(ℓ) < v(h₂) + v(z) of §3. Written proofs, not
  yet refereed. (E) itself stays open.
- **Data (EVIDENCE, §4; ledger K4.ZF1.BT4)**: in every hunt run here, and in all of PR #80's n = 4, 5 dumps, *no*
  non-completable f = 1 key with a big-top frozen agent exists at n ≥ 4. At n = 3 such keys exist, and at every one
  of them exactly one free agent values g. So S1c may hold at n ≥ 4 because its hypothesis is empty there (Conjecture
  BT4, §4), which no argument here proves.

## 0. Setting

Notation of `k4/c4x.md` §1, `k4/c4min.md` §1, `k4/c4min_reduce.md` §1–§3, `k4/c4min_f1.md` §1–§2 and `k4/sx.md` §1–§3.
f = 1, ω ≥ 1, κ = (g, x) a key, configurations Q at κ (pairs Q_y ⊆ M′ = M ∖ {g} of the free agents y ≠ x with
admissible parts H_y = Q_y ∩ U_y, U_y = R_y ∖ {g}; pool L, |L| = ω; X_o = Q_o ∪ L; "o threatens y" when
θ_y(X_o) > v_y(Q_y), and x is threatened when θ_x(X_o) > v_x(g)). A *filler* of y is the good of Q_y ∖ H_y when
|H_y| = 1; Φ is the set of fillers, Φ₋w those of the agents other than w. A Z′-maximum maximizes (r′, Λ′) (r′ = number
of robust free agents, Λ′ = Σ ℓ_y(H_y)). L_x := U_x (the lower goods of x). x is *big-top* on g when |R_x| = 4 and
v_x(g) > v_x(b) + v_x(c) for its two best lower goods b, c.

Facts used (all PROVED rows):
- (Z′) Theorem Z′ (K4.C4MIN.RED.Z): a Z′-maximum is pool-optimal; in a configuration where every free agent is
  threatened by at most one owner, at least r′ owners are free-valid. Its proof shows that pool-optimality of y (no pair
  S ⊆ Q_y ∪ L beats Q_y) alone gives "y is threatened by at most one owner", with the kinds and threat conditions of
  `k4/c4min_f1.md` Lemma 3 (K4.C4MIN.F1): a non-robust y is (T3), (Tg), (T4) (one valued good and a filler), (D) or
  (R) (two valued goods).
- (BT) If x is big-top, a set Z ∌ g threatens x holding {g} iff L_x ⊊ Z (`k4/c4min_f1.md` Lemma 8(a)).
- (K) If some configuration at κ has an owner valid with C = ∅ (its bundle threatens nobody), def*(κ) ≤ 0
  (`k4/sx.md` Lemma 0, K4.SX.KEY).
- (θ₂) If Y ∩ R_w ⊆ Z ∩ R_w and |Y| ≤ |Z|, then θ_w(Y) ≤ θ_w(Z) (`k4/f2.md` §5 Fact 2).
- Robust free agents are threatened by no owner (`k4/c4min_reduce.md` §2, first line of the proof of Theorem Z′).

## 1. Where S1c stands

Conjecture S1c (K4.TB.S1C): at a Z′-maximum of a non-completable f = 1 key with two or more terminals, x is not
big-top. Its n = 3 case is PR #88's Proposition S1c₃ (`k4/zmove_hall.md` §3, unrefereed, PR #88; the PR #88 referee
reports the proof correct). For K4.SX.COVER, S1c is needed only to exclude the exception (E) of Lemma P
(`k4/thetab.md` §7, K4.TB.P), and only at n ≥ 4, since Lemma P (iii) excludes (E) at n = 3.

The PR #88 referee lists where the n = 3 proof does not transfer: (a) the fourth good of a terminal may lie in a third
agent's pair; (b) the count m = 6; (c) the leaf need not be a terminal; (d) three or more terminals. The tools of §2 do
not use the n = 3 proof; they replace its exchanges by the counting certificate CNT, which needs only *two robust
agents and at most one threatener per agent*, not a configuration in which nobody is threatened.

## 2. Tools at a Z′-maximum (written proofs, not yet refereed)

**Lemma JO (junk-optimality).** Let Q be a Z′-maximum at an f = 1 key (x arbitrary) and w a free agent. No pair
B ⊆ Q_w ∪ L ∪ Φ₋w has v_w(B) > v_w(Q_w). Hence (a) an agent with a filler values no good of L ∪ Φ₋w; (b) an agent
holding two goods it values values every good of L ∪ Φ₋w less than each of them.

*Proof.* Suppose B exists. The goods of B ∖ Q_w lie in L or are fillers; two fillers in B belong to different agents,
since an agent's pair holds at most one filler (its admissible part is nonempty). Let D := Q_w ∖ B (|D| = |B ∖ Q_w|).
Build Q*: w holds B; each agent y whose filler lies in B receives a distinct good of D in its place (there are enough);
the remaining goods of D go to the pool, which loses B ∩ L, so it keeps ω goods. The pairs are disjoint and lie in M′.
B ∩ U_w is worth more than the admissible H_w, hence admissible (`k4/c4min.md` §1: a set of at most two goods worth more
than an admissible set is admissible); each such y keeps H_y inside its new pair, so its part contains H_y and is again
admissible. So Q* is a configuration at κ. w's level rises; every other level stays or rises; robustness is monotone in
the value of the holding (if v(B) > v(Q_w) ≥ v(U_w ∖ Q_w), then v(U_w ∖ B) < v(U_w ∖ Q_w) < v(B)). So
(r′, Λ′)(Q*) > (r′, Λ′)(Q), a contradiction. (a): for z ∈ L ∪ Φ₋w valued by w, B = H_w ∪ {z} would beat Q_w.
(b): for such z worth more than the lesser good h of Q_w, B = (Q_w ∖ h) ∪ {z} would. ∎

**Lemma CNT (counting certificate).** Let x be big-top on g, κ = (g, x), and Q* any configuration at κ with
- L_x ⊄ L*,
- r′(Q*) ≥ 2, and
- every free agent threatened by at most one owner.

Then def*(κ) ≤ 0.

*Proof.* Robust agents are threatened by no owner. Map each owner that threatens a free agent to one free agent it
threatens; the map is injective (one threatener each) into the non-robust agents, so at most (n − 1) − r′ owners
threaten a free agent, and at least r′ ≥ 2 owners are free-valid. If an owner o threatens x, then L_x ⊊ X*_o by (BT)
(g ∉ X*_o), so L_x ∖ L* ⊆ Q*_o; as L_x ∖ L* ≠ ∅ and pairs are disjoint, at most one owner threatens x. So some
free-valid owner threatens nobody; it is valid with C = ∅ (its bundle contains its admissible part), and (K) gives
def*(κ) ≤ 0. ∎

**Corollary R1.** Let x be big-top, def*(κ) > 0, and Q a Z′-maximum at κ.
- (a) If L_x ⊄ L, every configuration at κ has at most one robust free agent.
- (b) If L_x ⊆ L and some free agent has a filler, every configuration at κ has at most one robust free agent.
- (c) Hence, if r′(Q) ≥ 2: L_x ⊆ L, no free agent has a filler (every free agent holds two goods it values), and every
  non-robust free agent is of kind (D) or (R). Call this **shape (I)**; otherwise (**shape (II)**) r′ ≤ 1 at every
  configuration at κ, and with two or more terminals some terminal is not robust, hence of kind (Tg).

*Proof.* Q maximizes r′ over all configurations at κ, so it suffices to show r′(Q) ≤ 1.
(a) Q is pool-optimal (Z′), so every free agent has at most one threatener; CNT with Q* = Q.
(b) Let y have the filler f and ℓ ∈ L_x. Q*: y holds H_y ∪ {ℓ}, the pool is (L ∖ {ℓ}) ∪ {f}. By JO(a) y does not value
ℓ, so H*_y = H_y: Q* is a configuration with every holding's value unchanged, so r′(Q*) = r′(Q). Q* is pool-optimal:
for y, Q*_y ∪ L* = Q_y ∪ L; for w ≠ y, Q_w ∪ L* ⊆ Q_w ∪ L ∪ Φ₋w (JO). So every free agent has at most one threatener
(Z′), L_x ⊄ L*, and CNT gives r′(Q) ≤ 1.
(c) The kinds (T3), (Tg), (T4) hold one valued good and a filler (`k4/c4min_f1.md` Lemma 3); a non-robust terminal
values g, so it is of kind (Tg). ∎

Note: when B ⊆ U_w, robustness of B implies its admissibility (each good z of U_w ∖ B has v(z) ≤ v(U_w ∖ B) ≤ v(B),
strictly by distinct subset sums); Lemma ABS below uses this.

**Lemma ABS (no robust absorber in shape (I)).** Let x be big-top, def*(κ) > 0, and Q a Z′-maximum at κ of shape
(I). Then no free agent w has goods k ∈ Q_w and ℓ ∈ L_x such that B := {k, ℓ} has B ∩ U_w admissible and robust for w
(v_w(B) ≥ v_w(U_w ∖ B)).

*Proof.* Suppose w, k, ℓ exist; let h be the other good of Q_w; ℓ ∈ L (shape (I)). Q*: w holds B, the pool is
L* = (L ∖ {ℓ}) ∪ {h}. It is a configuration (B ∩ U_w admissible, pool of ω goods), w is robust in it, the other agents
keep their holdings, so r′(Q*) ≥ 2 (r′(Q) ≥ 2, and only w's robustness can change, to robust), and L_x ⊄ L*. Threats in
Q*: X*_w = B ∪ L* = X_w, and X*_o = (X_o ∖ {ℓ}) ∪ {h} for o ≠ w.
- w is robust, so unthreatened.
- A free y ≠ w that does not value h: X*_o ∩ R_y ⊆ X_o ∩ R_y and |X*_o| = |X_o|, so by (θ₂) its threateners in Q* are
  among those in Q: at most one (Z′).
- A free y ≠ w that values h, robust: unthreatened. Non-robust: kind (D) or (R) (shape (I)). Suppose two owners
  threaten it; their bundles meet in L*, so the goods needed for the threat lie in L*.
  - (D), H_y = {a, d}: a threat needs both b, c (each alone is worth less than a + d). Both in L* = (L ∖ ℓ) ∪ {h}
    puts one of them in L, against pool-optimality ({a, b} or {a, c} beats {a, d}).
  - (R), R_y = {a, p, q, s}, H_y = {p, q}: a threat needs both a and s (each alone is worth less than p + q, as
    {p, q} is admissible). a ∉ L by pool-optimality, so a = h and s ∈ L ∖ {ℓ}. Then Q**: y holds {h, s}, w holds B,
    the pool is (L ∖ {ℓ, s}) ∪ {p, q}. It is a configuration ({a, s} contains y's top a), y is robust in it
    (v(a) + v(s) > v(p) + v(q), the condition of kind (R)), w is robust, and every other holding is unchanged. So
    r′(Q**) ≥ r′(Q) + 1, against the maximality of Q.

So every free agent has at most one threatener in Q*, and CNT gives def*(κ) ≤ 0, a contradiction. ∎

Two instances: (i) k the top of U_w with v_w(k) ≥ v_w(U_w ∖ {k}) (then B ∩ U_w = {k} if w does not value ℓ); (ii) w
values ℓ, holds {h₁, h₂} with v(h₁) > v(h₂) (> v(ℓ) by JO(b)), and U_w ⊆ {h₁, h₂, ℓ}: then {h₁, ℓ} is robust
(v(h₁) + v(ℓ) > v(h₂)).

## 3. The exception (E) of Lemma P

Setting of `k4/thetab.md` §7: Q a Z′-maximum of a non-completable f = 1 key, the terminals are exactly two leaves τ₁,
τ₂, both θ-b (four goods, big-top on g, Q_τ = {α, β} its two best lower goods, its third lower good γ in L), and (E):
x big-top, L_x ⊆ L, L_x ∩ (U_τ₁ ∪ U_τ₂) = ∅. θ-b terminals are robust, so r′(Q) ≥ 2 and Q has shape (I) (Corollary
R1(c)): no free agent holds a filler.

**Corollary E (written proof, not yet refereed).** In (E):
- (E1) each τ_i is non-steep: v(β_i) + v(γ_i) > v(α_i);
- (E2) every free agent w that values a lower good of x is a third agent (not τ₁, τ₂), holds two goods h₁, h₂ it values
  (v(h₁) > v(h₂)), has exactly four goods R_w = {h₁, h₂, ℓ, z} with g ∉ R_w, values exactly one lower good ℓ of x, and
  v(h₁) + v(ℓ) < v(h₂) + v(z); in particular v(z) > v(ℓ), z ∉ L_x;
- (E3) such a w exists (core condition (C3): x has at most two private goods, and the terminals value no lower good of
  x).

*Proof.* (E1): Lemma ABS, instance (i), with w = τ_i, k = α_i (the top of U_τᵢ) and any ℓ ∈ L_x (τ_i does not value
it). (E2): w ∉ {τ₁, τ₂} by (E); no filler by shape (I). If U_w ⊆ {h₁, h₂, ℓ}, instance (ii) of ABS applies. So w has a
good z outside {g, h₁, h₂, ℓ}; with four goods at most, R_w = {h₁, h₂, ℓ, z} and g ∉ R_w. If {h₁, ℓ} were robust ABS
would apply, so v(h₁) + v(ℓ) < v(h₂) + v(z), which forces v(z) > v(ℓ). If z were a lower good of x, ABS with the pair
{h₁, z} would apply (v(h₁) + v(z) > v(h₂) + v(ℓ)). (E3): (C3) of K4.CORE. ∎

**What remains of (E) (plan).** The surviving configuration is narrow: a third agent w = {h₁, h₂, ℓ, z} with
v(h₁) + v(ℓ) < v(h₂) + v(z), z ∉ L_x, both terminals non-steep. Its two locations are z ∈ L (then v(z) < v(h₂) by JO(b))
and z in another agent's pair. In the second case, if {h₁, ℓ} is admissible for w (v(z) < v(h₁) + v(ℓ)), then after
w → {h₁, ℓ} the agent w is threatened at most by the holder of z (L* ∩ R_w = {h₂}, and v(h₂) < v(h₁) + v(ℓ)), so CNT
applies unless another blocker appears; the next step is to
show that every blocker leads to an r′-raising exchange, as in the proof of ABS. The case z ∈ L needs another move
(every owner then threatens w after w → {h₁, ℓ}). The structured search of §4 (`k4/zf1_eshape.py`) builds exactly
this shape at n = 4.

**The plan for S1c at every n.** By Corollary R1 a counterexample has shape (I) or (II).
- Shape (I): every terminal is robust, no fillers, L_x ⊆ L, r′ ≥ 2; any lower good of x parked anywhere must break
  CNT. Lemma ABS removes every robust absorber; what is left is the analogue of (E2) for every agent and every lower
  good of x.
- Shape (II): at most one robust agent in *every* configuration, and a (Tg) terminal τ exists. Then τ's goods u₂, u₃ are
  valued holdings of other agents (JO(a)), and any exchange that makes τ and one more agent robust is a contradiction
  (no CNT needed). The case analysis of these exchanges (by the threat forest: one leaf and a path when L_x ⊄ L) is not
  done.

## 4. Data (EVIDENCE)

Tools (this workstream; `k4/zf1_lib.py` is written from the definitions and imports no repository code):
- `k4/zf1_lib.py`: keys, configurations, Z′-maxima, terminals, threats, the valid-owner test with the unfreezing
  clause (`k4/c4min.md` §1). Sanity check: on PR #80's n = 4 hunts (`n4_3_r40k`, `n4_pure_r40k`) it finds the same 299
  non-completable keys and 565 Z′-maxima as `k4/sx.md` §4.2.
- `k4/zf1_embed.py`: extends a profile with a non-completable big-top key by one agent (or two, `--depth=2`) with new
  private goods and shared goods, keeping ω ≥ 2.
- `k4/zf1_bthunt.py`: hill-climbing over the value types of a random n = 4 core (one agent forced big-top), minimizing
  the number of completable configurations at its big-top keys.
- `k4/zf1_eshape.py`: every profile of the n = 4 core shaped like (E) with the third agent of (E2)
  (sets [[0,1,2,3],[0,4,5,6],[0,7,8,6],[9,10,1,4]], x, τ₁, τ₂ big-top on 0).

Results (`results/k4_zmove_f1/`):
- `embed_n4.log`: 400 n = 3 profiles with a non-completable big-top key, 40 one-agent extensions each: 16,000 f = 1
  profiles at n = 4, 20,679 big-top keys, all completable.
- `embed_n5.log`: 120 bases, 30 two-agent extensions each: 3,480 f = 1 profiles at n = 5, 5,254 big-top keys, all
  completable.
- `bthunt_n4_s11.log`: 500 hill-climbs of 200 steps on the 222 n = 4 cores with ω ≥ 2: no non-completable big-top key.
  (The same search at n = 3 finds one in 60 runs, so it is weak.)
- `eshape_n4_z4.log`: see the log (run at the end of the session; if it is missing or cut off, rerun as in §5).
- n = 3 (every 20th profile of PR #80's dumps `n3_all_30`, `n3_all_40`, not logged here): at every non-completable
  big-top key exactly one free agent values g (so S1c₃ holds there for a stronger reason), and at every non-completable
  key whose x is not big-top both free agents are big-top on g.
- `count_hunts.log` (`k4/zf1_count.py`): PR #80's n = 4 hunts (`n4_3_r40k`, `n4_pure_r40k`, `n4_pure_r400k`), its two
  n = 5 pure hunt files with keys, and the T1-stuck profiles of `k4/dl13.md`: 2,691 non-completable keys at n ≥ 4
  (4,253 Z′-maxima), none with x big-top; the 135 big-top ones are at n = 3. (`k4/thetab.md` §7.1's table agrees.)

**Conjecture BT4 (CONJECTURE, EVIDENCE only).** At n ≥ 4 every f = 1 key whose frozen agent is big-top is completable.
It would make S1c at n ≥ 4 vacuous, and with S1 (K4.ON.S) it would confine the single-terminal regime to n = 3.

## 5. Where to resume

1. Finish (E): the two locations of z in §3, with CNT and r′-raising exchanges as in Lemma ABS. Test each step on the
   shape of `k4/zf1_eshape.py` (sets with Z = 5, 7, 8 as well: `--sets=...`).
2. Shape (II) of Corollary R1: exchanges around a (Tg) terminal that make it and a second agent robust.
3. Conjecture BT4: a proof attempt, or a larger structured hunt (two-agent extensions of the n = 3 keys without private
   goods, `k4/zf1_embed.py --depth=2`).

Reproduce:
```
python3 k4/zf1_embed.py results/k4_sx/hunt/n3_all_30.jsonl.gz results/k4_sx/hunt/n3_all_40.jsonl.gz --every=7 --max=400 --trials=40 --seed=2   # embed_n4.log (~30 s)
python3 k4/zf1_embed.py results/k4_sx/hunt/n3_all_40.jsonl.gz --every=11 --max=120 --trials=30 --seed=3 --depth=2                           # embed_n5.log (~40 s)
python3 k4/zf1_bthunt.py results/k4_certs_4_n4_1.json.gz results/k4_certs_4_n4_2.json.gz results/k4_certs_4_n4_3.json.gz results/k4_certs_4_pure.json.gz --runs=500 --steps=200 --seed=11   # ~3 min
python3 k4/zf1_eshape.py      # eshape_n4_z4.log (248,832 profiles, ~13 min)
```
