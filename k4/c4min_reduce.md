# C₄ᵐⁱⁿ at one frozen agent: reduction to Theorem Z

Workstream `proof/k4-c4min-reduce`, ledger rows K4.C4MIN.RED.* (CONJECTURE / EVIDENCE only). It builds on PR #41
(`k4/c4min.md` on branch `proof/k4-c4min`: configurations §1, Theorem Z §3, Theorem F §3.6, Conjecture Φ′ and the
f = 1 roadmap §4) and uses the definitions of `k4/c4x.md` §1 (PR #36). It does not edit their files.

**Target.** Prove C₄ᵐⁱⁿ on every strict profile whose fewest frozen agents is f = 1 by reducing to Theorem Z:
1. remove the frozen agent x and its good g = φ(x);
2. apply Theorem Z to the smaller instance I′ = I − x − g;
3. reinsert x with {g}.

Three variants were asked for:
- **(a)** reduce and reinsert at a fixed key;
- **(b)** rerun Theorem Z's argument with 𝒩 = {g} fixed and the extra constraint that x is protected;
- **(c)** swap the roles of x and a terminal z that needs g.

**Status.** No proof of the f = 1 case. The result is partly positive, partly negative. Every written proof below is
unreviewed, and every lemma was checked by brute force before use (§6).

- **Proved in writing: the reduction itself works** (§1–§3).
  - The configurations at a key (g, x) are exactly the all-pairs allocations of I′, and I′ always has one.
  - Every terminal (a free agent that needs g) has g as its top.
  - **Theorem Z′** (Theorem Z on I′, from the lemmas of Theorem F): every maximum of (r′, Λ′) at any key has a free
    owner whose bundle threatens no free agent. More precisely, a pool-optimal configuration with r′ robust free agents
    has at least r′ such owners.
  - Reinsertion is then a pure counting condition (**Lemma C**): if every free agent is threatened by at most one owner
    and r′ exceeds the number |D_x| of owners threatening x, the configuration is completable.
  - **Lemma D** bounds |D_x|: it is ≤ 1 when the pool alone does not threaten x (t = 0) and x has 3 goods or is of
    type a > b + d. It is ≤ 2 otherwise.
- **Refuted: each reduction as stated** (§4; two implementations replay each instance).
  - **(a)** There are keys with no completable configuration at all (smallest n = 3, m = 6). Worse, in the core H★
    (n = 3, m = 8), *at every key* the unique maximum of Theorem Z's potential (r′, Λ′) is not completable: it puts
    all of x's lower goods in the pool. So no rule for choosing the key, and no tie-break after (r′, Λ′), rescues a
    black-box use of Theorem Z. The potential must see where x's goods lie before it sees Λ′.
  - **(b)** At a fixed key, Theorem Z's argument survives the constraint t = 0 on every profile with n ≤ 3: every
    maximum of (−t, r′, Λ′) has a free-valid owner. It breaks at n = 4. A non-robust agent's pool improvement would
    release one of x's goods into the pool, so it is blocked. That agent is then threatened by every owner, and
    Lemma P fails.
  - **(c)** One role swap from a failed key to a terminal's key does not suffice: it fails in the same core H★.
- **Conjectured, with evidence: the key must be optimized together with the configuration** (§5).
  - Maximize over the configurations of *all* keys a potential that has t before Λ. Then every maximum was completable
    on every profile tested. This holds for #41's Φ = (−t, r, Λ) restricted to f = 1, for (r, −t, Λ), and for both with
    #41's tie-break −p.
  - Scope: every f = 1 profile with n ≤ 3 (7,285,840); every profile of the n = 4 cores with one or two 4-good agents
    (28,478 and 10,723,372); random samples of every n = 4 and n = 5 class (490,837 f = 1 profiles).
  - This is an independent confirmation, with a new implementation, of #41's Conjecture Φ′ at f = 1 on these sets.
  - At the maxima, Lemma C's counting certificate holds for 99.97% of maxima at n ≤ 3 (9,820,566 of 9,823,326); the
    exceptions are listed in §5.

So the reduction route turns into the global potential route of #41 and #50: Theorem Z′ handles the free agents.
What remains is precisely the local improvement lemma at the fewest-frozen maxima, with x's goods and the role swaps.
§5 states the exact gap.

- **The big-top case** (§5.1–§5.2) is what PR #50's Theorem F1 leaves: profiles in which every (r, Λ)-maximum has a
  big-top frozen agent.
  - There, restricted to big-top keys, (−t, r′, Λ) has every maximum completable on every profile tested
    (Conjecture K4.C4MIN.RED.BT). This includes every profile with n ≤ 3 and the n = 4 classes with one or two 4-good
    agents.
  - At those maxima t = 0 and the threats are injective, so Lemma C finishes whenever r′ ≥ 2.
  - **Lemma PM** (written proof, checked) shows that #50's path move from a terminal threatened off the path keeps t = 0
    and raises r′, for every type of x.
  - §5.2 lists the cases a proof still has to handle.
- **A local improvement lemma** (§5.3, Conjecture K4.C4MIN.RED.LIL): every configuration without a valid owner has a
  move that raises Φ_r = (r′, −t, Λ). The moves are #50's (rotation, path move), plus one free agent re-pairing inside
  its pair and the pool, which may lower its value.
  - No configuration is stuck on every profile with n ≤ 3 (25,552,144 non-completable configurations), on every profile
    of the n = 4 cores with one or two 4-good agents, or on the n = 4, 5 samples.
  - With −t first, a two-agent exchange is needed as well (244 stuck configurations at n = 4 otherwise).

Nothing here changes K4.D or K4.T.

## 1. Setting: keys and the reduced instance

Fix a strict profile of a k = 4 core with fewest frozen agents f = 1 and ω = f − σ = m − 2n + 1 ≥ 1 (for ω ≤ 0 there
is nothing to prove). 𝒫, needs, validity, frozen agents and slots are those of `k4/c4x.md` §1. Configurations,
admissibility and valid owners (with the unfreezing clause) are those of `k4/c4min.md` §1.

A **key** is a pair (g, x) such that some P ∈ 𝒫 with one frozen agent has x frozen on the base {g}. For a key write:
- U_y = R_y ∖ {g} for every agent y;
- a := v_x(g);
- the *lower goods* of x, U_x = {b, c} (3 goods) or {b, c, d} (4 goods), v(b) > v(c) > v(d).

**Lemma K (keys).** (g, x) is a key iff
- g is the top of x, and
- the agents y ≠ x have pairwise disjoint sets A_y ⊆ U_y, each admissible for U_y (1 ≤ |A_y| ≤ 2, and every
  good of U_y ∖ A_y worth less to y than A_y).

The configurations at the key are then exactly the families of pairwise disjoint pairs Q_y ⊆ M′ := M ∖ {g} (y ≠ x) with
Q_y ∩ U_y admissible for U_y, the pool L = M′ ∖ ⋃ Q_y having ω goods. That is, they are the all-pairs allocations
(APAs) of the **reduced instance** I′ = I − x − g, whose agents are the y ≠ x with relevant sets U_y. I′ has
n′ = n − 1 agents, m′ = m − 1 ≥ 2n′ + 1 goods, and fewest frozen agents 0.

*Proof.* Let P ∈ 𝒫 have x as its only frozen agent, with base {g}. Then NA = {g}, since every needed good is the base
of a frozen agent.
- x's needs lie in NA = {g} ∋ g, so they are empty and g is x's top.
- A free agent y has B_y ⊆ R_y and g ∉ B_y (bases are disjoint), so B_y ⊆ U_y.
- N_y ⊆ {g} says every good of U_y ∖ B_y is worth less than B_y. And B_y ≠ ∅, since otherwise N_y = R_y ⊄ {g}.

Conversely, given the sets A_y, the pre-allocation B_x = {g}, B_y = A_y has N_x = ∅ and N_y ⊆ {g}, so it is valid.
- If NA = ∅, it has no frozen agent, contradicting f = 1.
- So NA = {g}, and x is its only frozen agent.

The description of the configurations is `k4/c4min.md` §1 with 𝒩 = {g}. ∎

**Lemma T (terminals).** In every configuration at a key, some free agent z needs g, i.e. g ∈ R_z and
v_z(g) > v_z(Q_z) (a *terminal*). Every terminal has g as its top.

*Proof.*
- Existence. Otherwise the pre-allocation with B_x = {g} and B_y = Q_y ∩ U_y has NA = ∅, hence no frozen agent, which
  contradicts f = 1.
- Top. A = Q_z ∩ U_z is admissible for U_z, so every good of U_z is worth at most v_z(A) = v_z(Q_z) < v_z(g).
  (Q_z ∩ R_z = Q_z ∩ U_z, because g ∉ Q_z.) ∎

So the agents that compete for g are those whose top is g. At n ≤ 3 all keys of a profile share the same g (7,285,840
of 7,285,840 profiles). At n = 4, 5 some profiles have keys with different goods (for example 2,256 of the 28,478
profiles of the n = 4 cores with one 4-good agent).

## 2. Theorem Z on the reduced instance

At a key, a free agent y is **robust** if v_y(Q_y) ≥ v_y(U_y ∖ Q_y), and r′ is the number of robust free agents. Λ′ is a
sum over the free agents of levels ℓ_y(Q_y), for any level that increases strictly with v_y(Q_y ∩ U_y). The tools use
ℓ over the subsets of U_y and, for §5, over those of R_y. The configuration is **pool-optimal** if no free y has a pair
S ⊆ Q_y ∪ L with v_y(S) > v_y(Q_y). An owner o is **free-valid** if X = Q_o ∪ L threatens no free agent y ≠ o holding
Q_y.

**Theorem Z′.** Let (g, x) be a key.
- (i) If every free agent is threatened by at most one owner, at least r′ free agents are free-valid owners. This holds
  in particular for every pool-optimal configuration.
- (ii) Every configuration at the key that maximizes (r′, Λ′) lexicographically is pool-optimal and has a free-valid
  owner.

*Proof.* Every owner bundle X lies in M′, so X ∩ R_y ⊆ U_y ∖ Q_y for every free y ≠ o. Hence a robust y is threatened
by nobody: v_y(X ∖ h) ≤ v_y(X ∩ R_y) ≤ v_y(U_y ∖ Q_y) ≤ v_y(Q_y).

(i) Map each owner that threatens some free agent to one agent it threatens. The map is injective, since that agent
has no other threatener. Its image consists of non-robust agents. So at most (n − 1) − r′ owners threaten a free agent,
and at least r′ owners are free-valid.

For pool-optimal configurations, the kinds of `k4/c4min.md` §3.6 (Lemma Z2 with U_y in place of R_y) show that every
free agent is threatened by at most one owner. That list uses only y's own pool-optimality and |X| = ω + 2 ≥ 3, L ≠ ∅:
- |U_y| ≤ 2: y holds its top of U_y and is robust.
- |U_y| = 3: y is non-robust only in state (T3): it holds u₁ and a good outside U_y, with u₁ < u₂ + u₃. Then
  L ∩ U_y = ∅, and y is threatened exactly by the owner holding {u₂, u₃}.
- |U_y| = 4: then U_y = R_y and y does not value g. Lemma Z2 of `k4/c4min.md` §3.2 applies verbatim: kinds (T4), (D),
  (R), each threatened by at most one owner.

(ii) A pool improvement of y (replace Q_y by its best pair in Q_y ∪ L) gives a configuration at the same key, since a
pair worth more than an admissible pair is admissible (Lemma Z1 with U_y). It raises Λ′ strictly and keeps r′: if y
was robust, v_y(U_y ∖ S) < v_y(U_y ∖ Q_y) ≤ v_y(Q_y) < v_y(S). So a maximum is pool-optimal.

If it had no free-valid owner, then by (i) r′ = 0, and the threat map is a permutation of the free agents (every owner
threatens someone, injectively). Lemma R of `k4/c4min.md` §3.3, in the U_y form of §3.6, gives a configuration at the
same key with a robust agent, contradicting maximality, unless every free agent is of kind (T4). A (T4) agent has four
goods, all outside {g}, so it does not value g. Then no free agent values g, contradicting Lemma T. ∎

The last step replaces Theorem Z's use of "every good is relevant to someone": the pool may contain goods that only x
values (x's private goods, which are worthless in I′).

## 3. Reinsertion: the owners that threaten x

Let t := [v_x(L ∩ U_x) > a]. t = 1 means the pool alone threatens x, whoever the owner is (#41's t). D_x is the set of
free agents o whose bundle Q_o ∪ L threatens x holding {g}.

The type of x decides which sets of its lower goods threaten it: let Θ_x be the minimal subsets of U_x worth more
than a.

| x | Θ_x |
|---|---|
| 3 goods (b + c > a) | {b, c} |
| 4 goods, a > b + c ("big top") | {b, c, d} |
| 4 goods, b + d < a < b + c | {b, c} |
| 4 goods, c + d < a < b + d | {b, c}, {b, d} |
| 4 goods, a < c + d ("flat") | every pair |

**Lemma D.**
- (i) If t = 1, every owner threatens x (with C = ∅).
- (ii) If t = 0, then |D_x| ≤ 1 when x has 3 goods or is of the first two 4-good types, and |D_x| ≤ 2 otherwise.
- (iii) If t = 0, an owner o threatens x only if Q_o contains a good of some S ∈ Θ_x not in L.

*Proof.* X = Q_o ∪ L has ω + 2 ≥ 3 goods, and X ∩ R_x = X ∩ U_x. Two facts:
- If X ⊄ R_x, removing a good x does not value gives max_h v_x(X ∖ h) = v_x(X ∩ U_x). So x is threatened iff X
  contains some S ∈ Θ_x.
- If X ⊆ R_x, then X = U_x has three goods (ω = 1), and x is threatened iff b + c > a. Every type in the table
  except the big top has b + c > a and {b, c} ⊆ X, with {b, c} ∈ Θ_x.

In either case, *x threatened ⟹ X ⊇ some S ∈ Θ_x*.

(i) t = 1 means v_x(L ∩ U_x) > a, so L contains some S ∈ Θ_x. As |S| ≥ 2, |L| ≥ 2 and |X| ≥ 4 > |U_x|, so X ⊄ R_x.
Then S ⊆ X threatens x.

(iii) With t = 0, no S ∈ Θ_x lies in L, so an S ⊆ X has a good outside L, which lies in Q_o.

(ii) Pairs of distinct owners are disjoint.
- For 3-good x and the first two 4-good types, Θ_x has a single set S, and by (iii) the owner holds a good of
  S ∖ L ≠ ∅. Only one owner does, because an S ⊆ X needs all of S ∖ L in Q_o.
- For the type c + d < a < b + d, Θ_x = {{b, c}, {b, d}}:
  - if b ∉ L, the owner holds b, and that is one owner;
  - if b ∈ L, then c, d ∉ L (t = 0), and the owner holds c or d: two owners at most.
- For a flat x, at most one lower good is in L, since two would give t = 1.
  - If one is, the owner holds one of the other two.
  - If none is, the owner holds a pair of lower goods, and only one owner can. ∎

**Lemma C (counting certificate).** If in a configuration at a key every free agent is threatened by at most one owner
and r′ > |D_x|, then some free agent is a valid owner with C = ∅. So C₄ᵐⁱⁿ holds on the profile (`k4/c4min.md` Lemma
1(a)).

*Proof.* By Theorem Z′(i) at least r′ owners are free-valid, and at most |D_x| < r′ of them threaten x. ∎

**Corollary.** If some key has a pool-optimal configuration with t = 0 and r′ ≥ 2, and x has 3 goods or is of the first
two 4-good types, then C₄ᵐⁱⁿ holds on the profile. With r′ ≥ 3 the type of x does not matter.

How far this certificate reaches:
- Some configuration satisfies Lemma C's hypotheses on 7,285,024 of the 7,285,840 f = 1 profiles with n ≤ 3. The 816
  others are completable otherwise:
  - 720 (n = 2) need the unfreezing clause; these are exactly the 720 profiles of `k4/c4min.md` §1;
  - 96 (n = 3) have a valid owner that the count misses. In the one example inspected (core 41 of
    `results/k4_certs_3.json.gz`), the owner that threatens x also threatens a free agent, so the union bound of the
    proof is not tight.
- On the samples it fails on 90 of 294,342 f = 1 profiles with n = 4 and 22 of 224,973 with n = 5
  (`results/k4_red_n4.log`, `results/k4_red_n5.log`, counter `FAIL_prof_cert2`).

## 4. Why each reduction fails

Every instance below is replayed by `attempts/k4_c4min_reduce_attempts.py` with both implementations (`k4/red_lib.py`
and `k4/red.c`), log `results/k4_red_attempts.log` ("ALL CONFIRMED"). Each failed approach has its own file in
`attempts/`, ending with the smallest failing configuration.

### 4.1 (a) Theorem Z as a black box at a chosen key

**A key can be hopeless.** In `attempts/k4-c4min-reduce-a.md`, instance A1 (n = 3, m = 6, core 17 of
`results/k4_certs_3.json.gz`), the key (5, 0) has *no* completable configuration, while the keys (5, 1) and (5, 2) do.
- There x = 0 has two private goods, which are worthless in I′.
- With ω = 1, one of them must enter the pool, and every free-valid owner's pair holds another good of x.
- At n ≤ 3, 62,208 of the 14,259,424 keys are hopeless (`results/k4_red_n3.log`, `key_noncompletable`). This is the
  smallest n (at n = 2 every key works) and the smallest m (m = 2n, ω = 1).

So step 1 needs a rule for the key. Rules that pick the key by a score of x alone, then require every (r′, Λ′)-maximum
there to be completable, all fail (`attempts/k4_c4min_reduce_rules.py`, `results/k4_red_rules.log`: 6,000 random
profiles per n = 3 core, 8,402 with f = 1). The scores tried, with the number of profiles on which the rule fails:
- the level of x's top: 241;
- fewest private goods: 239;
- a / v(U_x): 215;
- that ratio minus the share of private goods: 157;
- least value of private goods: 145;
- "the key whose I′ has the largest maximum of (r′, Λ′)": 120.

**No key works with Theorem Z's potential.** Instance A2 is the core **H★**: n = 3, m = 8, agents {0, 2, 6, 7},
{1, 4, 6, 7}, {3, 5, 6, 7}, values 0:3, 2:4, 6:2, 7:8 | 1:4, 4:3, 6:2, 7:8 | 3:3, 5:4, 6:2, 7:8 (core 46 of
`results/k4_certs_3.json.gz`).
- All three agents have top 7, are of type a > b + c, and share good 6. Each has a private pair worth 7 < 8.
- Every agent can be the frozen one: keys (7, 0), (7, 1), (7, 2).
- At each key, (r′, Λ′) has a *unique* maximum: both free agents take their private pairs, so both are robust (r′ = 2).
  Their pairs hold no good of x. So the pool is x's private pair plus 6, i.e. all three lower goods of x (t = 1), and
  every owner threatens x.
- A completable configuration exists at every key: one free agent holds its top with 6 instead of its second good.
  It is robust too, and t = 0. Theorem Z's potential does not see this, because 6 is worth less to it.

Since the maximum is unique, no tie-break after (r′, Λ′) helps. A term that sees x's goods must come before Λ′, and
(r′, −t, Λ′) is enough here. 128 profiles with n ≤ 3 have no key at which every (r′, Λ′)-maximum is completable, all in
this core.

### 4.2 (b) Theorem Z's argument at a fixed key, with x protected

Rerun §2 at a fixed key with the constraint t = 0 first: maximize (−t, r′, Λ′).
- Pool improvements that would raise t are no longer available, so Lemma Z1's pool-optimality holds only for the moves
  that keep x's goods out of the pool.
- The modified rotation of Lemma R may put a good of x into the pool.

Measured (`results/k4_red_n3.log`, `results/k4_red_n4.log`, `results/k4_red_n5.log`, counters `tmax_*`):
- **n ≤ 3:** every maximum of (−t, r′, Λ′) at every key has a free-valid owner (17,603,288 maxima). 48,872 maxima
  have a non-robust agent that is not pool-optimal, and it is still threatened by at most one owner.
- **n = 4, 5:** Lemma P breaks. Instance B1 (`attempts/k4-c4min-reduce-b.md`; n = 4, m = 11, core 214 of
  `results/k4_certs_4_pure.json.gz`), key (10, 1), x flat. At the maximum shown there:
  - the g-top agent 2 holds its top 9 with x's good 1 as a filler, while its own lower goods 3 and 6 are in the pool;
  - so agent 2 is threatened by every owner;
  - its pool improvement would release 1, and with 5 already in the pool that threatens x (t = 1);
  - no owner is free-valid.
  - The profile is completable, at the keys of the big-top agents 0 and 2.
- Smallest n = 4 (n ≤ 3 has none). m = 11 is the first m found and is not claimed to be the smallest.

So the repair of (b) is not inside one key: it needs a different frozen agent.

### 4.3 (c) One role swap

Take a non-completable maximum of (r′, Λ′) at a key and a terminal z of it. By Lemma T, z has top g, and (g, z) is a key
(each such z was a key in every case tested). Test the two-level rule "then every (r′, Λ′)-maximum at (g, z) is
completable":
- it holds for 424,168 of the 424,552 such maxima with n ≤ 3;
- it fails for 384, all in H★, where every key fails.
- The narrower move "x takes an admissible pair from L ∪ Q_z, z freezes on g, everyone else keeps its pair" leaves 24 of
  the 392 non-completable (r′, Λ′)-maxima of the same n = 3 sample without a completable result
  (`results/k4_red_rules.log`). There x's best lower good sits with a third agent, so a longer exchange cycle is needed.

So one swap is not enough. What works is to optimize over the keys and the configurations together (§5).

## 5. What works: one potential over all keys

Maximize over the configurations of **all** keys a potential with t before Λ, where:
- r = r′ (a frozen agent at f = 1 is never robust, `k4/c4min.md` §3.6);
- Λ = Σ over all agents of the level ℓ_i of their holding over R_i, including ℓ_x({g}) (#41's Λ);
- p = |L ∩ U_x| (#41's p).

**Conjecture K4.C4MIN.RED.GLOB.** On every strict profile with f = 1 and ω ≥ 1, every maximum over all keys of each of
(−t, r, Λ), (r, −t, Λ), (−t, r, Λ, −p) and (r, −t, Λ, −p) is completable. The first and third are #41's Φ and Φ′
restricted to f = 1.

Evidence (every maximum completable, 0 failures, `k4/red.c`):
- every f = 1 profile with n ≤ 3 (7,285,840);
- every profile of the n = 4 cores with one 4-good agent (28,478);
- every profile of the n = 4 cores with two 4-good agents (10,723,372 f = 1 profiles, `results/k4_red_n4_2_all.log`);
- two samples of 4,000 random profiles per core of the n = 4 cores (seeds 7 and 9; 265,864 f = 1 profiles);
- n = 5 samples (224,973 f = 1 profiles).

Variants that fail, all at n ≤ 3 (`results/k4_red_n3.log`: counter `FAIL_glob_r,lamU`, and the second command's
`FAIL_pot[...]`):
- the same over all keys *without* t, i.e. (r′, Λ′) as in Theorem Z: 123,180 profiles;
- (−t, r′, Λ′) with Λ′ over U_y without x's level: 44,556;
- (−t, r′, Λ′, ℓ_x): 6,448.
This suggests that the maxima must prefer, through Λ, keys whose frozen agent's top is high in its own order, and
g-top agents holding pairs worth more than g.

**Structure at the maxima of (−t, r, Λ)** (counters `amax_*`):

| | n ≤ 3 (every profile) | n = 4 samples | n = 5 samples |
|---|---|---|---|
| maxima | 9,823,326 | 552,474 | 486,985 |
| t = 1 | 0 | 0 | 0 |
| a non-robust free agent not pool-optimal | 0 | 12 | 2 |
| some free agent threatened by two owners | 0 | 0 | 0 |
| x threatened by two owners (Lemma D(ii)) | 0 | 3,805 | 4,192 |
| r′ = 0 | 0 | 21 | 18 |
| Lemma C's certificate fails | 2,760 | 1,035 | 380 |

**The gap.** A proof of the conjecture along these lines needs the following at a non-completable maximum:
1. **t = 0.** Every f = 1 profile tested has a configuration with t = 0 at some key. It is not proved.
2. **Every free agent is threatened by at most one owner.** At n ≤ 3 every non-robust free agent at the maximum is
   pool-optimal (observed, not proved), which gives this by Lemma Z2. At n = 4 and 5 a blocked improvement (instance
   B1's mechanism) occurs at some global maxima (12 and 2 cases), but no double threat was observed.
3. **Counting.** Lemma C then finishes whenever r′ > |D_x|.
4. **The rest: r′ = 1 with |D_x| = 1, or |D_x| = 2.**
   - With threat-injectivity and no valid owner, the threat relation on the free agents and x misses exactly one
     vertex. That vertex is either x (then the free agents are permuted, and Lemma R applies) or the robust agent w
     (a path w → … → x plus cycles of non-robust agents).
   - The path must be closed by the need edge x → z at a terminal z (Lemma T: top g), which changes the key. This is
     the move of `k4/c4min.md` §4 ("roadmap for f = 1"), whose open steps (ii)–(iv) are the ones left here.
   - Instance A2 shows that the potential must rank keys through Λ (x's own level), not through (r′, Λ′) of I′ alone.

Items 1–2 are where the reduction stops being a black box: Theorem Z′ covers the free agents only while their
improvements do not move x's goods into the pool.

### 5.1 The big-top case, which PR #50 leaves open

PR #50 (branch `proof/k4-c4min-f1`, `k4/c4min_f1.md` §2, unreviewed) uses #41's Ψ = (r, Λ) over all keys. Its
Theorem F1 proves that every Ψ-maximum whose frozen agent is not **big-top** has an owner valid with C = ∅ (big-top:
four goods and a > b + c; for a 4-good x this is up to its case (E)). What remains at f = 1 are the **big-top
profiles**, those in which every Ψ-maximum has a big-top frozen agent (`results/k4_red_bt.log`, counters `bt_*`):
- 3,802,424 of the 7,285,840 f = 1 profiles with n ≤ 3;
- 2,940 of 28,478 at n = 4 with one 4-good agent;
- 2,204,312 of 10,723,372 at n = 4 with two 4-good agents (every profile).

In 38,016 of the n ≤ 3 ones some Ψ-maximum is not completable. In 128 (all in the core of H★) none is, so Ψ cannot be
kept there; #50 §3 reports the same obstruction.

For a big-top x the reduction's lemmas specialize:
- Θ_x = {U_x}, so t = [U_x ⊆ L]. With t = 0 at most one owner threatens x: the one holding all of U_x ∖ L
  (Lemma D).
- x's own level ℓ_x({g}) is 7 at every big-top key. The subsets ∅, {d}, {c}, {b}, {c, d}, {b, d}, {b, c} are worth
  less than a, and {b, c, d} more. So over the big-top configurations, Λ ranks only the free agents.
- A big-top agent whose top is g and which is not frozen is a terminal in every configuration: no pair of its other goods is
  worth more than g.

**Conjecture K4.C4MIN.RED.BT.** On every big-top profile, every maximum of (−t, r′, Λ) over the configurations whose
frozen agent is big-top is completable.

Evidence (counter `btx_prof_every`, 0 failures, `results/k4_red_bt.log`):
- every big-top profile with n ≤ 3 (3,802,424);
- every big-top profile of the n = 4 cores with one or two 4-good agents (2,940 and 2,204,312);
- samples at n = 4 with three or four 4-good agents (34,875 big-top profiles);
- samples at n = 5 (60,141).

At all these maxima:
- t = 0, and every free agent is threatened by at most one owner, so Lemma C finishes whenever r′ ≥ 2.
- Lemma C's hypothesis r′ > |D_x| fails at 2,136 maxima with n ≤ 3 (among them those of the n = 2 profiles that need
  unfreezing), at none in the n = 4 class with two 4-good agents, and at 7 and 3 in the samples.

Scope of the conjecture:
- It needs the big-top-profile hypothesis. On profiles that have a big-top key but are not big-top profiles, the
  restricted maxima can fail: 14,928 profiles at n ≤ 3, and 10 in the n = 4 sample (counters `anybt_*`).
- Not every key of a big-top profile is big-top: 1,052,984 of the 3,802,424 at n ≤ 3 have another key. So a path move
  to a terminal that is not big-top leaves the restricted space. A proof along §5.2 has to handle that.

With #50's Theorem F1 (including its case (E)), Conjecture BT would give C₄ᵐⁱⁿ at f = 1.

### 5.2 The path move keeps t = 0 (Lemma PM)

The *path move* is #50's (`k4/c4min_f1.md` §2). Along a threat path τ = p₀ → p₁ → … → p_k → x through free agents
(p_{i+1} threatened by p_i, x by p_k), from a terminal τ:
- p_{i+1} receives Q_{p_i}. As in Lemma R, at most one receiver of kind (R) whose fourth good is in the pool takes
  {a, s} instead, and the other good goes to the pool.
- x receives a pair P_x ⊆ (Q_{p_k} ∪ L) ∩ U_x and becomes free.
- τ receives g and becomes frozen.
- The rest of Q_{p_k} ∪ L is the new pool.

For a big-top x, #50 takes P_x = x's best pair, which is worth less than g, so x's level drops and the move can tie in
Ψ. The next lemma says the move nevertheless raises (−t, r′, ·) when τ is threatened from off the path, for every type
of x.

**Lemma PM.** Let a configuration at a key (g, x) have t = 0, every non-robust free agent pool-optimal, and no owner
valid with C = ∅. Let τ = p₀ → … → p_k → x be a threat path from a terminal τ that is threatened by some owner o not
among p₁, …, p_k. Let P_x be a robust admissible pair of x inside (Q_{p_k} ∪ L) ∩ U_x. Then P_x exists, and the path
move gives a configuration at the key (g, τ) with t = 0 and with r′ larger by at least 1.

*Proof.*
- **P_x exists.** p_k threatens x, so Q_{p_k} ∪ L contains some S ∈ Θ_x (proof of Lemma D). A robust admissible pair
  inside S ∪ (U_x ∩ (Q_{p_k} ∪ L)):
  - {b, c} when S = {b, c} or S = U_x (it contains b, and b + c > d);
  - {b, d} when S = {b, d} (b + d > c);
  - for a flat x and S = {c, d}, the pair {c, d} itself: c + d > a > b makes it admissible and robust.
- **Validity.** As in #50's Lemma 7:
  - the receivers get pairs worth more than before, or pairs containing their top;
  - x gets P_x;
  - τ gets g, which is its top (Lemma T);
  - the pairs stay disjoint.
  
  By Lemma K the result is a configuration at the key (g, τ).
- **r′.** x is robust after the move. τ and p₁, …, p_k were threatened, so none was robust, and nobody else changes.
  So r′ rises by at least 1.
- **t = 0 at (g, τ).**
  - τ is threatened, so it is not robust. A terminal with three goods is always robust in I′ (|U_τ| = 2), so τ has
    four goods and is of kind (Tg): it holds u₁ and a good outside U_τ, with u₁ < u₂ + u₃. Pool-optimality gives
    L ∩ U_τ = ∅, and the only owner that threatens τ holds {u₂, u₃}. That owner is o, which the move leaves alone.
  - So u₂ and u₃ stay in o's pair, and u₁ lies in Q_τ.
  - The new pool is ((Q_{p_k} ∪ L) ∖ P_x) plus possibly one good released by a modified receiver from some Q_{p_i}.
    It meets U_τ in at most u₁, worth less than g. ∎

Check (`k4/red_pathmove.py`, from the definitions with `k4/red_lib.py`; `results/k4_red_pathmove.log`). Scope: every
configuration at every key with t = 0, every non-robust free agent pool-optimal, and no valid owner; every such path.
No failure on:
- every f = 1 profile with n = 2;
- 20,000 random profiles per n = 3 core (2,244 path moves);
- 150 random profiles per n = 4 core (125 path moves).

Without the hypothesis on o, t = 1 can follow (n = 3; n = 2 has a single free agent).
- Example: core 38 of `results/k4_certs_3.json.gz` (agents {0, 2, 5, 6}, {1, 4, 5, 6}, {3, 4, 5, 6}) with values 0:3, 2:6, 5:2, 6:10 |
  1:5, 4:6, 5:4, 6:8 | 3:2, 4:3, 5:4, 6:8; key (6, 0); pairs {3, 4}, {1, 5}; pool {0, 2}.
- Agents 1 and 2 threaten each other, and agent 2 also threatens x.
- The move along 1 → 2 → x puts agent 1's goods 1 and 5 in the pool, worth 9 > 8 to it.
- That configuration is not a maximum: rotating the 2-cycle makes both robust.

**What this leaves for Conjecture BT (and for GLOB).** Take a non-completable maximum with t = 0 at which every free
agent and x are threatened by at most one owner each. There are |A| owners, each threatening someone, and |A| + 1
vertices. So either exactly one vertex is unthreatened, or every vertex is threatened, r′ = 0, and one owner threatens
both x and a free agent.

In the first case the threats form a bijection: a path w → p₁ → … → p_k → x plus cycles, with w the unthreatened
vertex. If w = x, the whole bijection is cycles. Every cycle rotates with a gain in Φ:
- plain rotations keep the pool;
- a modified rotation cannot make t = 1. It would put the rotating owner's other good y′ into the pool, and a
  threatening set of x inside L ∪ {y′} means that owner threatens x. (A threatening set has at least two goods, so
  ω ≥ 2, and the owner's bundle of ω + 2 goods is not inside R_x.)
  In the bijection it threatens only its successor.

So a maximum has no cycle, every free agent lies on the path, and so does every terminal.
- A terminal p_j with j ≥ 1 is threatened by p_{j−1}, off the moved segment, so Lemma PM gives a larger Φ. For
  Conjecture BT this also needs p_j to be big-top.
- What remains:
  1. the only terminal is the start w;
  2. the terminals on the path are not big-top (Conjecture BT only);
  3. a non-robust agent is not pool-optimal because its improvement would raise t (instance B1's mechanism);
  4. t = 0 at the maximum (Lemma T0, not proved). A key can have no configuration with t = 0: 208 keys at n ≤ 3
     (`results/k4_red_n3.log`, counter `key_no_t0`); every profile has another key with one. An example, with a flat
     x, is core 41 of `results/k4_certs_3.json.gz`
     with values 0:2, 2:3, 5:4, 6:8 | 1:3, 3:5, 4:6, 6:7 | 3:2, 4:3, 5:6, 6:10: its key (6, 1) has a flat x and only
     configurations with t = 1, while its keys (6, 0) and (6, 2) have none with t = 1;
  5. every vertex threatened (r′ = 0): the owner that threatens both x and a free agent may need a modified rotation
     that makes t = 1.

### 5.3 A local improvement lemma

The moves used so far are all local:
- **M1**: one free agent y re-pairs inside Q_y ∪ L. Its new pair is any pair whose part in U_y is admissible, so this
  includes pool improvements and swaps that lower y's value but change the pool.
- **M2**: two free agents re-pair inside Q_y ∪ Q_z ∪ L (#41's pool-assisted exchange).
- **M4**: the rotation along a threat cycle of free agents (Lemma R, plain or modified).
- **M5**: #50's path move from a terminal along a threat path to x, with x taking any admissible pair inside
  Q_{p_k} ∪ L and at most one modified receiver. The result is at the terminal's key.

`k4/red.c -L` checks, for every configuration at every key that is not completable, whether one of these moves gives a
configuration (at any key) with a larger potential.

**Conjecture K4.C4MIN.RED.LIL.** On every strict profile with f = 1 and ω ≥ 1, every configuration without a valid
owner has an M1, M4 or M5 move that raises Φ_r = (r′, −t, Λ). This is #50's Ψ = (r, Λ) with −t inserted. Then every
maximum of Φ_r over all keys is completable, and C₄ᵐⁱⁿ holds at f = 1. It would also give an algorithm: apply improving
moves until an owner is valid. Φ_r takes at most 2n(15n + 1) values (r′ ≤ n − 1, t ∈ {0, 1}, every level ≤ 15), so
that is a bound on the number of moves.

Evidence and variants (`results/k4_red_lil.log`, counters `lil_*`; "stuck" = no improving move):

| potential, moves | scope | non-completable configurations | stuck |
|---|---|---|---|
| (r′, −t, Λ), M1 M4 M5 | every profile with n ≤ 3 | 25,552,144 | 0 |
| (r′, −t, Λ), M1 M4 M5 | every profile, n = 4 with one or two 4-good agents | 11,520 + 12,744,968 | 0 |
| (r′, −t, Λ), M1 M4 M5 | n = 4, three or four 4-good agents, 4,000 per core | 831,672 | 0 |
| (r′, −t, Λ), M1 M4 M5 | n = 5 samples (3,000, 600, 200 per core) | 4,009,551 | 0 |
| (−t, r′, Λ), M1 M2 M4 M5 | all the scopes above | the same | 0 (M2 used 244 times at n = 4, 374 at n = 5, never at n ≤ 3 or in the exhaustive n = 4 classes) |
| (−t, r′, Λ), M1 M4 M5 | n = 4, three or four 4-good agents, 4,000 per core | 831,672 | 244, all with a big-top x |

Putting r′ first lets a pool improvement that makes its agent robust count even when it puts a good of x into the pool;
that is exactly the configuration of instance B1. With t first, the two-agent exchange M2 is needed there instead.

Proved parts:
- Theorem Z′ (M1 pool improvements and M4 at a fixed key);
- Lemma PM (M5 from a terminal threatened off the path keeps t = 0 and raises r′).

#50's Lemmas 2–7 (written proofs, unreviewed) show that these moves raise Ψ at a Ψ-maximum whose frozen agent is not
big-top. A proof of LIL has to add:
- the bookkeeping of t: Lemma PM is one piece, and the configurations where a pool improvement is blocked by t are
  another;
- the big-top case, where the path move ties in Ψ (§5.1–§5.2).

## 6. Checks and evidence

All counts are strict profiles of the certified core lists `results/k4_certs_*.json.gz` (types from `k4/check4.py`).
"f = 1" counts profiles with ω ≥ 1.

| claim | scope | result | log |
|---|---|---|---|
| f = 1 profiles, keys | n ≤ 3 all; n = 4 one 4-good agent all | 7,285,840 and 28,478, as #41's `k4/c4min.c` (`k4/c4min.md` §4 table); profiles with f ≥ 2 (any ω): 463,772, the number #46 reports for two frozen agents (`k4/hall.md` §5) | `results/k4_red_n3.log`, `results/k4_red_n4.log` |
| Lemma T (a terminal in every (r′, Λ′)-maximum) | same | 0 violations | same |
| Theorem Z′(ii) (free-valid owner at every (r′, Λ′)-maximum, which is pool-optimal) | every key of every f = 1 profile with n ≤ 3 (17,448,196 maxima); n = 4, 5 samples | 0 violations | `results/k4_red_n3.log`, `…_n4.log`, `…_n5.log` |
| Theorem Z′(i) (≥ r′ free-valid owners at every pool-optimal configuration) | every pool-optimal configuration of every key, same scopes | 0 violations | same |
| Lemma C (certificate ⟹ completable) | every configuration, same scopes | 0 violations | same |
| §4 instances | 3 profiles | both implementations agree | `results/k4_red_attempts.log` |
| key rules, narrow swap (§4.1, §4.3) | 6,000 random profiles per n = 3 core | as stated there | `results/k4_red_rules.log` |
| Conjecture GLOB | §5 | 0 failures | `results/k4_red_n3.log`, `…_n4.log`, `…_n4_2_all.log`, `…_n5.log` |
| Conjecture BT, big-top profiles | §5.1 | 0 failures | `results/k4_red_bt.log` |
| Lemma PM | §5.2 | 0 failures | `results/k4_red_pathmove.log` |
| Conjecture LIL | §5.3 | 0 stuck configurations | `results/k4_red_lil.log` |

Independence: `k4/red.c` and `k4/red_lib.py` share no code with each other or with #41's `k4/c4min.c` and
`k4/c4min_*.py`, only the type generator `k4/check4.py` and the core lists. The Python library was run on the n = 2
profiles and on random n = 3 samples during development (same counts as the C tool on n = 2). The §4 instances are
replayed by both. The f = 1 count agrees with #41's implementation, and the f ≥ 2 count with the number #46 reports.

## 7. Reproduce

```
python3 k4/red_run.py results/k4_certs_2.json.gz results/k4_certs_3.json.gz --pots="mt,r,lamR;r,mt,lamR;mt,r,lamR,mp;r,mt,lamR,mp" -x 3   # ~45 s on 4 CPUs
python3 k4/red_run.py results/k4_certs_4_n4_1.json.gz --pots=...                                  # ~2 s
python3 k4/red_run.py results/k4_certs_4_n4_2.json.gz results/k4_certs_4_n4_3.json.gz results/k4_certs_4_pure.json.gz --rand=4000 --seed=7 --pots=...
python3 attempts/k4_c4min_reduce_attempts.py                                                       # < 1 s
```
Each log starts with the `# command:` lines that wrote it. `k4/red_run.py` compiles `k4/red.c` into the temporary
directory under a name made from a hash of the source (`RED_BIN` overrides). `-x N` prints up to N example profiles per counter. Potentials (`--pots`) are lexicographic and
maximized over all keys. Their features are:
- `r` (robust free agents);
- `lamU` (levels over U_y);
- `lamR` (levels over R_y plus ℓ_x({g}));
- `mt` (−t), `mp` (−p), `mvp` (−v_x(L ∩ U_x));
- `mterm` (−terminals), `lx` (ℓ_x({g})), `mndx` (−|D_x|).

The analysis counters `amax_*` use the first potential given. A counter named `FAIL_*` is a failed *hypothesis*; several
are the refuted reductions of §4, as listed in the text.
