# Induction on agents along the serial-dictatorship order

Workstream `proof/k4-sd-induct` (branch `claude/k4-sd-induct`). Angle of the k = 4 campaign (`k4/attack_log.md`):
grow the instance one agent at a time along a serial-dictatorship order, as agent-count results do, using the SD-C
structure of `k4/sdc.md` (§2, §6, §26–§30). Code: `k4/sdind/`; logs: `results/k4_sdind/`. Everything computed is
evidence only (PROMPT.md §5 rule 3). Notation as in `k4/sdc.md`: Y = SD(π) the picks, J the junk (unpicked goods), a
*one-absorber completion* gives every junk good to some agent with at most one agent (the absorber) receiving two or
more.

## Status (burst 2)

- **Proved** (written proofs, short):
  - Lemma D (§1): deleting any agent together with its pick is SD-consistent. The junk J stays the same, so a
    completion of any sub-instance I_U is a map J → U.
  - Lemma F (§1): an agent inserted *first* (holding its top among the goods present) is threatened only by the
    absorber's bundle.
  - Lemma S (§3): in a completion where every agent but o holds its pick and at most one junk good, EFX₀ ⟺ (S1) no one
    is threatened by o's bundle and (S2) no one values the pick of a two-good holder above its own bundle. When every
    pick-frozen agent is alone and o is not frozen, (S2) is automatic.
  - Lemma U (§3): an unfrozen first agent can always make itself safe with its best junk good of the absorber's
    bundle. That move can hurt only the absorber, and only through a two-good bundle whose pick the absorber wants.
- **Evidence** (insertion in reverse SD order; each new agent is first):
  - *AB₁* (§3, `e7_absorber.py`): whenever an unfrozen agent o absorbs in some one-absorber completion (or none is
    needed), some order with o last gives an insertion path with at most one junk move per step. 10,106 of 10,106
    cases: screen, suite, 1,500 random n = 4 profiles.
  - Any insertion sequence (any agent order) with at most one move per step exists on every start with a one-absorber
    completion: 580 screen, 529 suite, 3,234 random n = 4. Reverse SD alone misses 3 random starts, all of which have
    only frozen absorbers (§2).
  - *Projection* (§3, `e8_projection.py`): 95% of completions are reached by insertions in which each new agent takes
    at most one junk good from the absorber, permanently.
  - *Free BOTH* (§5, `e12_both_free.py`): if u holds its top and nobody wants its pick, every free completion of the
    picks of I − u − Y_u extends to one of I by moving at most 4 junk goods, and the sub-instance never extends while
    I does not (12,883 cases, n ≤ 5). Conjecture: a minimal counterexample to SD-C has no agent with a private top.
- **Refuted** (each with a replay in `attempts/k4_sdind_attempts.py`):
  - inserting into an *arbitrary* completion of the sub-instance with a bounded repair, in either direction
    (`attempts/k4-sdind-every-completion.md`, Q2: distance 4);
  - Lemma BOTH for *one-absorber* completions (`attempts/k4-sdind-both-one-absorber.md`, r1179, n = 4, m = 9). The
    sub-instance extends with one absorber, but I needs two, because the absorber's compensation is the new agent's
    danger set;
  - the two-phase shape TP (every pick-frozen agent alone, absorber unfrozen) fails on 77 of 580 screen starts. A
    frozen agent may hold junk when its wanter is compensated (A131), so the frozen status has to use current values.
- **Where it stands.** A pure induction (hypothesis on the sub-instance only) cannot work in the reverse SD direction.
  The future frozen agents' danger sets are arbitrary, and the absorber's bundle has to avoid them before they arrive.
  So the order structure gives:
  - an *algorithm* shape: one move per insertion, with lookahead;
  - a *reduction* (free BOTH, if proved);
  - and it leaves the same core as §30 of `k4/sdc.md`: the frozen agents' demands against the free slots, Lemma S
    being its exact form.
- **Next**:
  1. prove free BOTH (a potential over completions of I − u − Y_u);
  2. the chain-needing starts in insertion form (§4, `e9_chain.py`: a chain at the insertion where the one-move path
     breaks works for 92% of orders);
  3. AB₁ at n = 5 and on the logged hard profiles.

## 1. Deleting an agent with its pick

**Lemma D (SD-consistency of deletion).** Let Y = SD(π) with junk J, and let u be an agent. In I − u − Y_u (u and its
pick deleted; I − u if u picked nothing), SD(π − u) gives every other agent its pick Y_i, and its junk is J.

*Proof.* Agents before u in π: Y_u was available at their turns and not taken, so deleting it changes none of their
choices. Agents after u: Y_u was already gone at their turns. By induction along π every agent i ≠ u faces the same
available goods minus at most Y_u, which it did not take, so it takes Y_i. The unpicked goods are the same. ∎

So for every set U of agents, I_U = (U, Y[U] ∪ J) has SD outcome Y restricted to U (π restricted to U), and junk J.
Write A(U) for the one-absorber EFX₀ completions of I_U, as maps J → U.
- A(U ∪ {u}) contains every X ∈ A(U) in which u, holding {Y_u} alone, is not threatened (u's singleton cannot be
  strongly envied, and nothing else changes for the agents of U);
- conversely, restricting X ∈ A(U ∪ {u}) with no junk at u gives an element of A(U) (deleting an agent and its bundle
  keeps EFX₀ for the rest).

**Which agents can be first or last.** By Lemma 1 of `k4/sdc.md`, the orders producing Y are exactly the topological
orders of the want relation (i before j whenever j wants Y_i). So u can be *last* iff nobody wants Y_u (u is not
frozen), and u can be *first* iff u wants nothing, i.e. Y_u is u's top.

**Lemma F (a first agent is threatened only by the absorber).** Let f be first in an order producing Y on I_U (Y_f
is f's top among the goods of I_U), and X a one-absorber completion of I_U ∖ f. Then X + (f ↦ {Y_f}) is EFX₀ iff f is
not threatened by the absorber's bundle B_o, i.e. iff v_f(B_o ∖ h) ≤ v_f(Y_f) for every h ∈ B_o.

*Proof.* f's singleton is never strongly envied, and the other agents' bundles and values do not change. A bundle
{Y_j} or {Y_j, g} with g junk: removing a good leaves a single good of I_U, worth at most v_f(Y_f) since Y_f is f's
top there. Only the absorber holds three or more goods. ∎

By contrast, an agent inserted *last* can want every earlier pick, so every two-good bundle {Y_j, g} with a pick it
wants threatens it.

## 2. Paths of completions (`k4/sdind/e2_paths.py`, `results/k4_sdind/e2_paths.log`)

An insertion sequence u_1, …, u_n adds one agent at a time; A({u_1}) is the single map J → u_1. A *path* picks
X_k ∈ A({u_1, …, u_k}) for every k; its step size is the largest Hamming distance (number of junk goods whose holder
changes) between consecutive X_k. For each SD outcome Y with a one-absorber completion (n ≤ 5, every order):

| insertion sequence | screen (580 starts) | suite (529 starts) |
|---|---|---|
| SD order (new agent last), best order producing Y: least step 0 / 1 / 2 / 3–6 / some level empty | 16 / 158 / 192 / 196 / 18 | 15 / 157 / 147 / 190 / 20 |
| reverse SD order (new agent first), first order producing Y: some level empty | 25 | 25 |
| **reverse SD order, best order producing Y: least step 0 / 1** | **298 / 282** | **249 / 280** |
| any insertion sequence: least step 0 / 1 | 298 / 282 | 249 / 280 |

So the reverse SD order is as good as any insertion sequence, and one move per insertion always suffices for some
order producing Y. The SD order (new agent last) needs up to 6 moves, and on 18 screen and 20 suite starts some
intermediate sub-instance has no one-absorber completion at all.

`e1_delete.py` (`results/k4_sdind/e1_delete.log`) shows that a bounded repair from *every* completion of the
sub-instance fails in both directions (distance 3–4 at n = 4, e.g. Q2 and A131), so the induction has to carry a
choice, not an arbitrary completion.

Cross-check of the brute force (`k4/sdind/xcheck_lib.py`, `results/k4_sdind/xcheck_lib.log`): existence of a
one-absorber completion agrees with the SAT test `oc_absorb.extends_A` on all 1,550 screen and 1,452 suite cases;
every returned assignment passes the raw EFX₀ check; the full sets agree with itertools enumeration on 82 sampled
cases.

## 3. The reverse-SD insertion: absorber, projection, and the shape of a completion

**Lemma S (shape of a one-absorber completion; written proof, checked on 8,664 assignments by `e10_twophase.py`).** Let
Y be SD picks with junk J, and X a completion in which every agent i ≠ o holds Y_i plus at most one junk good. Then X
is EFX₀ iff
- (S1) no agent i ≠ o is threatened by X_o (v_i(X_o ∖ h) ≤ v_i(X_i) for every h ∈ X_o); and
- (S2) for every j ≠ o holding a junk good, every agent i ≠ j has v_i(Y_j) ≤ v_i(X_i).

*Proof.*
- Singletons are never strongly envied.
- A two-good bundle {Y_j, g} with g junk loses either good:
  - removing g leaves Y_j, which is (S2);
  - removing Y_j leaves g. If i values g, then v_i(g) < v_i(Y_i) ≤ v_i(X_i), by (I2) of `k4/sdc.md` §2. If i has no
    pick, every good of R_i was picked and v_i(g) = 0.
- Only X_o can have three or more goods, and (S1) is EFX₀ toward it. ∎

*Corollary TP.* If every agent whose pick someone wants (pick-frozen) holds its pick alone and o is not pick-frozen,
then (S2) holds automatically. A two-good holder j is then not pick-frozen, so v_i(Y_j) ≤ v_i(Y_i) ≤ v_i(X_i) for all
i. So EFX₀ ⟺ (S1): a covering problem in which unfrozen agents take at most one junk good each, so that o's bundle
threatens nobody. This two-phase shape exists on 503 of 580 screen and 458 of 529 suite starts (`e10_twophase.log`).
The exceptions need a frozen agent to hold junk, which is allowed when every wanter is compensated (A131: the
absorber wants agent 0's pick and is compensated by its own junk).

**Lemma U (an unfrozen first agent makes itself safe with one good; written proof).** Let f be first among the
agents present (Y_f = a is its top among the goods present), let |R_f| ≤ 4, and let X be a one-absorber completion of
the others with absorber o. Suppose f is threatened by X_o, and let g be f's most valuable *junk* good in X_o. After
f takes g:
1. f is not threatened by any bundle;
2. f's bundle {a, g} threatens only agents i with v_i(a) > v_i(X_i);
3. among the old agents, only o can become threatened, and only by a two-good bundle {Y_j, g_j} with
   v_o(Y_j) > v_o(X_o ∖ g).

*Proof.*
1. Write R_f = {a, b, c, d} with values a ≥ b ≥ c ≥ d (missing goods worth 0). X_o contains at most one good of R_f
   that is not junk, namely Y_o.
   - If g = b, then the rest is at most c + d ≤ a + b.
   - If g = c, the goods of R_f left in X_o lie in {b, d}, and b + d ≤ a + c.
   - If g = d, then b and c are not junk in X_o, so at most one of them (Y_o) is in X_o. That is a single good, worth
     at most a.

   Two-good bundles never threaten f (Lemma F).
2. Removing g from {a, g} leaves a. Removing a leaves g, worth less than each valuer's pick by (I2).
3. Only o's bundle changed for the others, and it lost a good. o's own value dropped by v_o(g). By Lemma S, o can then
   be threatened only by (S2)-type bundles, or by f's bundle; for f's bundle the threat needs v_o(a) > v_o(X_o ∖ g). ∎

So inserting an *unfrozen* agent costs one move, unless the absorber's compensation is at stake. `e5_step.py` (from
every completion, not only reachable ones): the move of Lemma U works in 1,224 of the 1,247 threatened unfrozen
insertions on the screen set. The rest need the absorber's cheapest good instead (gap-local-n3-m7-n3c43) or a second
move.

**Which order, which absorber** (`e3_suffix.py`, `e6_orders.py`, `e7_absorber.py`; logs of the same names).
- Some order producing Y works on every start, but not every order (451 of 580 screen starts work with every order).
- The order matters mainly through its last agent, the absorber: for 503 of the 580 starts, whether an order works
  depends only on its last agent.
- *Conjecture AB₁.* If an unfrozen agent o is the absorber of some one-absorber completion of Y (or no absorber is
  needed), then some order producing Y with π_n = o admits an insertion path with at most one junk move per step.
  Evidence: no exception in 901 screen, 841 suite and 8,364 random n = 4 cases. With o fixed, every order works in
  91–94% of these cases.
- Putting all frozen agents first in π (inserted last) works for some arrangement on all 580 screen starts.
- Greedy move rules do not suffice: 'f takes its best junk good', 'f takes its least valuable junk good', helpers
  first, and 'keep π_n the absorber' fail on 4–14 screen starts for every order (`e4_rule.log`). The failures need
  lookahead. In c4min-pareto-n3-m7, agent 2 must take good 3 rather than its better good 5, because agent 0
  (frozen, inserted later) needs 3 out of the absorber's bundle.

**Projection** (`e8_projection.py`). For a final completion X* with absorber o, its projection on a set U ∋ o gives o
every junk good whose X*-holder is not in U. Along an insertion order starting at o, consecutive projections differ
by the inserted agent's own junk good, so the steps are at most 1. The projection on U is EFX₀ iff no agent of U is
threatened by o's inflated bundle: the other bundles are final, and o's value is at least its final value. 124,294 of
136,362 completions (random n = 4) are reached this way by some insertion order. Every screen and suite start has
such a completion, and 3,228 of the 3,234 random starts do; the exceptions have only frozen absorbers. So the
insertion is, in the main, the static covering problem of Corollary TP, solved one agent at a time.

**Why a pure induction cannot work here.** At level k the agents still to come are arbitrary first agents. A frozen
one among them needs its danger sets (any two or three goods present) out of the absorber's bundle when it arrives,
and no property of the current completion alone can guarantee this for every possible future agent. The successful
paths make their early choices with knowledge of the later agents (c4min-pareto-n3-m7 above). A proof along these
lines is therefore a global count, as in §30 of `k4/sdc.md`, with the insertion order as its bookkeeping. The angle
that avoids lookahead is a reduction that deletes an agent whose insertion never needs it: §5.

## 4. The starts that need a chain (`e9_chain.py`, `results/k4_sdind/e9_chain.log`)

Starts whose picks have no one-absorber completion (OC₁ needs one improving chain): 16 special, 194 screen (n ≤ 5).
Along each order's reverse-SD insertion, the chain-free path (one move per step) breaks at some level. Applying one
improving chain (`sdilib.chains`, the same moves as `de_free.iter_chains`, cross-checked on 310 states) to the picks of
the sub-instance at the breaking level, then taking any completion of the chain state and continuing with one move
per step:
- works for 611 of the 662 screen orders tried (65 of 69 special);
- the successful chain at the breaking level starts at the newly inserted agent on 126 of the 194 screen starts, and
  that agent is always frozen.

So the chain is, mostly, the frozen agent's own repair at its insertion (§29's "some repairing chain starts in D"),
and it can be applied as soon as the agent arrives. Without the chain-free prefix (fresh completion at any level),
the last level is OC₁ itself.

## 5. Deleting an agent that holds its top and is wanted by nobody (Lemma BOTH)

Call u a *both* agent of Y if Y_u = a is u's top and nobody wants a (v_i(a) ≤ v_i(Y_i) for every i ≠ u). An agent
with a private top is a both agent of every SD outcome in which it picks first. By Lemma F and Lemma U, a both agent
can always make itself safe with one junk good, and its bundle {a, g} threatens nobody. So it is the natural agent to
delete.

**One absorber: refuted** (`e11_both.py`; `attempts/k4-sdind-both-one-absorber.md`). The repair "u takes the absorber's
junk good that makes it safe and costs the absorber least; if the absorber is then threatened by a two-good bundle
{Y_j, g_j}, j hands g_j to the absorber" works from every completion on screen and suite (888, 1,526). On 1,500
random n = 4 profiles it fails 4 times, and on r1179 the sub-instance extends with one absorber while I has no
one-absorber completion at all. There the absorber's junk is both its compensation for wanting a two-good holder's
pick and the new agent's danger set; the free completions of I use two absorbers.

**Free completions: Conjecture BOTH** (`e12_both_free.py`, `results/k4_sdind/e12_both_free.log`). If u is a both
agent of Y and the picks of I − u − Y_u have an EFX₀ completion, so do the picks of I. Moreover from *every* EFX₀
completion of the sub-instance, at most 4 junk moves reach one of I.

| data | cases (Y, u) | completions X′ tested | least distance 0 / 1 / 2 / 3 / 4 | sub extends, I does not |
|---|---|---|---|---|
| screen (n ≤ 5) | 148 | 2,019 | 1,294 / 721 / 3 / 1 / 0 | 0 |
| suite (n ≤ 5) | 166 | 35,134 | 16,588 / 18,542 / 3 / 1 / 0 | 0 |
| random n = 4 (3,000 profiles, seed 7) | 10,868 | 582,202 | 375,694 / 206,117 / 361 / 27 / 3 | 0 |
| random n = 5 (300 profiles, seed 8) | 1,701 | 96,642 | 76,044 / 20,587 / 10 / 1 / 0 | 0 |

*Consequence (if BOTH is proved).* SD-C reduces to instances in which no agent has a private top. Take u with a
private top a, apply SD-C to I − u − a (fewer agents): some outcome Y′ extends. Then Y′ + (u ↦ a) is an SD outcome of I
(u first), u is a both agent of it, and BOTH extends it. The same works for any agent whose top nobody values above
that agent's pick in the extending outcome, but that condition depends on Y′.

*What a proof must handle.* After u takes its best junk good g* from a bundle of three or more goods (u is then safe,
as in Lemma U, case by case on a ≥ b ≥ c ≥ d), only the holder j of g* can be hurt, and only if v_j(g*) > 0. The
cascade (j needs compensation, and so on) is what the distance-3 and distance-4 cases show. The simple rule "u takes
its best junk good of a threatening bundle, up to three times" already works on 99% of the completions.
