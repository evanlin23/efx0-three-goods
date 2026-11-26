# Induction on agents along the serial-dictatorship order

Workstream `proof/k4-sd-induct` (branch `claude/k4-sd-induct`). Angle of the k = 4 campaign (`k4/attack_log.md`):
grow the instance one agent at a time along a serial-dictatorship order, as agent-count results do, using the SD-C
structure of `k4/sdc.md` (§2, §6, §26–§30). Code: `k4/sdind/`; logs: `results/k4_sdind/`. Everything computed is
evidence only (PROMPT.md §5 rule 3). Notation as in `k4/sdc.md`: Y = SD(π) the picks, J the junk (unpicked goods), a
*one-absorber completion* gives every junk good to some agent with at most one agent (the absorber) receiving two or
more.

## Status (burst 4)

- **Proved** (written proofs, short):
  - Lemma D (§1): deleting any agent with its pick is SD-consistent, and the junk stays the same.
  - Lemma F (§1): an agent inserted *first* (holding its top among the goods present) is threatened only by bundles
    of three or more goods.
  - Lemma S and Corollary TP (§3): the exact EFX₀ condition for a one-absorber completion of picks. If every
    pick-frozen agent is alone and the absorber is not frozen, EFX₀ ⟺ nobody is threatened by the absorber's bundle.
  - Lemma U (§3): an unfrozen first agent makes itself safe with its best junk good of the absorber's bundle. Only the
    absorber can be hurt, and only through a two-good bundle whose pick it wants.
  - Lemma BOTH-TP (§5): inserting an agent that holds its top and is wanted by nobody preserves the TP shape with one
    move.
  - Lemma H and Proposition PR-step (§7): prefix-robust completions restrict to every suffix sub-instance. The
    insertion of the first agent succeeds with at most one move unless that agent is wanted at current values, or the
    absorber loses its compensation.
  - Theorem PR-TP (§7): keeping frozen agents junk-free, every insertion of a pick-unfrozen agent succeeds. This
    re-proves Theorems DT and DT⁺ as inductions along any order. The only failing insertions are those of threatened
    frozen agents.
- **Evidence** (reverse-SD insertion; each new agent is first):
  - *Conjecture AB₁* (§3). If an unfrozen agent o is the absorber of some one-absorber completion, some order with o
    last inserts the agents with at most one junk move per step. If no absorber is needed, some order works.
    - Evidence: 17,403 of 17,403 cases (screen, suite, the logged hard profiles, 1,500 random n = 4 and 150 random
      n = 5 profiles).
    - The original form also claimed every unfrozen o when no absorber is needed. That form is **refuted** by a climb
      (`attempts/k4-sdind-ab1-no-absorber.md`, n = 4, m = 7).
  - One move per step along *some* insertion sequence exists on every start that has a one-absorber completion (§2).
  - *Projection* (§3): 91% of completions (random n = 4) are reached with each new agent taking at most one junk good
    from the absorber, permanently.
  - *Chains* (§4): at the insertion where the one-move path breaks, one improving chain (usually from the frozen
    agent just inserted) repairs 92% of the orders.
- **Refuted** (each with an independent replay in `attempts/k4_sdind_attempts.py`):
  - inserting into an arbitrary completion with a bounded repair (`attempts/k4-sdind-every-completion.md`, Q2);
  - Lemma BOTH with one absorber (`attempts/k4-sdind-both-one-absorber.md`, r1179, n = 4);
  - **Lemma BOTH with free completions** (`attempts/k4-sdind-both-free.md`, log174, n = 3, m = 7). An agent with a
    private top cannot always be added to an extending outcome of the rest. Its danger set is a wanter's
    compensation, so a private-top reduction of SD-C would need a rule for *which* outcome to lift;
  - TP-SD-C, i.e. some SD outcome has a TP-shaped completion (`e13_tpsdc.py`): fails at n = 2 (14 of 168 screen
    instances). Frozen agents must sometimes hold junk, with their wanters compensated.
  - AB₁ / PR with "every unfrozen o when no absorber is needed" (`attempts/k4-sdind-ab1-no-absorber.md`, n = 4,
    m = 7, found by `e16_ab1_climb.py`).
  - greedy rules for the one move, with and without lookahead (`attempts/k4-sdind-greedy-moves.md`, §8):
    c4min-pareto-n3-m7 (n = 3) without lookahead, GM4-C (n = 4) with it.
- **Deletion classes** (§6, `e17_classes.py`): for every class of deleted agents except the both agents (the first,
  the last, a frozen agent with its wanters, suffix- or prefix-closed pairs), "the sub-instance's picks extend ⟹ the
  instance's do" fails on 2–25% of cases.
- **Where the angle stands.** Every black-box induction step tried fails at the same configuration: the new agent's
  danger set is exactly the junk that compensates a wanter of a frozen agent (r1179, log174; also hall-local3's
  cascade). So the SD-order structure does not yield an induction on agents. It yields:
  - a bookkeeping order for a global argument (AB₁: choose the absorber, then one move per insertion);
  - the exact local lemmas (D, F, S, U, BOTH-TP);
  - a precise description of the obstruction any induction must carry: *compensation chains*. A frozen agent j can
    hold junk only while its wanters are compensated, and their compensation can be some later agent's danger set.
- **The invariant** (§7).
  - *Prefix-robust* completions are hereditary along the reverse SD order (Lemma H, proved).
  - A step fails only at a first agent that is frozen at current values, or at a compensated absorber (Proposition
    PR-step, proved).
  - *Conjecture PR* (the monotone form of refined AB₁) holds on 15,786 of 15,786 cases.
  - Climbs against the original AB₁: 200 rounds at n ≤ 3 and 40 at n = 5 found nothing. 400 rounds at n = 4 found
    the 3 no-absorber counterexamples.
  - Climbs against the refined form found no counterexample: 800 rounds at n = 4, including the run that broke the
    original, and 300 at n ≤ 3. It also holds at k = 3 on 8,002 cases (§3).
- **Next** (if this angle continues):
  1. the strengthened invariant PR(F), which carries the danger sets of the frozen agents still to come, and its
     local step (the Hall count with the agents ordered);
  2. a selection rule among the sub-instance's extending outcomes for private tops (log174: the other outcome
     lifts);
  3. PR for the chain states, extending §4: does the state after OC₁'s chain have a PR completion?

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

| insertion sequence | screen (580 starts) | suite (529) | logged hard profiles, n ≤ 4 (2,393) | random n = 4, seed 92 (3,234) |
|---|---|---|---|---|
| SD order (new agent last), best order producing Y: least step 0 / 1 / 2 / 3–6 / some level empty | 16 / 158 / 192 / 196 / 18 | 15 / 157 / 147 / 190 / 20 | | |
| reverse SD order (new agent first), first order producing Y: some level empty | 25 | 25 | | 237 |
| **reverse SD order, best order producing Y: least step 0 / 1 / 2+** | **298 / 282 / 0** | **249 / 280 / 0** | **1,276 / 1,115 / 2** | **1,341 / 1,890 / 3** |
| any insertion sequence: least step 0 / 1 / 2+ | 298 / 282 / 0 | 249 / 280 / 0 | 1,276 / 1,117 / 0 | 1,341 / 1,893 / 0 |

So:
- one move per insertion always suffices for *some* insertion sequence;
- the reverse SD order is as good as any sequence, except on 5 starts (`e2_paths_n4.log`, `e2_paths_logs.log`, which
  print them). Each of those 5 has only frozen absorbers: every one-absorber completion's absorber is wanted by
  someone, so it cannot be last in an order producing Y. The good sequences insert it first, before its wanter;
- the SD order (new agent last) needs up to 6 moves, and on 18 screen and 20 suite starts some intermediate
  sub-instance has no one-absorber completion at all.

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
  **Refuted in the "no absorber needed" clause** by an adversarial climb (`e16_ab1_climb.py`,
  `attempts/k4-sdind-ab1-no-absorber.md`; 3 instances with n = 4, m = 7). When every completion gives each agent at
  most one junk good, some unfrozen agent may not be put last.
  *Refined AB₁:* (i) if o holds two or more junk goods in some one-absorber completion, some order with π_n = o works;
  (ii) if no completion needs an absorber, some order works. The curated and random data below satisfy the original
  form, hence the refined one. Climb against the refined form, n = 4, the same 400 rounds × 150 steps and seed that
  found the 3 counterexamples (`e16_ab1_climb_n4_refined.log`): no counterexample; the lowest final fraction of
  working orders is 1/6. Two more climbs found nothing either: 400 rounds × 200 steps at n = 4 (seed 6) and 300 × 100
  at n ≤ 3 (`e16_ab1_climb_n4_refined_b.log`, `e16_ab1_climb_n3_refined.log`).
- *At k = 3* (1,000 random profiles of the certified n = 5 cores of `results/certs_5_6.json.gz`; `e18_mono_k3.log`),
  the monotone form holds on all 8,002 cases (Y, o). On 300 profiles, reverse-SD insertion with one move per step
  works on all 688 starts that have a one-absorber completion.
  Evidence: no exception in 901 screen, 841 suite, 5,658 logged hard profiles (n ≤ 4), 8,364 random n = 4 and 1,639
  random n = 5 cases (`e7_absorber.log`, `e7_absorber_more.log`). With o fixed, every order works in 90–97% of these
  cases.
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

**One absorber: refuted** (`e11_both.py`, `results/k4_sdind/e11_both.log`; `attempts/k4-sdind-both-one-absorber.md`). The repair "u takes the absorber's
junk good that makes it safe and costs the absorber least; if the absorber is then threatened by a two-good bundle
{Y_j, g_j}, j hands g_j to the absorber" works from every completion on screen and suite (888, 1,526). On 1,500
random n = 4 profiles it fails 4 times, and on r1179 the sub-instance extends with one absorber while I has no
one-absorber completion at all. There the absorber's junk is both its compensation for wanting a two-good holder's
pick and the new agent's danger set; the free completions of I use two absorbers.

**Free completions: refuted** (`e12_both_free.py`, `results/k4_sdind/e12_both_free.log`,
`results/k4_sdind/e12_both_free_logs.log`; `attempts/k4-sdind-both-free.md`). The free form (if the picks of
I − u − Y_u have an EFX₀ completion with any number of absorbers, so do the picks of I) survived every random test,
in the strong form that *every* completion of the sub-instance is within 4 junk moves of one of I:

| data | cases (Y, u) | completions X′ tested | least distance 0 / 1 / 2 / 3 / 4 | sub extends, I does not |
|---|---|---|---|---|
| screen (n ≤ 5) | 148 | 2,019 | 1,294 / 721 / 3 / 1 / 0 | 0 |
| suite (n ≤ 5) | 166 | 35,134 | 16,588 / 18,542 / 3 / 1 / 0 | 0 |
| random n = 4 (3,000 profiles, seed 7) | 10,868 | 582,202 | 375,694 / 206,117 / 361 / 27 / 3 | 0 |
| random n = 5 (300 profiles, seed 8) | 1,701 | 96,642 | 76,044 / 20,587 / 10 / 1 / 0 | 0 |
| random n ≤ 3 (3,000 profiles, seed 5) | 6,932 | 45,620 | 22,537 / 23,054 / 22 / 6 / 1 | 0 |
| logged hard profiles (n ≤ 5) | 4,502 | 380,531 | 293,111 / 87,266 / 120 / 25 / 6 (and 3 with no completion of I) | **1 (log174)** |

It fails on a logged hard profile, log174 (n = 3, m = 7):
- agent 0 has the private top 5 (31) and the danger set {3, 0} (24 + 10);
- agent 2 wants agent 1's pick 2 (65 > 27), and it is compensated only by {3, 4, 0} (27 + 15 + 24 = 66). This
  compensation is what lets agent 1 hold the junk {1, 6} it needs;
- with agent 0 present, agent 2's compensating bundle threatens agent 0, so the picks (5, 2, 3) have no EFX₀
  completion. The sub-instance has 3.

SD-C holds on log174 via the other outcome (5, 6, 2). So the private-top reduction is not refuted as a statement
about SD-C, but it needs a rule choosing the outcome of the sub-instance to lift.

**Repairs and potentials tried for BOTH** (`e14_both_pot.py`, `e15_sink.py`; logs of the same names).
- *One move from a well-chosen X′.* Some completion of the sub-instance reaches one of I by giving u at most one junk
  good in 5,141 of 5,142 random n = 4 cases; r1179 is the exception.
- *Potentials.* Taking every maximizer of one of seven potentials fails on 1–16 of those cases each. The potentials
  were utilitarian welfare (either sign), u's exposure (value of its junk in large bundles), the number of junk goods
  in large bundles, leximin, and junk held by valuers (either sign).
- *The sink rule* (u absorbs whatever threatens it or makes others threatened; junk moves only to u) fails from 0.7% of
  the starting completions, in 5% of the random n = 4 cases. The failure: u's growing bundle threatens someone.

**Lemma BOTH-TP (written proof).** Let u be a both agent of Y and X′ a one-absorber completion of the picks of
I − u − Y_u of TP shape: pick-frozen agents alone, the absorber o not pick-frozen. Then I has a TP-shaped one-absorber
completion within one junk move of X′.

*Proof.*
1. *The pick-frozen agents are the same in I and in I − u − Y_u.* u wants nothing, since it holds its top, and
   nobody wants Y_u.
2. *Reduction.* By Corollary TP (absorber o), X = X′ + (u ↦ {Y_u}) is EFX₀ iff no agent other than o is threatened
   by X_o. Only u's safety is new.
3. *If u is threatened,* it takes its best junk good g of X_o.
   - u is then safe (Lemma U).
   - The shape stays TP: u is not frozen and holds one junk good.
   - θ_i(X_o ∖ g) ≤ θ_i(X_o) for every i. Removing a good lowers the value by v_i(g), and the minimum rises by at most
     that much.

   So by Corollary TP the result is EFX₀. ∎

TP shapes do not always exist (TP-SD-C fails at n = 2), so BOTH-TP gives no reduction for SD-C. It shows that the
whole difficulty of both-agent insertion lies in completions where frozen agents hold junk, i.e. in compensation.

## 6. Which deletions a black-box induction could use (`e17_classes.py`, `results/k4_sdind/e17_classes.log`)

A black-box induction step deletes a set D of agents with their picks (Lemma D) and needs: *if the picks of
I − D extend, so do the picks of I*. Violations, i.e. cases where I − D extends and I does not:

| class of D | screen (n ≤ 5): violations / cases, free | one-absorber | random n = 4 (500 profiles, seed 93): free | one-absorber |
|---|---|---|---|---|
| a both agent (top, unwanted) | 0 / 148 | 0 / 148 | 0 / 1,826 | 0 / 1,826 |
| an agent holding its top (first) | 116 / 1,479 | 137 / 1,479 | 50 / 3,055 | 65 / 3,055 |
| an unwanted agent (last) | 152 / 1,206 | 172 / 1,206 | 59 / 2,880 | 68 / 2,880 |
| a frozen agent with all its wanters | 385 / 1,707 | 413 / 1,707 | 174 / 1,535 | 192 / 1,535 |
| a frozen agent with one wanter | 429 / 2,089 | 460 / 2,089 | 185 / 1,759 | 203 / 1,759 |
| a suffix-closed set, at most 2 agents (first agents of some order) | 437 / 2,797 | 491 / 2,797 | 205 / 6,806 | 236 / 6,806 |
| a prefix-closed set, at most 2 agents (last agents of some order) | 302 / 3,131 | 356 / 3,131 | 126 / 6,981 | 152 / 6,981 |

Only the both agents come close to safe, and they fail too: r1179 (one absorber) and log174 (free), §5. Every other
class fails on 2–25% of its cases. That is expected: not every SD outcome extends, and the failure of an outcome
usually survives the deletion of any agent not involved in it. So an induction on agents along the SD order cannot
take its hypothesis as a black box. It must carry a choice of outcome and completion. The obstruction in every
refuted step is the same: the new agent's danger set is a wanter's compensation (§5).

## 7. Prefix-robust completions: the invariant the reverse-SD induction carries

**Definition.** Let Y = SD(π), with o = π_n, and let X be a one-absorber completion in which every agent other than o
holds Y_i and at most one junk good g_i (g_i = ∅ if none). X is *prefix-robust* (PR) for π if for every k < n, agent
π_k is not threatened by

  X_o ∪ g_{π_1} ∪ … ∪ g_{π_{k−1}},

i.e. by the absorber's bundle with the junk of every agent *before* π_k in π handed back to it. For k = 1 this is
plain EFX₀ toward X_o, and every PR completion is EFX₀ (Lemma S: the other conditions do not involve X_o).

**Conjecture PR (= monotone refined AB₁; `e18_mono.py`, `results/k4_sdind/e18_mono.log`).**
- If an unfrozen agent o holds two or more junk goods in some one-absorber completion of Y, then some order π
  producing Y with π_n = o has a PR completion with absorber o.
- If no completion needs an absorber, some order has a PR completion.

The form "every unfrozen o, when no absorber is needed" is refuted with AB₁ (`attempts/k4-sdind-ab1-no-absorber.md`).
- *Equivalence.* PR is exactly the condition that inserting π_n, π_{n−1}, …, π_1, with each agent taking its own junk
  good g_i from o on arrival and keeping it, passes through EFX₀ allocations. The projection of §3 is EFX₀ on
  {π_k, …, π_n} iff those agents are unthreatened by X_o ∪ g_{π_1} ∪ … ∪ g_{π_{k−1}}; the strongest condition for
  π_k is the one at its own arrival.
- *Evidence.* 15,786 of 15,786 cases (Y, o), in the original (stronger) form: 21 special, 901 screen, 841 suite,
  5,659 logged hard profiles (n ≤ 4), 8,364 random n = 4.

**Lemma H (PR is hereditary along the reverse order; written proof).** Let X be a PR completion for π on I, with
f = π_1 ≠ o. Give f's junk good g_f (if any) back to o, and delete f with its pick. The result X° is a PR
completion for π° = (π_2, …, π_n) on I° = I − f − Y_f.

*Proof.*
1. *Completion.* By Lemma D, the picks of I° are those of π° and its junk is the same J, so X° is a completion. Only o
   can hold two or more junk goods.
2. *Toward singletons and two-good bundles.* These bundles are the same as in X. Every agent's value is at least its
   value in X: o's went up, the others' did not change. By Lemma S their conditions still hold.
3. *Toward o's bundle, now X_o ∪ g_f.* For π_k with k ≥ 2, PR for π_k in I gives that π_k is unthreatened by
   X_o ∪ g_f ∪ … ⊇ X_o ∪ g_f. So X° is EFX₀.
4. *PR for π° in I°.* X°_o ∪ g_{π_2} ∪ … ∪ g_{π_{k−1}} = X_o ∪ g_{π_1} ∪ … ∪ g_{π_{k−1}}, so π_k's PR condition in I°
   is its PR condition in I. ∎

So PR is an induction hypothesis that the instance hands down to every suffix. The induction step is local.

**Proposition PR-step (written proof).** Let X° be a PR completion for π° on I°, with absorber o, and insert f = π_1
with its pick (f holds its top among the goods of I).
1. *f is not threatened by X°_o.* Then X° + (f ↦ {Y_f}) is a PR completion for π on I.
2. *f is threatened by X°_o.* Let g be f's most valuable junk good of X°_o, and let X be X° with g moved to f. X is a
   PR completion for π iff
   - (b) every agent i ∉ {f, o} has v_i(Y_f) ≤ v_i(X°_i), and v_o(Y_f) ≤ v_o(X°_o ∖ g) (nobody wants f's pick at its
     current value), and
   - (c) every two-good holder j has v_o(Y_j) ≤ v_o(X°_o ∖ g) (the absorber is not hurt).

*Proof.*
1. f's singleton threatens nobody. f is threatened only by X°_o (Lemma F, since f holds its top). The PR conditions
   of π_2, …, π_{n−1} are unchanged, because g_f = ∅.
2. f is safe after taking g (Lemma U). The PR condition of π_k (k ≥ 2) involves
   X_o ∪ g ∪ g_{π_2} ∪ … = X°_o ∪ g_{π_2} ∪ …, the same set as before.
   - By Lemma S, the remaining conditions are those toward the new two-good bundle {Y_f, g}, which is (b): the junk
     good g is worth less than every valuer's pick.
   - The other condition is o's, after o loses g. o is threatened only by two-good bundles whose pick it values above
     v_o(X°_o ∖ g): that is (c), together with the o-part of (b). ∎

**What this gives.**
- *Where a step can fail.* Suppose (I, π) has no PR completion but the suffix sub-instance (I°, π°) has one. Then
  for every PR completion X° of (I°, π°) with absorber o, the first agent π_1 is threatened by X°_o, and either π_1
  is wanted at current values or the absorber's compensation is at stake.
- When π_1 is not frozen and o wants no two-good holder's pick (e.g. o holds its top), the step always succeeds.
- So PR is an induction on agents along the reverse SD order whose only failing steps are:
  - *frozen first agents* (frozen at current values) whose danger sets lie in o's bundle;
  - *a compensated absorber*.
- Both have to be prevented earlier in the induction, by the agents π_2, …, π_{n−1} taking the right junk goods. This
  is the lookahead of §3 in its exact form.
- The two refutations of §5 (r1179, log174) are instances of the second and first failure respectively, under the
  absorber the sub-instance happened to use.

**A next target.** Strengthen PR so that the frozen first agents' needs are carried:
- *PR(F)*: a PR completion of a suffix sub-instance whose inflated absorber bundles also avoid the danger sets of a
  given family F of future frozen agents.
- By Lemma H, any PR completion of the whole instance restricts to a PR(F) completion of every suffix, with F the
  frozen agents not yet inserted. The question is whether PR(F) has a local step, i.e. whether a helper can always be
  found among π_2, …, π_{n−1} when F is fixed in advance.
- This is the Hall-type count of `k4/sdc.md` §30, with the agents ordered.

**Theorem PR-TP (written proof): the induction succeeds at every unfrozen agent.** Keep the TP shape throughout:
pick-frozen agents never take junk. Insert the agents in reverse order of an order π producing Y, with π_n = o
unfrozen. At each insertion of f = π_k:
- if f is not threatened by X_o, f takes nothing;
- if f is threatened and pick-unfrozen, f takes its best junk good of X_o.

Then every such step yields a PR completion of the larger sub-instance.

*Proof.* Proposition PR-step, case 2, needs (b) and (c).
- (b): f is pick-unfrozen, so v_i(Y_f) ≤ v_i(Y_i) ≤ v_i(X_i) for every i. For o, X_o ∖ g still contains Y_o.
- (c): in a TP-shaped state every two-good holder j is pick-unfrozen. So v_o(Y_j) ≤ v_o(Y_o) ≤ v_o(X_o ∖ g).
∎

So the reverse-SD induction can fail only when a pick-frozen agent arrives and is threatened by the absorber's
bundle. Two known theorems follow at once:
- *Theorem DT* (distinct tops, `k4/sdc.md` §6): there are no frozen agents, so every step succeeds. This holds for
  every order and every absorber o, with one move per insertion.
- *Theorem DT⁺* (no frozen agent values junk). A frozen x arriving first among the agents present holds its top among
  the goods present. Its only good in X_o is at most Y_o, a single good worth at most v_x(Y_x), so x is never
  threatened.

Beyond DT⁺, a pick-unfrozen agent that is *not* threatened may still take any one junk good of X_o. Its safety and
(b), (c) are unaffected. So the pick-unfrozen agents are free slots, one junk good each, and the frozen agents' danger
sets must be cleared by those slots before the frozen agents arrive. With frozen agents first in π, this is exactly
the static covering of Corollary TP: the count of `k4/sdc.md` §30. The exceptions to the TP shape (A131,
induct-b-r0-pot-minvw at n = 2) are where a frozen agent's wanter is compensated, which PR-TP does not use.

## 8. A greedy lookahead rule for the free slots fails (`e19_lookahead.py`, `results/k4_sdind/e19_lookahead.log`)

Theorem PR-TP leaves one choice: which junk good each pick-unfrozen agent takes on arrival (frozen agents first in π,
so all helpers arrive before them). A greedy rule takes the good with the highest *demand*:
- *need*: the number of frozen agents still to come that value it and are threatened by the absorber's current
  bundle;
- *val*: the number of frozen agents still to come that value it.

Threatened agents choose among the goods that make them safe. Over the cases (Y, o) where o absorbs a TP-shaped
completion (or none is needed):

| data | cases | need | val |
|---|---|---|---|
| screen | 792 | 773 | 752 |
| suite | 736 | 722 | 687 |

The arrangement of the frozen-first orders hardly matters: when some order works, every order does, except in one
suite case per variant. GM4-C and GM4-D are among the failures. A count of demands does not see that a frozen agent needs a *specific* pair removed. The choice has to
solve the frozen agents' hitting-set problem (which goods leave the absorber's bundle) and then match those goods to
the free slots. That is the static covering problem of Corollary TP, i.e. the count of `k4/sdc.md` §30, and nothing
here makes it local.

## 9. OC₁ fails on a core (B<, reported by the coordinator); independent check

The coordinator reports that OC₁ fails on a strict connected k = 4 core, B< (`k4/oc1_hall.md` §16 on the
coordinator's branch, not read here; replay `k4/sdc/oc1_core_cex_verify.py` there).
- Sets [[0,2,3,1],[6,4,5,9],[1,2,3,9],[1,6,7,8],[3,6,9],[1,3,6,9]], values
  [[6,14,16,12],[4,18,12,28],[28,4,16,21],[16,14,12,6],[28,8,24],[20,30,8,4]].
- `k4/sdind/verify_blt.py` (`results/k4_sdind/verify_blt.log`) confirms it with this branch's brute force. Order
  0..5 gives picks (3, 9, 1, 6, –, –). They have no one-absorber completion (8 free ones), and none of the 57 states
  after one improving chain or ring has one. The 54 chains agree between `de_free.moves` and `sdilib.chains`; the
  3 rings come from `de_free` only.
- Agents 4 and 5 get no pick and value only picked goods. Every holder of a good they value must stay alone, so the
  six junk goods go to agents 4 and 5, which makes two absorbers.

Bearing on this note:
- AB₁ and PR presuppose a one-absorber completion, so B< is not a counterexample to them.
- The chain part (§4) is about OC₁, which B< refutes in general. The coordinator states that the K4.MC2 class (no
  agent with two private goods) is the form that still implies TARGET₄; B<'s agents 1 and 3 have two private goods
  each. [unverified here: the reduction itself.]
