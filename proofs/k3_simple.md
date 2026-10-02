# K3S: a simpler statement of the k = 3 algorithm

Workstream `proof/k3-simplify`. Code: `k3/simplify/k3s.py` (the algorithm), `k3/simplify/lbx.py` (K3ALG's Stage L
with pluggable rules), `k3/simplify/test_k3s.py` and `k3/simplify/exp_*.py` (experiments). Logs: `results/k3_simplify/`.

**Status.**
- §3 gives a written proof that K3S always returns an EFX₀ allocation with at most one bundle of more than two
  goods. It is a short list of changes to the proof of construction LB⁺ (`paper/k3/long.tex` §5;
  `proofs/lb_last_step.md`). One independent referee report found no error (its wording fixes and one missing
  citation are applied below). It is **not machine-checked**.
- §5 is evidence: raw EFX₀ checks of K3S on every ranking profile of every core with n ≤ 5, samples of every
  certified core with n = 6, 7, 8, every ranking profile with n = 4 agents on up to 7 goods, and 5 million random
  instances. K3S never failed (about 240,000 of these runs used the rotation).
- §4 is a list of simplifications that **fail**, each with its smallest failing configuration.
- Lemma T (§3.6) is new and is proved here: when the absorber r fails, every leader is exposed.
- The referee's own checker found no failure. It also checked the bad-case structure and Lemma T on every rotation,
  on every instance with n = 2, m ≤ 6 and with n = 3, m = 4 (values including ties, a = b + c, top-heavy agents and
  agents valuing 0–3 goods); on every tie-free instance with n = 4, m = 5; and on 1.74 million random
  rotation-heavy instances.

## 1. The algorithm

The input is n agents and m goods with additive values v_i(g) ≥ 0. Each agent positively values at most three goods,
ranked by value, largest first, with ties broken by index. a_i, b_i, c_i are agent i's first, second and third good.

> **K3S**
> 1. **Draft.** The agents take turns. Each takes its favourite remaining good, or nothing if none of its goods is
>    left. The next agent is one that *can be peeled*: its favourite remaining good is worth at least all its other
>    remaining goods together. That holds for every agent that has lost a good, values at most two goods, or has
>    a ≥ b + c. If no agent can be peeled, any agent goes; it is a *leader* and takes its top.
> 2. **Upgrades.** Repeat: if an agent with a ≤ b + c holds its b, its c is left over, and nobody needs b alone,
>    it also takes c.
> 3. **Absorber.** r is the last agent of the draft that was not upgraded. For every exposed agent, put one of its
>    goods b, c into the bundle of a free agent other than r, one good per free agent (HitSet). Then r takes every
>    other leftover good.
> 4. **Rotation**, only if step 3 runs out of free agents. k, the last exposed agent, gives up its top and takes its
>    b and c. Its top goes to an agent that needs it, that agent's old good goes to an agent that needs that good,
>    and so on along a need chain, which ends at r. Then k is the absorber, as in step 3.

The words are those of the paper:
- an agent *needs* the goods it ranks above the good it holds, or all its goods if it holds none; upgraded agents
  need nothing;
- an agent is *free* if it is not upgraded and nobody needs its good alone (agents holding nothing are free);
- an agent x ≠ o is *exposed* (for the absorber o) if its values are strictly balanced (a < b + c), it is not
  upgraded, it holds its top a, and each of its b and c is left over or in o's *base*: o's good, or b_o and c_o if o
  is upgraded;
- *HitSet* takes one leftover good of {b_x, c_x} per exposed agent x. If two exposed agents share a leftover good,
  it uses that one good for both. The code removes a repeated entry, which changes nothing: a good can repeat only
  when two pairs share a leftover good, and then the list has |E| − 1 entries, which fit by Lemma `count`.

**Two goods per agent.** If every agent values at most two goods, every agent can always be peeled. So there are
no leaders, and no agent is upgraded (that needs three goods) or exposed (exposed agents are leaders, Lemma `lead`).
K3S is then exactly serial dictatorship in index order, with the last agent taking all leftovers: the algorithm of
Corollary L2c. Checked on 1,000,000 random instances (`results/k3_simplify/k3s_sd2.log`).

So K3S is the two-goods algorithm plus three additions: leaders, upgrades with protecting goods, and one rotation.
Each addition is forced by a small instance (§4 and the examples in `paper/k3/long.tex` §8).

## 2. Differences from K3ALG

| | K3ALG (`proofs/k3_algorithm.md`) | K3S |
|---|---|---|
| peeling | Stage R removes peelable agents, then Stage L drafts with R1 priority | one draft; peelable agents go first |
| leftovers | fill every free slot first; no absorber if everything fits | the absorber takes everything except HitSet |
| slots | 1 per free agent with a good, 2 per free agent without | 1 per free agent |
| who rotates | k* = the exposed agent of r's block (blocks of Phase 1) | k = the last exposed agent; no blocks |
| when to rotate | only if \|J\| > S, and then if \|HitSet(E_r)\| > S − cap(r) | if HitSet(E_r) has more entries than there are free agents other than r, whatever the number of leftovers |

Upgrades, HitSet and the rotation are K3ALG's, unchanged. Blocks are still used in the proof.

## 3. Correctness

Labels refer to `paper/k3/long.tex` (lemma `inv`, lemma `upgrades`, theorem `sound`, lemma `owner`, lemma `r`,
lemma `lead`, lemma `chains`, lemma `count`, theorems `A` and `B`). Each step below says what changes.

**Types of agents.** Call agent i *strict* if it values exactly three goods and v_i(a_i) < v_i(b_i) + v_i(c_i);
these are the only agents a leader can be. Every other agent is *easy*: it values at most two goods, or three with
v_i(a_i) ≥ v_i(b_i) + v_i(c_i). An agent can be peeled at a moment of the draft iff it is easy, or it is strict and
has lost one of its goods. Proof: a strict agent with all three goods left has favourite a < b + c. A strict agent
with at most two goods left has a favourite worth at least the other one. An easy agent with three goods left has
a ≥ b + c. An easy agent with at most two goods behaves like the strict case.

So easy agents can always be peeled, and all of them are processed before the first leader. Every block after a
leader contains only strict agents, which is why the paper's arguments carry over to those blocks unchanged.

### 3.1 The draft

Blocks: block 0 is the run of turns before the first leader (possibly empty), and block β ≥ 1 is the β-th leader
with the turns after it, up to the next leader.

- (I1) and (I2) hold for any order, as in the paper.
- (B1) When a leader goes, every unprocessed agent is strict and still has all three goods. This is the
  characterisation above.
- (I3) A strict agent that finds all its goods available at its turn is a leader. Again by the characterisation.
- (B2) A good that agent j lost was picked earlier *in j's block*. For j in block β ≥ 1 the paper's proof applies
  with (B1). For j in block 0 it holds because block 0 is a prefix of the draft.

### 3.2 Upgrades

The upgrade loop runs only over agents with three goods and a ≤ b + c. Lemma `upgrades` holds as stated: the state is
valid ((V1) leftover goods are needed by nobody, by (I2); (V2) b_u, c_u ∉ NA), and (UT) holds for every agent that the
loop may upgrade.

### 3.3 Soundness

Theorem `sound` holds with the owner constraint required only for strict agents:

> (OC′) no strict agent x ∉ U, x ≠ o, holding a_x has both b_x and c_x in the absorber's bundle.

The proof is the paper's, with one more case at the end. Take agent i ∉ U holding a good, and a bundle X_j of at
least two goods with two of i's goods. Those two goods are ranked below i's good, so i holds a_i and they are b_i and
c_i.
- If |X_j| = 2, the threat is v_i(b_i) ≤ v_i(a_i).
- If |X_j| ≥ 3, then X_j is the absorber's bundle.
  - An easy agent i has v_i(X_j ∖ {h}) ≤ v_i(b_i) + v_i(c_i) ≤ v_i(a_i).
  - A strict agent i is excluded by (OC′).

The other cases (i ∈ U, holding nothing, at most one good of R_i in X_j) are the paper's. Upgraded agents have
a ≤ b + c by step 2.

### 3.4 The absorber takes everything

Lemma `owner` (b) shows that a completion with owner o satisfies (OC′) when H meets every exposed pair and every good
of H goes into a slot. Its proof never uses that the other slots are filled, or that ω ≥ 1. So "o takes all leftovers
except H" is such a completion, provided H fits:

> o is a *valid absorber* if HitSet(E_o) consists of leftover goods, one per exposed pair (or one shared good for two
> pairs), and has at most as many entries as there are free agents other than o.

With one slot per free agent, the paper's capacities become cap(i) = 1 for every free agent. The counting below uses
only cap(i) ≥ 1.

### 3.5 The absorber r and the rotation

- **Lemma `r`.** (A0) The first agent of the draft takes its top, or holds nothing, so it is not upgraded. (A1) and
  (A2) are as in the paper.
- **Lemma `lead`.** An exposed agent is strict by definition, so by (I3) it is a leader. Hence exposed agents lie in
  different blocks β ≥ 1, and π_x ≠ ∅.
- **Lemma `chains`.** By (B2), now including block 0.
- **Lemma `count` and Theorem A.** They hold with S − cap(r) = the number of free agents other than r, and their
  proofs never use ω ≥ 1. If HitSet(E_r) does not fit, then by Proposition `O` (`paper/k3/long.tex`, the HitSet test
  is exact; ledger K3.OWNER), no set of leftover goods meeting every exposed pair fits. Proposition `O`'s proof does
  not use ω ≥ 1 either. So r is not a valid owner in the paper's sense, and *the bad case holds.*
- **k = the last exposed agent.** In the bad case, E_r ∩ B* = {k*}, where B* = r's block is the last block (remark
  after Lemma `r`). Every other exposed agent leads an earlier block, so k* is the last exposed agent of the draft.
- **The chain.** K3S scans the agents after k in draft order. It appends j whenever the current agent is frozen,
  j ∉ U and j needs the current agent's good. If the current agent is frozen, every agent that needs its good
  comes later in the draft (I1), so the scan reaches one. So the scan ends at a free agent and yields a need chain.
  By the bad case (ii), it ends at r.
- **Theorem B.** It holds as stated.
  - In (e) ("x = r is impossible"), r ∈ E′_k needs r to be strict. A strict r is in the upgrade loop's range, so
    (UT) applies to it.
  - (d) and (g) use only cap ≥ 1.
  - So after the rotation, k is a valid absorber, whatever the number of leftovers.
- **Conclusion.** Every output of K3S is a completion of a valid pre-allocation that satisfies (OC′). By §3.3 it is
  EFX₀, and only the absorber's bundle can have more than two goods.

### 3.6 Lemma T: when r fails, every leader is exposed

**Lemma T.** If r is not a valid absorber, then block 0 is empty and every leader is exposed for r. Moreover, every
block other than B* has exactly one free agent, and B* has no free agent other than r.

*Proof.* Every non-empty block β contains a free agent: its last agent z_β that is not upgraded.
- Such an agent exists. A leader takes its top, so it is not upgraded. In block 0, the first agent takes its top or
  nothing.
- If some j ∉ U needed z_β's good, then by (B2) j would be a later agent of the same block, contradicting the choice
  of z_β.

The agents z_β are distinct, and the one of B* is r. Let F be the number of free agents other than r; then
F ≥ (number of non-empty blocks) − 1. On the other side, HitSet(E_r) has at most |E_r| entries, and
|E_r| ≤ number of leaders by Lemma `lead`. If r fails, HitSet(E_r) has more than F entries, so

  number of leaders ≥ |E_r| ≥ F + 1 ≥ number of non-empty blocks = number of leaders + [block 0 is non-empty].

So block 0 is empty and every inequality is an equality. |E_r| = number of leaders, so every leader is exposed. F is
exactly the number of blocks minus 1, so the free agents other than r are exactly the agents z_β with β ≠ B*. ∎

*Consequences.*
- If any agent can be peeled at the start of the draft, block 0 is non-empty, and K3S never rotates.
- To avoid the rotation, a leader rule would have to make sure that **one** leader is never exposed. §4.1 shows
  that the simple rules tried do not achieve this.

Checked on data: all 1,188 bad cases at n ≤ 4 (every profile) and in a sample at n = 5 have every leader exposed
(`k3/simplify/exp_leaders.py`).

## 4. What did not work

Each item has its own file in `attempts/` with the smallest failing configuration and the script that reproduces it.

| Simplification | Smallest failure | Attempts file |
|---|---|---|
| "2 goods each": two-round drafts, snake order or top two at once, then the last agent absorbs | n = 3, m = 4 (snake); n = 2, m = 3 (others) | `k3s-two-goods-each.md` |
| "2 absorbers": one good each, the leftovers split between two agents (best split, any pair) | n = 3, m = 5 | `k3s-two-absorbers.md` |
| no rotation, with a simple leader rule (6 rules) | n = 3, m = 5 (4 rules); n = 4, m = 6 (2 rules) | `k3s-leader-rules.md` |
| restart instead of rotation (x takes {b, c} and the draft is redone; or x may not lead) | n = 5, m = 7; n = 4, m = 7 | `k3s-restart.md` |
| no upgrade step (the rotation covers it) | n = 2, m = 5 | `k3s-no-upgrades.md` |
| one pass of upgrades in draft order instead of the loop | n = 3, m = 5 | `k3s-single-pass-upgrades.md` |

## 5. Evidence

Raw EFX₀ checks (`k3/simplify/test_k3s.py`). Values are the three balanced realizations (4, 3, 2), (10, 9, 2),
(10, 6, 5) on cores, (4, 3, 2) on all small profiles, and values 1–6 with ties, a = b + c, top-heavy agents and
agents valuing 0–3 goods on random general instances.

| Test | Profiles or instances | Rotations | Failures | Log |
|---|---|---|---|---|
| every profile of every core, n ≤ 5 (× 3 realizations) | 2,446,840 | 33,104 | 0 | `k3s_cores_5.log` |
| random profiles of every certified core, n = 6 (300 per core, × 3) | 962,100 | 4,536 | 0 | `k3s_cores_6_sample.log` |
| random profiles of every certified core, n = 7 (20 per core, × 3) | 823,400 | 1,352 | 0 | `k3s_cores_7_sample.log` |
| random profiles of every certified core, n = 8, m ≥ 14 (100 per core, × 3) | 128,500 | 13 | 0 | `k3s_cores_8_sample.log` |
| every ranking profile, n = 2, m ≤ 7; n = 3, m ≤ 8; n = 4, m ≤ 5 (worthless goods allowed) | 406,068 | 7,984 | 0 | `k3s_small_upto_4_5.log` |
| every ranking profile, n = 4, m = 6 | 1,728,000 | 33,168 | 0 | `k3s_small_4_6.log` |
| every ranking profile, n = 4, m = 7 | 9,261,000 | 147,336 | 0 | `k3s_small_4_7.log` |
| random ranking profiles, n ≤ 9, m ≤ 2n + 3 | 2,000,000 | 10,705 | 0 | `k3s_rprof.log` |
| random general instances, n ≤ 9 | 2,000,000 | 308 | 0 | `k3s_random.log` |
| ≤ 2 goods per agent: K3S = serial dictatorship | 1,000,000 | — | 0 differences | `k3s_sd2.log` |

The logs are in `results/k3_simplify/`. "Every ranking profile" fixes agent 0's ranking as 0 ≻ 1 ≻ 2 (relabelling the
goods), and goods nobody ranks are worthless. These instances are not cores, so they also test what Stage R would
have removed.

Earlier runs of the intermediate variants: `results/k3_simplify/variants_n5_all.log` (every profile of every core
with n = 5) and `variants_n6_sample.log` (4.8 million profiles at n = 6). The variant "upgrades, absorber takes all,
k = last exposed" with two slots for agents holding nothing had 0 failures. The variant without upgrades failed 3
times.

## 6. What remains

- A referee of §3.
- A Lean proof. The Lean development proves LB⁺ for every order with R1 priority, and K3S's Stage L is one such
  run up to the three changes of §2. The merged draft, one slot per free agent and "absorber takes all" would need
  new lemmas.
- Whether the rotation can be avoided. No fixed leader rule tested does it (§7), but choosing the first leader by a
  search does, on every case tested (Conjecture FL, §7). A proof would give a rotation-free algorithm.

## 7. Without the rotation (evidence, open)

**When the rotation can occur.** By Lemma T it is needed only if nobody can be peeled at the start, that is, only on
instances where every agent values exactly three goods with a < b + c. On 300,000 random general instances, K3S
rotated 54 times, each time on such an instance.

**Fixed leader rules do not remove it.** See `attempts/k3s-leader-rules.md`. The best is construction LB's lookahead
(the leader leaving the fewest goods needed alone). With K3S's absorber it still needs the rotation on 30 of the
2,445,840 core profiles with n ≤ 5, and on 12 of the 3,600 ranking profiles with n = 3, m = 5.

**Conjecture FL (first leader).** On every instance, some choice of the *first* leader of the draft (later leaders by
smallest index) makes step 3 succeed. So the following rotation-free algorithm would always work:

> run steps 1–3 with each agent in turn as the first leader, and return the first run in which step 3 succeeds.

Evidence (`k3/simplify/exp_first_leader.py`, log `results/k3_simplify/first_leader.log`). Each row counts the
profiles on which K3S with index leaders needs the rotation. In every one of them some first leader works, and so
does some choice of the *last* leader (Conjecture LL).

| Set | Profiles needing the rotation | Fixed by choosing the first leader | Fixed by choosing the last leader |
|---|---|---|---|
| every profile of every core, n ≤ 5 | 33,104 | 33,104 | 33,104 |
| every ranking profile, n = 3, m = 8 | 1,960 | 1,960 | 1,960 |
| every ranking profile, n = 4, m = 5 | 4,344 | 4,344 | 4,344 |
| every ranking profile, n = 4, m = 6 | 33,168 | 33,168 | 33,168 |
| cores n = 6, 300 random profiles per core | 4,536 | 4,536 | 4,536 |
| 1,000,000 random ranking profiles, n ≤ 9 | 6,072 | 6,072 | 6,072 |

On average 58–79% of the agents work as the first leader. No fixed choice always works, so the search is needed:
- the agent that was r in the failed run works on 1,643 of 1,648 profiles (n ≤ 4);
- the agent whose b and c are valued by the most agents works on 1,618 of 1,648
  (`results/k3_simplify/first_leader_static_rules.log`).

**Is this simpler?** It is shorter to state ("restart from another first leader") and needs no need chains. But it
costs up to n runs, and Conjecture FL has no proof. The rotation is one local step with a proof (Theorem B). A
proof of FL could start from Lemma T: it would suffice to show that for some first leader, some leader of the
resulting draft is never exposed, or some block ends with two free agents.
