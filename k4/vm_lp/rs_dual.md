# The LP view of RKMAX's min-rank-sum form: dual prices at RS-optimal starts (workstream proof/k4-vm)

Branch `claude/k4-vm`. This is the coordinator's task: the LP/duality angle on the RS form of Conjecture RKMAX
(K4.SDC.RKMAX; RKMAX itself is owned by proof/k4-rkmax, PR #158, which was told of this angle).
- Code: `k4/vm_lp/`. It uses `rklib_copy.py`, an unchanged read-only copy of `k4/rkmax/rklib.py` at `ebd17e7` on
  proof/k4-rkmax, for OC₁.
- Logs: `results/k4_vm_lp/`.
- Everything below except Lemma RSD is evidence (PROMPT.md §5 rule 3).

## Status

- **Lemma RSD** (proved): at a perfect-agent maximum matching, RS-optimality is equivalent to the existence of dual
  prices on goods. Those prices are a potential that rises along the wants digraph and is capped at every agent that
  values junk.
- **The candidate dual certificate is refuted.** The statement was: at an RS-optimal start, if every dangerous agent
  has slack in its dual junk cap then the picks complete; otherwise a chain read off the tight dual constraints
  repairs.
  - It fails on 160 of the 10,840 RS-optimal starts that need a move, in the certifier's n = 4 failure export.
  - It fails on random n = 4 cores.
  - The smallest counterexample has n = 4, m = 6 (`attempts/k4-vm-lp-rs-dual.md`, independent replay).
- **Why.** The obstruction to a one-absorber completion is cardinal: an observer values the absorber's pick plus the
  junk above its own pick. The RS LP sees only ranks.
- **What survives** (evidence):
  - RS-optimal starts satisfy OC₁ everywhere tested;
  - at 10,680 of the 10,840 move-needing export starts, a canonical chain from a tight dangerous agent repairs.

## 1. The RS LP and its dual

Let Y be a maximum matching that matches every agent (ν = n; every hypergraph of the certifier's n = 4 export has
ν = 4). Write rank_i(g) = 1 + #{h ∈ R_i : v_i(h) > v_i(g)}, J for the junk (goods Y leaves free), and
RS(Y) = Σ_i rank_i(Y_i). The RS LP is

  min Σ rank_i(g) x_ig over relevant edges, s.t. Σ_g x_ig = 1 for every agent, Σ_i x_ig ≤ 1 for every good, x ≥ 0.

Its polytope is integral (bipartite), so its optima are the RS-optimal perfect-agent matchings.

**Lemma RSD (proved).** Y is RS-optimal iff there are prices β on goods with:
- (a) β ≥ 0, and β_g = 0 for every g ∈ J;
- (b) β_g ≥ β_{Y_i} − (rank_i(g) − rank_i(Y_i)) for every agent i and every g ∈ R_i.

In particular:
- (c) if i wants Y_j, then β(Y_j) ≥ β(Y_i) + (rank_i(Y_i) − rank_i(Y_j)) > β(Y_i): prices strictly rise along the
  wants digraph, which is therefore acyclic;
- (d) the **junk cap**: if x values a junk good g, then β(Y_x) ≤ rank_x(g) − rank_x(Y_x).

*Proof.* The dual LP is max Σ_i α_i − Σ_g β_g subject to α_i − β_g ≤ rank_i(g) on edges and β ≥ 0.
- (⇒) Take an optimal dual. Complementary slackness with Y gives α_i = rank_i(Y_i) + β(Y_i), and β_g = 0 for every good
  Y leaves free. Substituting α into the edge constraints gives (b).
- (⇐) Put α_i = rank_i(Y_i) + β(Y_i). Then (α, β) is dual feasible by (a) and (b), and its value is
  Σ_i rank_i(Y_i) + Σ_i β(Y_i) − Σ_g β_g = RS(Y), because β vanishes on J. So Y is optimal.
- (c) and (d) are (b) for the edges (i, Y_j) and (x, g). ∎

The least prices β_min are a longest-path potential (`rs_dual.beta_min`, a Bellman–Ford relaxation). A junk cap (d)
that holds with equality at β_min means an RS-neutral alternating path: x steps down to a junk good, and its wanters
shift up along tight arcs. Lemma RSD is the dual form of Lemma COMP for the rank sum (`k4/rkmax.md` §1): RS-optimal ⇔ no
rank-sum-lowering cycle or chain.

## 2. The candidate certificate and its tests

The dangerous agents x at an RS-optimal Y are taken in two senses:
- D_T: rklib's *truly dangerous* agents, frozen and threatened by the bundle J at p_x;
- D\*: frozen agents with v_x(J) > p_x.

The *slack* of x is min over junk g ∈ R_x of (rank_x(g) − rank_x(Y_x)) − β_min(Y_x) ≥ 0.

The candidates tested (`rs_dual_full.py`, `rs_dual_rand.py`):
- **D1**: if every dangerous agent has slack > 0, the picks have a one-absorber completion.
- **D2**: if the picks need a move, a *canonical tight chain* repairs. In that chain, x₀ is a tight dangerous agent
  ending with junk only, and every other changed agent has a tight wants-arc into x₀.
- **D2wide**: if the picks need a move, some repairing official move changes only agents in the backward closure of
  the tight dangerous agents along tight wants-arcs.

| data | RS-optimal starts (need a move) | D1 fails | D2 fails | D2wide fails | log |
|---|---|---|---|---|---|
| certifier's n = 4 failure export (111,600 profiles, D_T) | 213,120 (10,840) | 160 | 160 | (not run with D_T) | `rs_dual_export_n4_DT.log` |
| the same, D\* | 213,120 (10,840) | 160 | 160 | 160 | `rs_dual_export_n4_Dstar.log` |
| random strict n = 4 cores (3,000), D_T | 4,440 (11) | 5 | 5 | 5 | `rs_dual_rand_cores_4_3000_301_DT.log` |
| the same, D\* | 4,440 (11) | 2 | 3 | 3 | `rs_dual_rand_cores_4_3000_301_Dstar.log` |
| random strict n = 5 cores (1,000) | 1,671 (0) | 0 | – | – | `rs_dual_rand_cores_5_1000_302_*.log` |

**Consistency with proof/k4-rkmax.** On the export, the RS optima number 213,120, and 10,840 of them need a move. That
is exactly rkmax's count for RS (`k4/rkmax.md` §2), from code that shares only rklib's OC₁. No RS-optimal start fails
OC₁ in any data set here.

**The smallest counterexample** (to D1, D2 and D2wide, in both senses) is the random core `cores:4:3000:301` #2548:
n = 4, m = 6, with sets [[0,2,3,4],[1,2,3,5],[2,4,5],[3,4,5]] and values [[4,6,3,8],[6,7,10,2],[3,4,2],[4,3,2]].
- It is a connected k = 4 core (`is_core4` passes).
- Y = (4, 2, 5, 3) has the least rank sum, 7, among the 38 perfect-agent matchings.
- Its least prices exist, β = {2: 1, 3: 2, 4: 2}.
- No frozen agent values the junk {0, 1} above its pick, so every slack condition holds vacuously.
- Yet the picks have no one-absorber completion:
  - all junk on the receiver 2 is envied by agent 1 (v₁({5, 0, 1}) = 2 + 6 = 8 > 7);
  - on agent 0, by agent 2;
  - on agent 1, by agents 0 and 2;
  - on agent 3, by agent 1.
- One ring with junk repairs it: ({0, 2}, {1, 5}, {4}, {3}).
- Independent replay: `attempts/k4_vm_lp_rs_dual.py`.

## 3. What this says about a dual certificate

The RS LP is ordinal: its constraints compare ranks. Completion at the picks is cardinal. It fails when some observer
values an absorber's bundle above its own pick, and that bundle is the absorber's pick plus junk. In the counterexample
the decisive threat is agent 1 valuing the receiver's pick and one junk good above its own pick, although no junk set
alone threatens anyone.

No condition on β, which depends only on ranks, can separate profiles that agree on ranks but differ in such sums. The
export and random data show that such profiles exist at RS-optimal starts. So a usable LP certificate would have to
come from an LP with cardinal coefficients, for instance the one-absorber completion itself as a flow or LP over
values. That is open; it is not attempted here.

**What survives** (evidence only):
- RS-optimal starts satisfy OC₁ on all data here (213,120 + 4,440 + 1,671 starts), as in proof/k4-rkmax.
- On the export, where the hard starts are, D1 and the canonical tight chain D2 hold at 10,680 of the 10,840
  move-needing RS-optimal starts. The dual names the repairing chain in 98.5 % of the hard cases, but not in all.

Reproduce:
- `python3 k4/vm_lp/rs_dual_full.py results/k4_oc1max/two_move_starts_n4.json.gz [DT|Dstar]`: about 35 min on 4 CPUs;
- `python3 k4/vm_lp/rs_dual_rand.py cores:4:3000:301 [DT|Dstar]` and `... cores:5:1000:302 ...`;
- `python3 attempts/k4_vm_lp_rs_dual.py`.
