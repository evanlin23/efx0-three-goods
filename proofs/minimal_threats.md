# Minimal threats and the boundary of the pair-based proof

Workstream `formal/minimal-threats`. This develops the k-relevant exploration into a
verified specification and small obstructions. It does not prove TARGET₄, ZMOVE, or a
general existence theorem. No literature novelty is claimed. Values in the Lean files
are natural numbers; extension to real values is not formalized here.

## 1. The exact obstruction to safety

Fix agent i and a threshold t. A **minimal threat** T is a duplicate-free set with
v_i(T) > t and v_i(T minus g) ≤ t for every g in T. With nonnegative additive values,
this is inclusion-minimality: any proper subset misses a good and is contained in the
corresponding deletion. Every member of T is relevant to i.

**Theorem.** A complete allocation X is EFX₀ iff no bundle of another agent properly
contains a minimal threat at threshold t = v_i(X_i).

Proof. If T is properly contained in X_j, delete a good in X_j outside T: the remainder
is still worth more than t. Conversely, if deleting h violates EFX₀, repeatedly delete
goods from X_j minus h while its value remains greater than t. This terminates at a
minimal threat, properly contained in X_j. ∎

`lean/EFX/MinimalThreats.lean` proves the finite minimization by induction on list length,
the characterization over duplicate-free lists (`efx0L_iff`), and its equivalence with
the original owner-map model (`efx0_iff`). No hypothesis on relevance counts is used.
Minimal threats form an antichain (`minimal_antichain`).

The **proper** containment condition cannot be dropped. A bundle equal to a minimal
threat is safe: deleting any good makes its value affordable. Appending any new good
makes it threatening, even when that new good is worthless.

## 2. What changes when ordinary bundles grow

If a bundle of size at most b violates safety, a minimal witness has fewer than b goods
(`exists_small_minimal`). In particular, for a bundle of size at most two, a violation
is exactly a singleton need in a bundle with another good (`pair_threat_iff`).

At size three, pairs become relevant. For threshold 3 and good values 2, 2, 0:

* `[0,1]` is safe;
* `[0,2]` is safe;
* `[0,1,2]` is not safe;
* no individual good is worth more than 3, but `[0,1]` is a minimal threat.

`SparseShape.individually_safe_jointly_unsafe` checks these statements in the kernel.
Thus two separately safe modifications need not be safe when performed together.
This is a counterexample to that composition rule, not to EFX₀ existence.

There is an exact incremental rule (`safe_append_iff`). For a new good g outside S,
S plus g is safe at threshold t iff

1. v_i(S) ≤ t, and
2. v_i(g) + v_i(S minus h) ≤ t for every h in S.

When g is worthless, condition 1 is necessary and sufficient (`safe_append_zero_iff`).
Also, every safe bundle is either fully unenvied or itself a minimal threat (`safe_iff`).
These are rules for a fixed observer and threshold. If an exchange changes the observer's
own bundle, its threshold must be recomputed too.

## 3. A strict k = 5 core requiring two triple bundles

The original five-relevant example can be made strict using the repository's verified
tie-breaking construction. `lean/EFX/SparseShapeLimits.lean` uses the rows

```
agent 0: 96 80 72 68 66  0
agent 1: 96 80 72 68  0 65
```

Lean proves: each support has size five; the profile is strict in the existing `Strict`
sense; every good is worth less than the remaining goods to its observer; each agent
has one private good, worth less than its shared goods; the incidence structure is
connected; and no good is junk. These are the relevant natural analogues of the core
conditions. The k = 4 predicate `IsCore4` is deliberately not asserted for this instance.

If one agent has at most two goods, its value is at most 176. The other has at least
four goods, of which at most one is worthless to the first agent. Delete that worthless
good if present, or any good otherwise. At least three relevant goods remain, worth
at least 205, so EFX₀ fails. Both agents must therefore have exactly three goods.
An EFX₀ allocation exists: agent 0 takes `{0,1,4}` and agent 1 takes `{2,3,5}`.

`five_sizes` proves the shape for all owner maps, using an explicit six-coordinate
representation and a kernel evaluation of all 64 cases. `five_not_d2` refutes the
extension of the at-most-one-large-bundle, capacity-two shape to five relevant goods;
`five_exists` proves non-vacuity. No general existence statement is refuted.

The Python checker independently evaluates the raw EFX₀ inequalities on the same 64
owner maps. It finds 8 EFX₀ allocations, all with sizes 3 and 3. This differs from the
14 allocations for the earlier `[129,130,132,136,144,0]` variant: both variants have
the same negative shape conclusion, but their subset-sum orders need not coincide.

## 4. How this helps the k = 4 exchange route

The current live target is ZMOVE (`k4/zmove_hall.md`, `k4/zmove_pot.md`), not the refuted
DL₂ or the refuted one-first-agent rule. Hold the frozen assignments fixed, maximize
robust free agents and then their rank sum, and seek a frozen-chain repair or a lower
deficit key.

The new `exchange_certificate` theorem separates **verification** from **existence**.
Starting with an EFX₀ allocation, it proves a simultaneous exchange sound when unchanged
target bundles stay fixed, unchanged observers do not lose own value, and all directed
envy edges incident to a changed agent satisfy the new minimal-threat specification.
It does not produce an exchange. In particular, the current ZMOVE pre-allocations are
not automatically complete EFX₀ allocations: this theorem cannot be applied to them
without establishing its starting-allocation hypothesis. Its bundle-level lemmas can
be used directly to discharge their owner-safety obligations.

The next mathematical target is still an exchange-closure statement at an optimized
key: either blocked owner candidates permit a joint reassignment that raises robustness,
or one yields a safe completion. This note does not establish that dichotomy. The new
framework makes its missing obligations explicit:

* evaluate all changes jointly, as the composition example requires;
* check other agents observing a modified bundle, including changes by worthless goods;
* recompute thresholds for agents whose own bases change;
* permit a different final owner and the needed-set changes already forced by the suite.

Do not replace this with a claim that every local state improves, or that ordinary
graph matching supplies the exchange: pair assignments are labelled hyperedge packings,
and the required exchange property has not been proved.

## 5. Larger k: necessary capacity, not a sufficiency theorem

The earlier exploration gives a simple necessary lower bound b(k) ≥ ceil(k/2) for a
universal shape in which all but at most one bundle have at most b(k) goods. For k = 2t,
two agents valuing the same 2t goods equally need at least t goods each. For k = 2t−1,
use 2t−2 common goods and one private good per agent: with 2t goods total, a bundle of
size at most t−1 faces one of at least t+1. After one deletion the latter still contains
at least t relevant goods for the first agent. Equal splits with private goods assigned
to their owners are EFX₀. Small binary perturbations preserve the argument and make the
profile strict.

This symbolic bound is a written argument, not yet a Lean theorem. The checker verifies
strict examples for k = 3 through 8. **Sufficiency of ceil(k/2) is not established.**
For k = 5 it suggests exploring triple bases and pair threats, rather than carrying
the singleton-needs model forward unchanged. A proof for all finite k would settle
the full finite additive EFX₀ existence problem.

## 6. Validation and scope

Run from the repository root:

```
python tools/check_minimal_threats.py
python tools/check_ledger.py
lean/check.sh
```

The independent checker compares literal EFX₀ with the minimal-threat specification
on 10,456 allocations. These exhaust allocations of the six named family profiles,
the Lean example, and 40 seeded sampled three-agent profiles. It also checks the exact
extension rule on 5,376 small bundle/threshold cases. The samples do not certify all
profiles. Output is retained in `results/minimal_threats_checks.log`.

The Lean modules are imported by `EFX.lean`, have declaration certificates, and are
covered by the existing full build, axiom audit, and fresh-kernel replay. No new move
relation was proposed or asserted to pass the k = 4 counterexample suite. No external
literature survey or independent human review was performed.
