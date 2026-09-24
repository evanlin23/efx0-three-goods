# Real values reduce to natural numbers (L12)

Workstream `formal/lbplus` (PR #18), ledger item L12. The Lean theorems `EFX.target` and `EFX.LB.corollaryD` are stated
for natural-number values, as in evanlin23/mrd-efx. This note extends them to nonnegative real additive valuations,
the setting in which EFX results are usually stated.

**Lemma (L12).** Let v be nonnegative real additive valuations of n agents over m goods in which every agent has at most
three relevant goods (R_i = {g : v_i(g) > 0}, |R_i| ≤ 3). There are natural-number additive valuations w such that
every agent i has the same relevant goods under w, and for all sets S, T of goods

  v_i(S) ≤ v_i(T)  ⟺  w_i(S) ≤ w_i(T).

*Proof.* Fix an agent i; w_i is built from v_i alone. Goods outside R_i contribute 0 to both sides under v_i and will
contribute 0 under w_i, so S and T may be replaced by S ∩ R_i and T ∩ R_i. By additivity, removing the goods common to
S and T does not change either comparison, so it suffices that w_i preserves v_i(X) ≤ v_i(Y) for disjoint subsets
X, Y of R_i.

Name the relevant goods so that their values are a ≥ b ≥ c > 0 (if |R_i| = 3; fewer letters if |R_i| < 3). The
comparisons between disjoint X, Y ⊆ R_i are:
- X = ∅ or Y = ∅: decided by positivity (a nonempty set of relevant goods has positive value);
- two single goods: decided by the ties among a, b, c;
- a single good against the other two: a against b + c is free, while b < a + c and c < a + b always hold (a ≥ b,
  a ≥ c and all values are positive).

Two disjoint pairs do not fit in three goods. So all these comparisons, and hence the relation v_i(S) ≤ v_i(T) on all
sets, are determined by which of a = b, b = c hold and by the sign of a − (b + c). Choose w_i on R_i (in the same
order, a ≥ b ≥ c) by one natural-number representative per pattern:

| pattern | w_i |
|---|---|
| a > b > c, a < b + c | (4, 3, 2) |
| a > b > c, a = b + c | (3, 2, 1) |
| a > b > c, a > b + c | (5, 2, 1) |
| a = b > c (then a < b + c) | (2, 2, 1) |
| a > b = c, a < 2b | (3, 2, 2) |
| a > b = c, a = 2b | (2, 1, 1) |
| a > b = c, a > 2b | (3, 1, 1) |
| a = b = c | (1, 1, 1) |
| two relevant goods, a > b / a = b | (2, 1) / (1, 1) |
| one relevant good | (1) |

and w_i(g) = 0 for g ∉ R_i (in particular w_i = 0 if R_i = ∅). Each row realizes its own pattern: the ties are the
same, and a − (b + c) has the stated sign (4 < 5, 3 = 3, 5 > 3, 2 < 3, 3 < 4, 2 = 2, 3 > 2, 1 < 2). So w_i and v_i agree
on every comparison between disjoint subsets of R_i, hence on every comparison v_i(S) ≤ v_i(T). ∎

**Consequences.** EFX₀ of an allocation X is a conjunction of comparisons v_i(X_j ∖ {g}) ≤ v_i(X_i), so X is EFX₀ for v
iff it is EFX₀ for w, with the same bundles. Hence:
- *TARGET for real values.* Given v with |R_i| ≤ 3 for every agent (and at least one agent), w is a natural-number
  instance with `numRelevant ≤ 3`; `EFX.target` gives an allocation that is EFX₀ for w, hence for v.
- *Conjecture D for real values.* Exactly three relevant goods is preserved, and so is balance: 2 v_i(g) ≤ v_i(M) is the
  comparison v_i({g}) ≤ v_i(M ∖ {g}), and the strict form is its negation with the sides exchanged. `EFX.LB.corollaryD`
  gives an allocation that is EFX₀ for w with at most one bundle of more than two goods; the same bundles are EFX₀ for v.
- Cores are preserved (K1–K4 depend only on the relevant sets and on balance).

Machine-checked in Lean (`formal/real-values`, `lean/EFX/RealValues.lean`): `EFX.l12`, for values in any type satisfying
`EFX.OrderedValue` (a linearly ordered cancellative additive commutative monoid; ℝ≥0 is one), and from it
`EFX.target_ordered` and `EFX.corollaryD_ordered`. The Lean proof uses the representatives above in every order (31
triples, checked by `decide`) instead of sorting the goods, and treats agents with one or two relevant goods as three
slots, one or two of them phantom. Core preservation is not formalized.
