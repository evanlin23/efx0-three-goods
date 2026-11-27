# Making every order bad (against SD-C at larger k): fails

Workstream `proof/k4-ksens` (`k4/ksens.md`, status). Idea: SD-C needs only one good order, so a counterexample has
to recreate a PW-type deficit (`k4/ksens.md` §1) in every order.

**Attempt 1, symmetric.** Every agent values every top p₁ > … > p_n, ranked the same way, and a shared pool D in which
every pair is worth more than any top.
- In every order, the agents served before the last are frozen at the start.
- But junk satisfies wanters who value the pool. An agent holding its pick plus one good of D values its bundle above
  every top, so it stops wanting.
- The picks extend: each agent takes one good of D.

Smallest case: n = 2, k = 4. Tops worth 100, 99 to both; D = {d, d′} worth 60, 59 to both. Order (A, B), bundles
{p₁, d}, {p₂, d′}.

**Attempt 2, PW5 itself.** In the order (w₁, w₂, x₁, x₂, x₃) the wanters take p₁ and p₂, and x₁ and x₂ take pool
goods worth 9 and 8. Then:
- x₂ and x₃ are unfrozen and absorb the two remaining pool goods;
- the wanters' q's go to an absorber with at most one pool good;
- the picks extend (`results/k4_ksens/refute_oc_k5.log`: SD-C holds on PW5).

**Why PW does not transfer.** PW's deficit needs wanters that value nothing but the frozen picks. Any order that
serves those wanters first gives them picks they like and leaves the frozen agents free to absorb their pool. Nothing
here suggests a mechanism that defeats every order. No SD-C failure was found at any k (`k4/ksens.md`, status).

Reproduce: `python3 k4/ksens/ocsat.py '[[[0,1,2,3],[0,1,2,3]],[[100,99,60,59],[100,99,59,60]]]'` (attempt 1, n = 2; SD-C holds)
and `python3 k4/ksens/refute_oc_k5.py` (attempt 2).
