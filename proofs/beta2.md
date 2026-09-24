# Conjecture D for β = 2 (connected cores with m = 2n − 1)

Workstream `proof/beta2`, plan Step 3.1, ledger open item 4 (second half). Work in progress: nothing in this file is
PROVED until the ledger says so.

## Target
D(β = 2): every connected core with m = 2n − 1 has, under every ranking profile, an EFX₀ allocation in which at most
one bundle has more than two goods.

## Route (PROMPT.md Step 3.1)
1. By L11, such a core is a subdivision of the theta, the dumbbell or the figure-eight, with pendant private goods.
2. Reduction: a long path of degree-2 agents and goods can be shortened without changing whether an allocation with at
   most one large bundle exists. Test every candidate reduction exhaustively on small cases before proving it.
3. Base cases: the finitely many cores left after the reduction, checked by the certified search.
