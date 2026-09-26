# Attempt: let the 4-good agent stop valuing one of its goods (V-form)

Workstream `proof/k4-induct` (`k4/induct.md` §2). Failed; kept for the record.

**Idea.** Keep every good and agent; set v_w(d) := 0 for one d ∈ R_w (w then has 3 relevant goods). An EFX₀ allocation
Y of this instance is EFX₀ for I whenever d ∈ Y_w, and otherwise only w's view of the bundle holding d changes (by
v_w(d) when that bundle has a good outside R_w). Hope: every Y is within a bounded repair of E(I), or an extremal Y is
EFX₀ for I.

**Result.** ρ = 0 fails at n = 2, ρ = 1 and ρ = 3 at n = 3; the potential (fewest agents envying w, then utilitarian
welfare), which had no failure on 25,500 sampled n = 3 profiles, fails at n = 2 (66 of the 189,216 strict profiles).

**Smallest failing configurations:**
- ρ = 0 (n = 2, m = 5): {0, 1, 3, 4} (4, 3, 8, 2); {2, 3, 4} (4, 3, 2).
- ρ = 1 (n = 3, m = 5): {0, 2, 3, 4} (3, 6, 8, 4); {1, 3, 4} (3, 4, 2); {2, 3, 4} (4, 3, 2).
- ρ = 3 (n = 3, m = 6): {0, 2, 4, 5} (3, 6, 2, 10); {1, 3, 5} (3, 4, 2); {3, 4, 5} (3, 2, 4). Every d: 4.
- potential (n = 2, m = 5): {0, 2, 3, 4} (8, 4, 3, 2); {1, 2, 3, 4} (8, 4, 3, 2).

Reproduce: `python3 attempts/k4_induct_attempts.py V-r0 V-r1 V-r3 V-pot-env-util`.
