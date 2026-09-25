# C₄∃ by an extremal valid pre-allocation

Workstream `proof/k4-c4x`, ledger rows K4.C4X.* (CONJECTURE / EVIDENCE only), ledger open item 18. A second,
independent attempt at the last open step of the k = 4 case; the other one is the draft PR on `proof/k4-c4`
(`k4/c4.md` there, unreviewed), which follows LB⁺'s counting over runs of Phase 1. This file does not follow that route.

**Target C₄∃.** For every strict profile of every k = 4 core, *some* valid pre-allocation (`k4/lb4.md` §1) has a
completion satisfying (OC₄) in which frozen agents hold their base and only the owner's bundle has more than two
goods. By Theorem 1′₄ (machine-checked, `lean/EFX/PreAllocK.lean`), K4.TIE and K4.CORE this gives TARGET₄.

**Route.** Let 𝒫 be the finite set of valid pre-allocations of an instance. Pick P ∈ 𝒫 maximizing a potential Φ; if
P has ω ≥ 1 and no valid owner, construct P′ ∈ 𝒫 with Φ(P′) > Φ(P). Step 1 finds Φ by exhaustive computation;
step 2 proves "Φ-maximal ⇒ completable".

**Status.** Work in progress (skeleton).
