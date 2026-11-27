# Charity independent of n from CKMS's update rules (kgen/charity.md §4)

**Idea.** Run Chaudhury–Kavitha–Mehlhorn–Sgouritsa's rules U0 (add a pool good to a bundle), U1 (an agent that
envies the pool takes a minimal envied subset of it) and U2 (a cycle of sources, pool goods and champions), with
envy-cycle elimination, and bound the pool at the stopping state by a function of k alone. Lemma CH1 makes this look
plausible: a pool good can be blocked at a source only by its own valuers, through goods they value in that source's
bundle, so the charity can be charged to small neighbourhoods (route (a)); and with genuine zeros the rainbow-cycle
reduction keeps its parts small (route (b), Theorems CH-A and CH-B).

**Where it breaks.** The stopping states themselves can leave Θ(√n) goods out at k = 3. In S(σ, 3)
(`kgen/charity/stuck_family.py`), σ sources each hold {x_j, x′_j}; for every pool good g the only champion of
X_{s_j} ∪ g is c(g, j), which hangs in the envy tree of s_{j+1}; so the source digraph is a directed σ-cycle in
every colour and a rainbow cycle needs σ distinct pool goods, one more than the σ − 1 there are. No rule applies
under any choice of champion (Proposition CH-D). The charge of route (a) is tight there: each pool good has σ
valuers, one per source, and Lemma CH4's σ ≤ (k − 2)|V(g)| holds with equality.

So any proof of CH(k) must use moves outside U0/U1/U2. (The S(σ, 3) states are not Pareto maxima: in them a source
holds x_j, worth nothing to it, and one Pareto improvement completes each; but the variant S′ of
`attempts/kgen-charity-pareto-maxima.md` closes that door too.)

**Smallest failing configuration.** S(3, 3): n = 9, m = 14, every agent values at most 3 goods, two goods
unallocated, a robust stopping state (and S(2, 3), n = 4, m = 7, one good). The instance has a complete EFX₀
allocation, as TARGET says.

Reproduce: `python3 kgen/charity/stuck_family.py 7 3 14` (log `results/kgen_charity/stuck_family_k3.log`; line
"sigma 3 k 3": U0 moves 0, no rainbow cycle, CKMS with all champion options makes no move, least charity 0).
