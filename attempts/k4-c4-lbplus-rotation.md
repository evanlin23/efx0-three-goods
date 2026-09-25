# LB⁺'s rotation when r has four goods

**Idea.** In LB⁺'s bad case (`proofs/lb_last_step.md` Theorem B) the leader k* of the last block gives its top up a
need chain to r and takes {b_k*, c_k*}; then k* is a valid owner. At k = 4 this is Theorem B₄ of `k4/c4.md`: the
rotation leaves W = J ∪ {Y_r} unchanged, so no agent other than r can become exposed, and a 3-good r cannot. Does it
also hold when r has four goods?

**Where it breaks.** No: a 4-good r moves up the chain and can then be threatened by k*'s new base itself.
Smallest (n = 3, m = 6): agents 0 = {0, 1, 2, 5} with values (2, 4, 8, 5) (ranking 2 > 5 > 1 > 0), 1 = {2, 3, 4, 5} with
(8, 3, 4, 6) (ranking 2 > 5 > 4 > 3, c + d < a < b + d), 2 = {3, 4, 5} with (2, 3, 4) (ranking 5 > 4 > 3); insertion
choices (5, 3, 7): agent 2 takes 5, agent 0 (lost 5) takes its top 2, agent 1 (lost 2 and 5) takes 4 and is r. After
envy-free upgrades (none apply) the only exposed agent is the 3-good leader 2 (3 and 4 = Y_r in W), r has no spare
slot: LB⁺'s bad case, with no 4-good agent exposed. LB⁺'s rotation: agent 1 takes 5, agent 2 takes {4, 3}. Now
agent 1 holds 5 (worth 6) and O = {4, 3} is its c and d, worth 7: agent 1 strongly envies k*'s bundle whatever it
receives (its slot holds junk outside its goods), so k* is not a valid owner, and ω′ = 1. A different rotation works
(agent 0 gives 2 to agent 1 and takes its private goods {0, 1}; owner 0), and brute force finds 6 EFX₀ allocations
with at most one large bundle, e.g. {0, 1, 3} | {2} | {4, 5}.

So Theorem B₄'s exception (G2 in `k4/c4.md` §6) is real: at n = 3 it occurs in 72,876 of the 73,936 + 72,876 rotation
cases of LB⁺'s bad case and makes k* fail in 1,288 of them (`results/k4_c4_check.log`); with at most one 4-good agent
(n = 4) it occurs in 32,232 runs, and k* never fails there.

**Smallest failing configuration**: the one above (n = 3, m = 6).
Reproduce: `python3 attempts/k4_c4_attempts.py lbplus-rotation`.
