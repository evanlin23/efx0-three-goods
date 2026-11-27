# Frozen agents that stay frozen ("complete want"): fails

Workstream `proof/k4-ksens` (`k4/ksens.md` §5). Idea: make every frozen pick stay wanted after any one chain, so that
the frozen agents' shared pool D can never be spread out.
- Everyone who values the hot goods p₁ > … > p_f ranks them the same way.
- Agent x_j values p₁, …, p_j and the pool D, every pair of D being worth more than its pick.
- The last agent u values every p_j and its own good u₀.
- Order x₁, …, x_f, u: x_j picks p_j, and every p_j is wanted by every later agent.

**Why it fails.** The chain ends at a frozen agent and dumps that agent's pick on its last remaining wanter as that
wanter's single junk good, and this satisfies the wanter.
- In CW(3, 5) the chain is x₁ → x₃: x₁ takes three pool goods, x₃ takes p₁, and p₃ is dumped.
- u receives p₃ as junk. Its bundle {u₀, p₃} is then worth more to it than any p, so u stops wanting p₂.
- x₂ is therefore unfrozen and takes a pool good itself.

The analysis behind the idea assumed that a frozen agent's pick can never become junk; it can, as one junk good of an
unfrozen wanter.

**Smallest failing configuration:** CW(2, 3) (`k4/ksens/fam_cw.py 2 3 1 40`): n = 3, k = 5, OC₁ holds. In all
240 instances, CW(f, r) with f = 2, 3, r = 3, 4, 5 and k = 5–8, OC, OC₁ and MD hold
(`results/k4_ksens/fam_cw.log`).

**What works instead** (PW, `k4/ksens.md` §1): wanters that value nothing but the hot goods and their own good, so
that junk never satisfies them. At least two of them are needed, so that one is still unused after the chain.

Reproduce: `for fr in "2 3" "2 4" "2 5" "3 3" "3 4" "3 5"; do python3 k4/ksens/fam_cw.py $fr 1 40; done`.
