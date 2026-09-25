# Attempt: remove the private good of a P3 or P4 agent (k = 4 minimal counterexample)

Workstream `proof/k4-mincex` (`k4/MINCEX.md`). Failed; kept for the record.

**Idea.** For a PP4 agent (4 goods, two private) the one-agent gadget with one private good fewer always works
(K4.MC2: every one of the 144 types reduces). The same move one step down would remove P-agents altogether: replace a
P3 agent e (goods s, t, p; p private) by an agent e′ on {s, t} alone, or a P4 agent (s, t, u, p) by e′ on {s, t, u}.
The instance keeps its agents and loses a good, so it is smaller, and the gadget may depend on e's type.

**Result.** No type reduces, for any gadget. Every valuation class of e′ on the boundary goods was tried (5 for P3, 43
for P4, values 0..10, `k4/mincex4.py single P3` / `single P4`): 0 of 6 and 0 of 288 types reduce.

**Why (smallest failing configuration).** A single P3 agent e with values s = 4, t = 3, p = 2 (ranking s > t > p) and
the gadget e′ valuing s = t = 1. The local state of Y: e′ holds {s}, and t lies in an outside bundle {t, w} with
outside goods w, which nobody envies. It is admissible: e′ holds 1 and the threat {t, w} is worth 1. The extension must give s
(held by e′) to e, since no outside bundle consists of gadget goods only. The private good p cannot join it: X_e = {s, p}
contains a good worthless to outside agents and has the same outside-visible part {s} as Y_{e′} = {s}, which contains no
such good. So X_e is not dominated: an outside agent valuing s sees θ = v(s) > 0 in {s, p} and θ = 0 in {s}. If p goes to
the unenvied bundle, e faces {t, w, p}, whose threat v(t) + v(p) = 5 exceeds v(s) = 4. The other gadgets fail in the same
way: a worthless good cannot be added to a bundle holding boundary goods without a gadget good that makes that
bundle "inner" already in Y. A gadget good costs a good (so e′ on {s, t, z′} is not smaller than e). The PP4 case
works precisely because e has two private goods and the gadget keeps one of them as z′.

Reproduce: `cd k4 && python3 mincex_attempts.py drop-private` (prints the coverage and one failing state per gadget).
