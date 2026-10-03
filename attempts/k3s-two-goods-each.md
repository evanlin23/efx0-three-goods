# "Two goods each": a two-round draft, then one absorber

Workstream `proof/k3-simplify` (`proofs/k3_simple.md` §4).

**Idea.** For two relevant goods per agent, serial dictatorship with the last agent taking the leftovers is EFX₀
(L2c). For three goods, let every agent take a second good in a second round, then let the last agent take the rest.
The shape is right: K3ALG's output has every bundle but one of at most two goods (Theorem D).

**Where it breaks.** A second good can put a good that another agent needs alone into a two-good bundle. An agent
holding only its b needs its a alone, and an agent holding only its c needs a and b alone (Lemma L5). K3ALG gives
second goods only where this cannot happen: upgrades need "nobody needs b alone", and slots go only to agents
whose good nobody needs.

Variants tested (every ranking profile with values 4, 3, 2, agent order 0, …, n − 1). Failures on the 44,100 profiles
with n = 3, m = 7:
- two rounds 1..n, 1..n, then the last agent absorbs: 9,328;
- snake order 1..n, n..1, then the last picker absorbs: 6,360;
- snake order, with the best absorber: 5,712;
- each agent takes its top two remaining goods at once: 21,940.

**Smallest failing configurations.**
- Two rounds 1..n, 1..n, at n = 2, m = 3, both agents ranking 0 ≻ 1 ≻ 2. Agent 0 takes 0, agent 1 takes 1, then
  agent 0 takes 2. Agent 1 holds its b and needs 0 alone, but 0 is in {0, 2}: v₁({0, 2} ∖ {2}) = 4 > 3. Taking the
  top two at once fails on the same instance.
- Snake order at n = 3, m = 4, with three agents ranking 0 ≻ 1 ≻ 2 and good 3 worthless. The picks are 0, 1, 2, and
  then the last picker (agent 0) takes 3. Agent 1 holds its b and needs 0 alone, but 0 is in {0, 3}.

Reproduce: `python3 k3/simplify/exp_shapes.py index` (and `r1` for R1-priority orders; the counts are similar).
