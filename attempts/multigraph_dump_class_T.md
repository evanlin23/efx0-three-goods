# Lemma 4.2 (the dump) in class 𝒯

**Idea.** Extend Theorem X of `proofs/multigraph_extension.md` from class 𝒰 to class 𝒯, the profiles in which no good with three or more valuers is anyone's top. In 𝒯 the moves keep I1–I3 and the terminal state has (F1)–(F3) (Lemmas 3.1 and 3.2 are proved for 𝒰 and 𝒯). Only Lemma 4.2, the existence of an admissible assignment of the free goods, is missing.

**Where the proof breaks.** Lemma 4.2 uses (F4): every good that is someone's b or c has at most two valuers. In 𝒯 it fails, and so do the two facts built on it:
- (i) |H_f| ≤ 2. A free good f can be the b or c of three or more envied agents, whose partners may be held by three different open agents. Then case (a) ("three open agents suffice") needs more open agents.
- (ii) an open agent k lies in H_f for at most one free good. If k's pick p has three or more valuers, p can be the partner of several envied agents' free goods. Then the two-agent case (c) can meet two bad goods at one agent.

Fact (i) or (ii) fails first at n = 5: on 8, 8 and 32 class-𝒯 profiles with m = 7, 8, 9, and on none with n ≤ 4 (search in the script). The first one, with n = 5, m = 7: Core [[0, 4, 5], [1, 4, 6], [0, 1, 3], [2, 3, 4], [2, 3, 4]], rankings (a, b, c):
- agent 0: 0, 4, 5;
- agent 1: 1, 4, 6;
- agent 2: 0, 1, 3;
- agent 3: 2, 4, 3;
- agent 4: 2, 3, 4.

Good 4 has four valuers (0, 1, 3, 4), and good 3 has three (2, 3, 4); neither is anyone's top.
- Terminal state: the popular matching itself (no move applies): picks 0, 1, 3, 4, 2.
- Envied agents: 0, 1, 4. Open agents: 2 and 3. Free goods: 5 and 6.
- Agent 3 holds good 4, which is the partner of free good 5 for agent 0 and of free good 6 for agent 1, so agent 3 is bad for both.

The construction does not fail here. Agent 2 lies in no H_f, so case (b) sends both free goods to agent 2: owners of goods 0..6 = (0, 1, 4, 2, 3, 2, 2), EFX₀ by the raw definition. On every class-𝒯 profile with a popular matching and n ≤ 6 the case analysis (b), (a), (c) succeeded (`results/mgx_T.log`), so the conjecture MX-C (the case analysis always succeeds in 𝒯) stands; what fails is only its proof.

Reproduce: `python attempts/multigraph_limits.py dump` (the search over n ≤ 5, then this profile; about 10 s). For the exhaustive class-𝒯 runs: `cd src && python mgx.py 5 T --search` (8 s on 4 CPUs; `--search` also searches all assignments whenever the case analysis does not apply).
