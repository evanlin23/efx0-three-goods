# Minimal counterexample: reducing a P-agent next to a Q-agent

Workstream `proof/min-counterexample` (`proofs/min_counterexample.md`, §8). After Theorem M3 every good of degree 2 is
valued by a Q-agent, so the next configuration to reduce is a P-agent e and a Q-agent u sharing a good g of degree 2:
R_e = {gl, g, p} (p private, gl shared), R_u = {g, y1, y2}. Two reductions were tried, both with the unenvied bundle
of Lemma M1(b):
- **CON** (contract e: delete e, g, p; u values gl where it valued g). Reduces 14 of the 36 profiles: the 12 in which
  e ranks p last, and e: g > p > gl with u ranking g last. So in a minimal counterexample a P-agent next to a Q-agent
  (through a good of degree 2) never ranks its private good last. Not certified; not yet used.
- **DEL** (delete e, u, g, p; no gadget). Reduces none: in the local state where gl, y1, y2 all lie in one outside
  bundle with outside goods, u has at most one good of its own left (g) and both others together, so u is unsafe
  whatever e and u hold.

Smallest failing configuration for CON: e: gl > p > g, u: g > y1 > y2, with local state of Y: u′ holds {y1}, gl is
alone, y2 is alone and is the unenvied bundle. In H, u needs g alone or two of its goods; e needs gl alone to take g,
or both g and p; the only goods available are g and p, and p cannot join y2's outside bundle (it would stop being a
singleton for the agents valuing y2) nor u's bundle {y1} (same reason). The failure is that of this reduction, not a
proof that the configuration is irreducible.

Reproduce: `python attempts/min_cex_failed.py pq` (a few seconds).
