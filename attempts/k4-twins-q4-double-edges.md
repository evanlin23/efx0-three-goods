# Attempt: reduce double edges at a Q4 agent (two agents sharing two goods nobody else values, one of them Q4)

Workstream `proof/k4-twins` (`k4/TWINS.md`, row K4.MC8). Partly failed: every double edge without a Q4 agent, and the
closed ones between a Q3 or P4 agent and a Q4 agent, are reduced and certified (K4.MC8); the cases below are only
partly reduced. Their reduced counts are certified (both implementations agree), and the profiles left are recorded
(`results/k4_twins/dbl_q3_uncovered.json`, `results/k4_twins/dbl_p4q4_uncovered.json`) and used as domain cuts
(`k4/twins_filter.py`).

| configuration (k4/TWINS.md §2) | boundary goods | profiles | reduced |
|---|---|---|---|
| dbl-Q3-Q4 (open) | a; x, y | 1,728 | 1,708 |
| dbl-P4-Q4 (open) | a; x, y | 82,944 | 81,944 |
| dbl-Q4-Q4 (open) | a, b; x, y | 82,944 | 50,392 |
| dbl-Q4-Q4-c1 | a (common), b, y | 82,944 | 71,512 |
| dbl-Q4-Q4-c2 (Q4 twins on g0, g1, a, b) | a, b | 82,944 | 80,152 |

Reductions tried: DEL; every one-agent gadget h on the boundary goods plus 0 or 1 gadget good (on 3-subsets of ∂ when
|∂| = 4), and with 2 gadget goods where |∂| ≤ 2 (dbl-Q4-Q4-c2: no gain); the copy gadgets KEEP-e / KEEP-f (dbl-P4-Q4: no
gain); DROP-g0 (e′, f′ = e, f with g0 deleted, the same agents and one good fewer: 0 on dbl-Q4-Q4-c2). All with the
unenvied bundle.

**Why Q4 is the obstacle.** A Q4 agent brings two boundary goods. With the other agent's boundary good(s), ∂ has 3 or 4
goods, so a one-agent gadget has room for at most one gadget good (none when |∂| = 4); the double edges that reduce
fully all have |∂| ≤ 2, or |∂| = 3 with a private good in I. Two-agent gadgets are not smaller here unless they drop a
good, and DROP-g0 fails.

**Smallest failing configuration.** dbl-Q3-Q4 (open): e (Q3) on (g0, g1, a) = (3, 2, 4) and f (Q4) on (g0, g1, x, y) =
(1, 8, 6, 4). The 20 profiles left all have this shape: e ranks a first, f ranks first the double-edge good e ranks
last and the other one last.
- DEL fails at the state where a, x, y lie together in one outside bundle without outside goods, unenvied.
- The gadget h = (x: 2, y: 2, z′: 3) (the menu item that reduces the most profiles, 448) fails at the state h holds
  {x, z′}, {a, y} is an outside bundle, h's bundle unenvied.

Reproduce: `cd k4 && python3 twins4.py why dbl-Q3-Q4 --zs=1` (seconds);
`python3 twins4.py certify dbl-P4-Q4 dbl-Q4-Q4 dbl-Q4-Q4-c1 dbl-Q4-Q4-c2 --zs=0,1 --write=OUT.json.gz` (about an hour
on 4 CPUs) for the coverage of the others; `python3 twins4.py explore dbl-Q4-Q4-c2 --zs=2` for two gadget goods.
