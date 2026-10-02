# The portfolio survival table (compute/k4-portfolio)

Made by `python3 k4/portfolio.py table` from `results/k4_portfolio/*.json`. EVIDENCE only. Each cell: failures / states tested (single-step forms) or failures / keys with def* > 0 tested (key-graph forms). Rows are ordered from the strongest statement to the weakest along the lattice: RC3 < RC_W1 < RC < {RC_noneed, RC_Yfree, RC_Yany} < RC_U0 < NA1 < NAbal = NAall; RC3 < NA3 < NAall; NA1 < U1Z1; D2 < D3 < D4; NA3 < D3; FR3 apart; RT4 (control) is not inside RC3 (its rotations and T4 moves may change more than three agents); RC3_noT4 < RC3 is a probe (is T4 needed?). Key-graph: K3b_noT4 (probe) < K3b < K3 < K2 < {K2_noneed, K2_Yany} < K4 < K5; K4 < KU1; K1 (control).

## Datasets

| dataset | command | profiles | evaluated profiles | states | keys def* > 0 | states by f |
|---|---|---:|---:|---:|---:|---|
| suite | `suite --name=suite --jobs=3 --chunk=5` | 154 | 49 | 215 | 37 | f=1: 115, f=2: 64, f=3: 36 |
| validate10 | `inst results/k4_rt4/n5b_failures_inst.json results/k4_rt4/n5c_fail_inst.json --name=validate10 --chunk=1` | 10 | 10 | 168 | 41 | f=3: 168 |
| dumps | `dumps results/k4_rt4/dump_a_failures.jsonl.gz results/k4_rt4/dump_a_nbhd123.jsonl.gz results/k4_rt4/dump_a_suite2.jsonl.gz results/k4_rt4/dump_b_n4_1.jsonl.gz results/k4_rt4/dump_c_n4_2.jsonl.gz results/k4_rt4/dump_d_cat_gap_n4_pure_s4000.jsonl.gz results/k4_rt4/dump_d_pure_s500_1.jsonl.gz results/k4_rt4/dump_d_pure_s500_2.jsonl.gz results/k4_rt4/dump_d_pure_s500_3.jsonl.gz results/k4_rt4/dump_e_n4_3_s500_1.jsonl.gz results/k4_rt4/dump_e_n4_3_s500_2.jsonl.gz results/k4_rt4/dump_e_n4_3_s500_3.jsonl.gz results/k4_rt4/dump_n4_3_x1.jsonl.gz results/k4_rt4/dump_n4_3_x2.jsonl.gz results/k4_rt4/dump_n4_3_x3.jsonl.gz results/k4_rt4/dump_n4_3_x4.jsonl.gz results/k4_rt4/dump_n5b_3.jsonl.gz results/k4_rt4/dump_n5b_3bt.jsonl.gz results/k4_rt4/dump_n5b_4.jsonl.gz results/k4_rt4/dump_n5b_4bt.jsonl.gz results/k4_rt4/dump_n5c_cat_gap_n5_2_s100.jsonl.gz results/k4_rt4/dump_n5c_cat_gap_n5_3_s100.jsonl.gz results/k4_rt4/dump_n5c_cat_gap_n5_4_s100.jsonl.gz results/k4_rt4/dump_n5c_cat_gap_n5_pure_s100.jsonl.gz results/k4_rt4/dump_n5c_cat_hard_hunt.jsonl.gz results/k4_rt4/dump_n5c_cat_hard_hunt_smallest.jsonl.gz results/k4_rt4/dump_n5c_pure.jsonl.gz results/k4_rt4/dump_n5c_purebt.jsonl.gz results/k4_rt4/dump_n5c_suite.jsonl.gz results/k4_dl13/dl134_xcheck_n4.jsonl.gz results/k4_dl13/dl134_xcheck_n5.jsonl.gz results/k4_dl13/dl134_xcheck_own.jsonl.gz results/k4_dl13/dump_n4_1.jsonl.gz results/k4_dl13/dump_n4_2.jsonl.gz results/k4_dl13/dump_n4_3_s200.jsonl.gz results/k4_dl13/dump_n4_3_s200b.jsonl.gz results/k4_dl13/dump_n4_pure_s200.jsonl.gz results/k4_dl13/dump_n4_pure_s200b.jsonl.gz results/k4_dl13/fails_all.jsonl.gz results/k4_dl13/fails_classified.jsonl.gz results/k4_dl13/fails_hunt_m6.jsonl.gz results/k4_dl13/fails_hunt_m8.jsonl.gz results/k4_dl13/fails_hunt_n5.jsonl.gz results/k4_dl13/hunt_n4_3_m6.jsonl.gz results/k4_dl13/hunt_n4_3_m8.jsonl.gz results/k4_dl13/hunt_n5.jsonl.gz results/k4_dl13/hunt_pure_m6.jsonl.gz results/k4_dl13/hunt_pure_m8.jsonl.gz results/k4_dl13/states_cat.jsonl.gz results/k4_dl13/states_ht.jsonl.gz results/k4_dl13/states_n3.jsonl.gz results/k4_dl13/states_nbhd123.jsonl.gz results/k4_dl13/states_rand.jsonl.gz results/k4_dl13_stuck/stuck_certs_3_r2000.jsonl.gz results/k4_dl13_stuck/stuck_certs_4_n4_1_r100.jsonl.gz results/k4_dl13_stuck/stuck_certs_4_n4_2_r100.jsonl.gz results/k4_dl13_stuck/stuck_certs_4_n4_3_r100.jsonl.gz results/k4_dl13_stuck/stuck_certs_4_pure_r100.jsonl.gz results/k4_dl13_stuck/stuck_certs_5_n4_1_r4.jsonl.gz results/k4_dl13_stuck/stuck_certs_5_n4_2_r4.jsonl.gz results/k4_dl13_stuck/stuck_certs_5_n4_3_r4.jsonl.gz results/k4_dl13_stuck/stuck_certs_5_n4_4_r4.jsonl.gz results/k4_dl13_stuck/stuck_certs_5_pure_r4.jsonl.gz results/k4_dl13_stuck/stuck_gap_n3.jsonl.gz results/k4_dl13_stuck/stuck_gap_n4_1_e4.jsonl.gz results/k4_dl13_stuck/stuck_gap_n4_1_f2.jsonl.gz results/k4_dl13_stuck/stuck_gap_n4_2_s4000_e4.jsonl.gz results/k4_dl13_stuck/stuck_gap_n4_2_s4000_f2.jsonl.gz results/k4_dl13_stuck/stuck_gap_n4_3_s4000_e4.jsonl.gz results/k4_dl13_stuck/stuck_gap_n4_3_s4000_f2.jsonl.gz results/k4_dl13_stuck/stuck_gap_n4_pure_s4000_e4.jsonl.gz results/k4_dl13_stuck/stuck_gap_n4_pure_s4000_f2.jsonl.gz results/k4_dl13_stuck/stuck_gap_n5_1_s100_e20.jsonl.gz results/k4_dl13_stuck/stuck_gap_n5_1_s100_f2e4.jsonl.gz results/k4_dl13_stuck/stuck_gap_n5_2_s100_e20.jsonl.gz results/k4_dl13_stuck/stuck_gap_n5_2_s100_f2e4.jsonl.gz results/k4_dl13_stuck/stuck_gap_n5_3_s100_e20.jsonl.gz results/k4_dl13_stuck/stuck_gap_n5_3_s100_f2e4.jsonl.gz results/k4_dl13_stuck/stuck_gap_n5_4_s100_e20.jsonl.gz results/k4_dl13_stuck/stuck_gap_n5_4_s100_f2e4.jsonl.gz results/k4_dl13_stuck/stuck_gap_n5_pure_s100_e20.jsonl.gz results/k4_dl13_stuck/stuck_gap_n5_pure_s100_f2e4.jsonl.gz results/k4_dl13_stuck/stuck_hard_hunt.jsonl.gz results/k4_dl13_stuck/stuck_hunt_n4_2_all_e10.jsonl.gz results/k4_dl13_stuck/stuck_hunt_n4_3_s400k_e10.jsonl.gz results/k4_dl13_stuck/stuck_hunt_n4_3_s400k_f2.jsonl.gz results/k4_dl13_stuck/stuck_hunt_n4_pure_s400k_e10.jsonl.gz results/k4_dl13_stuck/stuck_hunt_n4_pure_s400k_f2.jsonl.gz results/k4_dl13_stuck/stuck_hunt_n5_3_s2000_e2.jsonl.gz results/k4_dl13_stuck/stuck_hunt_n5_4_s2000_e2.jsonl.gz results/k4_dl13_stuck/stuck_hunt_n5_pure_s2000_e2.jsonl.gz results/k4_dl13_stuck/stuck_suite.jsonl.gz results/k4_dl13_stuck/t4_certs_3_r2000.jsonl.gz results/k4_dl13_stuck/t4_certs_4_n4_1_r100.jsonl.gz results/k4_dl13_stuck/t4_certs_4_n4_2_r100.jsonl.gz results/k4_dl13_stuck/t4_certs_4_n4_3_r100.jsonl.gz results/k4_dl13_stuck/t4_certs_4_pure_r100.jsonl.gz results/k4_dl13_stuck/t4_failures_n4_1.jsonl.gz results/k4_dl13_stuck/t4_failures_n4_2.jsonl.gz results/k4_dl13_stuck/t4_failures_n4_3_s200b.jsonl.gz results/k4_dl13_stuck/t4_gap_n4_1_f2.jsonl.gz results/k4_dl13_stuck/t4_gap_n4_2_s4000_f2.jsonl.gz results/k4_dl13_stuck/t4_gap_n4_3_s4000_f2.jsonl.gz results/k4_dl13_stuck/t4_gap_n4_pure_s4000_f2.jsonl.gz results/k4_dl13_stuck/t4_gap_n5_1_s100_f2e4.jsonl.gz results/k4_dl13_stuck/t4_gap_n5_2_s100_f2e4.jsonl.gz results/k4_dl13_stuck/t4_gap_n5_3_s100_f2e4.jsonl.gz results/k4_dl13_stuck/t4_gap_n5_4_s100_f2e4.jsonl.gz results/k4_dl13_stuck/t4_gap_n5_pure_s100_f2e4.jsonl.gz results/k4_dl13_stuck/t4_hard_hunt.jsonl.gz results/k4_dl13_stuck/t4_hunt_n4_3_s400k_f2.jsonl.gz results/k4_dl13_stuck/t4_hunt_n4_pure_s400k_f2.jsonl.gz results/k4_dl13_stuck/t4_suite.jsonl.gz results/k4_dl2/repairs_cycle.jsonl.gz results/k4_dl2/repairs_cycle_n3.jsonl.gz results/k4_dl2/repairs_ht.jsonl.gz results/k4_dl2/repairs_n3.jsonl.gz results/k4_dl2/repairs_n4_1.jsonl.gz results/k4_dl2/repairs_n4_2.jsonl.gz results/k4_dl2/repairs_n4cat.jsonl.gz results/k4_dl2/repairs_n5cat.jsonl.gz results/k4_dl2/trapped_cycle_n4.jsonl.gz results/k4_dl2/trapped_n3.jsonl.gz results/k4_dl2/trapped_n4cat.jsonl.gz results/k4_dl2_classify/gap_n2_e1.jsonl.gz results/k4_dl2_classify/gap_n3_e1.jsonl.gz results/k4_dl2_classify/gap_n4_1_e10.jsonl.gz results/k4_dl2_classify/gap_n4_2_s4000_e10.jsonl.gz results/k4_dl2_classify/gap_n4_3_s4000_e10.jsonl.gz results/k4_dl2_classify/gap_n4_pure_s4000_e10.jsonl.gz results/k4_dl2_classify/gap_n5_1_s100_e20.jsonl.gz results/k4_dl2_classify/gap_n5_2_s100_e20.jsonl.gz results/k4_dl2_classify/gap_n5_3_s100_e20.jsonl.gz results/k4_dl2_classify/gap_n5_4_s100_e20.jsonl.gz results/k4_dl2_classify/gap_n5_pure_s100_e20.jsonl.gz results/k4_dl2_classify/hard_hunt_e1.jsonl.gz results/k4_dl2_classify/suite.jsonl.gz results/k4_dl2_relations/certs_2_all.jsonl.gz results/k4_dl2_relations/certs_3_r400.jsonl.gz results/k4_dl2_relations/certs_4_n4_1_r20.jsonl.gz results/k4_dl2_relations/certs_4_n4_2_r20.jsonl.gz results/k4_dl2_relations/certs_4_n4_3_r20.jsonl.gz results/k4_dl2_relations/certs_4_pure_r20.jsonl.gz results/k4_dl2_relations/gap_n2_e1.jsonl.gz results/k4_dl2_relations/gap_n3_e1.jsonl.gz results/k4_dl2_relations/gap_n4_1_e10.jsonl.gz results/k4_dl2_relations/gap_n4_2_s4000_e10.jsonl.gz results/k4_dl2_relations/gap_n4_3_s4000_e10.jsonl.gz results/k4_dl2_relations/gap_n4_pure_s4000_e10.jsonl.gz results/k4_dl2_relations/gap_n5_1_s100_e20.jsonl.gz results/k4_dl2_relations/gap_n5_2_s100_e20.jsonl.gz results/k4_dl2_relations/gap_n5_3_s100_e20.jsonl.gz results/k4_dl2_relations/gap_n5_4_s100_e20.jsonl.gz results/k4_dl2_relations/gap_n5_pure_s100_e20.jsonl.gz results/k4_dl2_relations/hard_hunt_e1.jsonl.gz results/k4_dl2_relations/hunt_n4_2_all_e1.jsonl.gz results/k4_dl2_relations/hunt_n4_3_s400k_e1.jsonl.gz results/k4_dl2_relations/hunt_n4_pure_s400k_e1.jsonl.gz results/k4_dl2_relations/hunt_n5_3_s2000_e1.jsonl.gz results/k4_dl2_relations/hunt_n5_4_s2000_e1.jsonl.gz results/k4_dl2_relations/hunt_n5_pure_s2000_e1.jsonl.gz --chunk=500 --jobs=3 --maxpairs=1000000 --name=dumps --ckpt` | 168,799 | 166,323 | 700,635 | 70,749 | f=1: 366955, f=2: 258856, f=3: 74514, f=4: 310 |
| n5_4 | `certs results/k4_certs_5_n4_4.json.gz --sample=4000 --seed=3 --jobs=3 --maxst=600 --name=n5_4 --ckpt` | 39,384,000 | 92,992 | 280,604 | 476 | f=1: 225873, f=2: 52011, f=3: 2696, f=4: 24 |
| r3 | `certs results/k4_certs_3.json.gz --sample=20 --seed=101 --jobs=3 --name=r3 --ckpt` | 1,020 | 4 | 4 | 0 | f=1: 4 |
| r3b | `certs results/k4_certs_3.json.gz --sample=2000 --seed=102 --jobs=3 --name=r3b --ckpt` | 102,000 | 445 | 1,156 | 155 | f=1: 957, f=2: 199 |
| r4 | `certs results/k4_certs_4_n4_1.json.gz results/k4_certs_4_n4_2.json.gz results/k4_certs_4_n4_3.json.gz results/k4_certs_4_pure.json.gz --sample=20 --seed=101 --jobs=3 --name=r4 --ckpt` | 20,040 | 48 | 210 | 3 | f=1: 198, f=2: 12 |
| r4b | `certs results/k4_certs_4_n4_1.json.gz results/k4_certs_4_n4_2.json.gz results/k4_certs_4_n4_3.json.gz results/k4_certs_4_pure.json.gz --sample=1000 --seed=102 --jobs=3 --name=r4b --ckpt` | 1,002,000 | 2,902 | 8,776 | 135 | f=1: 7610, f=2: 1116, f=3: 50 |
| **all** (summed over the datasets; validate10 and part of suite repeat profiles of dumps) | | 40,678,023 | 262,773 | 991,768 | 71,596 | f=1: 601712, f=2: 312258, f=3: 77464, f=4: 334 |

## Single-step forms DL_R

| predicate | definition | suite | validate10 | dumps | n5_4 | r3 | r3b | r4 | r4b | **all** | least margin |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| RT4 | T1 + T2 + T3 + T4 (control: refuted at n = 5) | **3**/215 | **67**/168 | **67**/700635 | 0/280604 | 0/4 | 0/1156 | 0/210 | 0/8776 | **137**/991768 | 0 |
| RC3 | RC_W1 moves changing at most three agents (added: no smallest repair on the data changes more than three) | 0/215 | 0/168 | 0/700635 | 0/280604 | 0/4 | 0/1156 | 0/210 | 0/8776 | 0/991768 | 1 |
| RC_W1 | RC with \|W\| <= 1 in T3+ | 0/215 | 0/168 | 0/700635 | 0/280604 | 0/4 | 0/1156 | 0/210 | 0/8776 | 0/991768 | 1 |
| RC | T1 + T2 + T3+ + T4 (K4.DL2.RC) | 0/215 | 0/168 | 0/700635 | 0/280604 | 0/4 | 0/1156 | 0/210 | 0/8776 | 0/991768 | 1 |
| RC_noneed | RC without "z needs its new good" | 0/215 | 0/168 | 0/700635 | 0/280604 | 0/4 | 0/1156 | 0/210 | 0/8776 | 0/991768 | 1 |
| RC_Yfree | RC with the helper (at most one) unrestricted (need not give up a good) | 0/215 | 0/168 | 0/700635 | 0/280604 | 0/4 | 0/1156 | 0/210 | 0/8776 | 0/991768 | 1 |
| RC_Yany | RC with any number of helpers, each giving up a good | 0/215 | 0/168 | 0/700635 | 0/280604 | 0/4 | 0/1156 | 0/210 | 0/8776 | 0/991768 | 2 |
| RC_U0 | NA kept and U empty (T1, T2, T4 and their unions: frozen goods permuted while free agents re-partition) + T3+ | 0/215 | 0/168 | 0/700635 | 0/280604 | 0/4 | 0/1156 | 0/210 | 0/8776 | 0/991768 | 1 |
| RC3_noT4 | RC3 without T4 (added as a probe: is the frozen permutation needed next to the chains?) | 0/215 | 0/168 | 0/700635 | 0/280604 | 0/4 | 0/1156 | 0/210 | 0/8776 | 0/991768 | 1 |
| NA3 | NA kept and \|ch\| <= 3 (added: D3 within the NA-keeping moves) | 0/215 | 0/168 | 0/700635 | 0/280604 | 0/4 | 0/1156 | 0/210 | 0/8776 | 0/991768 | 1 |
| NA1 | NA kept, \|U\| <= 1, \|Z\| <= 1 (W, Y arbitrary) | 0/215 | 0/168 | 0/700635 | 0/280604 | 0/4 | 0/1156 | 0/210 | 0/8776 | 0/991768 | 3 |
| NAbal | NA kept, \|U\| = \|Z\| (= NAall, see the docstring) | 0/215 | 0/168 | 0/700635 | 0/280604 | 0/4 | 0/1156 | 0/210 | 0/8776 | 0/991768 | 3 |
| NAall | NA kept | 0/215 | 0/168 | 0/700635 | 0/280604 | 0/4 | 0/1156 | 0/210 | 0/8776 | 0/991768 | 3 |
| U1Z1 | \|U\| <= 1 and \|Z\| <= 1, NA free | 0/215 | 0/168 | 0/700635 | 0/280604 | 0/4 | 0/1156 | 0/210 | 0/8776 | 0/991768 | 3 |
| D2 | \|ch\| <= 2 (DL2; control: refuted at n = 3) | **5**/215 | **67**/168 | **32387**/700635 | **4**/280604 | 0/4 | 0/1156 | 0/210 | 0/8776 | **32463**/991768 | 0 |
| D3 | \|ch\| <= 3 | 0/215 | 0/168 | 0/700635 | 0/280604 | 0/4 | 0/1156 | 0/210 | 0/8776 | 0/991768 | 1 |
| D4 | \|ch\| <= 4 | 0/215 | 0/168 | 0/700635 | 0/280604 | 0/4 | 0/1156 | 0/210 | 0/8776 | 0/991768 | 3 |
| FR3 | \|U\| + \|Z\| + \|W\| <= 3, free agents unrestricted, NA free | 0/215 | 0/168 | 0/700635 | 0/280604 | 0/4 | 0/1156 | 0/210 | 0/8776 | 0/991768 | 3 |

Smallest failure and smallest-repair distribution (all datasets):

| predicate | smallest failure (n, m, f, def; id) | smallest repairs "U\|W\|Z\|Y" (count) |
|---|---|---|
| RT4 | n=5, m=9, f=3, def=1; `k4_certs_5_n4_4.json.gz#3206:108,86,1,108,27`; P=[[7], [8], [3], [5], [6]] | 0\|0\|0\|1: 761564, 1\|0\|1\|0: 165018, 1\|0\|1\|1: 29203, 0\|0\|0\|2: 21534, 0\|2\|0\|0: 11188, 0\|0\|0\|3: 3116, 0\|3\|0\|0: 8 |
| RC3 | - | 0\|0\|0\|1: 761564, 1\|0\|1\|0: 165018, 1\|0\|1\|1: 29203, 0\|0\|0\|2: 21534, 0\|2\|0\|0: 11188, 0\|0\|0\|3: 3116, 1\|1\|1\|0: 145 |
| RC_W1 | - | 0\|0\|0\|1: 761564, 1\|0\|1\|0: 165018, 1\|0\|1\|1: 29203, 0\|0\|0\|2: 21534, 0\|2\|0\|0: 11188, 0\|0\|0\|3: 3116, 1\|1\|1\|0: 145 |
| RC | - | 0\|0\|0\|1: 761564, 1\|0\|1\|0: 165018, 1\|0\|1\|1: 29203, 0\|0\|0\|2: 21534, 0\|2\|0\|0: 11188, 0\|0\|0\|3: 3116, 1\|1\|1\|0: 145 |
| RC_noneed | - | 0\|0\|0\|1: 761564, 1\|0\|1\|0: 165038, 1\|0\|1\|1: 29202, 0\|0\|0\|2: 21534, 0\|2\|0\|0: 11169, 0\|0\|0\|3: 3116, 1\|1\|1\|0: 145 |
| RC_Yfree | - | 0\|0\|0\|1: 761564, 1\|0\|1\|0: 165018, 1\|0\|1\|1: 29203, 0\|0\|0\|2: 21534, 0\|2\|0\|0: 11188, 0\|0\|0\|3: 3116, 1\|1\|1\|0: 145 |
| RC_Yany | - | 0\|0\|0\|1: 761564, 1\|0\|1\|0: 165018, 1\|0\|1\|1: 29203, 0\|0\|0\|2: 21534, 0\|2\|0\|0: 11188, 0\|0\|0\|3: 3116, 1\|1\|1\|0: 145 |
| RC_U0 | - | 0\|0\|0\|1: 761564, 1\|0\|1\|0: 165018, 1\|0\|1\|1: 29203, 0\|0\|0\|2: 21534, 0\|2\|0\|0: 11188, 0\|0\|0\|3: 3116, 1\|1\|1\|0: 145 |
| RC3_noT4 | - | 0\|0\|0\|1: 761564, 1\|0\|1\|0: 165018, 1\|0\|1\|1: 29387, 0\|0\|0\|2: 21534, 1\|1\|1\|0: 11149, 0\|0\|0\|3: 3116 |
| NA3 | - | 0\|0\|0\|1: 761564, 1\|0\|1\|0: 165038, 1\|0\|1\|1: 29202, 0\|0\|0\|2: 21534, 0\|2\|0\|0: 11169, 0\|0\|0\|3: 3116, 1\|1\|1\|0: 145 |
| NA1 | - | 0\|0\|0\|1: 761564, 1\|0\|1\|0: 165038, 1\|0\|1\|1: 29202, 0\|0\|0\|2: 21534, 0\|2\|0\|0: 11169, 0\|0\|0\|3: 3116, 1\|1\|1\|0: 145 |
| NAbal | - | 0\|0\|0\|1: 761564, 1\|0\|1\|0: 165038, 1\|0\|1\|1: 29202, 0\|0\|0\|2: 21534, 0\|2\|0\|0: 11169, 0\|0\|0\|3: 3116, 1\|1\|1\|0: 145 |
| NAall | - | 0\|0\|0\|1: 761564, 1\|0\|1\|0: 165038, 1\|0\|1\|1: 29202, 0\|0\|0\|2: 21534, 0\|2\|0\|0: 11169, 0\|0\|0\|3: 3116, 1\|1\|1\|0: 145 |
| U1Z1 | - | 0\|0\|0\|1: 761564, 1\|0\|1\|0: 165038, 1\|0\|1\|1: 29202, 0\|0\|0\|2: 21534, 0\|2\|0\|0: 11169, 0\|0\|0\|3: 3116, 1\|1\|1\|0: 145 |
| D2 | n=3, m=7, f=1, def=1; `k4_certs_3.json.gz#33:10,0,212`; P=[[3], [2, 6], [4, 5]] | 0\|0\|0\|1: 761564, 1\|0\|1\|0: 165038, 0\|0\|0\|2: 21534, 0\|2\|0\|0: 11169 |
| D3 | - | 0\|0\|0\|1: 761564, 1\|0\|1\|0: 165038, 1\|0\|1\|1: 29202, 0\|0\|0\|2: 21534, 0\|2\|0\|0: 11169, 0\|0\|0\|3: 3116, 1\|1\|1\|0: 145 |
| D4 | - | 0\|0\|0\|1: 761564, 1\|0\|1\|0: 165038, 1\|0\|1\|1: 29202, 0\|0\|0\|2: 21534, 0\|2\|0\|0: 11169, 0\|0\|0\|3: 3116, 1\|1\|1\|0: 145 |
| FR3 | - | 0\|0\|0\|1: 761564, 1\|0\|1\|0: 165038, 1\|0\|1\|1: 29202, 0\|0\|0\|2: 21534, 0\|2\|0\|0: 11169, 0\|0\|0\|3: 3116, 1\|1\|1\|0: 145 |

## Key-graph forms

| predicate | definition | suite | validate10 | dumps | n5_4 | r3 | r3b | r4 | r4b | **all** | least margin |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| K1 | T3 + T4 edges (control: refuted at n = 5, K4.DL13.KEY) | **2**/37 | **10**/41 | **10**/70749 | 0/476 | 0/0 | 0/155 | 0/3 | 0/135 | **22**/71596 | 0 |
| K3b | K3 edges changing at most three agents (added, as RC3) | 0/37 | 0/41 | 0/70749 | 0/476 | 0/0 | 0/155 | 0/3 | 0/135 | 0/71596 | 6 |
| K3b_noT4 | K3b without T4 edges (added as a probe) | 0/37 | 0/41 | 0/70749 | 0/476 | 0/0 | 0/155 | 0/3 | 0/135 | 0/71596 | 4 |
| K3 | T3+ with \|W\| <= 1, + T4 | 0/37 | 0/41 | 0/70749 | 0/476 | 0/0 | 0/155 | 0/3 | 0/135 | 0/71596 | 6 |
| K2 | T3+ + T4 edges (K4.DL2.RC key-graph form) | 0/37 | 0/41 | 0/70749 | 0/476 | 0/0 | 0/155 | 0/3 | 0/135 | 0/71596 | 6 |
| K2_noneed | T3+ without "z needs" + T4 | 0/37 | 0/41 | 0/70749 | 0/476 | 0/0 | 0/155 | 0/3 | 0/135 | 0/71596 | 6 |
| K2_Yany | T3+ with any number of giving helpers + T4 | 0/37 | 0/41 | 0/70749 | 0/476 | 0/0 | 0/155 | 0/3 | 0/135 | 0/71596 | 6 |
| K4 | NA1 moves (NA kept, \|U\| <= 1) | 0/37 | 0/41 | 0/70749 | 0/476 | 0/0 | 0/155 | 0/3 | 0/135 | 0/71596 | 6 |
| K5 | NA kept | 0/37 | 0/41 | 0/70749 | 0/476 | 0/0 | 0/155 | 0/3 | 0/135 | 0/71596 | 6 |
| KU1 | \|U\| <= 1, NA free | 0/37 | 0/41 | 0/70749 | 0/476 | 0/0 | 0/155 | 0/3 | 0/135 | 0/71596 | 6 |

Smallest failure and smallest-repair distribution (all datasets):

| predicate | smallest failure (n, m, f, def; id) | smallest repairs "U\|W\|Z\|Y" (count) |
|---|---|---|
| K1 | n=5, m=9, f=3, def=1; `k4_certs_5_n4_4.json.gz#3206:108,86,1,108,27`; NA=[6, 7, 8], frozen={'0': [7], '1': [8], '4': [6]} | 1\|0\|1\|0: 63704, 0\|2\|0\|0: 7849, 1\|0\|1\|1: 13, 0\|3\|0\|0: 8 |
| K3b | - | 1\|0\|1\|0: 63704, 0\|2\|0\|0: 7849, 1\|1\|1\|0: 30, 1\|0\|1\|1: 13 |
| K3b_noT4 | - | 1\|0\|1\|0: 63704, 1\|1\|1\|0: 7874, 1\|0\|1\|1: 18 |
| K3 | - | 1\|0\|1\|0: 63704, 0\|2\|0\|0: 7849, 1\|1\|1\|0: 30, 1\|0\|1\|1: 13 |
| K2 | - | 1\|0\|1\|0: 63704, 0\|2\|0\|0: 7849, 1\|1\|1\|0: 30, 1\|0\|1\|1: 13 |
| K2_noneed | - | 1\|0\|1\|0: 63704, 0\|2\|0\|0: 7849, 1\|1\|1\|0: 30, 1\|0\|1\|1: 13 |
| K2_Yany | - | 1\|0\|1\|0: 63704, 0\|2\|0\|0: 7849, 1\|1\|1\|0: 30, 1\|0\|1\|1: 13 |
| K4 | - | 1\|0\|1\|0: 63704, 0\|2\|0\|0: 7849, 1\|1\|1\|0: 30, 1\|0\|1\|1: 13 |
| K5 | - | 1\|0\|1\|0: 63704, 0\|2\|0\|0: 7849, 1\|1\|1\|0: 30, 1\|0\|1\|1: 13 |
| KU1 | - | 1\|0\|1\|0: 63704, 0\|2\|0\|0: 7849, 1\|1\|1\|0: 30, 1\|0\|1\|1: 13 |

## Implications observed (all datasets)

States: 991,768; distinct verdict vectors 3. A row "A => B" is listed when B holds wherever A holds on the data although A's relation is not inside B's (non-trivial implications), and "A =/=> B" with the number of states where A holds and B fails.

- RT4 => RC3 (on 991,631)
- RT4 => RC3_noT4 (on 991,631)
- RT4 => NA3 (on 991,631)
- RT4 => D3 (on 991,631)
- RT4 => D4 (on 991,631)
- RT4 => FR3 (on 991,631)
- RC3 => RC3_noT4 (on 991,768)
- RC3 => FR3 (on 991,768)
- RC_W1 => RC3 (on 991,768)
- RC_W1 => RC3_noT4 (on 991,768)
- RC_W1 => NA3 (on 991,768)
- RC_W1 => D3 (on 991,768)
- RC_W1 => D4 (on 991,768)
- RC_W1 => FR3 (on 991,768)
- RC => RC3 (on 991,768)
- RC => RC_W1 (on 991,768)
- RC => RC3_noT4 (on 991,768)
- RC => NA3 (on 991,768)
- RC => D3 (on 991,768)
- RC => D4 (on 991,768)
- RC => FR3 (on 991,768)
- RC_noneed => RC3 (on 991,768)
- RC_noneed => RC_W1 (on 991,768)
- RC_noneed => RC (on 991,768)
- RC_noneed => RC_Yfree (on 991,768)
- RC_noneed => RC_Yany (on 991,768)
- RC_noneed => RC_U0 (on 991,768)
- RC_noneed => RC3_noT4 (on 991,768)
- RC_noneed => NA3 (on 991,768)
- RC_noneed => D3 (on 991,768)
- RC_noneed => D4 (on 991,768)
- RC_noneed => FR3 (on 991,768)
- RC_Yfree => RC3 (on 991,768)
- RC_Yfree => RC_W1 (on 991,768)
- RC_Yfree => RC (on 991,768)
- RC_Yfree => RC_noneed (on 991,768)
- RC_Yfree => RC_Yany (on 991,768)
- RC_Yfree => RC_U0 (on 991,768)
- RC_Yfree => RC3_noT4 (on 991,768)
- RC_Yfree => NA3 (on 991,768)
- RC_Yfree => D3 (on 991,768)
- RC_Yfree => D4 (on 991,768)
- RC_Yfree => FR3 (on 991,768)
- RC_Yany => RC3 (on 991,768)
- RC_Yany => RC_W1 (on 991,768)
- RC_Yany => RC (on 991,768)
- RC_Yany => RC_noneed (on 991,768)
- RC_Yany => RC_Yfree (on 991,768)
- RC_Yany => RC_U0 (on 991,768)
- RC_Yany => RC3_noT4 (on 991,768)
- RC_Yany => NA3 (on 991,768)
- RC_Yany => D3 (on 991,768)
- RC_Yany => D4 (on 991,768)
- RC_Yany => FR3 (on 991,768)
- RC_U0 => RC3 (on 991,768)
- RC_U0 => RC_W1 (on 991,768)
- RC_U0 => RC (on 991,768)
- RC_U0 => RC_noneed (on 991,768)
- RC_U0 => RC_Yfree (on 991,768)
- RC_U0 => RC_Yany (on 991,768)
- RC_U0 => RC3_noT4 (on 991,768)
- RC_U0 => NA3 (on 991,768)
- RC_U0 => D3 (on 991,768)
- RC_U0 => D4 (on 991,768)
- RC_U0 => FR3 (on 991,768)
- RC3_noT4 => FR3 (on 991,768)
- NA3 => RC3 (on 991,768)
- NA3 => RC_W1 (on 991,768)
- NA3 => RC (on 991,768)
- NA3 => RC_noneed (on 991,768)
- NA3 => RC_Yfree (on 991,768)
- NA3 => RC_Yany (on 991,768)
- NA3 => RC_U0 (on 991,768)
- NA3 => RC3_noT4 (on 991,768)
- NA3 => NA1 (on 991,768)
- NA3 => U1Z1 (on 991,768)
- NA3 => FR3 (on 991,768)
- NA1 => RC3 (on 991,768)
- NA1 => RC_W1 (on 991,768)
- NA1 => RC (on 991,768)
- NA1 => RC_noneed (on 991,768)
- NA1 => RC_Yfree (on 991,768)
- NA1 => RC_Yany (on 991,768)
- NA1 => RC_U0 (on 991,768)
- NA1 => RC3_noT4 (on 991,768)
- NA1 => NA3 (on 991,768)
- NA1 => D3 (on 991,768)
- NA1 => D4 (on 991,768)
- NA1 => FR3 (on 991,768)
- NAbal => RC3 (on 991,768)
- NAbal => RC_W1 (on 991,768)
- NAbal => RC (on 991,768)
- NAbal => RC_noneed (on 991,768)
- NAbal => RC_Yfree (on 991,768)
- NAbal => RC_Yany (on 991,768)
- NAbal => RC_U0 (on 991,768)
- NAbal => RC3_noT4 (on 991,768)
- NAbal => NA3 (on 991,768)
- NAbal => NA1 (on 991,768)
- NAbal => U1Z1 (on 991,768)
- NAbal => D3 (on 991,768)
- NAbal => D4 (on 991,768)
- NAbal => FR3 (on 991,768)
- NAall => RC3 (on 991,768)
- NAall => RC_W1 (on 991,768)
- NAall => RC (on 991,768)
- NAall => RC_noneed (on 991,768)
- NAall => RC_Yfree (on 991,768)
- NAall => RC_Yany (on 991,768)
- NAall => RC_U0 (on 991,768)
- NAall => RC3_noT4 (on 991,768)
- NAall => NA3 (on 991,768)
- NAall => NA1 (on 991,768)
- NAall => U1Z1 (on 991,768)
- NAall => D3 (on 991,768)
- NAall => D4 (on 991,768)
- NAall => FR3 (on 991,768)
- U1Z1 => RC3 (on 991,768)
- U1Z1 => RC_W1 (on 991,768)
- U1Z1 => RC (on 991,768)
- U1Z1 => RC_noneed (on 991,768)
- U1Z1 => RC_Yfree (on 991,768)
- U1Z1 => RC_Yany (on 991,768)
- U1Z1 => RC_U0 (on 991,768)
- U1Z1 => RC3_noT4 (on 991,768)
- U1Z1 => NA3 (on 991,768)
- U1Z1 => NA1 (on 991,768)
- U1Z1 => NAbal (on 991,768)
- U1Z1 => NAall (on 991,768)
- U1Z1 => D3 (on 991,768)
- U1Z1 => D4 (on 991,768)
- U1Z1 => FR3 (on 991,768)
- D2 => RT4 (on 959,305)
- D2 => RC3 (on 959,305)
- D2 => RC_W1 (on 959,305)
- D2 => RC (on 959,305)
- D2 => RC_noneed (on 959,305)
- D2 => RC_Yfree (on 959,305)
- D2 => RC_Yany (on 959,305)
- D2 => RC_U0 (on 959,305)
- D2 => RC3_noT4 (on 959,305)
- D2 => NA3 (on 959,305)
- D2 => NA1 (on 959,305)
- D2 => NAbal (on 959,305)
- D2 => NAall (on 959,305)
- D2 => U1Z1 (on 959,305)
- D2 => FR3 (on 959,305)
- D3 => RC3 (on 991,768)
- D3 => RC_W1 (on 991,768)
- D3 => RC (on 991,768)
- D3 => RC_noneed (on 991,768)
- D3 => RC_Yfree (on 991,768)
- D3 => RC_Yany (on 991,768)
- D3 => RC_U0 (on 991,768)
- D3 => RC3_noT4 (on 991,768)
- D3 => NA3 (on 991,768)
- D3 => NA1 (on 991,768)
- D3 => NAbal (on 991,768)
- D3 => NAall (on 991,768)
- D3 => U1Z1 (on 991,768)
- D3 => FR3 (on 991,768)
- D4 => RC3 (on 991,768)
- D4 => RC_W1 (on 991,768)
- D4 => RC (on 991,768)
- D4 => RC_noneed (on 991,768)
- D4 => RC_Yfree (on 991,768)
- D4 => RC_Yany (on 991,768)
- D4 => RC_U0 (on 991,768)
- D4 => RC3_noT4 (on 991,768)
- D4 => NA3 (on 991,768)
- D4 => NA1 (on 991,768)
- D4 => NAbal (on 991,768)
- D4 => NAall (on 991,768)
- D4 => U1Z1 (on 991,768)
- D4 => D3 (on 991,768)
- D4 => FR3 (on 991,768)
- FR3 => RC3 (on 991,768)
- FR3 => RC_W1 (on 991,768)
- FR3 => RC (on 991,768)
- FR3 => RC_noneed (on 991,768)
- FR3 => RC_Yfree (on 991,768)
- FR3 => RC_Yany (on 991,768)
- FR3 => RC_U0 (on 991,768)
- FR3 => RC3_noT4 (on 991,768)
- FR3 => NA3 (on 991,768)
- FR3 => NA1 (on 991,768)
- FR3 => NAbal (on 991,768)
- FR3 => NAall (on 991,768)
- FR3 => U1Z1 (on 991,768)
- FR3 => D3 (on 991,768)
- FR3 => D4 (on 991,768)

Verdict vectors (order RT4, RC3, RC_W1, RC, RC_noneed, RC_Yfree, RC_Yany, RC_U0, RC3_noT4, NA3, NA1, NAbal, NAall, U1Z1, D2, D3, D4, FR3):

- `111111111111111111`: 959,305
- `111111111111110111`: 32,326
- `011111111111110111`: 137

Keys: 71,596; distinct verdict vectors 2. A row "A => B" is listed when B holds wherever A holds on the data although A's relation is not inside B's (non-trivial implications), and "A =/=> B" with the number of states where A holds and B fails.

- K1 => K3b (on 71,574)
- K1 => K3b_noT4 (on 71,574)
- K3b => K3b_noT4 (on 71,596)
- K3 => K3b (on 71,596)
- K3 => K3b_noT4 (on 71,596)
- K2 => K3b (on 71,596)
- K2 => K3b_noT4 (on 71,596)
- K2 => K3 (on 71,596)
- K2_noneed => K3b (on 71,596)
- K2_noneed => K3b_noT4 (on 71,596)
- K2_noneed => K3 (on 71,596)
- K2_noneed => K2 (on 71,596)
- K2_noneed => K2_Yany (on 71,596)
- K2_Yany => K3b (on 71,596)
- K2_Yany => K3b_noT4 (on 71,596)
- K2_Yany => K3 (on 71,596)
- K2_Yany => K2 (on 71,596)
- K2_Yany => K2_noneed (on 71,596)
- K4 => K3b (on 71,596)
- K4 => K3b_noT4 (on 71,596)
- K4 => K3 (on 71,596)
- K4 => K2 (on 71,596)
- K4 => K2_noneed (on 71,596)
- K4 => K2_Yany (on 71,596)
- K5 => K3b (on 71,596)
- K5 => K3b_noT4 (on 71,596)
- K5 => K3 (on 71,596)
- K5 => K2 (on 71,596)
- K5 => K2_noneed (on 71,596)
- K5 => K2_Yany (on 71,596)
- K5 => K4 (on 71,596)
- K5 => KU1 (on 71,596)
- KU1 => K3b (on 71,596)
- KU1 => K3b_noT4 (on 71,596)
- KU1 => K3 (on 71,596)
- KU1 => K2 (on 71,596)
- KU1 => K2_noneed (on 71,596)
- KU1 => K2_Yany (on 71,596)
- KU1 => K4 (on 71,596)
- KU1 => K5 (on 71,596)

Verdict vectors (order K1, K3b, K3b_noT4, K3, K2, K2_noneed, K2_Yany, K4, K5, KU1):

- `1111111111`: 71,574
- `0111111111`: 22

