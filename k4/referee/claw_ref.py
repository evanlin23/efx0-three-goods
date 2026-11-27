#!/usr/bin/env python3
"""Referee check (concrete instances, brute force) of the K4.MC9 certificates (k4/TWINS.md §4, branch proof/k4-twins-2
at ea71fb54; results/k4_twins/claw.json.gz, claw_y12.json.gz, claw_y123.json.gz). Same method and own code as the
K4.MC8 check (twins_ref.py; nothing from k4/ is run or imported): random concrete instances H containing the claw
configuration (f1, f2, f3 on G, y_i, p_i with random strict balanced values; 2-3 outside agents on random subsets of
the boundary goods and 2-3 outside goods), every record with fixed gadgets (DEL, one gadget agent, or the two gadget
agents h1, h2 with their gadget goods), every EFX0 allocation Y of H' with an acyclic envy graph and every unenvied
bundle; the local state looked up; every stored extension realized and tested by raw EFX0 on H (domination: S safe ⟹
all safe; coverage: some record works for H). All three configurations are claimed for every profile.
Also: the 𝒞_β count for every two-agent gadget record (forest on the boundary goods, supports ⊆ ∂ plus one own
gadget good, <= 4 goods per gadget agent)."""
import sys, json, gzip
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import twins_ref

def gadget_shapes(files):
    from collections import Counter
    c = Counter()
    for fn in files:
        for r in json.load(gzip.open(fn)):
            D = set(r["D"]); sps = sorted(r["Sp"])
            if len(sps) != 2:
                continue
            sup = {s: {g for g, x in r["Sp"][s]["fix"].items() if x > 0} for s in sps}
            ok = True
            own = []
            for s in sps:
                T = sup[s] & D; Z = sup[s] - D
                ok &= len(Z) == 1 and len(sup[s]) <= 4 and Z <= set(r["Ip"])
                own.append(Z)
            ok &= not (own[0] & own[1])
            # forest on the boundary goods: |T1| + |T2| <= #vertices - #components
            T1, T2 = (sup[s] & D for s in sps)
            verts = 2 + len(T1 | T2); comps = 1 if T1 & T2 else 2
            ok &= len(T1) + len(T2) <= verts - comps
            c[f"{r['config']}_two_agent_records"] += 1; c[f"{r['config']}_legal_forest"] += ok
    print(json.dumps(dict(source="K4.MC9 two-agent gadget shapes", **dict(sorted(c.items())))))

if __name__ == "__main__":
    if sys.argv[1] == "shapes":
        gadget_shapes(sys.argv[2].split(",")); sys.exit()
    twins_ref.EXCLUDED |= {"claw", "claw-y12", "claw-y123"}; twins_ref.LABEL = "K4.MC9"
    files = sys.argv[1].split(","); N = int(sys.argv[2]); seed = int(sys.argv[3])
    cfgs = sys.argv[4].split(",") if len(sys.argv) > 4 and sys.argv[4] != "all" else None
    if len(sys.argv) > 5:
        twins_ref.MUT = sys.argv[5]
    twins_ref.main(files, N, seed, cfgs)
