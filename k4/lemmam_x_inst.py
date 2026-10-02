"""Instances for k4/lemmam_x.md: H_t (k4/c4.md §7, built by k4/adaptive_H.py), HH_t (two copies of H_t sharing l's good
u, k4/lemmam_bt.md §3, PR #83, rebuilt here from its text), and relabelings of both.
Usage: lemmam_x_inst.py NAME [NAME ...] [--relabel=K] [--seed=S] > FILE    (NAME: H<t> or HH<t>, or SUITE: every strict
core of k4/suite/instances except c4-H5, which is H5)
Writes one {"name", "sets", "vals"} line per instance (K seeded relabelings after each original)."""
import glob, json, os, random, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import adaptive_H as AH


def build_hh(t):
    """agents l_A, l_B, A's gadget agents, B's gadget agents (each in H_t's order); B's good u is A's u"""
    S, V, m = AH.build(t)
    u = t + 1                                   # adaptive_H.build: g_1..g_t, z, u, u', then a, b, c per gadget
    SA = [list(s) for s in S]
    SB = [[g + m for g in s] for s in S]
    SB[0] = [u if g == u + m else g for g in SB[0]]
    sets = [SA[0], SB[0]] + SA[1:] + SB[1:]
    vals = [V[0], V[0]] + V[1:] + V[1:]
    used = sorted(set(g for s in sets for g in s))
    ren = {g: i for i, g in enumerate(used)}
    return [[ren[g] for g in s] for s in sets], vals, len(used)


def build(name):
    if name.startswith('HH'):
        return build_hh(int(name[2:]))
    return AH.build(int(name[1:]))


def main():
    args = sys.argv[1:]
    names = [a for a in args if not a.startswith('--')]
    K = int(next((a.split('=')[1] for a in args if a.startswith('--relabel=')), 0))
    seed = int(next((a.split('=')[1] for a in args if a.startswith('--seed=')), 1))
    for nm in names:
        if nm == 'SUITE':
            for f in sorted(glob.glob(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'suite', 'instances', '*.json'))):
                o = json.load(open(f))
                if o.get('is_core') and o.get('strict') and o['id'] != 'c4-H5':
                    print(json.dumps({'name': o['id'], 'sets': o['sets'], 'vals': o['vals']}))
            continue
        sets, vals, m = build(nm)
        print(json.dumps({'name': nm, 'sets': sets, 'vals': vals}))
        rng = random.Random(seed * 1000 + len(nm) * 100 + int(nm.lstrip('H')))
        for p in range(K):
            S, V, pa = AH.relabel(sets, vals, m, rng)
            print(json.dumps({'name': f'{nm} relabel {p + 1}', 'sets': S, 'vals': V}))


if __name__ == '__main__':
    main()
