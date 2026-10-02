"""For k4/lemmam_x.md §7.3 ((L1∃) at n = 4): the profiles without an insertion sequence whose non-last blocks all have
block count 0 (k4/lemmam_x.c -A46 -D46, best = cap + 2), and the greedy run's rotations d on exactly those profiles
(-A44 -D44 on the cores that have them; a profile without an ADPBAD line has d = 0). One implementation
(k4/lemmam_x.c); after the PR #77 audit's check (its scratch script l46_vs_greedy.py), redone here.
Usage: lemmam_x_l46greedy.py FILE [C options]      e.g. results/k4_certs_4_n4_2.json.gz -Y1 -r1 [-G1]"""
import collections, gzip, json, os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import adaptive_run as AR
import lemmam_x_run as LR


def main():
    f = sys.argv[1]
    opts = sys.argv[2:]
    LR.build()
    print('#', 'lemmam_x_l46greedy.py', ' '.join(sys.argv[1:]), '# lemmam_x.c sha256', LR.SHA, flush=True)
    rot = next((int(o[2:]) for o in opts if o.startswith('-r')), 2)
    data = json.load(gzip.open(f, 'rt'))
    fails = collections.defaultdict(dict)       # core -> {(sets, vals): weight}
    hist = None
    for i, c in enumerate(data['cores']):
        lines = LR.run(AR.encode_core(c['sets'], c['m']), opts + ['-A46', '-D46'])
        for l in lines:
            m = re.match(r'L46 w=(\d+) best=(\d+) runs=\d+ sets=(\S+) vals=(\S+)', l)
            if m and int(m.group(2)) == rot + 2:
                fails[i][(m.group(3), m.group(4))] = int(m.group(1))
            m = re.match(r'L46 hist (.*)', l)
            if m:
                h = list(map(int, m.group(1).split()))
                hist = h if hist is None else [x + y for x, y in zip(hist, h)]
    tot = sum(w for c in fails for w in fails[c].values())
    print(f"(L1∃) histogram (d = 0, 1, ..., cap; none certified; no sequence): {hist}")
    print(f"profiles with no sequence: {tot} (weighted), {sum(len(v) for v in fails.values())} leaves, cores"
          f" {sorted(fails)}", flush=True)
    gd = collections.Counter()
    small = None
    for i in sorted(fails):
        c = data['cores'][i]
        lines = LR.run(AR.encode_core(c['sets'], c['m']), opts + ['-A44', '-D44'])
        bad = {}
        for l in lines:
            m = re.match(r'ADPBAD w=\d+ d=(\d+) sets=(\S+) vals=(\S+)', l)
            if m:
                bad[(m.group(2), m.group(3))] = int(m.group(1))
        for k, w in fails[i].items():
            gd[bad.get(k, 0)] += w
            if small is None or c['m'] < small[0]:
                small = (c['m'], i, k)
    print(f"greedy rotations d on those profiles (weighted): {dict(sorted(gd.items()))}")
    if small:
        print(f"smallest: m = {small[0]}, core {small[1]}: sets={small[2][0]} vals={small[2][1]}")


if __name__ == '__main__':
    main()
