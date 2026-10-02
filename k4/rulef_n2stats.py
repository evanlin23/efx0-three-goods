"""Two counts on the n = 2 leaves (k4/rulef.md §2 Remark 1; attempts/k4-rulef-frozen-free-owner.md).

Reads the DATA lines of `k4/rulef.c -A40 -C3 -r1 -D3` on results/k4_certs_2.json.gz (every leaf, with its weight w and,
per first agent, the deficits of the counts and LB4r's fewest rotations) and prints
  (1) containment: for every leaf, first agent and count X in {A4+N, A4+(o), refined, refined with a kept set} (each
      with its upgrade policy), the number of checks "X's deficit <= 0 implies Lemma K's deficit <= 0 (same policy)" and
      the exceptions (unweighted: leaves x first agents x 6 pairs);
  (2) frozen-free states: (profile, first agent) pairs, weighted by w, with no frozen agent after need-shrinking
      upgrades, omega >= 1 and Lemma K's deficit > 0; and among them those on which LB4r needs a rotation (rot >= 1).
Usage: python3 k4/rulef_n2stats.py DATAFILE"""
import json, re, sys
F = ['rot', 'cov', 'dN', 'dE', 'hN', 'hE', 'omN', 'omE', 'fz', 'e4', 'r', 'uN', 'uE', 'kN', 'kE', 'c40']
PAIRS = (('dN', 'kN'), ('dE', 'kE'), ('hN', 'kN'), ('hE', 'kE'), ('uN', 'kN'), ('uE', 'kE'))


def main():
    path = sys.argv[1]
    leaves = profiles = checks = bad = ff = ffrot = 0
    for line in open(path):
        if not line.startswith('DATA'):
            continue
        w = int(re.search(r'w=(\d+)', line).group(1))
        fa = [dict(zip(F, map(int, x.split(':')[1].split(',')))) for x in line.split('fa=')[1].strip().split(';')]
        leaves += 1; profiles += w
        for f in fa:
            for a, b in PAIRS:
                checks += 1
                bad += f[a] <= 0 and f[b] > 0
            if f['fz'] == 0 and f['omN'] >= 1 and f['kN'] > 0:
                ff += w
                ffrot += w * (f['rot'] >= 1)
    print(f"{path}: leaves {leaves}, profiles {profiles}")
    print(f"(1) count <= 0 implies Lemma K <= 0: {checks} checks, {bad} exceptions")
    print(f"(2) no frozen agent after need-shrinking upgrades, omega >= 1, Lemma K deficit > 0: {ff} (profile, first "
          f"agent) pairs; LB4r needs a rotation on {ffrot} of them")


if __name__ == '__main__':
    main()
