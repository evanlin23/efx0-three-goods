"""For every n = 6, m = 10 core on which model C2 (all bundles <= 2) fails, count the ranking profiles (of 6^6) with no
C2 allocation. Reads frontier_results_5_6.json (run frontier.py 5 6 first). Hypergraphs run in parallel (--jobs=N)."""
import sys, json, itertools, os, multiprocessing, statistics
from frontier import build, options

def density(sets):
    S, sel, _ = build(6, 10, [tuple(T) for T in sets], 'C2')
    bad = sum(not S.solve(assumptions=[sel[(i, prof[i])] for i in range(6)]) for prof in itertools.product(range(6), repeat=6))
    S.delete(); return bad

if __name__ == '__main__':
    _, opts = options(sys.argv[1:])
    fails = [r['sets'] for r in json.load(open('frontier_results_5_6.json'))
             if r['n'] == 6 and r['m'] == 10 and r['modes']['C2']['status'] == 'FAIL']
    with multiprocessing.Pool(int(opts.get('jobs', os.cpu_count()))) as pool: bad = pool.map(density, fails)
    for sets, b in sorted(zip(fails, bad), key=lambda t: t[1]): print(f"{b:5d}/46656  {sets}")
    print(f"{len(bad)} hypergraphs; failing profiles per hypergraph: min {min(bad)}, median {statistics.median(bad)}, "
          f"max {max(bad)}; hypergraphs with <= 36 failing profiles: {sum(b <= 36 for b in bad)}")
