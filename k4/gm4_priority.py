"""Fixed-priority potential under every agent order (k4/gm4.md §6).  For each profile in the tagged lines of the
given files (GMFAIL / GMALL lines of gm4_fast.c), and each of the n! orders of the agents, runs gm4_fast.c -DW=4
(maximize the level vector in agent order, lexicographically) on the profile with the agents in that order, and
reports for how many orders some maximum (pfail) / every maximum (pallfail) admits no placement.  EVIDENCE only.
Usage: gm4_priority.py FILE[,FILE...] [TAG]"""
import itertools, json, os, subprocess, sys
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gm4_run import build

def run(args):
    exe, sets, vals, perm = args
    n, m = len(sets), 1 + max(g for S in sets for g in S)
    lines = [f"{n} {m}"] + [" ".join(map(str, [len(sets[p])] + sets[p])) for p in perm]
    for p in perm: lines += ["1", " ".join(map(str, vals[p]))]
    lines.append("0 0 1")
    out = subprocess.run([exe], input="\n".join(lines) + "\n", capture_output=True, text=True).stdout
    kv = dict(x.split('=') for x in [l for l in out.splitlines() if l.startswith('RESULT')][0].split()[1:])
    return int(kv['pfail']), int(kv['pallfail'])

def main():
    tag = sys.argv[2] if len(sys.argv) > 2 else 'GMFAIL'
    exe = build('-DW=4', 'gm4_fast')
    profs, seen = [], set()
    for f in sys.argv[1].split(','):
        for line in open(f):
            if not line.startswith(tag + ' '): continue
            body, meta = line.split(' # ')
            vals = [list(map(int, t.split(','))) for t in body.split(' | ')[0].split()[1:]]
            sets = json.loads(meta.split('sets=')[1])
            k = json.dumps([sets, vals])
            if k not in seen: seen.add(k); profs.append((sets, vals))
    print(f"# fixed priority (gm4_fast.c -DW=4) under all agent orders, {len(profs)} profiles from {sys.argv[1]} ({tag})", flush=True)
    tot = {'profiles': 0, 'orders': 0, 'orders_pfail': 0, 'orders_pallfail': 0, 'profiles_some_order_bad': 0,
           'profiles_every_order_all_bad': 0, 'profiles_some_order_all_bad': 0}
    with Pool(os.cpu_count()) as pool:
        for sets, vals in profs:
            perms = list(itertools.permutations(range(len(sets))))
            res = pool.map(run, [(exe, sets, vals, p) for p in perms])
            pf, pa = sum(r[0] for r in res), sum(r[1] for r in res)
            tot['profiles'] += 1; tot['orders'] += len(perms); tot['orders_pfail'] += pf; tot['orders_pallfail'] += pa
            tot['profiles_some_order_bad'] += pf > 0; tot['profiles_some_order_all_bad'] += pa > 0
            tot['profiles_every_order_all_bad'] += pa == len(perms)
            if pa: print(f"ALLBAD orders={pa}/{len(perms)} sets={json.dumps(sets)} vals={json.dumps(vals)}", flush=True)
    print('TOTAL', ' '.join(f"{k}={v}" for k, v in tot.items()))

if __name__ == '__main__':
    main()
