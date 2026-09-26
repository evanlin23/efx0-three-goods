"""Driver for k4/c4check.c -X -Y (k4/c4one.md): the runs with exactly one 4-good agent q that the theorems of
k4/c4.md §2-§4c do not prove, by case, with the repairs that work. Every strict profile of every core with exactly one
4-good agent in the given certificate files, every insertion sequence (-i1), envy-free upgrades (-u2).
Repairs (bits of mask): 1 owner r; 2 another owner, no rotation; 4 owner q, no rotation; 8 q rotated along a need
chain (to any end) taking every good of R_q in J, then owner q or none; 16 lb4.c's single-rotation search (-r1 -w0 -c0);
32 owner t for a terminal t that ends a need chain from a frozen q.
"first" = q is processed first (the first insertion step picks q).
Usage: c4one_run.py FILE [FILE ...] [--jobs=J]"""
import gzip, json, os, subprocess, sys, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import c4check_run, lb4_run
OPTS = ['-X', '-Y', '-i1', '-u2', '-o0', '-r1', '-w0', '-c0', '-f5']
BITS = [(1, 'r'), (2, 'other owner'), (4, 'q owner'), (8, 'rotate q'), (16, 'any 1 rotation'), (32, 'owner t (end of a chain from q)')]

def run(recs):
    inp = ''.join(lb4_run.encode(r['sets'], r['m'], False) for r in recs)
    p = subprocess.run([c4check_run.BIN] + OPTS, input=inp, capture_output=True, text=True)
    if p.returncode: raise RuntimeError(p.stderr[-2000:])
    Y = {}; viol = []
    for line in p.stderr.split('\n'):
        if line.startswith('C4Y'):
            kv = dict(x.split('=') for x in line.split()[1:])
            key = (int(kv['first']), kv['cls'], int(kv['mask'])); Y[key] = Y.get(key, 0) + int(kv['n'])
        elif line.startswith('C4CHK') or line.startswith('FAIL') or not line.strip(): continue
        else: viol.append(line)
    return Y, viol

def main():
    args = sys.argv[1:]
    files = [a for a in args if not a.startswith('-')]
    jobs = int(next((a.split('=')[1] for a in args if a.startswith('--jobs=')), os.cpu_count()))
    c4check_run.build()
    print('# c4one_run.py', ' '.join(args), 'options', ' '.join(OPTS), flush=True)
    for f in files:
        t0 = time.time()
        cores = [c for c in json.load(gzip.open(f, 'rt'))['cores'] if sum(len(s) == 4 for s in c['sets']) == 1]
        tasks = [cores[i:i + 2] for i in range(0, len(cores), 2)]
        Y = {}; viol = []
        with Pool(jobs) as pool:
            for y, v in pool.imap_unordered(run, tasks):
                for k, x in y.items(): Y[k] = Y.get(k, 0) + x
                viol += v
        print(f"{f}: {len(cores)} cores with one 4-good agent, {time.time() - t0:.0f}s")
        for first in (0, 1):
            tot = sum(x for (fi, c, mk), x in Y.items() if fi == first)
            pr = sum(x for (fi, c, mk), x in Y.items() if fi == first and c == 'proved')
            print(f"  {'q first' if first else 'q not first'}: runs needing an owner {tot}, proved {pr}")
            for cls in ['G2', 'G1F_nochain', 'G1F_cond', 'G1T_Tc', 'G1T_Tb', 'other']:
                rows = {mk: x for (fi, c, mk), x in Y.items() if fi == first and c == cls}
                if not rows: continue
                n = sum(rows.values())
                cnt = {nm: sum(x for mk, x in rows.items() if mk & b) for b, nm in BITS}
                print(f"    {cls}: {n}; works: " + ', '.join(f'{nm} {cnt[nm]}' for b, nm in BITS))
                print('      masks: ' + ' '.join(f'{mk}:{x}' for mk, x in sorted(rows.items())))
        print(f"  violation lines: {len(viol)}")
        for l in viol[:5]: print('   ', l)
        sys.stdout.flush()

if __name__ == '__main__':
    main()
