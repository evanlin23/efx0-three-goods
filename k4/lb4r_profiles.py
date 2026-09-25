"""Run k4/lb4.c on given strict profiles, or on the K-agent neighbourhoods of seed profiles (EVIDENCE).

Seeds are the TAG lines of #30's logs (k4/gm4.md; e.g. GMALL in results/k4_gm4_gmall_seeds_4.txt, GMFAIL in
results/k4_gm4_seeds_4.txt): values in k4/check4.py's core_domains order, and the core. A neighbourhood fixes every agent's
type but K of them, which range over their whole type domain (as k4/gm4_run.py --around --vary=K); it is fed to lb4.c
as one core whose type domains are restricted, so lb4.c's exhaustive (lazy) search covers every profile of it.
Neighbourhoods are deduplicated by (core, varied agents, fixed types); overlapping ones still count their common
profiles more than once. --named runs the instances of k4/gm4_counterexample.py.
Usage: lb4r_profiles.py [--seeds=FILE[:TAG]] [--vary=K] [--named] [--jobs=J] [lb4.c options, e.g. -i1 -u3 -r3 -w1 -c1]"""
import itertools, json, os, subprocess, sys
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lb4_run
from check4 import core_domains

def seeds(spec):
    f, _, tag = spec.partition(':'); tag = tag or 'GMFAIL'
    out = set()
    for line in open(f):
        if line.startswith(tag + ' '):
            body, meta = line.split(' # ')
            vals = tuple(tuple(map(int, t.split(','))) for t in body.split(' | ')[0].split()[1:])
            out.add((int(meta.split()[0][2:]), json.dumps(json.loads(meta.split('sets=')[1])), vals))
    return sorted(out)

def encode(sets, m, doms):
    """doms[i]: list of value tuples in the order of sets[i]"""
    out = [f"{len(sets)} {m}"]
    for S, D in zip(sets, doms):
        out.append(f"{len(S)} {' '.join(map(str, S))} {len(D)}")
        out += [' '.join(map(str, v)) for v in D]
    return '\n'.join(out) + '\n'

def run(task):
    inp, opts = task
    p = subprocess.run([lb4_run.BIN] + opts, input=inp, capture_output=True, text=True)
    if p.returncode: raise RuntimeError(p.stderr[-2000:])
    res = []
    for l in p.stdout.split('\n'):
        if l.startswith('total '):
            t = l.split(); res.append(dict(zip(t[0:22:2], map(int, t[1:22:2]))))
    return res, [l for l in p.stderr.split('\n') if l.startswith('FAIL') or l.startswith('RAWFAIL')]

def main():
    args = sys.argv[1:]
    opts = [a for a in args if a.startswith('-') and not a.startswith('--')]
    kw = dict(a[2:].split('=', 1) if '=' in a else (a[2:], '1') for a in args if a.startswith('--'))
    jobs = int(kw.get('jobs', os.cpu_count()))
    lb4_run.build()
    inputs = []
    if 'named' in kw:
        import gm4_counterexample as G
        for label, vals, Y, kind in G.INSTANCES:
            m = 1 + max(g for d in vals for g in d)
            sets = [sorted(d) for d in vals]
            inputs.append((label, encode(sets, m, [[tuple(d[g] for g in S)] for d, S in zip(vals, sets)])))
    if 'seeds' in kw:
        K = int(kw.get('vary', 0)); keys = set()
        for m, sj, vals in seeds(kw['seeds']):
            sets = json.loads(sj)
            dv = [[tuple(d[g] for g in S) for d in D] for S, D in zip(sets, core_domains(sets, m, False))]
            for A in itertools.combinations(range(len(sets)), K):
                key = (sj, A, tuple(v for i, v in enumerate(vals) if i not in A))
                if key in keys: continue
                keys.add(key)
                doms = [dv[i] if i in A else [vals[i]] for i in range(len(sets))]
                inputs.append((f"m={m} sets={sj} vary={A}", encode(sets, m, doms)))
    print('#', 'lb4r_profiles.py', ' '.join(args), f'({len(inputs)} inputs)', flush=True)
    tot = {}; fails = []
    with Pool(jobs) as pool:
        for (label, _), (res, fl) in zip(inputs, pool.imap(run, [(inp, opts) for _, inp in inputs], chunksize=4)):
            for kv in res:
                for k, v in kv.items(): tot[k] = tot.get(k, 0) + v
            if any(kv['fails'] or kv['rawfails'] for kv in res): fails.append((label, fl[:2]))
            if 'named' in kw and 'seeds' not in kw: print(f"  {label}: {res[0]['total']} run-profile pairs, fails {res[0]['fails']}, raw {res[0]['rawfails']}")
    print('  ' + ' '.join(f"{k}={v}" for k, v in tot.items()))
    print(f"  inputs with a failure: {len(fails)}")
    for f in fails[:10]: print('   ', f)

if __name__ == '__main__':
    main()
