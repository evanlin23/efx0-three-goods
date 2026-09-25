"""PS-selected placement rules H(w, d, h) for k4/induct.md §5 (k4/induct.c task H).

Rule H(w, d, h): delete the good d ∈ R_w (w a 4-good agent); among the EFX0 allocations X' of I - d take those with
the fewest agents envying h; the rule *works* if giving d to h keeps EFX0 for every such X'.
Per profile and 4-good agent w it records which kinds of rule work (h = w, h another valuer of d, h a non-valuer;
d = w's least good, d private), split by the kind of w (P4/PP4: has a private good; Q4: none), and, over the cores
whose 4-good agents are all Q4, whether any rule (w, d, h) works.

Usage: python3 k4/induct_rules.py CERTS.json.gz [...] [--samples=S] [--seed=K] [--jobs=J] [--max-cores=C] [--log=OUT]
"""
import gzip, json, os, random, subprocess, sys, time
from collections import Counter
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from induct_run import domain, build, BIN


def run(batch):
    inp = []; meta = []
    for sets, m, prof in batch:
        V = [[0] * m for _ in sets]
        for i, (S, t) in enumerate(zip(sets, prof)):
            for g, x in zip(S, t): V[i][g] = x
        T = [(w, d, h) for w, S in enumerate(sets) if len(S) == 4 for d in S for h in range(len(sets))]
        inp.append(f'{len(sets)} {m}'); inp += [' '.join(map(str, r)) for r in V]; inp.append(str(len(T)))
        inp += [f'H {w} {d} {h}' for w, d, h in T]
        meta.append((sets, m, prof, T))
    out = [l for l in subprocess.run([BIN], input='\n'.join(inp) + '\n', capture_output=True, text=True,
                                     check=True).stdout.split('\n') if l.startswith('TASK')]
    res = []; k = 0
    for sets, m, prof, T in meta:
        rows = []
        for (w, d, h) in T:
            f = out[k].split('|'); k += 1
            nmin, nok = int(f[3].split()[1]), int(f[3].split()[3])
            rows.append((w, d, h, nmin == nok))
        res.append((sets, m, prof, rows))
    return res


def main():
    argv = sys.argv[1:]
    files = [a for a in argv if not a.startswith('--')]
    opt = {a.split('=')[0][2:]: (a.split('=', 1)[1] if '=' in a else True) for a in argv if a.startswith('--')}
    samples = int(opt.get('samples', 20)); seed = int(opt.get('seed', 1)); jobs = int(opt.get('jobs', 4))
    maxc = int(opt.get('max-cores', 10 ** 9))
    logf = open(opt['log'], 'w') if 'log' in opt else None
    def log(s):
        print(s, flush=True)
        if logf: logf.write(s + '\n'); logf.flush()
    build()
    log('command: python3 k4/induct_rules.py ' + ' '.join(argv))
    rng = random.Random(seed)
    work = []
    for fn in files:
        for c in json.load(gzip.open(fn))['cores'][:maxc]:
            sets, m = c['sets'], c['m']
            deg = [sum(g in S for S in sets) for g in range(m)]
            doms = [domain(S, deg) for S in sets]
            work += [(sets, m, tuple(rng.choice(D) for D in doms)) for _ in range(samples)]
    log(f'{len(work)} (core, profile) pairs')
    t0 = time.time()
    C = Counter(); allq4 = Counter(); ex = []
    with Pool(jobs) as pool:
        for res in pool.imap_unordered(run, [work[i:i + 10] for i in range(0, len(work), 10)]):
            for sets, m, prof, rows in res:
                deg = [sum(g in S for S in sets) for g in range(m)]
                ws = sorted({r[0] for r in rows})
                kinds = {}
                for w in ws:
                    kind = 'P4' if any(deg[g] == 1 for g in sets[w]) else 'Q4'
                    kinds[w] = kind
                    R = [r for r in rows if r[0] == w]
                    least = min(sets[w], key=lambda g: prof[w][sets[w].index(g)])
                    C[(kind, 'agents')] += 1
                    C[(kind, 'some (d, h) works')] += any(r[3] for r in R)
                    C[(kind, 'h = w, some d')] += any(r[3] for r in R if r[2] == w)
                    C[(kind, 'h another valuer of d, some d')] += any(r[3] for r in R if r[2] != w and r[1] in sets[r[2]])
                    C[(kind, 'h a non-valuer of d, some d')] += any(r[3] for r in R if r[1] not in sets[r[2]])
                    C[(kind, 'd = least, some h')] += any(r[3] for r in R if r[1] == least)
                    if kind == 'P4':
                        C[(kind, 'd private, h = w')] += any(r[3] for r in R if deg[r[1]] == 1 and r[2] == w)
                if all(k == 'Q4' for k in kinds.values()):
                    allq4['profiles'] += 1
                    ok = any(r[3] for r in rows)
                    allq4['some (w, d, h) works'] += ok
                    if not ok:
                        cand = (m, sets, [list(t) for t in prof])
                        ex.append(cand); ex.sort(key=lambda z: z[0]); del ex[3:]
    log(f'time {time.time() - t0:.1f}s')
    for k in sorted(C): log(f'{k[0]} agents: {k[1]}: {C[k]}')
    log(f'cores whose 4-good agents are all Q4: {allq4["profiles"]} profiles; some rule (w, d, h) works on '
        f'{allq4["some (w, d, h) works"]}')
    for m, sets, prof in ex: log(f'  no rule works: m={m} sets={sets} prof={prof}')


if __name__ == '__main__':
    main()
