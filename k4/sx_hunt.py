#!/usr/bin/env python3
"""Collect strict f = 1 profiles that have a non-completable key (def*(κ) > 0), using PR #51's C tool k4/red.c
(k4/c4min_reduce.md; its counter key_noncompletable: a key none of whose configurations has a valid owner, which by
k4/c4min.md Lemma 1 in its per-key form, k4/sx.md Lemma 0, is def*(κ) > 0). Workstream proof/k4-sx; EVIDENCE tooling.

The driver runs red.c on every core of a certificate file (random strict profiles per core, seeded as
k4/red_run.py does: seed + core index), one process at a time, with the example limit raised, and keeps the profiles
that red.c prints under key_noncompletable (deduplicated). Output: gzip JSON lines in the format of
k4/sx_keygraph.py --dump (src, sets, vals, m, f = 1), for k4/sx_zprime.py and k4/sx_keygraph.py.

usage: python3 k4/sx_hunt.py CERTS.json.gz --rand=R [--seed=S] [--cores=a:b] --out=OUT.jsonl.gz"""
import gzip, json, os, re, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from red_run import binary, core_input, provenance


def parse(line):
    m = re.match(r'EX key_noncompletable n=(\d+) m=(\d+) vals=\[(.*)\]$', line)
    if not m: return None
    n, mm = int(m.group(1)), int(m.group(2))
    agents = re.findall(r'\{([^}]*)\}', m.group(3))
    sets, vals = [], []
    for a in agents:
        pr = [tuple(map(int, t.split(':'))) for t in a.split(',')]
        sets.append([g for g, _ in pr]); vals.append([v for _, v in pr])
    assert len(sets) == n
    return {'sets': sets, 'vals': vals, 'm': mm}


def main(argv):
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    f = [a for a in argv if not a.startswith('--')][0]
    rand = int(opt['rand']); seed = int(opt.get('seed', 1))
    print('# command: python3 k4/sx_hunt.py ' + ' '.join(argv)); print(provenance(), flush=True)
    b = binary()
    cores = json.load(gzip.open(f, 'rt'))['cores']
    lo, hi = (map(int, opt['cores'].split(':')) if 'cores' in opt else (0, len(cores)))
    seen = set(); out = gzip.open(opt['out'], 'wt'); t0 = time.time(); tot = {}
    for ci in range(lo, min(hi, len(cores))):
        c = cores[ci]
        p = subprocess.run([b, '-x', '1000000'], input=core_input(c['n'], c['m'], c['sets'], rand, seed + ci),
                           capture_output=True, text=True, check=True)
        for line in p.stdout.splitlines():
            if line.startswith('EX '):
                d = parse(line)
                if d is None: continue
                kk = json.dumps(d, sort_keys=True)
                if kk in seen: continue
                seen.add(kk)
                d2 = {'src': '%s#%d' % (os.path.basename(f), ci), 'f': 1}; d2.update(d)
                out.write(json.dumps(d2, separators=(',', ':')) + '\n')
            else:
                k, v = line.split(); tot[k] = tot.get(k, 0) + int(v)
    out.close()
    print('# cores %d:%d rand=%d seed=%d time=%.1fs' % (lo, min(hi, len(cores)), rand, seed, time.time() - t0))
    for k in ('profiles', 'f1', 'keys', 'key_noncompletable'): print('%-24s %d' % (k, tot.get(k, 0)))
    print('distinct profiles with a non-completable key: %d' % len(seen))


if __name__ == '__main__':
    main(sys.argv[1:])
