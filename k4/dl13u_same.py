#!/usr/bin/env python3
"""k4/dl13u.c and k4/dl13.c give the same output (compute/k4-dl13). EVIDENCE tooling.

k4/dl13u.c is k4/dl13.c (SHA-256 f891de3a…, commit 893c778) plus (1) the -v line "U" (the slack used by
k4/dl13_hunt.py) and (2) a dedupe of the candidates generated for large classes (more than BIGPP min-frozen P). Neither
changes the flags, types, deficits, distances or the witness of a state, so the output without -v is the same, and
with -s it is the same once the "U" lines are removed. This script checks that, byte for byte, on the given inputs, for
the default builds and for the -DBIGPP=0 builds (every class hashed, so (2) is exercised).

The exhaustive n <= 3 run (results/k4_dl13/n3.log, its header shows dl13.c sha256 e5ab32ae…) was made with the source
that is now k4/dl13u.c (same SHA-256); every other run of k4/dl13_run.py uses k4/dl13.c.

usage: python3 k4/dl13u_same.py certs FILE [--cores=A:B] [--sample=P]   (every profile of each core, or P random ones)
       python3 k4/dl13u_same.py catalog FILE [--every=E]
       python3 k4/dl13u_same.py suite"""
import gzip, hashlib, json, os, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check4
from dl13_run import block


def build(src, extra=()):
    sha = hashlib.sha256(open(os.path.join(HERE, src), 'rb').read()).hexdigest()
    b = os.path.join(tempfile.gettempdir(), 'k4same_' + sha[:16] + ''.join(e.replace('=', '') for e in extra))
    if not os.path.exists(b):
        subprocess.run(['gcc', '-O2'] + list(extra) + ['-o', b + '.tmp', os.path.join(HERE, src)], check=True)
        os.replace(b + '.tmp', b)
    return b, sha


def digest(binary, inp, opts):
    r = subprocess.run([binary] + opts, input=inp, capture_output=True, text=True, check=True)
    h = hashlib.sha256(); nl = 0
    for l in r.stdout.splitlines():
        if l.startswith('U '): continue
        h.update(l.encode()); h.update(b'\n'); nl += 1
    return h.hexdigest(), nl


def main(argv):
    mode = argv[0]; rest = [a for a in argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in argv[1:] if a.startswith('--'))
    print('# command: python3 k4/dl13u_same.py ' + ' '.join(argv), flush=True)
    bins = {}
    for src in ('dl13.c', 'dl13u.c'):
        for extra in ((), ('-DBIGPP=0',)):
            b, sha = build(src, extra); bins[(src, extra)] = b
        print(f'# {src} sha256 {sha}', flush=True)
    inputs = []
    if mode == 'certs':
        cores = json.load(gzip.open(rest[0], 'rt'))['cores']
        lo, hi = 0, len(cores)
        if 'cores' in opt: a, b = opt['cores'].split(':'); lo, hi = int(a or 0), int(b or len(cores))
        P = int(opt.get('sample', 0))
        for k in range(lo, hi):
            c = cores[k]
            inputs.append((f"{os.path.basename(rest[0])}#{k}", block(c['sets'], c['m'], check4.core_domains(c['sets'], c['m'], False), k, P)))
    else:
        if mode == 'catalog':
            recs = json.load(gzip.open(rest[0], 'rt'))['records'][::int(opt.get('every', 1))]
            insts = [(r['core']['sets'], r['core']['m'], r['vals']) for r in recs]
        else:
            import glob
            insts = []
            for fn in sorted(glob.glob(os.path.join(HERE, 'suite', 'instances', '*.json'))):
                d = json.load(open(fn))
                m = d.get('m') or 1 + max(g for S in d['sets'] for g in S)
                if 'kind' in d or len(d['sets']) > 16 or m > 32: continue      # the 32-bit build's limits
                insts.append((d['sets'], m, d['vals']))
        C = 500
        for i in range(0, len(insts), C):
            inp = ''.join(block(s, m, [[dict(zip(S, V))] for S, V in zip(s, vals)], k, 0)
                          for k, (s, m, vals) in enumerate(insts[i:i + C]))
            inputs.append((f'{mode} chunk {i // C}', inp))
    bad = 0; lines = 0
    for name, inp in inputs:
        for opts in (['-r10', '-o10'], ['-s', '-r0', '-o0']):
            ds = {k: digest(b, inp, opts) for k, b in bins.items()}
            if len({d for d, _ in ds.values()}) != 1:
                bad += 1; print('DIFFERENT', name, opts, ds, flush=True)
            lines += next(iter(ds.values()))[1]
        if 'progress' in opt: print(f'#   {name}: ok so far, {bad} differences', flush=True)
    print(f'{len(inputs)} inputs, 2 option sets (-r10 -o10; -s), 4 builds (dl13.c, dl13u.c; default, -DBIGPP=0): '
          f'{lines} output lines per build compared, {bad} differences', flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
