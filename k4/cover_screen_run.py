#!/usr/bin/env python3
"""Driver for k4/cover_screen.c (workstream compute/k4-cover; EVIDENCE tooling): runs it on the cores of a certificate
file (types from k4/check4.py through k4/red_run.py's core_input, as k4/red.c and k4/sx_hunt.py; random profiles per
core seeded with seed + core index, red.c's generator), in parallel, and keeps every profile that has a key with
def* > 0 (no completable configuration) and a fewest-frozen count f in the range asked for.

Resumable: one checkpoint per run (OUT.ckpt.jsonl, one line per finished core with its counters and hits); a rerun
skips the finished cores. At the end it writes OUT (gzip JSON lines in k4/sx_keygraph.py --dump's format: src, sets,
vals, m, f) and prints the summed counters.

usage: python3 k4/cover_screen_run.py CERTS.json.gz --rand=R [--seed=S] [--cores=a:b] [--f=a:b] [--jobs=J]
       [--maxhits=H (per core)] [--bt=all] --out=OUT.jsonl.gz
--rand=0 enumerates every strict profile of each core. --bt=all keeps only the big-top types of every 4-good agent."""
import gzip, hashlib, json, os, re, subprocess, sys, tempfile, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from red_run import core_input
from check4 import core_domains


def make_input(c, rand, seed, bt):
    """k4/red_run.py's core_input; with bt = 'all' every 4-good agent keeps only its big-top types (top > second +
    third), as k4/dl13_run.py --bt=all"""
    if bt != 'all': return core_input(c['n'], c['m'], c['sets'], rand, seed)
    doms = core_domains(c['sets'], c['m'], False)
    doms = [D if len(S) != 4 else [d for d in D if (lambda w: w[3] > w[2] + w[1])(sorted(d[g] for g in S))]
            for D, S in zip(doms, c['sets'])]
    lines = ['%d %d' % (c['n'], c['m'])]
    for S, D in zip(c['sets'], doms):
        lines.append('%d %s %d' % (len(S), ' '.join(map(str, S)), len(D)))
        for vals in D: lines.append(' '.join(str(vals[g]) for g in S))
    lines.append('%d %d' % (rand, seed))
    return '\n'.join(lines) + '\n'


def binary():
    src = os.path.join(HERE, 'cover_screen.c')
    h = hashlib.sha1(open(src, 'rb').read()).hexdigest()[:12]
    out = os.path.join(tempfile.gettempdir(), 'cover_screen_' + h)
    if not os.path.exists(out):
        subprocess.run(['gcc', '-O2', '-o', out + '.tmp%d' % os.getpid(), src], check=True)
        os.replace(out + '.tmp%d' % os.getpid(), out)
    return out


def parse_hit(line, n, m):
    p = line.split(None, 5)
    f, om = int(p[1]), int(p[2])
    agents = re.findall(r'\[([^\]]*)\]', p[5])
    sets, vals = [], []
    for a in agents:
        pr = [tuple(map(int, t.split(':'))) for t in a.split(',')]
        sets.append([g for g, _ in pr]); vals.append([v for _, v in pr])
    assert len(sets) == n
    return {'sets': sets, 'vals': vals, 'm': m, 'f': f, 'omega': om}


def run(task):
    b, ci, c, rand, seed, fr, maxhits, tag, bt = task
    args = [b, '-f', fr] + (['-x', str(maxhits)] if maxhits is not None else [])
    p = subprocess.run(args, input=make_input(c, rand, seed + ci, bt),
                       capture_output=True, text=True, check=True)
    cnt, hits = {}, []
    for line in p.stdout.splitlines():
        if line.startswith('HIT '):
            d = parse_hit(line, c['n'], c['m']); d['src'] = '%s#%d' % (tag, ci); hits.append(d)
        elif line.startswith('C '):
            _, k, v = line.split(); cnt[k] = int(v)
    return ci, cnt, hits


def main(argv):
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    f = [a for a in argv if not a.startswith('--')][0]
    rand = int(opt['rand']); seed = int(opt.get('seed', 1)); fr = opt.get('f', '1:99')
    jobs = int(opt.get('jobs', os.cpu_count())); maxhits = int(opt['maxhits']) if 'maxhits' in opt else None
    out = opt['out']; ck = out + '.ckpt.jsonl'
    print('# command: python3 k4/cover_screen_run.py ' + ' '.join(argv), flush=True)
    print('# source: k4/cover_screen.c sha1 %s' % hashlib.sha1(open(os.path.join(HERE, 'cover_screen.c'), 'rb').read()).hexdigest())
    b = binary()
    cores = json.load(gzip.open(f, 'rt'))['cores']
    lo, hi = (map(int, opt['cores'].split(':')) if 'cores' in opt else (0, len(cores)))
    hi = min(hi, len(cores))
    done = {}
    if os.path.exists(ck):
        for line in open(ck):
            try: r = json.loads(line)
            except ValueError: continue          # a torn last line
            done[r['ci']] = r
    tag = os.path.basename(f).replace('.json.gz', '')
    tasks = [(b, ci, cores[ci], rand, seed, fr, maxhits, tag, opt.get('bt')) for ci in range(lo, hi) if ci not in done]
    t0 = time.time()
    with open(ck, 'a') as fo, Pool(jobs) as pool:
        for ci, cnt, hits in pool.imap_unordered(run, tasks):
            r = {'ci': ci, 'cnt': cnt, 'hits': hits}
            fo.write(json.dumps(r, separators=(',', ':')) + '\n'); fo.flush()
            done[ci] = r
    tot = {}; nh = 0
    with gzip.open(out, 'wt') as fo:
        for ci in sorted(done):
            if not lo <= ci < hi: continue
            for k, v in done[ci]['cnt'].items(): tot[k] = tot.get(k, 0) + v
            for d in done[ci]['hits']:
                fo.write(json.dumps(d, separators=(',', ':')) + '\n'); nh += 1
    print('# cores %d:%d rand=%d seed=%d f=%s bt=%s time=%.1fs (this invocation)' % (lo, hi, rand, seed, fr, opt.get('bt'),
                                                                               time.time() - t0))
    for k in sorted(tot, key=lambda s: (len(s), s)): print('%-40s %d' % (k, tot[k]))
    print('profiles written: %d' % nh)


if __name__ == '__main__':
    main(sys.argv[1:])
