"""Certify the candidate cores left by k4/mincex_shapes.py (k4/MINCEX.md, sections 6 and 8): for every profile in the
product of the restricted type domains, an EFX0 allocation. CEGAR of k4/search4.py (model D2 first; profiles D2 misses
are solved without a shape limit), with the domains replaced by the restricted ones.
Each finished core is appended to a checkpoint (out + '.ckpt.jsonl'), and a rerun resumes from it; with --timeout=S a
core that takes longer than S seconds is recorded as 'timeout' (rerun with a larger limit, or --only-timeouts).
--scanner=frontier:DIR uses compute/k4-frontier's proposal step (DIR/search.py with scan2.c, draft PR #26) in place
of search4.py's; the certificate does not depend on it (the checkers re-check coverage).
Usage: mincex_cert.py shapes.json.gz out.json.gz [--jobs=J] [--timeout=S] [--only-timeouts] [--scanner=frontier:DIR]
       [--max-profiles=X] (skip cores with more profiles)"""
import sys, os, json, gzip, time, signal
from multiprocessing import Pool
import search4 as S4

TIMEOUT = None
FS = None                              # --scanner=frontier:DIR: compute/k4-frontier's search.py (scan2.c) from DIR


def key(rec):
    return json.dumps([rec['n'], rec['m'], rec['sets']])


def _alarm(*a): raise TimeoutError


def solve(rec):
    t0 = time.time()
    if TIMEOUT:
        signal.signal(signal.SIGALRM, _alarm); signal.alarm(TIMEOUT)
    try:
        C = S4.Core(rec['n'], rec['m'], rec['sets'])
        C.dom = [[tuple(v) for v in d] for d in rec['domains']]
        C.cache = {}
        if FS is None: allocs, fails, complete = C.cegar(2, 1, 1000)
        else: allocs, fails, complete = FS.cegar(C, 2, 1, 1000)[:3]
        assert complete, 'D2 CEGAR incomplete'
        extra = []
        for prof in fails:
            sol, x, z = C.inner(None, None)
            A = C.allocation(sol, x, z, prof)
            if A is None: return dict(rec, counterexample=[list(C.dom[i][t]) for i, t in enumerate(prof)])
            extra.append(A)
        return dict(rec, allocs=allocs + extra, d2_fails=len(fails), time=round(time.time() - t0, 1))
    except TimeoutError:
        return dict(rec, timeout=TIMEOUT)
    finally:
        if TIMEOUT: signal.alarm(0)


def _init(t, fdir):
    global TIMEOUT, FS
    TIMEOUT = t
    if fdir:
        sys.path.insert(0, fdir)
        import search as FS_
        FS = FS_


def main():
    src, out = sys.argv[1], sys.argv[2]
    opts = dict(a[2:].split('=', 1) for a in sys.argv[3:] if a.startswith('--') and '=' in a)
    timeout = int(opts['timeout']) if 'timeout' in opts else None
    recs = json.load(gzip.open(src, 'rt'))
    ck = out + '.ckpt.jsonl'
    done = {}
    if os.path.exists(ck):
        for line in open(ck):
            r = json.loads(line); done[key(r)] = r
    todo = [r for r in recs if key(r) not in done or ('--only-timeouts' in sys.argv and 'timeout' in done[key(r)])]
    if 'max-profiles' in opts: todo = [r for r in todo if r['profiles'] <= float(opts['max-profiles'])]
    print('%d cores, %d in the checkpoint, %d to run' % (len(recs), len(done), len(todo)), flush=True)
    fdir = opts['scanner'].split(':', 1)[1] if opts.get('scanner', '').startswith('frontier:') else None
    with Pool(int(opts.get('jobs', 4)), initializer=_init, initargs=(timeout, fdir)) as pool, open(ck, 'a') as f:
        for r in pool.imap_unordered(solve, todo):
            done[key(r)] = r
            f.write(json.dumps(r) + '\n'); f.flush()
            status = ('COUNTEREXAMPLE %s' % r['counterexample'] if 'counterexample' in r else
                      'timeout (%d s)' % r['timeout'] if 'timeout' in r else
                      '%d allocations, %d D2 failures, %.1f s' % (len(r['allocs']), r['d2_fails'], r['time']))
            print('n = %d, m = %d, kinds %s, %d profiles: %s' % (
                r['n'], r['m'], ''.join(k[0] + k[1] for k in r['kinds']), r['profiles'], status), flush=True)
    res = [done[key(r)] for r in recs]
    left = sum('allocs' not in r for r in res)
    print('certified %d of %d cores; %d not (timeout or counterexample)' % (len(res) - left, len(res), left))
    with gzip.open(out, 'wt') as f: json.dump(res, f)


if __name__ == '__main__':
    main()
