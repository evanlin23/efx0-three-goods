"""Driver for k4/rulef.c (k4/rulef.md): rule F data and explicit first-agent rules on every strict profile of every core
of the given certificate files (core lists loaded as in k4/check4.py), on random profiles (-SN) or on single profiles
(--profiles=FILE, one JSON object {"sets": [...], "vals": [...]} per line, or tagged log lines with sets=/vals=).

Usage: rulef_run.py FILE [FILE ...] [--jobs=J] [--n4=K] [--m=M] [--first=N] [--data=OUT] [--checkpoint=CK] [C options]
  --checkpoint=CK  append each core's result lines to CK and, when rerun with the same options, skip the cores in CK
  -A40 -C3 -r1  (data mode) every first agent: fewest rotations up to one, coverage by the theorems with A4+N, the
                deficits, Lemma K, Corollary C4^0's hypothesis, and the explicit rules of rulef_rules
  -A41 -r1      (rule RK, fast) the first agent with Lemma K deficit <= 0, else the first whose run one rotation
                brings to Lemma K deficit <= 0, else the first whose envy-free run satisfies
                C4^0's hypothesis, else the least Lemma K deficit; LB4r run on it
  -A42 -Q0 -r1  a static rule: the first big-top agent, else agent 0 (-Q1: else an agent whose least good is another's
                top; -Q2: else rule RK), with the class of its agent (K0, K1, C40, none)
  -E1           (with -A41) evaluate every first agent (for -D5 dumps of the profiles where index order is not K0)
  -Y1           Lemma K's kept-out sets may also hold the junk goods the served agent does not value (k4/rulef.md §2,
                Remark 4); off by default: the restricted count is at least Lemma K's deficit, so it is sound
  --data=OUT    append the DATA lines (-A40 with -D1/-D2/-D4/-D5/-D6), OPEN lines (-A41 -D1) or IDX lines (-A41 -E1 -D5)
One worker by default (--jobs=1): the machine is shared."""
import gzip, hashlib, json, os, subprocess, sys, tempfile, time
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import adaptive_run as AR

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, 'rulef.c')
SHA = hashlib.sha256(open(SRC, 'rb').read()).hexdigest()[:16]
BIN = os.environ.get('RULEF_BIN') or os.path.join(tempfile.gettempdir(), 'k4_rulef_' + SHA)
RULES = ['index', 'F', 'firstcov', 'minA4N', 'minA4o', 'minA4+', 'minHN', 'minH', 'cov|minH', 'minomegaN',
         'minH,frz', '4good', 'minHN,e4', 'minUN', 'minU', 'cov|minU', 'minKN', 'minK', 'cov|minK']


def build():
    if not os.path.exists(BIN):
        tmp = BIN + f'.tmp{os.getpid()}'
        subprocess.run(['gcc', '-O2', '-o', tmp, SRC], check=True)
        os.replace(tmp, BIN)


def run(task):
    inp, opts, k = task
    p = subprocess.run([BIN] + opts, input=inp, capture_output=True, text=True)
    if p.returncode: raise RuntimeError(p.stdout[-1000:] + p.stderr[-2000:])
    lines = p.stdout.strip().split('\n')
    tags = ('RULEF ', 'RK41', 'total ', 'single ', 'DATA ', 'OPEN ', 'IDX ')
    rf = [l for l in lines if l.startswith('RULEF ') or l.startswith('RK41')]
    tot = [l for l in lines if l.startswith('total ') or l.startswith('single ')]
    data = [l for l in lines if l.startswith('DATA ') or l.startswith('OPEN ') or l.startswith('IDX ')]
    other = [l for l in lines if not l.startswith(tags)]
    return rf, tot, data, other


def run_idx(task):
    inp, opts, k, i = task
    return run((inp, opts, k)) + (i,)


def parse_rf(line):
    """RULEF/RK41 line -> dict of int lists, keyed by the words of the line"""
    t = line.split()
    d = {}
    if t[0] == 'RULEF':
        d['total'] = [int(t[2])]; d['allunc'] = [int(t[4])]; t = t[5:]
    else:
        t = t[1:]
    key = None
    for x in t:
        if x.lstrip('-').isdigit():
            d.setdefault(key, []).append(int(x))
        else:
            key = x
    return d


def add(a, b):
    if a is None: return b
    for k in b:
        a[k] = [x + y for x, y in zip(a[k], b[k])] if k in a else b[k]
    return a


def summary(tot):
    out = []
    if 'total' in tot:
        out.append(f"  total={tot['total'][0]} no covered first agent (theorems + A4+N)={tot['allunc'][0]}")
        out.append(f"  rule F's fewest rotations (0, 1, fails with <= 1): {tot['min']}; on the uncovered: {tot['umin']}")
        out.append(f"  ... where some first agent has Lemma K deficit <= 0: {tot['kneg']}; none: {tot['kpos']}")
        out.append(f"  ... none, but some first agent satisfies C4^0: {tot['c40']}; neither: {tot['open']}")
        out.append(f"  violations: Lemma K deficit <= 0 but a rotation needed: {tot['kviol'][0]}; C4^0 but > 1 rotation: {tot['cviol'][0]}")
        for i in range(len(RULES)):
            out.append(f"  rule {i:2d} {RULES[i]:12s} worse-than-F={tot['rel'][i]:>12d} fails-with-<=1={tot['abs'][i]:>12d}"
                       f"   on uncovered: worse={tot['urel'][i]:>10d} fails={tot['uabs'][i]:>10d}")
    if 'c0' in tot:
        out.append(f"  rule (-A41: RK; -A42: static, -Q), rotations LB4r needs on its sequence (0, 1, fails with <= 1) by the class of its agent:")
        out.append(f"    K0  (Lemma K at the Phase 1 state)           {tot['c0']}")
        out.append(f"    K1  (Lemma K after one rotation)             {tot['c1']}")
        out.append(f"    C40 (Corollary C4^0's hypothesis)            {tot['c2']}")
        out.append(f"    open (none of them; -A41: for any first agent) {tot['c3']}")
        out.append(f"    violations (a class's promise not met by LB4r): {tot['viol'][0]}")
    return '\n'.join(out)


def main():
    args = sys.argv[1:]
    files = [a for a in args if not a.startswith('-')]
    jobs = int(next((a.split('=')[1] for a in args if a.startswith('--jobs=')), 1))
    monly = next((int(a.split('=')[1]) for a in args if a.startswith('--m=')), None)
    n4 = next((int(a.split('=')[1]) for a in args if a.startswith('--n4=')), None)
    first = next((int(a.split('=')[1]) for a in args if a.startswith('--first=')), None)
    out = next((a.split('=', 1)[1] for a in args if a.startswith('--data=')), None)
    prof = next((a.split('=', 1)[1] for a in args if a.startswith('--profiles=')), None)
    opts = [a for a in args if a.startswith('-') and not a.startswith('--')] or ['-A41', '-r1']
    build()
    print('#', 'rulef_run.py', ' '.join(args), '# rulef.c sha256', SHA, flush=True)
    if '-A40' in opts: print('# rules:', ' '.join(f'{i}={r}' for i, r in enumerate(RULES)), flush=True)
    fo = open(out, 'a') if out else None
    if prof:
        P = AR.load_profiles(prof)
        tasks = [(AR.encode_profile(s, v), opts + ['-T1'], 1) for s, v in P]
        tot = None; fails = 0
        with Pool(jobs) as pool:
            for rf, tl, data, other in pool.imap(run, tasks):
                for l in other: print(l)
                if fo:
                    for l in data: fo.write(l + '\n')
                for l in rf: tot = add(tot, parse_rf(l))
                for l in tl:
                    if 'fail=1' in l: fails += 1
        print(f"{prof}: profiles={len(P)} fails={fails}", flush=True)
        if tot: print(summary(tot), flush=True)
        return
    ck = next((a.split('=', 1)[1] for a in args if a.startswith('--checkpoint=')), None)
    for f in files:
        t0 = time.time()
        data_ = json.load(gzip.open(f, 'rt'))
        idxs = [i for i, c in enumerate(data_['cores']) if (monly is None or c['m'] == monly)
                and (n4 is None or sum(len(S) == 4 for S in c['sets']) == n4)]
        if first: idxs = idxs[:first]
        cores = [data_['cores'][i] for i in idxs]
        key = f"{os.path.basename(f)} {' '.join(opts)} {SHA}"
        done = {}
        if ck and os.path.exists(ck):      # --checkpoint: per-core results of an interrupted run with the same key
            for line in open(ck):
                o = json.loads(line)
                if o['key'] == key: done[o['core']] = o
        if done: print(f"# resuming: {len(done)} cores from {ck}", flush=True)
        tasks = [(AR.encode_core(data_['cores'][i]['sets'], data_['cores'][i]['m']), opts, 1, i) for i in idxs if i not in done]
        tot = None; fails = 0; total = 0; shown = 0
        fc = open(ck, 'a') if ck else None

        def results():
            for o in done.values():
                yield o['rf'], o['tl'], [], [], None
            with Pool(jobs) as pool:
                for r in pool.imap_unordered(run_idx, tasks):
                    yield r
        for rf, tl, data, other, i in results():
            for l in other:
                if shown < 20 and (l.startswith('FAIL') or 'VIOL' in l or l.startswith('RAWFAIL')): print(l); shown += 1
            if fo:
                for l in data: fo.write(l + '\n')
                fo.flush()
            if fc and i is not None:
                fc.write(json.dumps({'key': key, 'core': i, 'rf': rf, 'tl': tl}) + '\n'); fc.flush()
            for l in rf: tot = add(tot, parse_rf(l))
            for l in tl:
                d = AR.parse(l); fails += d['fails'] + d['rawfails']; total += d['total']
        if fc: fc.close()
        lab = os.path.basename(f) + ('' if n4 is None else f' n4={n4}') + ('' if monly is None else f' m={monly}')
        print(f"{lab}: cores={len(cores)} profiles={total} fails or raw-check failures of the rule run={fails} time {time.time() - t0:.0f}s", flush=True)
        if tot: print(summary(tot), flush=True)
    if fo: fo.close()


if __name__ == '__main__':
    main()
