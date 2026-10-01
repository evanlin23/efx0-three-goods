"""Driver for k4/lemmam_x.c -A43 (k4/lemmam_x.md): the class (K0, K1, bad) of every first agent on every strict
profile of every core of the given certificate files (core lists as in k4/check4.py), on random profiles (-SN), by
hill-climbing (-SN -HM), or on given profiles (--profiles=FILE: {"sets", "vals"} lines or tagged lines with sets=/vals=);
for every bad first agent the class of its run, the roles of the other agents and the candidates a' of
k4/lemmam_x.md §2.
Usage: lemmam_x_run.py FILE [FILE ...] [--n4=K] [--m=M] [--range=LO:HI] [--data=OUT] [--checkpoint=CK] [C options]
  --checkpoint=CK  append each core's result lines to CK; a rerun with the same options skips the cores in CK
  --data=OUT       append the BAD / ALLBAD lines (-D43)
One worker (the machine is shared). The binary is compiled into the temporary directory under a name made from a hash
of the source (LMX_BIN overrides)."""
import gzip, hashlib, json, os, subprocess, sys, tempfile, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import adaptive_run as AR

SRC = os.path.join(HERE, 'lemmam_x.c')
SHA = hashlib.sha256(open(SRC, 'rb').read()).hexdigest()[:16]
BIN = os.environ.get('LMX_BIN') or os.path.join(tempfile.gettempdir(), 'k4_lemmam_x_' + SHA)
ROLE_KEYS = None


def build():
    if not os.path.exists(BIN):
        tmp = BIN + f'.tmp{os.getpid()}'
        subprocess.run(['gcc', '-O2', '-o', tmp, SRC], check=True)
        os.replace(tmp, BIN)


def run(inp, opts):
    p = subprocess.run([BIN] + opts, input=inp, capture_output=True, text=True)
    if p.returncode:
        raise RuntimeError(p.stdout[-1000:] + p.stderr[-2000:])
    return p.stdout.strip().split('\n')


def add_lines(acc, lines):
    for l in lines:
        t = l.split()
        if l.startswith('LMX '):
            vals = [int(x) for x in t[1:] if x.lstrip('-').isdigit()]
            acc['LMX'] = [x + y for x, y in zip(acc['LMX'], vals)] if 'LMX' in acc else vals
        elif l.startswith('LMXC '):
            name = 'C:' + t[1]; vals = [int(t[3]), int(t[5]), int(t[7])]
            acc[name] = [x + y for x, y in zip(acc[name], vals)] if name in acc else vals
        elif l.startswith('LMXR '):
            name = t[1]; vals = [int(t[i]) for i in range(3, len(t), 2)]
            acc[name] = [x + y for x, y in zip(acc[name], vals)] if name in acc else vals


def report(acc):
    if 'LMX' not in acc:
        return
    v = acc['LMX']
    print(f"  profiles {v[0]}  with a bad first agent {v[1]}  with no good first agent (Lemma M fails) {v[2]}"
          f"  bad (profile, a) pairs {v[3]}  bad runs of class A4 or B4 (would contradict C40 in K0+K1) {v[4]}")
    print(f"  profiles by number of good first agents (0, 1, 2, 3, 4): {v[5:10]}")
    print(f"  bad pairs by the class of the envy-free run (omega<=0, A4, B4, G2, one exposed 4-good frozen, free,"
          f" two or more): {v[10:17]}")
    for k, x in acc.items():
        if k.startswith('C:'):
            print(f"  candidate {k[2:]:20s} good {x[0]:>10d}   good after iterating {x[1]:>10d}   undefined {x[2]:>8d}"
                  f"   (of {v[3]} bad pairs)")
    print(f"  {'role':24s} {'has':>10s} {'some good':>10s} {'all good':>10s} {'earliest':>10s} {'latest':>10s}"
          f"   (holders of the role in the bad agent's run; earliest/latest processed holder good)")
    for k, x in acc.items():
        if k == 'LMX' or k.startswith('C:'):
            continue
        if x[0]:
            print(f"  {k:24s} {x[0]:10d} {x[1]:10d} {x[2]:10d} {x[3]:10d} {x[4]:10d}")


def main():
    args = sys.argv[1:]
    files = [a for a in args if not a.startswith('-')]
    n4 = next((int(a.split('=')[1]) for a in args if a.startswith('--n4=')), None)
    monly = next((int(a.split('=')[1]) for a in args if a.startswith('--m=')), None)
    rng = next((a.split('=', 1)[1] for a in args if a.startswith('--range=')), None)
    out = next((a.split('=', 1)[1] for a in args if a.startswith('--data=')), None)
    prof = next((a.split('=', 1)[1] for a in args if a.startswith('--profiles=')), None)
    ck = next((a.split('=', 1)[1] for a in args if a.startswith('--checkpoint=')), None)
    opts = [a for a in args if a.startswith('-') and not a.startswith('--')]
    build()
    print('#', 'lemmam_x_run.py', ' '.join(args), '# lemmam_x.c sha256', SHA, flush=True)
    fo = open(out, 'a') if out else None
    acc = {}
    t0 = time.time()
    if prof:
        P = AR.load_profiles(prof)
        for s, v in P:
            lines = run(AR.encode_profile(s, v), opts + ['-T1'])
            add_lines(acc, lines)
            for l in lines:
                if l.startswith(('BAD', 'ALLBAD')) and fo:
                    fo.write(l + '\n')
                if l.startswith('ALLBAD'):
                    print(l)
        print(f"{prof}: profiles={len(P)} time {time.time() - t0:.0f}s", flush=True)
        report(acc)
        return
    for f in files:
        data = json.load(gzip.open(f, 'rt'))
        idxs = [i for i, c in enumerate(data['cores']) if (monly is None or c['m'] == monly)
                and (n4 is None or sum(len(S) == 4 for S in c['sets']) == n4)]
        if rng:
            lo, hi = map(int, rng.split(':')); idxs = idxs[lo:hi]
        key = f"{os.path.basename(f)} {' '.join(opts)} {SHA}"
        done = {}
        if ck and os.path.exists(ck):
            for line in open(ck):
                o = json.loads(line)
                if o['key'] == key:
                    done[o['core']] = o['lines']
        if done:
            print(f"# resuming: {len(done)} cores from {ck}", flush=True)
        fc = open(ck, 'a') if ck else None
        ncores = 0
        for i in idxs:
            ncores += 1
            if i in done:
                add_lines(acc, done[i]); continue
            c = data['cores'][i]
            lines = run(AR.encode_core(c['sets'], c['m']), opts)
            add_lines(acc, lines)
            for l in lines:
                if l.startswith(('BAD', 'ALLBAD')) and fo:
                    fo.write(l + '\n')
                if l.startswith('ALLBAD'):
                    print('core', i, l, flush=True)
            if fo:
                fo.flush()
            if fc:
                keep = [l for l in lines if l.startswith(('LMX', 'total', 'ALLBAD'))]
                fc.write(json.dumps({'key': key, 'core': i, 'lines': keep}) + '\n'); fc.flush()
        lab = os.path.basename(f) + ('' if n4 is None else f' n4={n4}') + ('' if monly is None else f' m={monly}') + \
            ('' if rng is None else f' cores[{rng}]')
        print(f"{lab}: cores={ncores} time {time.time() - t0:.0f}s", flush=True)
    report(acc)
    print('ACC', json.dumps(acc), flush=True)


if __name__ == '__main__':
    main()
