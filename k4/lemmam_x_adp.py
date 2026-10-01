"""Driver for k4/lemmam_x.c -A44 (k4/lemmam_x.md §6): the adaptive rule (at every insertion step the agent whose block
has the least block count) on given profiles (--profiles=FILE: {"sets", "vals"[, "name"]} lines, or tagged lines with
sets=/vals=) or on every strict profile of every core of certificate files (resumable with --checkpoint).
Usage: lemmam_x_adp.py --profiles=FILE [C options]          one line per profile: tau, block counts, rotations d
       lemmam_x_adp.py FILE [FILE ...] [--n4=K] [--range=LO:HI] [--checkpoint=CK] [--data=OUT] [C options]
C options: -A44 is added; -rN caps the rotations tried at the end (default here -r2); -Y1 for Lemma K's Remark 4."""
import gzip, json, os, re, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import adaptive_run as AR
import lemmam_x_run as LR


def parse_adp(lines):
    for l in lines:
        if l.startswith('ADP '):
            t = l.split()
            i = t.index('hist'); j = t.index('hist_all0'); k = t.index('bad_with_last_delta1')
            q = t.index('nonlast_positive'); h = t.index('nonlast_hist')
            return {'prof': int(t[2]), 'all0': int(t[4]), 'hist': list(map(int, t[i + 1:j])),
                    'hist0': list(map(int, t[j + 1:k])), 'lastd1': int(t[k + 1]), 'nonlast': int(t[q + 1]),
                    'nonlast_hist': list(map(int, t[h + 1:]))}
    return None


def add(a, b):
    if a is None:
        return b
    return {k: ([x + y for x, y in zip(a[k], b[k])] if isinstance(a[k], list) else a[k] + b[k]) for k in a}


def main():
    args = sys.argv[1:]
    files = [a for a in args if not a.startswith('-')]
    prof = next((a.split('=', 1)[1] for a in args if a.startswith('--profiles=')), None)
    n4 = next((int(a.split('=')[1]) for a in args if a.startswith('--n4=')), None)
    rng = next((a.split('=', 1)[1] for a in args if a.startswith('--range=')), None)
    ck = next((a.split('=', 1)[1] for a in args if a.startswith('--checkpoint=')), None)
    out = next((a.split('=', 1)[1] for a in args if a.startswith('--data=')), None)
    opts = [a for a in args if a.startswith('-') and not a.startswith('--')]
    if not any(o.startswith('-r') for o in opts):
        opts.append('-r2')
    if '-A45' in opts:           # every first agent: the least rotations with Lemma K (the rotation bound of rule F)
        LR.build()
        print('#', 'lemmam_x_adp.py', ' '.join(args), '# lemmam_x.c sha256', LR.SHA, flush=True)
        for line in open(prof):
            o = json.loads(line)
            t1 = time.time()
            lines = LR.run(AR.encode_profile(o['sets'], o['vals']), opts + ['-T1', '-D45'])
            fa = next(l for l in lines if l.startswith('FA '))
            print(f"{o.get('name', 'profile')}: n={len(o['sets'])} {fa}  time {time.time() - t1:.1f}s", flush=True)
        return
    opts = ['-A44'] + opts
    LR.build()
    print('#', 'lemmam_x_adp.py', ' '.join(args), '# lemmam_x.c sha256', LR.SHA, flush=True)
    fo = open(out, 'a') if out else None
    tot = None
    t0 = time.time()
    if prof:
        for line in open(prof):
            line = line.strip()
            if not line:
                continue
            if line.startswith('{'):
                o = json.loads(line); sets, vals, name = o['sets'], o['vals'], o.get('name', '')
            else:
                sets = json.loads(re.search(r'sets=(\[\[.*?\]\])', line).group(1))
                vals = json.loads(re.search(r'vals=(\[\[.*?\]\])', line).group(1)); name = ''
            t1 = time.time()
            lines = LR.run(AR.encode_profile(sets, vals), opts + ['-T1', '-D44'])
            bad = [l for l in lines if l.startswith('ADPBAD')]
            st = parse_adp(lines)
            tot = add(tot, st)
            d = next((k for k, x in enumerate(st['hist']) if x), None)
            tau = re.search(r'tau=(\S+)', bad[0]).group(1) if bad else ''
            print(f"{name or 'profile'}: n={len(sets)} rotations needed after the adaptive run d={d}"
                  f" (cap {len(st['hist']) - 2}; {len(st['hist']) - 1} = none found)"
                  f" every block count 0: {bool(st['all0'])} {('tau=' + tau) if tau else ''} time {time.time() - t1:.1f}s",
                  flush=True)
            if fo:
                for l in bad:
                    fo.write(l + '\n')
    else:
        for f in files:
            data = json.load(gzip.open(f, 'rt'))
            idxs = [i for i, c in enumerate(data['cores']) if n4 is None or sum(len(S) == 4 for S in c['sets']) == n4]
            if rng:
                lo, hi = map(int, rng.split(':')); idxs = idxs[lo:hi]
            key = f"{os.path.basename(f)} {' '.join(opts)} {LR.SHA}"
            done = {}
            if ck and os.path.exists(ck):
                for line in open(ck):
                    o = json.loads(line)
                    if o['key'] == key:
                        done[o['core']] = o['st']
            fc = open(ck, 'a') if ck else None
            for i in idxs:
                if i in done:
                    tot = add(tot, done[i]); continue
                c = data['cores'][i]
                lines = LR.run(AR.encode_core(c['sets'], c['m']), opts + (['-D44'] if fo else []))
                st = parse_adp(lines)
                tot = add(tot, st)
                if fo:
                    for l in lines:
                        if l.startswith('ADPBAD'):
                            fo.write(l + '\n')
                    fo.flush()
                if fc:
                    fc.write(json.dumps({'key': key, 'core': i, 'st': st}) + '\n'); fc.flush()
            print(f"{os.path.basename(f)}{'' if n4 is None else f' n4={n4}'}{'' if rng is None else f' cores[{rng}]'}:"
                  f" cores={len(idxs)} time {time.time() - t0:.0f}s", flush=True)
    if tot:
        print(f"  profiles {tot['prof']}; every block count 0: {tot['all0']}")
        print(f"  rotations d needed after the adaptive run (0, 1, ..., cap, none within the cap): {tot['hist']}")
        print(f"  ... among the runs with every block count 0: {tot['hist0']}")
        print(f"  runs with d >= 1 whose last block has count 1: {tot['lastd1']}")
        print(f"  runs where some block other than the last has count > 0 (the local step fails there): {tot['nonlast']};"
              f" their d: {tot['nonlast_hist']}")


if __name__ == '__main__':
    main()
