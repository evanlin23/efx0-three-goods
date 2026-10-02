#!/usr/bin/env python3
"""Collect the explicit profiles of other workstreams' dumps and screen them for keys with def* > 0 (workstream
compute/k4-cover). EVIDENCE tooling.

Every record of every input file (JSON, JSON lines, gzipped or not; a git object "REV:PATH" is read with git show) is
walked recursively; every object with "sets" and "vals" (or "core": {"sets", "m"} beside "vals") of a k = 4 profile
(3 or 4 goods per agent) is a profile. Records that give only type indices ("prof") without values are counted and
skipped. The distinct profiles are fed to k4/cover_screen.c as single-profile blocks; the ones whose fewest-frozen
count f lies in the range and that have a non-completable key (def* > 0) are written to OUT (gzip JSON lines: src,
sets, vals, m, f, omega) for k4/cover_check.py.

usage: python3 k4/cover_inputs.py OUT.jsonl.gz [--f=a:b] FILE|REV:PATH ...   (prints the counts per input)"""
import gzip, json, os, re, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from cover_screen_run import binary, parse_hit


def records(spec):
    if ':' in spec and not os.path.exists(spec):
        raw = subprocess.run(['git', 'show', spec], capture_output=True, check=True).stdout
        name = spec.split(':', 1)[1]
    else:
        raw = open(spec, 'rb').read(); name = spec
    if name.endswith('.gz'): raw = gzip.decompress(raw)
    txt = raw.decode()
    try:
        yield json.loads(txt); return
    except ValueError:
        pass
    for line in txt.splitlines():
        line = line.strip()
        if not line: continue
        try: yield json.loads(line)
        except ValueError: continue


def profiles(obj, out, stats):
    if isinstance(obj, dict):
        sets = vals = m = None
        if 'vals' in obj and 'sets' in obj: sets, vals, m = obj['sets'], obj['vals'], obj.get('m')
        elif 'vals' in obj and isinstance(obj.get('core'), dict) and 'sets' in obj['core']:
            sets, vals, m = obj['core']['sets'], obj['vals'], obj['core'].get('m')
        elif 'prof' in obj and 'vals' not in obj and ('core' in obj or 'tag' in obj):
            stats['index-only records skipped'] = stats.get('index-only records skipped', 0) + 1
        if sets is not None:
            ok = (isinstance(sets, list) and isinstance(vals, list) and len(sets) == len(vals) >= 2 and
                  all(isinstance(S, list) and isinstance(V, list) and len(S) == len(V) and 3 <= len(S) <= 4
                      and all(isinstance(g, int) for g in S) and all(isinstance(x, int) for x in V)
                      for S, V in zip(sets, vals)))
            if ok:
                m = m or 1 + max(max(S) for S in sets)
                out.add(json.dumps([sets, vals, m]))
                return
        for v in obj.values():
            if isinstance(v, (dict, list)): profiles(v, out, stats)
    elif isinstance(obj, list):
        for v in obj:
            if isinstance(v, (dict, list)): profiles(v, out, stats)


def screen(profs, fr):
    """[(sets, vals, m)] -> the HIT records of k4/cover_screen.c"""
    b = binary(); hits = []
    for lo in range(0, len(profs), 20000):
        blocks = []
        for sets, vals, m in profs[lo:lo + 20000]:
            blocks.append('%d %d' % (len(sets), m))
            for S, V in zip(sets, vals):
                blocks.append('%d %s 1' % (len(S), ' '.join(map(str, S)))); blocks.append(' '.join(map(str, V)))
            blocks.append('0 1')
        p = subprocess.run([b, '-f', fr], input='\n'.join(blocks) + '\n', capture_output=True, text=True, check=True)
        for line in p.stdout.splitlines():
            if line.startswith('HIT '):
                n = line.count('[')
                d = parse_hit(line, n, None)
                hits.append(d)
    return hits


def main(argv):
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    rest = [a for a in argv if not a.startswith('--')]
    out, specs = rest[0], rest[1:]
    fr = opt.get('f', '1:99')
    print('# command: python3 k4/cover_inputs.py ' + ' '.join(argv), flush=True)
    allp = {}; tot_hits = 0
    with gzip.open(out, 'wt') as fo:
        for spec in specs:
            got = set(); stats = {}
            for r in records(spec): profiles(r, got, stats)
            new = [p for p in got if p not in allp]
            for p in new: allp[p] = spec
            profs = [json.loads(p) for p in new]
            hits = screen(profs, fr) if profs else []
            # restore m (the screen's HIT line has no m) from the block order: match by sets and vals
            idx = {json.dumps([s, v]): m for s, v, m in profs}
            for d in hits:
                d['m'] = idx[json.dumps([d['sets'], d['vals']])]
                d['src'] = spec
                fo.write(json.dumps(d, separators=(',', ':')) + '\n')
            tot_hits += len(hits)
            print('%-90s profiles %7d new %7d hits(f in %s, def*>0) %5d %s' % (spec, len(got), len(new), fr, len(hits),
                                                                              stats or ''), flush=True)
    print('distinct profiles %d, written %d' % (len(allp), tot_hits))


if __name__ == '__main__':
    main(sys.argv[1:])
