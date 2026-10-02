#!/usr/bin/env python3
"""Sum the counters of the logs of k4/sx_hunt.py (results/k4_sx/hunt/), k4/sx_zprime.py (results/k4_sx/zprime/) and
k4/sx_f2.py (results/k4_sx/f2/) per input, and write results/k4_sx/SUMMARY.md (workstream proof/k4-sx; k4/sx.md §4).
A log counts only if it is complete (k4/sx_hunt.py: a 'distinct' line; the others: a '# time' line).
usage: python3 k4/sx_summary.py"""
import collections, glob, os, re

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def counters(path, done_pat):
    lines = open(path).read().splitlines()
    if not any(re.match(done_pat, l) for l in lines): return None
    c = collections.Counter()
    for l in lines:
        m = re.match(r'^([^#\s].*?)\s{2,}(\d+)$', l)
        if m: c[m.group(1)] += int(m.group(2))
        m = re.match(r'^distinct profiles with a non-completable key: (\d+)$', l)
        if m: c['distinct profiles with a non-completable key'] += int(m.group(1))
    return c


def group(name):
    """n3_all_10_s4000 -> n3_all; n5_pure_r1000_3000 -> n5_pure_r1000 (the pieces of one run)"""
    return re.sub(r'_\d+$', '', re.sub(r'_s\d+$', '', name))


def section(title, pattern, done_pat, grp=lambda n: n, keys=None):
    per = collections.defaultdict(collections.Counter); n = collections.Counter()
    for p in sorted(glob.glob(os.path.join(ROOT, pattern))):
        c = counters(p, done_pat)
        if c is None: continue
        g = grp(os.path.basename(p)[:-4]); per[g].update(c); n[g] += 1
    out = ['## ' + title, '']
    tot = collections.Counter()
    for g in sorted(per):
        out.append('### %s (%d logs)' % (g, n[g])); out.append('')
        for k in sorted(per[g]):
            if keys is None or any(k.startswith(x) for x in keys): out.append('- %s: %d' % (k, per[g][k]))
        out.append(''); tot.update(per[g])
    out.append('### total'); out.append('')
    for k in sorted(tot):
        if keys is None or any(k.startswith(x) for x in keys): out.append('- %s: %d' % (k, tot[k]))
    out.append('')
    return out


def main():
    out = ['# proof/k4-sx: summed counters', '', 'Made by `python3 k4/sx_summary.py` from the complete logs under '
           '`results/k4_sx/`. Every log starts with the command that wrote it.', '']
    out += section('Hunts for non-completable f = 1 keys (k4/sx_hunt.py on k4/red.c)', 'results/k4_sx/hunt/*.log',
                   r'^distinct', group)
    out += section('Repair lemmas at the Z′-maxima of the non-completable f = 1 keys (k4/sx_zprime.py)',
                   'results/k4_sx/zprime/*.log', r'^# time', group)
    out += section('Lemma A⁺ at f ≥ 2 (k4/sx_f2.py)', 'results/k4_sx/f2/*.log', r'^# time')
    open(os.path.join(ROOT, 'results/k4_sx/SUMMARY.md'), 'w').write('\n'.join(out) + '\n')
    print('\n'.join(out))


if __name__ == '__main__':
    main()
