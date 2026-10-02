#!/usr/bin/env python3
"""Summaries of k4/zmove_check.py outputs (workstream compute/k4-zmove). EVIDENCE tooling.

Per group of outputs (one group per argument; a group is a glob, NAME=GLOB names it): profiles, keys with def* > 0 per
f and per n, the margin histogram (margin = min over the Z′-maxima of the least def(P′) over the (T3⁺) moves with <= 1
helper from P_Q), keys with margin exactly 0, keys where some maximum has no one-move repair (so the choice of the
maximum matters), keys passing only by a (T4) edge, ZMOVE failures, the kind of the best
repair at the margin (T3 / T3 with helper / T3⁺ with |W| >= 1), margin_U (the level over U_y) where it differs, and
the cross-checks (k4/zmove_indep.py agreements and differences, model.py verifications, assertions). The profiles are
deduplicated across the files of a group and across groups (first group wins), unless --nodedup.
--hard=OUT.json writes the hardest keys (margin desc, then fewest repairing moves at the maxima, then fewest maxima
that repair), as {sets, vals, m, id, src, key, dstar, margin, ...} records (k4/suite-compatible profile fields).
usage: python3 k4/zmove_summary.py [--hard=OUT.json] [--top=N] [--nodedup] [NAME=]GLOB ..."""
import collections, glob, gzip, json, sys


def recs(fn):
    try:
        for line in gzip.open(fn, 'rt'):
            try: yield json.loads(line)
            except ValueError: return
    except (EOFError, OSError):
        return


def mkey(x): return (1, 0) if x == 'inf' else (0, x)


def best_kind(kr):
    """the simplest kind of a best move at a maximum attaining the margin"""
    ks = set()
    for mr in kr['maxima']:
        if mr['best'] != kr['margin'] or mr['move'] is None: continue
        mv = mr['move']
        ks.add(('T3' if not mv['W'] else 'T3+W%d' % len(mv['W'])) + ('+helper' if mv['helper'] is not None else ''))
    order = ['T3', 'T3+helper', 'T3+W1', 'T3+W1+helper', 'T3+W2', 'T3+W2+helper', 'T3+W3', 'T3+W3+helper']
    for o in order:
        if o in ks: return o
    return 'none' if not ks else sorted(ks)[0]


def hardness(kr):
    nrep = sum(sum(mr['kinds'].values()) for mr in kr['maxima'])
    mrep = sum(1 for mr in kr['maxima'] if mr['best'] != 'inf' and mr['best'] <= 0)
    return (mkey(kr['margin']), -nrep, -mrep, -kr['dstar']), nrep, mrep


def main(argv):
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    groups = [a for a in argv if not a.startswith('--')]
    top = int(opt.get('top', 30))
    seen = set(); hard = []
    tot = collections.Counter(); thist = collections.Counter()
    for g in groups:
        name, pat = g.split('=', 1) if '=' in g else (g, g)
        files = sorted(glob.glob(pat))
        c = collections.Counter(); hist = collections.Counter(); hist_f = collections.defaultdict(collections.Counter)
        kinds0 = collections.Counter(); kn = collections.Counter(); fails = []
        for fn in files:
            for r in recs(fn):
                pk = json.dumps([r['sets'], r['vals'], r['m']])
                if pk in seen and '--nodedup' not in argv: c['duplicates skipped'] += 1; continue
                seen.add(pk)
                c['profiles'] += 1
                if 'assert' in r: c['ASSERT'] += 1; continue
                if 'skip' in r: c['skipped (%s)' % r['skip']] += 1; continue
                if r.get('verified'): c['profiles verified against model.py'] += 1
                if 'indep' in r:
                    c['indep agree' if r['indep'].startswith('agree') else 'INDEP-DIFFER'] += 1
                for kr in r['keys']:
                    f, n = r['f'], r['n']
                    c['keys'] += 1; kn['f=%d' % f] += 1; kn['n=%d' % n] += 1; kn['n=%d f=%d' % (n, f)] += 1
                    hist[kr['margin']] += 1; hist_f[f][kr['margin']] += 1; thist[kr['margin']] += 1
                    if kr['margin'] == 0:
                        c['margin 0'] += 1; kinds0[best_kind(kr)] += 1
                    if not kr['pass']: fails.append((r, kr))
                    elif kr['margin'] == 'inf' or kr['margin'] > 0: c['pass by (T4) edge only'] += 1
                    if kr['t4edge']: c['keys with a (T4) edge to smaller def*'] += 1
                    worst = max(mkey(mr['best']) for mr in kr['maxima'])
                    if worst[0] or worst[1] > 0:
                        c['keys where some maximum has no one-move repair to <= 0'] += 1
                        if kr['margin'] != 'inf' and kr['margin'] <= 0: c['  ... but another maximum has one'] += 1
                    if len(kr['maxima']) > 1: c['keys with several maxima (distinct P_Q)'] += 1
                    if kr['margin_U'] != kr['margin']:
                        c['margin_U != margin'] += 1
                        a = kr['margin'] != 'inf' and kr['margin'] <= 0; b = kr['margin_U'] != 'inf' and kr['margin_U'] <= 0
                        if a != b: c['margin_U and margin differ in sign (<= 0 or not)'] += 1
                    hk, nrep, mrep = hardness(kr)
                    hard.append((hk, nrep, mrep, r, kr, name))
        print('== %s (%d files)' % (name, len(files)))
        for k in sorted(c): print('  %-48s %d' % (k, c[k]))
        print('  keys by f / n:', dict(sorted(kn.items())))
        print('  margin histogram:', dict(sorted(hist.items(), key=lambda t: mkey(t[0]))))
        for f in sorted(hist_f): print('    f = %d:' % f, dict(sorted(hist_f[f].items(), key=lambda t: mkey(t[0]))))
        if kinds0: print('  margin-0 keys by the simplest best repair:', dict(sorted(kinds0.items())))
        print('  ZMOVE failures:', len(fails))
        for r, kr in fails[:20]:
            print('    FAIL', json.dumps({x: r[x] for x in ('sets', 'vals', 'm', 'f')}), json.dumps(kr)[:1500])
        for k, v in c.items(): tot[k] += v
    print('== TOTAL')
    for k in sorted(tot): print('  %-48s %d' % (k, tot[k]))
    print('  margin histogram:', dict(sorted(thist.items(), key=lambda t: mkey(t[0]))))
    hard.sort(key=lambda t: t[0], reverse=True)
    print('== hardest keys (margin, then fewest repairing moves at the maxima, then fewest repairing maxima)')
    out = []
    for i, (hk, nrep, mrep, r, kr, name) in enumerate(hard[:top]):
        print('  margin %s dstar %d nrep %d mrep %d/%d nconf %d n %d f %d %s key %s src %s' % (
            kr['margin'], kr['dstar'], nrep, mrep, len(kr['maxima']), kr['nconf'], r['n'], r['f'], name, kr['key'],
            r.get('src')))
        out.append({'id': 'zmove-hard-%d' % i, 'sets': r['sets'], 'vals': r['vals'], 'm': r['m'], 'n': r['n'],
                    'f': r['f'], 'omega': r['omega'], 'src': r.get('src'), 'group': name, 'key': kr['key'],
                    'dstar': kr['dstar'], 'margin': kr['margin'], 'margin_U': kr['margin_U'], 'repairing_moves': nrep,
                    'repairing_maxima': mrep, 'maxima': kr['maxima'], 'nconf': kr['nconf'], 't4edge': kr['t4edge']})
    if 'hard' in opt:
        json.dump(out, open(opt['hard'], 'w'), indent=1)


if __name__ == '__main__':
    main(sys.argv[1:])
