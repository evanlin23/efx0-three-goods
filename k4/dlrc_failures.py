#!/usr/bin/env python3
"""List the DL_RC failures in k4/dlrc_run.py dumps (compute/k4-rc). EVIDENCE bookkeeping.

Reads dlrc.c's "D" records (k4/dlrc.c's header) with f >= 1 and R_C branch "none" (DL_RC fails), and writes
  OUT.tsv            one line per failing state: core, m, sets, values, state, f, def, nearest distance k, frozen agents,
                     NA, J, def* of its key, kmin, key form, the shapes of its nearest better states;
  OUT_inst.json      one record per distinct profile in k4/suite/instances form (id, n, m, sets, vals, is_core, strict,
                     core_ref, fail_bases) -- also a dlrc_run.py / dlrc_ref.py "inst" list;
and prints, over all failing states, the better states (at most 400 per state, dlrc.c's list) and the nearest ones by
shape (|U|, |Z|, |W|, |Y|) and R_C kind ("-": no R_C move; "T3w": the T3+ shape without z's need), and the profiles
ordered by simplicity (largest value, then the sum of the values).

usage: python3 k4/dlrc_failures.py OUT DUMP.jsonl.gz ..."""
import collections, gzip, json, sys


def main(out, files):
    print('# command: python3 k4/dlrc_failures.py ' + ' '.join([out] + files))
    rows, profs = [], collections.OrderedDict()
    shapes_all, shapes_near, keyform = collections.Counter(), collections.Counter(), collections.Counter()
    for fn in files:
        for l in gzip.open(fn, 'rt'):
            r = json.loads(l)
            if r.get('f', 0) < 1 or r.get('rc') != 'none': continue
            c = r['core']
            key = json.dumps([c['sets'], r['vals']])
            B = [sorted(b) for b in r['B']]
            if key in profs and B in profs[key]['fail_bases']: continue
            n = len(c['sets'])
            better = r.get('better', [])
            dist = lambda b: sum(1 for x, y in zip(b['B'], r['B']) if sorted(x) != sorted(y))
            kmin = min((dist(b) for b in better), default=None)
            near = [b for b in better if dist(b) == kmin]
            for b in better: shapes_all[(tuple(b['sh']), b['kind'])] += 1
            for b in near: shapes_near[(tuple(b['sh']), b['kind'])] += 1
            keyform[r['keyok']] += 1
            ns = collections.Counter((tuple(b['sh']), b['kind']) for b in near)
            rows.append([c.get('id', c.get('file', '')), str(c['m']), json.dumps(c['sets']), json.dumps(r['vals']), json.dumps(B),
                         str(r['f']), str(r['def']), str(r['k']), json.dumps(r['frozen']), json.dumps(r['NA']), json.dumps(r['J']),
                         str(r['dstar']), str(r['kmin']), str(r['keyok']), str(len(better)),
                         ';'.join('%s:%s:%d' % (','.join(map(str, s)), k, v) for (s, k), v in sorted(ns.items()))])
            e = profs.setdefault(key, {'id': c.get('id', c.get('file', '')), 'n': n, 'm': c['m'], 'sets': c['sets'],
                                       'vals': r['vals'], 'is_core': True, 'strict': True,
                                       'core_ref': c.get('id', c.get('file', '')), 'fail_bases': []})
            e['fail_bases'].append(B)
    with open(out + '.tsv', 'w') as fo:
        fo.write('\t'.join(['core', 'm', 'sets', 'vals', 'bases', 'f', 'def', 'k', 'frozen', 'NA', 'J', 'dstar', 'kmin',
                            'keyok', 'nbetter', 'nearest(shape U,Z,W,Y:kind:count)']) + '\n')
        for r in rows: fo.write('\t'.join(r) + '\n')
    json.dump(list(profs.values()), open(out + '_inst.json', 'w'), indent=0)
    print('%d failing states in %d profiles; key form holds at %d, fails at %d' % (len(rows), len(profs), keyform[1], keyform[0]))
    print('better states by (shape |U|,|Z|,|W|,|Y|; kind):', dict(shapes_all.most_common()))
    print('nearest better states by (shape; kind):', dict(shapes_near.most_common()))
    print('profiles by simplicity (largest value, sum of values):')
    for e in sorted(profs.values(), key=lambda e: (max(max(v) for v in e['vals']), sum(map(sum, e['vals']))))[:10]:
        print('  max %d sum %d  %s  vals %s  failing %s' % (max(max(v) for v in e['vals']), sum(map(sum, e['vals'])), e['id'],
                                                          e['vals'], e['fail_bases']))


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2:])
