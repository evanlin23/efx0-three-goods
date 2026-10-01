#!/usr/bin/env python3
"""The chain states (DL_RT4 fails, DL_RC holds) and the DL_RC failures in k4/dlrc_run.py dumps (compute/k4-rc). EVIDENCE.

Reads the "D" records of dlrc.c (k4/dlrc.c's header) and reports, per dump: the states with R_C branch "T3c" alone
(chain states) and "none" (DL_RC failures), by f, def, least |W|, nearest distance k; per state the improving T3c moves
listed in the record ("chains": x, z, W, Y) by (|W|, |Y|); the better states of every such state by shape (|U|, |Z|, |W|,
|Y|) and R_C kind; and the cores (file, pos) with their number of chain states and distinct profiles.

usage: python3 k4/dlrc_chains.py DUMP.jsonl.gz ..."""
import collections, gzip, json, sys


def main(files):
    print('# command: python3 k4/dlrc_chains.py ' + ' '.join(files))
    for fn in files:
        st = collections.Counter(); mv = collections.Counter(); bt = collections.Counter(); cores = collections.defaultdict(set)
        ncs = collections.Counter(); seen = set()
        for l in gzip.open(fn, 'rt'):
            r = json.loads(l)
            if r.get('f', 0) < 1 or r.get('rc') not in ('T3c', 'none'): continue
            c = r.get('core', {})
            key = (c.get('file', c.get('id')), c.get('pos'), tuple(r.get('prof', [])), json.dumps(r['B']))
            if key in seen: continue
            seen.add(key)
            kind = 'chain' if r['rc'] == 'T3c' else 'DL_RC FAILS'
            st[(kind, r['f'], r['def'], r['wmin'], r['k'])] += 1
            for ch in r.get('chains', []): mv[(len(ch['W']), len(ch['Y']))] += 1
            for b in r.get('better', []): bt[(tuple(b['sh']), b['kind'], b['nak'])] += 1
            cores[(c.get('file', c.get('id')), c.get('pos'), c.get('m'))].add(tuple(r.get('prof', [])))
            ncs[(c.get('file', c.get('id')), c.get('pos'), c.get('m'))] += 1
        print('== %s: %d chain states, %d DL_RC failures' % (fn, sum(v for k, v in st.items() if k[0] == 'chain'),
                                                          sum(v for k, v in st.items() if k[0] != 'chain')))
        print('  states by (kind, f, def, least |W|, nearest k):')
        for k, v in sorted(st.items()): print('    %s : %d' % (k, v))
        print('  improving T3c moves listed (at most 100 per state) by (|W|, |Y|):', dict(sorted(mv.items())))
        print('  better states (at most 400 per state) by (shape |U|,|Z|,|W|,|Y|; R_C kind; NA kept):')
        for k, v in sorted(bt.items(), key=lambda x: -x[1])[:25]: print('    %s : %d' % (k, v))
        print('  cores (file, pos, m): chain / failing states, distinct profiles')
        for k in sorted(ncs): print('    %s : %d states, %d profiles' % (k, ncs[k], len(cores[k])))


if __name__ == '__main__':
    main(sys.argv[1:])
