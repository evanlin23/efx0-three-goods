#!/usr/bin/env python3
"""The DL13 failures of k4/dl13_run.py dumps, listed per (core, profile) (compute/k4-dl13, n = 4 slice). EVIDENCE.

  python3 results/k4_dl13/n4_failures_list.py NAME=DUMP.jsonl.gz[,TABLES.json]... [--tsv=PREFIX] [--nearest]

Reads every dump record with f >= 1 and branch "none" (dl13.c: no R_13 neighbour; dl13_run.py dumps all of them) and
prints per run the counters of TABLES.json (when given), then per core the number of failing profiles and states with
their (f, def, k, signature) values. --tsv writes PREFIX_NAME.tsv with one line per failing (core, profile): file, pos,
idx, m, sets, profile (type indices of check4.core_domains), values, number of failing states, their bases. --nearest
adds per failing state the shape of the nearest better min-frozen states (c4x_check.py's 𝒫 and deficit): the changed
agents, and per changed agent "F" (frozen before and after), "x" (frozen before, free after), "z" (free before, frozen
after) or "y" (free before and after), with "=NA" when the needed set is unchanged, e.g. "FF=NA" for an exchange
between two frozen agents keeping NA."""
import collections, gzip, json, os, sys
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, 'k4'))


def shapes(sets, vals, m, Bs, cache={}):
    import c4x_check as CX
    key = json.dumps([sets, vals, m])
    if key not in cache:
        vl = [dict(zip(S, V)) for S, V in zip(sets, vals)]
        res = CX.analyse(sets, m, vl)
        mf = max(r[2]['-frozen'] for r in res)
        cache.clear()
        cache[key] = (vl, {tuple(frozenset(B) for B in r[0]): r[2]['rodef'] for r in res if r[2]['-frozen'] == mf})
    vl, mp = cache[key]
    val = lambda i, B: sum(vl[i].get(g, 0) for g in B)
    nd = lambda i, B: frozenset(g for g in vl[i] if g not in B and vl[i][g] > val(i, B))
    NA = lambda Q: frozenset().union(*[nd(i, Q[i]) for i in range(len(Q))])
    P = tuple(frozenset(B) for B in Bs); dv = mp[P]; na = NA(P)
    fz = lambda Q, i, A: len(Q[i]) == 1 and Q[i] <= A
    better = [(sum(a != b for a, b in zip(P, P2)), P2) for P2, d2 in mp.items() if d2 < dv]
    k = min(b[0] for b in better)
    out = set()
    for _, P2 in (b for b in better if b[0] == k):
        na2 = NA(P2)
        s = ''.join('FxzY'[2 * (not fz(P, i, na)) + (not fz(P2, i, na2))].replace('Y', 'y')
                    for i in range(len(P)) if P[i] != P2[i])
        out.add(''.join(sorted(s)) + ('=NA' if na == na2 else ''))
    return k, sorted(out)


def main(argv):
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in argv if a.startswith('--'))
    runs = [a for a in argv if not a.startswith('--')]
    print('# command: python3 results/k4_dl13/n4_failures_list.py ' + ' '.join(argv))
    for spec in runs:
        name, files = spec.split('=', 1)
        dump, tables = (files.split(',') + [None])[:2]
        print(f'\n## {name} ({os.path.basename(dump)})')
        if tables:
            t = json.load(open(tables))
            c = t['counters']
            print(f"command: {t['command']}")
            print(f"profiles {c['prof']}, omega >= 1 {c['om1']}, def > 0 states with f = 0 {c['st0']} (R_13 fails at "
                  f"{c['fail0']}), with f >= 1 {c['st1']}; DL13 fails at {c['fail1']}; T1 only {c['t1only']}, T3 only "
                  f"{c['t3only']} (T3 with a helper only {c['t3hOnly']}), both {c['both']}; anomalies {c['anom']}")
        byprof = collections.OrderedDict()
        for l in gzip.open(dump, 'rt'):
            r = json.loads(l)
            if r['f'] >= 1 and r['br'] == 'none':
                cr = r['core']
                byprof.setdefault((cr['file'], cr['pos'], tuple(r['prof'])), (cr, r['vals'], []))[2].append(r)
        bycore = collections.OrderedDict()
        for (fn, pos, pr), (cr, vals, rs) in sorted(byprof.items()):
            bycore.setdefault((fn, pos), (cr, []))[1].append((pr, vals, rs))
        nst = sum(len(rs) for _, _, rs in byprof.values())
        print(f'failing: {nst} states, {len(byprof)} profiles, {len(bycore)} cores')
        tsv = open(f"{opt['tsv']}_{name}.tsv", 'w') if 'tsv' in opt else None
        if tsv:
            tsv.write('file\tpos\tidx\tm\tsets\tprofile\tvals\tnstates\tbases' + ('\tnearest' if 'nearest' in opt else '')
                      + '\n')
        shp_tot = collections.Counter()
        for (fn, pos), (cr, lst) in bycore.items():
            rs = [r for _, _, x in lst for r in x]
            fdk = collections.Counter((r['f'], r['def'], r['k'], r['sig']) for r in rs)
            shp_core = collections.Counter()
            for pr, vals, x in lst:
                nshp = []
                if 'nearest' in opt:
                    for r in x:
                        k, sh = shapes(cr['sets'], vals, cr['m'], r['B'])
                        nshp.append(f"k{k}:{'|'.join(sh)}")
                        shp_core[nshp[-1]] += 1
                if tsv:
                    tsv.write('\t'.join(map(str, [fn, pos, cr.get('idx'), cr['m'], json.dumps(cr['sets']),
                                                  ','.join(map(str, pr)), json.dumps(vals), len(x),
                                                  json.dumps([r['B'] for r in x])] + ([';'.join(nshp)] if nshp else [])))
                              + '\n')
            shp_tot.update(shp_core)
            print(f"- core pos {pos} (idx {cr.get('idx')}, m = {cr['m']}, sets {cr['sets']}): {len(lst)} profiles, "
                  f"{len(rs)} states; (f, def, k, sig): "
                  + ', '.join(f'{a}: {c}' for a, c in sorted(fdk.items(), key=lambda z: (-z[1], str(z[0]))))
                  + ('; nearest repairs: ' + ', '.join(f'{a}: {c}' for a, c in shp_core.most_common()) if shp_core else ''))
        if shp_tot:
            print('nearest repairs over the run: ' + ', '.join(f'{a}: {c}' for a, c in shp_tot.most_common()))
        if tsv: tsv.close()


if __name__ == '__main__':
    main(sys.argv[1:])
