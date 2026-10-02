#!/usr/bin/env python3
"""The DL_RT4 failures in dumps of k4/dlrt4_run.py (compute/k4-rt4-n5b), and the shape of their better states. EVIDENCE.

usage: python3 k4/dlrt4_failures.py DUMP.jsonl.gz ... [--inst=OUT.json] [--tsv=OUT.tsv] [--jobs=J]

Reads dlrt4.c's "D" records with no RT4 move (br "none", f >= 1) from the dumps (complete gzip members only, so a dump
that a running driver is appending to can be read), and per distinct (core, profile):
  --inst  writes the profile as an entry {"id", "sets", "vals", "m"} of a JSON list for `k4/dlrt4_ref.py inst` (the
          Python reference, which re-derives every state of the profile and reports its DL_RT4 failures);
  --tsv   writes one line per failing state (file, pos, idx, m, sets, profile, vals, bases, f, def, k).
Per failing state it prints, from the suite's model (k4/suite/model.py, written independently of dlrt4.c): f, def,
NA, the frozen agents, every better min-frozen state (def < def(P)) by distance, a check that this set equals the
dump's "better" list (dlrt4.c's, kept when it has at most 400 states), and for the nearest ones the shape of the move
(k4/dl2_relations.py's shape: U frozen -> free, Z free -> frozen, W frozen -> frozen, Y free -> free; chain = every
agent of W + Z holds in P' the single good of an agent of U + W), the goods each changed agent gives and takes, and
the relations of dl2_relations.RELATIONS that hold for some better move."""
import gzip, json, os, sys, zlib, collections
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import dl2_relations as DR
from dl2_classify import PA, M, bits, pc


def read_dump(path):
    data, recs = open(path, 'rb').read(), []
    while data:
        d = zlib.decompressobj(16 + zlib.MAX_WBITS)
        try: out = d.decompress(data)
        except zlib.error: break
        if not d.eof: break                                   # a member still being written
        recs += [json.loads(l) for l in out.decode().splitlines() if l]
        data = d.unused_data
    return recs


def fmt_B(Bs): return '(' + ', '.join('{' + ','.join(map(str, b)) + '}' for b in Bs) + ')'


def analyse(item):
    core, prof, vals, states = item
    I = M.Inst(core['sets'], vals, core['m'])
    I.preallocs()
    mp = [Bs for Bs, NA in I.minP]
    D = {}
    for Bs in mp:
        x = I.deficit(Bs); D[Bs] = 10 ** 6 if x is None else x
    PAs = {Bs: PA(I, Bs) for Bs in mp}
    out = []
    for r in states:
        Bs = tuple(M.mask(b) for b in r['B'])
        lines = []
        if Bs not in PAs:
            out.append((r, ['  NOT a min-frozen state of the model'], None)); continue
        P = PAs[Bs]
        better = [B2 for B2 in mp if D[B2] < D[Bs]]
        dist = {B2: sum(1 for i in range(I.n) if Bs[i] != B2[i]) for B2 in better}
        kmin = min(dist.values()) if dist else None
        rels = collections.Counter()
        for B2 in better:
            s = DR.shape(P, PAs[B2])
            for name, (desc, pred) in DR.RELATIONS.items():
                if pred(s): rels[name] += 1
        dump_better = r.get('better')
        same = None
        if dump_better is not None:
            same = {tuple(M.mask(b) for b in x['B']) for x in dump_better} == set(better)
        lines.append('  model: f %d, def(P) %s, NA {%s}, frozen %s; better states %d (by distance %s); nearest k = %s; '
                     'equal to the dump\'s better list: %s' % (
                         I.f, D[Bs], ','.join(map(str, bits(P.NA))), [i for i in range(I.n) if P.frozen[i]], len(better),
                         dict(sorted(collections.Counter(dist.values()).items())), kmin, same))
        shapes = collections.Counter()
        for B2 in sorted((B2 for B2 in better if dist[B2] == kmin), key=lambda b: (D[b], b)):
            P2 = PAs[B2]
            s = DR.shape(P, P2)
            ch = [i for i in range(I.n) if Bs[i] != B2[i]]
            role = {i: ('U' if P.frozen[i] and not P2.frozen[i] else 'Z' if not P.frozen[i] and P2.frozen[i] else
                        'W' if P.frozen[i] else 'Y') for i in ch}
            mv = '; '.join('%d%s: {%s} -> {%s}' % (i, role[i], ','.join(map(str, bits(Bs[i]))),
                                                   ','.join(map(str, bits(B2[i])))) for i in ch)
            key = 'U%d Z%d W%d Y%d%s chain %s swap %s, NA %s' % (
                s['U'], s['Z'], s['W'], len(s['Y']), (' ' + '+'.join(s['Y'])) if s['Y'] else '', s['chain'], s['swap'],
                'kept' if P.NA == P2.NA else 'changed')
            shapes[key] += 1
            lines.append('    P\' = %s, def %s, NA {%s}: %s  [%s]' % (
                fmt_B([list(bits(b)) for b in B2]), D[B2], ','.join(map(str, bits(P2.NA))), mv, key))
        lines.append('  nearest shapes: %s' % dict(shapes))
        lines.append('  relations of k4/dl2_relations.py holding for some better move: %s'
                     % (', '.join('%s (%d)' % kv for kv in rels.items()) or 'none'))
        out.append((r, lines, shapes))
    return core, prof, vals, out


def main(argv):
    files = [a for a in argv if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in argv if a.startswith('--'))
    print('# command: python3 k4/dlrt4_failures.py ' + ' '.join(argv), flush=True)
    groups = collections.OrderedDict()
    for f in files:
        recs = read_dump(f)
        fails = [r for r in recs if r.get('br') == 'none' and r['f'] >= 1]
        print('# %s: %d complete records, %d DL_RT4 failures (f >= 1)' % (f, len(recs), len(fails)), flush=True)
        for r in fails:
            c = r['core']
            key = (os.path.basename(f), c['file'], c['pos'], tuple(r['prof']))
            groups.setdefault(key, (c, list(r['prof']), r['vals'], []))[3].append(r)
    if 'inst' in opt:
        json.dump([{'id': '%s#%d[m=%d,idx=%d]:%s' % (c['file'], c['pos'], c['m'], c['idx'], ','.join(map(str, p))),
                    'sets': c['sets'], 'vals': v, 'm': c['m'], 'fail_bases': [r['B'] for r in st]}
                   for c, p, v, st in groups.values()], open(opt['inst'], 'w'), indent=0)
    items = list(groups.values())
    jobs = int(opt.get('jobs', 1))
    res = Pool(jobs).map(analyse, items) if jobs > 1 else list(map(analyse, items))
    tsv = []
    allshapes = collections.Counter()
    for (dumpf, *_), (core, prof, vals, out) in zip(groups.keys(), res):
        print('\n%s: core %s pos %d (idx %d, m %d), sets %s, profile %s, values %s' % (
            dumpf, core['file'], core['pos'], core['idx'], core['m'], core['sets'], prof, vals))
        for r, lines, shapes in out:
            print(' state P = %s: dlrt4.c f %d, def %d, nearest k %d, %d nearest' % (fmt_B(r['B']), r['f'], r['def'], r['k'],
                                                                                   r['nn']))
            print('\n'.join(lines))
            if shapes: allshapes.update(shapes)
            tsv.append('\t'.join(map(str, [core['file'], core['pos'], core['idx'], core['m'], json.dumps(core['sets']),
                                           ','.join(map(str, prof)), json.dumps(vals), json.dumps(r['B']), r['f'], r['def'],
                                           r['k']])))
    print('\n# %d failing states in %d profiles; nearest-move shapes over all of them: %s'
          % (len(tsv), len(items), dict(allshapes)))
    if 'tsv' in opt:
        with open(opt['tsv'], 'w') as fo:
            fo.write('file\tpos\tidx\tm\tsets\tprofile\tvals\tbases\tf\tdef\tk\n' + ''.join(l + '\n' for l in tsv))


if __name__ == '__main__':
    main(sys.argv[1:])
