#!/usr/bin/env python3
"""List the DL_RT4 failures (f >= 1) of dlrt4_run.py dumps and the shape of their nearest better states. EVIDENCE tooling
(compute/k4-rt4, n5c slice).

  python3 results/k4_rt4/n5c_failures_list.py OUT.tsv DUMP.jsonl.gz ... [--inst=OUT.json]

Reads dlrt4.c's "D" records (complete gzip members only, so a dump still being written can be read), keeps those with
"br": "none" and f >= 1 (DL_RT4 fails), and writes one TSV line per failing state: dump, core file, pos, idx, m, sets,
profile, values, bases B, f, def, k, signature, frozen, NA, the number of better min-frozen P' in the record, and the
shapes of the better P' at distance k. --inst also writes the distinct failing profiles as a k4/dlrt4_ref.py inst list.

Shape of a move P -> P' (ch = the agents whose base changes; frozen = a one-good base inside NA, dlrt4.c's "frozen"):
each agent of ch is tagged F>F, F>f, f>F or f>f (frozen in P > frozen in P'), and the move is named
  chain3   : ch = {x, y, z}, NA' = NA, x F>f with base {g}, y F>F from {h} to {g}, z f>F to {h}
             (x frees g, y moves from h to g, z takes h), i.e. a role swap passed through a frozen agent;
  T4-like  : every agent F>F, NA' = NA;
  other    : anything else, written as the sorted tags plus "NA=" or "NA!".
Prints the counts per (core, f, def, k, signature) and per nearest shape."""
import collections, gzip, json, sys, zlib


def members(path):
    raw, out = open(path, 'rb').read(), []
    while raw:
        d = zlib.decompressobj(16 + zlib.MAX_WBITS)
        try: data = d.decompress(raw)
        except zlib.error: break
        if not d.eof: break
        out.append(data); raw = d.unused_data
    return b''.join(out).decode()


def shape(r, b):
    B, B2 = [sorted(x) for x in r['B']], [sorted(x) for x in b['B']]
    fr, fr2 = set(r['frozen']), set(b['frozen'])
    ch = [i for i in range(len(B)) if B[i] != B2[i]]
    tag = {i: ('F' if i in fr else 'f') + '>' + ('F' if i in fr2 else 'f') for i in ch}
    na = sorted(r['NA']) == sorted(b['NA'])
    if na and len(ch) == 3 and sorted(tag.values()) == ['F>F', 'F>f', 'f>F']:
        x, y, z = (next(i for i in ch if tag[i] == t) for t in ('F>f', 'F>F', 'f>F'))
        if B2[y] == B[x] and B2[z] == B[y]: return 'chain3', ch
    if na and all(t == 'F>F' for t in tag.values()): return 'T4-like', ch
    return '+'.join(sorted(tag.values())) + (' NA=' if na else ' NA!'), ch


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[1:] if a.startswith('--') and '=' in a)
    out, dumps = args[0], args[1:]
    rows, cells, near_shapes, all_shapes, insts = [], collections.Counter(), collections.Counter(), collections.Counter(), {}
    for dp in dumps:
        for l in members(dp).splitlines():
            if not l: continue
            r = json.loads(l)
            if r['br'] != 'none' or int(r['f']) < 1: continue
            c = r['core']
            near = []
            for b in r.get('better', []):
                s, ch = shape(r, b)
                all_shapes[s] += 1
                if len(ch) == r['k']: near.append(s)
            near_shapes.update(set(near))
            cells[(c['file'], c['pos'], c.get('idx'), c['m'], r['f'], r['def'], r['k'], r['sig'])] += 1
            rows.append([dp.split('/')[-1], c['file'], c['pos'], c.get('idx'), c['m'], json.dumps(c['sets']), json.dumps(r['prof']),
                         json.dumps(r['vals']), json.dumps(r['B']), r['f'], r['def'], r['k'], r['sig'], json.dumps(r['frozen']),
                         json.dumps(r['NA']), len(r.get('better', [])), json.dumps(dict(collections.Counter(near)))])
            rid = f"{c['file']}#{c['pos']}[m={c['m']},idx={c.get('idx')}]:{','.join(map(str, r['prof']))}"
            insts.setdefault(rid, {'id': rid, 'sets': c['sets'], 'm': c['m'], 'vals': r['vals']})
    with open(out, 'w') as fo:
        fo.write('\t'.join('dump file pos idx m sets prof vals B f def k sig frozen NA nbetter nearest_shapes'.split()) + '\n')
        for w in rows: fo.write('\t'.join(map(str, w)) + '\n')
    if 'inst' in opt: json.dump(list(insts.values()), open(opt['inst'], 'w'), indent=0)
    print(f'# {len(rows)} failing states (f >= 1) in {len(insts)} profiles; written to {out}')
    print('# (file, pos, idx, m, f, def, k, signature) : states')
    for k, v in sorted(cells.items()): print(f'  {k} : {v}')
    print('# shapes among the nearest better states (states having at least one such move):', dict(near_shapes))
    print('# shapes among all better states listed in the records:', dict(all_shapes))


if __name__ == '__main__':
    main()
