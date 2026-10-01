"""Repair a dump of k4/dl2_run.py whose gzip stream was cut by a killed run (compute/k4-dl2).

  python3 k4/dl2_dumpfix.py DUMP.jsonl.gz [--ckpt=CKPT.jsonl]

A run killed while appending leaves a gzip member without its trailer; the resumed run appends a new member after it.
This reads every member (a cut one up to its last decodable byte), keeps the complete JSON lines, drops exact
duplicates, and rewrites DUMP as one gzip member (the original is kept as DUMP.orig). With --ckpt, it checks that every
core of the checkpoint has as many records with k* >= 3 (or inf) as its counters say (dl2.c dumps all of them), so
that nothing was lost."""
import gzip, json, os, sys, zlib
from collections import Counter


def members(data):
    pos = 0
    while True:
        s = data.find(b'\x1f\x8b\x08', pos)
        if s < 0: return
        d = zlib.decompressobj(31); out = []; p = s; end = None
        while p < len(data):
            chunk = data[p:p + 4096]; dc = d.copy()
            try:
                out.append(d.decompress(chunk))
            except zlib.error:
                d = dc                                           # redo this chunk byte by byte up to the break
                for q in range(len(chunk)):
                    dc2 = d.copy()
                    try: out.append(d.decompress(chunk[q:q + 1]))
                    except zlib.error: d = dc2; break
                    if d.eof: break
                end = p + 1; break
            if d.eof:
                end = p + len(chunk) - len(d.unused_data); break
            p += len(chunk)
        yield b''.join(out), end is not None and d.eof
        pos = end if end is not None and end > s else s + 3


def main():
    fn = sys.argv[1]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[2:] if a.startswith('--'))
    data = open(fn, 'rb').read()
    recs, seen, nm, cut = [], set(), 0, 0
    for txt, complete in members(data):
        nm += 1; cut += not complete
        lines = txt.decode('utf-8', 'replace').split('\n')
        if not complete: lines = lines[:-1]                     # the last line of a cut member may be partial
        for l in lines:
            if not l.strip(): continue
            try: r = json.loads(l)
            except json.JSONDecodeError: continue
            key = l
            if key in seen: continue
            seen.add(key); recs.append(r)
    print(f'{fn}: {nm} gzip members ({cut} cut), {len(recs)} records kept')
    if not os.path.exists(fn + '.orig'): os.replace(fn, fn + '.orig')
    with gzip.open(fn, 'wt') as fo:
        for r in recs: fo.write(json.dumps(r, separators=(',', ':')) + '\n')
    if 'ckpt' in opt:
        have = Counter((r['core'].get('file'), r['core'].get('pos')) for r in recs if r['kstar'] >= 3 or r['kstar'] == -1)
        bad = 0
        for l in open(opt['ckpt']):
            d = json.loads(l); K = d['block']['K']
            want = K['kstar3'] + K['kstar4'] + K['kstarinf']
            if have[(d['file'], d['pos'])] != want:
                bad += 1; print(f"  core {d['file']}#{d['pos']}: {have[(d['file'], d['pos'])]} records with k* >= 3, counters say {want}")
        print(f'checkpoint check: {bad} cores with missing k* >= 3 records')
        sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
