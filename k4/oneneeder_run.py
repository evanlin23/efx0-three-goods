#!/usr/bin/env python3
"""Driver for k4/oneneeder.c (workstream proof/k4-oneneeder; k4/oneneeder.md). EVIDENCE only.

  python3 k4/oneneeder_run.py certs FILE... [--sample=P] [--seed=S] [--cores=A:B] [--bt=all] [--every=E]
  python3 k4/oneneeder_run.py catalog FILE [--every=E] [--max=N]
  python3 k4/oneneeder_run.py inst FILE.json                  (a JSON list of {"id", "sets", "vals", "m"})
common: [--dump=PATH.jsonl.gz] [--rep=R] (dump every R-th one-needer T3-stage state besides the exceptions)
        [--ckpt=PATH] (certs: one JSON line per finished core; a rerun with the same options skips the cores in it and
        appends to the dump, so a killed run resumes)

certs: every strict profile (check4.core_domains) of every core of a certificate file, or P random ones per core with
k4/dlrt4.c's generator (seeded by --seed and the core's position); --bt=all restricts every 4-good agent to its big-top
types; --every=E takes every E-th core. --target: instead, one block per (x, z, g) with g a good valued by exactly two
agents x, z and |R_x| = 4: x restricted to its big-top types with top g, z to its types with top g (the shape of the
one-needer regime: only z can need g); P random profiles per block. catalog: the profiles of a k4/gap_run.py catalogue. One k4/oneneeder.c process
at a time (one CPU). Prints the command, the SHA-256 of k4/oneneeder.c, the counters per file and in total, and writes
the "D" records (with the core and the values) to --dump."""
import gzip, hashlib, json, os, subprocess, sys, tempfile, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check4

SRC = os.path.join(HERE, 'oneneeder.c')
SHA = hashlib.sha256(open(SRC, 'rb').read()).hexdigest()
BIN = os.path.join(tempfile.gettempdir(), 'k4_oneneeder_' + SHA[:16])


def build():
    if not os.path.exists(BIN):
        subprocess.run(['gcc', '-O2', '-o', BIN + '.tmp', SRC], check=True)
        os.replace(BIN + '.tmp', BIN)


def block(sets, m, doms, tag, P, profs=None):
    out = [f"{len(sets)} {m} {tag}"]
    out += [f"{len(S)} {' '.join(map(str, S))}" for S in sets]
    out.append(' '.join(str(len(D)) for D in doms))
    for S, D in zip(sets, doms):
        out += [' '.join(str(d[g]) for g in S) for d in D]
    out.append(str(P))
    return '\n'.join(out) + '\n'


def run(inp, opts):
    r = subprocess.run([BIN] + opts, input=inp, capture_output=True, text=True)
    if r.returncode: raise RuntimeError(r.stderr)
    blocks, D = [], []
    for l in r.stdout.splitlines():
        if l.startswith('K '):
            w = l.split(); blocks.append({'tag': int(w[1]), 'K': {k: int(x) for k, x in zip(w[2::2], w[3::2])}, 'D': D}); D = []
        elif l.startswith('D '): D.append(json.loads(l[2:]))
    return blocks


def add(tot, K):
    for k, c in K.items(): tot[k] = tot.get(k, 0) + c


def report(name, tot, secs):
    print(f'{name}: ' + ', '.join(f'{k} {c}' for k, c in tot.items()) + f' [{secs:.0f} s]', flush=True)


def bt_dom(D, S):
    if len(S) != 4: return D
    return [d for d in D if (lambda w: w[3] > w[2] + w[1])(sorted(d[g] for g in S))]


def main():
    argv = sys.argv[1:]; mode = argv[0]
    args = [a for a in argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in argv[1:] if a.startswith('--'))
    print('# command: python3 k4/oneneeder_run.py ' + ' '.join(argv), flush=True)
    print(f'# oneneeder.c sha256 {SHA}', flush=True)
    build()
    copts = [f"-r{int(opt.get('rep', 0))}", f"-S{int(opt.get('seed', 1))}"]
    dump = opt.get('dump'); P = int(opt.get('sample', 0))
    ck = opt.get('ckpt')
    fo = gzip.open(dump, 'wt') if dump and not ck else None
    tot = {}; t0 = time.time()
    if mode == 'certs':
        ckey = {'P': P, 'seed': int(opt.get('seed', 1)), 'bt': opt.get('bt'), 'rep': int(opt.get('rep', 0)), 'sha': SHA,
                'target': 'target' in opt}
        done = {}
        if ck and os.path.exists(ck):
            for l in open(ck):
                try: e = json.loads(l)
                except ValueError: continue
                if e['ckey'] == ckey: done[(e['file'], e['pos'])] = e['K']
        for f in args:
            cores = json.load(gzip.open(f, 'rt'))['cores']
            lo, hi = 0, len(cores)
            if 'cores' in opt: a, b = opt['cores'].split(':'); lo, hi = int(a or 0), int(b or len(cores))
            ftot = {}; ft = time.time(); nd = 0
            for k in range(lo, hi, int(opt.get('every', 1))):
                if (os.path.basename(f), k) in done:
                    add(ftot, done[(os.path.basename(f), k)]); nd += 1; continue
                c = cores[k]
                doms0 = check4.core_domains(c['sets'], c['m'], False)
                if opt.get('bt') == 'all': doms0 = [bt_dom(D, S) for D, S in zip(doms0, c['sets'])]
                units = [doms0]
                if 'target' in opt:
                    units = []
                    for g in range(c['m']):
                        who = [i for i, S in enumerate(c['sets']) if g in S]
                        if len(who) != 2: continue
                        for x, z in (who, who[::-1]):
                            if len(c['sets'][x]) != 4: continue
                            d = list(doms0)
                            d[x] = [t for t in bt_dom(doms0[x], c['sets'][x]) if max(t, key=t.get) == g]
                            d[z] = [t for t in doms0[z] if max(t, key=t.get) == g]
                            if d[x] and d[z]: units.append(d)
                kt = {}; recs = []
                bl = run(''.join(block(c['sets'], c['m'], d, u, P) for u, d in enumerate(units)), copts) if units else []
                for b in bl:
                    doms = units[b['tag']]
                    add(kt, b['K'])
                    for d in b['D']:
                        d['vals'] = [[D[p][g] for g in S] for S, D, p in zip(c['sets'], doms, d['prof'])]
                        d['core'] = {'file': os.path.basename(f), 'pos': k, 'idx': c.get('idx', k), 'm': c['m'], 'sets': c['sets']}
                        d['unit'] = b['tag']
                        recs.append(d)
                        if d['why'] != 'sample': print('# ' + json.dumps(d, separators=(',', ':')), flush=True)
                if fo:
                    for d in recs: fo.write(json.dumps(d, separators=(',', ':')) + '\n')
                elif dump and recs:
                    with gzip.open(dump, 'at') as fa:
                        for d in recs: fa.write(json.dumps(d, separators=(',', ':')) + '\n')
                if ck:
                    with open(ck, 'a') as fc:
                        fc.write(json.dumps({'ckey': ckey, 'file': os.path.basename(f), 'pos': k, 'K': kt}) + '\n')
                add(ftot, kt)
            if nd: print(f'# {os.path.basename(f)}: {nd} cores from the checkpoint', flush=True)
            report(os.path.basename(f) + (f" cores {lo}..{hi - 1}" if 'cores' in opt else ''), ftot, time.time() - ft)
            add(tot, ftot)
    else:
        if mode == 'catalog':
            recs = json.load(gzip.open(args[0], 'rt'))['records'][::int(opt.get('every', 1))]
            if 'max' in opt: recs = recs[:int(opt['max'])]
            insts = [{'id': f"{r['core']['file']}[m={r['core']['m']},idx={r['core'].get('idx')}]:{','.join(map(str, r['prof']))}",
                      'sets': r['core']['sets'], 'm': r['core']['m'], 'vals': r['vals']} for r in recs]
        else:
            insts = json.load(open(args[0]))
        for i in range(0, len(insts), 2000):
            chunk = insts[i:i + 2000]
            inp = ''.join(block(d['sets'], d.get('m') or 1 + max(g for S in d['sets'] for g in S),
                                [[dict(zip(S, V))] for S, V in zip(d['sets'], d['vals'])], k, 0) for k, d in enumerate(chunk))
            for b in run(inp, copts):
                add(tot, b['K'])
                d0 = chunk[b['tag']]
                for d in b['D']:
                    d['vals'] = d0['vals']; d['core'] = {'id': d0['id'], 'm': d0.get('m'), 'sets': d0['sets']}
                    if fo: fo.write(json.dumps(d, separators=(',', ':')) + '\n')
                    if d['why'] != 'sample': print('# ' + json.dumps(d, separators=(',', ':')), flush=True)
    if fo: fo.close()
    report('total', tot, time.time() - t0)


if __name__ == '__main__':
    main()
