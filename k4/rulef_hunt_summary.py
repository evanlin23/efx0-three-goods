"""Tables for results/k4_rulef_hunt/SUMMARY.md and the merged dump of tight profiles.

  rulef_hunt_summary.py RUN [RUN ...]   per run (results/k4_rulef_hunt/ck/RUN.jsonl): units, evaluations, restarts,
                                        the least nwork reached per unit (histogram), the best keys and where; by m
                                        and number of 4-good agents; then merges every tight_RUN.jsonl.gz given into
                                        results/k4_rulef_hunt/tight.jsonl.gz (each line tagged with its run)
Options: --merge (write tight.jsonl.gz), --top=K (best units listed per run, default 5), --tight (analyse the distinct
profiles of tight.jsonl.gz: the working first agents, their classes, big-top status, RK3 and rule F counts, and the
frozen agents of the failing runs)."""
import collections, gzip, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, '..', 'results', 'k4_rulef_hunt')


def n4_of(rec, cache):
    if 'file' in rec:
        f = rec['file']
        if f not in cache:
            cache[f] = json.load(gzip.open(os.path.join(HERE, '..', 'results', f), 'rt'))['cores']
        return sum(len(S) == 4 for S in cache[f][rec['core']]['sets'])
    return sum(len(S) == 4 for S in rec['sets'])


def main():
    runs = [a for a in sys.argv[1:] if not a.startswith('--')]
    top = int(next((a.split('=')[1] for a in sys.argv[1:] if a.startswith('--top=')), 5))
    cache = {}
    tot_ev = 0
    for run in runs:
        path = os.path.join(OUT, 'ck', run + '.jsonl')
        if not os.path.exists(path):
            print(f'## {run}: no checkpoint'); continue
        recs = {}
        for line in open(path):
            r = json.loads(line); recs[r['unit']] = r       # a unit finished twice (resume) counts once
        recs = list(recs.values())
        ev = sum(r['evals'] for r in recs); tot_ev += ev
        rs = sum(r['restarts'] for r in recs)
        h = collections.Counter(r['best_nwork'] for r in recs)
        tm = sum(r['time'] for r in recs)
        print(f"## {run}: units {len(recs)}, profiles evaluated {ev:,}, restarts/rounds {rs:,}, worker time {tm / 3600:.2f} h")
        print(f"   least nwork reached per unit: {dict(sorted(h.items()))}; tight profiles (nwork <= 1) dumped: "
              f"{sum(r['ntight'] for r in recs)}")
        by = collections.defaultdict(list)
        for r in recs:
            by[(r['n'], n4_of(r, cache), r['m'])].append(r['best_nwork'])
        rows = []
        for k in sorted(by):
            c = collections.Counter(by[k])
            rows.append(f"n={k[0]} n4={k[1]} m={k[2]}: {len(by[k])} units, " + ' '.join(f'{w}:{c[w]}' for w in sorted(c)))
        print('   by class: ' + '; '.join(rows))
        recs.sort(key=lambda r: (r['best_nwork'], tuple(r['best_key'])))
        for r in recs[:top]:
            print(f"   best: {r['unit']} {r.get('tag', '')} m={r['m']} nwork={r['best_nwork']} key={r['best_key']} "
                  f"vals={json.dumps(r['best_vals'])}")
    print(f'# all runs: profiles evaluated {tot_ev:,}')
    if '--merge' in sys.argv:
        n = 0
        with gzip.open(os.path.join(OUT, 'tight.jsonl.gz'), 'wt') as fo:
            for run in runs:
                p = os.path.join(OUT, f'tight_{run}.jsonl.gz')
                if not os.path.exists(p): continue
                for line in gzip.open(p, 'rt'):
                    o = json.loads(line); o['run'] = run
                    fo.write(json.dumps(o) + '\n'); n += 1
        print(f'# merged {n} tight profiles into results/k4_rulef_hunt/tight.jsonl.gz')
    if '--tight' in sys.argv:
        tight_analysis()


def tight_analysis():
    path = os.path.join(OUT, 'tight.jsonl.gz')
    rows, seen = [], set()
    for line in gzip.open(path, 'rt'):
        o = json.loads(line)
        k = json.dumps([o['sets'], o['vals']])
        if k in seen: continue
        seen.add(k); rows.append(o)
    print(f'# tight.jsonl.gz: {len(rows)} distinct profiles (sets, vals)')
    agg = collections.Counter(); cores = collections.Counter(); fz = collections.Counter()
    for o in rows:
        det = o['detail']
        n = len(det)
        work = [a for a in range(n) if o['cls'][a] != 9]
        rk3 = sum(1 for d in det if min(d['kN'], d['kE'], d['k0']) <= 0 or d['t1N'] or d['t1E'] or d['t10'])
        rkc = sum(1 for d in det if min(d['kN'], d['kE']) <= 0 or d['k1N'] or d['k1E'])     # rulef.c's K1 (-T0)
        rf = sum(1 for d in det if d['rot'] <= 1)                                            # rule F, <= 1 rotation
        nbt = sum(d['bt'] for d in det)
        bts = [a for a in range(n) if det[a]['bt']]
        deg = collections.Counter(g for S in o['sets'] for g in S)
        priv = [sum(deg[g] == 1 for g in S) for S in o['sets']]
        firstbt = 'the first big-top' if work and bts and work[0] == bts[0] else 'not the first big-top'
        fewest = ('fewest private goods among big-top' if work and bts and priv[work[0]] == min(priv[a] for a in bts)
                  else 'not fewest private')
        key = (o['nwork'], 'working ' + ','.join(f"a{a}:{'K0' if o['cls'][a] == 0 else 'K1'}:{'bigtop' if det[a]['bt'] else 'not-bigtop'}" for a in work),
               f'big-top agents {nbt}', firstbt if nbt > 1 else '', fewest if nbt > 1 else '', f'RK3 {rk3}',
               f'rulef.c K1 {rkc}', f'rule F {rf}')
        agg[key] += 1
        base = o.get('file', '') + ':' + str(o.get('core', o.get('tag', '')))
        cores[(o['unit'] if 'file' in o else o.get('tag', o['unit']), o['m'])] += 1
        for a in range(n):
            if o['cls'][a] == 9:
                d = det[a]
                fz[(f"failing first agent big-top={d['bt']}", 'frozen after shrink/envy-free/none: ' +
                    '/'.join(','.join(str(i) for i in range(n) if d[k] >> i & 1) or '-' for k in ('fzN', 'fzE', 'fz0')),
                    f"LB4r rotations {d['rot']}")] += 1
    for k, v in sorted(agg.items(), key=lambda z: -z[1]): print(f'   {v:5d}  {k}')
    print('   by unit: ' + '; '.join(f'{u} m={m}: {v}' for (u, m), v in sorted(cores.items())))
    print('   failing runs (first agent: frozen agents by policy, LB4r rotations), most common:')
    for k, v in fz.most_common(15): print(f'   {v:5d}  {k}')


if __name__ == '__main__':
    main()
