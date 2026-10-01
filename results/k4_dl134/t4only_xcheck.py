#!/usr/bin/env python3
"""Cross-check of the states repaired by T4 only (the DL13 failures; dl134.c "D" records with branch "T4") in the dumps
of the runs (b), (c), (d) with the Python reference k4/dl134_ref.py (compute/k4-dl134). EVIDENCE tooling.

  python3 results/k4_dl134/t4only_xcheck.py DUMP.jsonl.gz...

For each record: the reference on the record's profile must have the state, with f >= 1, the same def and nearest
distance k, no improving T1 or T3 move, an improving T4 move, and the same T4 cycle types. Prints one line per state
(core, profile, bases, cycle types) and the totals."""
import collections, gzip, json, os, sys
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, 'k4'))
import dl134_ref as R


def main(argv):
    print('# command: python3 results/k4_dl134/t4only_xcheck.py ' + ' '.join(argv), flush=True)
    tot = collections.Counter(); cache = {}
    for fn in argv:
        n = collections.Counter()
        for l in gzip.open(fn, 'rt'):
            d = json.loads(l)
            if d['f'] < 1 or d['br'] not in ('T4', 'none'): continue
            c = d['core']
            key = json.dumps([c['sets'], d['vals'], c['m']])
            if key not in cache: cache = {key: R.ref_states({'sets': c['sets'], 'vals': d['vals'], 'm': c['m']})}
            a = cache[key].get(tuple(tuple(B) for B in d['B']))
            ok = (a is not None and a['f'] >= 1 and a['def'] == d['def'] and a['k'] == d['k'] and not (a['t1'] or a['t3p'] or a['t3h'])
                  and (a['t4'] == 1) == (d['br'] == 'T4') and a['t4types'] == set(d['t4types']))
            n['states'] += 1; n['agree' if ok else 'DISAGREE'] += 1; n['branch ' + d['br']] += 1
            if d['br'] == 'T4': n['a 2-swap repairs' if '2' in d['t4types'] else 'only longer cycles'] += 1
            if n['states'] <= 5 or not ok or 'pos' in c and n[('pos', c['pos'])] == 0:
                print(f"  {os.path.basename(fn)}: {c.get('file', c.get('id'))} pos {c.get('pos')} (idx {c.get('idx')}, m {c['m']}) "
                      f"prof {d['prof']} B {d['B']} f {d['f']} def {d['def']} k {d['k']} sig {d['sig']} branch {d['br']} "
                      f"T4 types {d['t4types']}: {'agree' if ok else 'DISAGREE'}", flush=True)
            if 'pos' in c: n[('pos', c['pos'])] += 1
        cores = sorted(k[1] for k in n if isinstance(k, tuple))
        print(f'{os.path.basename(fn)}: ' + ', '.join(f'{k} {v}' for k, v in sorted((k, v) for k, v in n.items() if isinstance(k, str)))
              + f'; cores (pos) {cores}', flush=True)
        for k, v in n.items():
            if isinstance(k, str): tot[k] += v
    print('total: ' + ', '.join(f'{k} {v}' for k, v in sorted(tot.items())), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
