#!/usr/bin/env python3
"""Seeds for the ZMOVE hunt from k4/zmove_check.py outputs (workstream compute/k4-zmove). EVIDENCE tooling.

Every key is scored by k4/zmove_hunt.key_score (higher = closer to a ZMOVE failure: the margin first, then no (T4)
edge, then few repairing moves); every core (sets, m) keeps its best-scoring profile; the cores are ranked by that score
and the top --per of each n in --ns are written to OUT (a JSON list of {id, sets, vals, m, n, f, score, margin, nrep,
src}).
usage: python3 k4/zmove_seeds.py OUT.json [--per=8] [--ns=4,5,6] GLOB ..."""
import glob, gzip, json, sys, os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zmove_hunt import key_score


def main(argv):
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    rest = [a for a in argv if not a.startswith('--')]
    out, pats = rest[0], rest[1:]
    per = int(opt.get('per', 8)); ns = set(int(x) for x in opt.get('ns', '4,5,6').split(','))
    best = {}
    for pat in pats:
        for fn in sorted(glob.glob(pat)):
            try:
                for line in gzip.open(fn, 'rt'):
                    try: r = json.loads(line)
                    except ValueError: break
                    if not r.get('keys') or r.get('n') not in ns: continue
                    for kr in r['keys']:
                        s, nrep = key_score(kr)
                        ck = json.dumps([r['sets'], r['m']])
                        if ck not in best or s > best[ck]['score']:
                            best[ck] = {'sets': r['sets'], 'vals': r['vals'], 'm': r['m'], 'n': r['n'], 'f': r['f'],
                                        'score': s, 'margin': kr['margin'], 'nrep': nrep, 't4edge': kr['t4edge'],
                                        'key': kr['key'], 'src': r.get('src')}
            except (EOFError, OSError):
                pass
    res = []
    for n in sorted(ns):
        L = sorted((v for v in best.values() if v['n'] == n), key=lambda v: -v['score'])[:per]
        for i, v in enumerate(L): v['id'] = 'seed-n%d-%d' % (n, i)
        res += L
    json.dump(res, open(out, 'w'), indent=0)
    print('%d cores seen; written %d: %s' % (len(best), len(res), [(v['id'], v['score'], v['margin'], v['nrep'], v['f'])
                                                                   for v in res]))


if __name__ == '__main__':
    main(sys.argv[1:])
