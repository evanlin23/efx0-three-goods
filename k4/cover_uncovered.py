#!/usr/bin/env python3
"""Every key that k4/cover_check.py found uncovered, confirmed and classified (workstream compute/k4-cover). EVIDENCE
tooling.

For each profile of the inputs (k4/cover_check.py or k4/cover_hunt.py outputs) with an uncovered key:
- confirmation by k4/cover_indep.py (the lemma tests re-implemented from the statements, k4/rt4_n5_indep.py's
  deficits): the same keys with def* > 0, the same def*, the same maxima, and no lemma at any maximum of the key;
- Theorem Z′⁺'s conclusion without its hypothesis ("ZMOVE"): at some maximum, one (T3) or (T3⁺) move from P_Q reaches
  a state of deficit <= 0; the best such move per maximum (least |W|, then no helper), with its deficit and kind by
  k4/rt4_n5_indep.py;
- DLKey (from k4/cover_check.py's record);
- at f >= 2, PR #80's sx_f2 reasons why A⁺ and B⁺ fail at the maxima (its "no A+/B+" counters, (R) leaves with s in L,
  chains whose θ condition fails).
Output: one JSON line per uncovered key (OUT), and the counts.

usage: python3 k4/cover_uncovered.py OUT.jsonl.gz INPUT.jsonl.gz ... [--maxn=N]"""
import collections, gzip, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import cover_check as CC
import cover_indep as CI
from f2_lib import Prof, lst
from model import bits


def fs(Bs): return tuple(frozenset(bits(B)) for B in Bs)


def main(argv):
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    rest = [a for a in argv if not a.startswith('--')]
    out, ins = rest[0], rest[1:]
    maxn = int(opt.get('maxn', 99))
    seen = set(); cnt = collections.Counter()
    print('# command: python3 k4/cover_uncovered.py ' + ' '.join(argv), flush=True)
    with gzip.open(out, 'wt') as fo:
        for fn in ins:
            lines = []
            try:
                for line in gzip.open(fn, 'rt'): lines.append(line)
            except (EOFError, OSError): pass                  # a file still being written: its readable part
            for line in lines:
                try: r = json.loads(line)
                except ValueError: continue
                unc = [kr for kr in r.get('keys', []) if not kr['covered']]
                if not unc or len(r['sets']) > maxn: continue
                pk = json.dumps([r['sets'], r['vals'], r['m']])
                if pk in seen: continue
                seen.add(pk)
                d = {'sets': r['sets'], 'vals': r['vals'], 'm': r['m']}
                pf, res, fails = CI.analyse(d)
                pr = Prof(d, fmin=1); kp = CC.f2_cc.keyprofile(pr)
                for kr in unc:
                    k = tuple(kr['key']); cnt['uncovered keys f=%d n=%d' % (r['f'], len(r['sets']))] += 1
                    target = CI.F1_LEMMAS if r['f'] == 1 else CI.F2_LEMMAS
                    ok = (k in res and pf.dstar[k] == kr['dstar']
                          and set(res[k]) == set(mr['Q'] for mr in kr['maxima'])
                          and not any(set(l) & set(target) for l in res[k].values()))
                    cnt['confirmed by k4/cover_indep.py=%s' % ok] += 1
                    zm = []; why = set()
                    for c, Bs, V, X in CC.f2_cc.maxima(kp, k):
                        if r['f'] >= 2:
                            c1 = CC.one_max(kp.I, c, CC.sx_f2.analyse_key, kp, k)
                            for kk, v in c1.items():
                                if v and (kk.startswith('no A+/B+') or kk.startswith('B+ leaf of kind (R)')
                                          or kk.startswith('A+ chain found but theta fails')):
                                    why.add(kk)
                        mv = [(len(W), h is not None, kp.D[b2], b2, x, z, W, h) for b2, x, z, W, h in kp.t3plus_moves(Bs)
                              if kp.D[b2] <= 0]
                        if not mv: zm.append(None); continue
                        w, hh, dd, b2, x, z, W, h = min(mv, key=lambda t: t[:3])
                        ks, _ = pf.classify(fs(Bs), fs(b2))
                        zm.append({'P_Q': lst(Bs), 'to': lst(b2), 'x': x, 'z': z, 'W': list(W), 'helper': h,
                                   'def': dd, 'indep def': pf.D.get(fs(b2)), 'indep kinds': sorted(ks)})
                    zmove = any(zm)
                    cnt['ZMOVE (a (T3+) move from some P_Q to def <= 0)=%s' % zmove] += 1
                    if zmove:
                        best = min((z for z in zm if z), key=lambda z: (len(z['W']), z['helper'] is not None))
                        cnt['ZMOVE best: %s' % ('T3' if not best['W'] else 'T3+|W|=%d' % len(best['W']))
                            + (' with helper' if best['helper'] is not None else ' no helper')] += 1
                    for w in why: cnt['PR #80 obstruction (at some maximum): ' + w] += 1
                    cnt['PR #80 obstructions: ' + ' + '.join(sorted(why))] += 1
                    dk = kr.get('dlkey', {})
                    cnt['DLKey holds=%s' % dk.get('holds')] += 1
                    fo.write(json.dumps({'sets': r['sets'], 'vals': r['vals'], 'm': r['m'], 'n': len(r['sets']),
                                         'f': r['f'], 'omega': r.get('omega'), 'key': kr['key'], 'dstar': kr['dstar'],
                                         'maxima': [mr['Q'] for mr in kr['maxima']], 'indep_confirmed': ok,
                                         'zmove': zm, 'dlkey': dk, 'why': sorted(why), 'src': r.get('src', fn)},
                                        separators=(',', ':')) + '\n')
                for f in fails: cnt['LEMMA-FAIL in k4/cover_indep.py'] += 1; print('LEMMA-FAIL', d, f)
    for k in sorted(cnt): print('%-70s %d' % (k, cnt[k]))


if __name__ == '__main__':
    main(sys.argv[1:])
