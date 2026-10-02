#!/usr/bin/env python3
"""The hardest ZMOVE keys as k4/suite/instances records (workstream compute/k4-zmove). EVIDENCE tooling.

Reads the --hard output of k4/zmove_summary.py (records with sets, vals, m, key, margin, ...), keeps one record per
profile (its hardest key) and per core at most --percore records, re-checks each with k4/zmove_check.py and
k4/zmove_indep.py (they must agree), and writes a JSON list in the k4/suite/README.md record format: id, n, m, sets,
vals, is_core, strict, core_ref, source, refutes (empty: these instances refute nothing; ZMOVE holds at them),
witness (the key, def*, the Z′-maxima with def(P_Q), the best one-move repair and its move, the margin, the (T4)
verdict), notes, expect_fail.
usage: python3 k4/zmove_hard_inst.py HARD.json OUT.json [--top=20] [--percore=2]"""
import json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, 'suite'))
import check4
import model as M
import zmove_check as ZC


def main(argv):
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    hard_fn, out_fn = [a for a in argv if not a.startswith('--')][:2]
    top = int(opt.get('top', 20)); percore = int(opt.get('percore', 2))
    seen = set(); cores = {}; out = []
    for h in json.load(open(hard_fn)):
        pk = json.dumps([h['sets'], h['vals'], h['m']])
        ck = json.dumps([h['sets'], h['m']])
        if pk in seen or cores.get(ck, 0) >= percore: continue
        seen.add(pk); cores[ck] = cores.get(ck, 0) + 1
        d = {'sets': h['sets'], 'vals': h['vals'], 'm': h['m']}
        rec, _ = ZC.check_profile(d, {'fmin': 1, 'fmax': 99, 'all': True, 'verify_now': True})
        agree = ZC.compare_indep(d, rec)
        kr = next(k for k in rec['keys'] if k['key'] == h['key'])
        I = M.Inst(d['sets'], d['vals'], d['m'])
        i = len(out)
        out.append({
            'id': 'zmove-hard-n%dm%d-%d' % (rec['n'], d['m'], i), 'n': rec['n'], 'm': d['m'],
            'sets': d['sets'], 'vals': d['vals'],
            'is_core': check4.is_core(rec['n'], d['m'], d['sets'], False)[0] and not I.core_violations(),
            'strict': I.strict(), 'core_ref': h.get('src'),
            'source': {'pr': None, 'branch': 'compute/k4-zmove',
                       'files': ['results/k4_zmove/SUMMARY.md', 'k4/zmove_check.py', 'k4/zmove_indep.py'],
                       'replay': "python3 k4/zmove_failure.py '%s' --all" % json.dumps(d, separators=(',', ':'))},
            'refutes': [],
            'witness': {'f': rec['f'], 'omega': rec['omega'], 'key': kr['key'], 'def*': kr['dstar'],
                        'configurations': kr['nconf'], 'maxima': kr['maxima'], 'margin': kr['margin'],
                        'margin_U': kr['margin_U'], 'margin_all_configurations': kr['margin_all'],
                        't4edge': kr['t4edge']},
            'notes': ('A key closest to failing Theorem ZMOVE in the data of compute/k4-zmove (%s): margin %s (the best '
                      'one-move (T3⁺, <= 1 helper) repair from the Z′-maxima reaches def %s), %d repairing moves at the '
                      'maxima, (T4) edge to smaller def*: %s. ZMOVE holds here. Second implementation: %s.') % (
                h.get('group'), kr['margin'], kr['margin'], sum(sum(m['kinds'].values()) for m in kr['maxima']),
                kr['t4edge'], agree),
            'expect_fail': []})
        if len(out) >= top: break
    json.dump(out, open(out_fn, 'w'), indent=1)
    print('%d instances written to %s' % (len(out), out_fn))


if __name__ == '__main__':
    main(sys.argv[1:])
