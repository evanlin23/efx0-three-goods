"""Writes results/k4_m_portfolio/FAILURES_<cand>.md for every candidate (or exchange partner) of the Lemma M portfolio
that failed somewhere: where it fails (per dataset), its smallest failure, and the confirmation of that failure by the
second implementation (k4/lemmam_xcheck.py on PR #33's independent model).

Usage: lemmam_failures.py [DIR] [--only=cand1,cand2]   (default results/k4_m_portfolio; reads *.json summaries and the
       hunt summaries hunt*.json)"""
import glob, json, os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lemmam_portfolio as LP
import lemmam_xcheck as XC
import rulef_model as RM

INV = {v: k for k, v in LP.ALIAS.items()}


def confirm(line):
    """recompute the failure in the second implementation; returns (confirmed, text)"""
    sets, vals = XC.parse_line(line)
    inst = RM.make_inst(sets, vals)
    D = [XC.agent_data(inst, a) for a in range(inst.n)]
    ver, bt = XC.candidates(inst, D)
    summ = '; '.join(f"agent {a}: K0={int(D[a]['K0'])} K1={int(D[a]['K1'])} M1={int(D[a]['M1'])} KRb={int(D[a]['KRb'])} "
                     f"KRa={int(D[a]['KRa'])} KRo={int(D[a]['KRo'])} Rw={int(D[a]['Rw'])} Rwo={int(D[a]['Rwo'])} big-top={int(bt[a])}" for a in range(inst.n))
    if 'cand=' in line and not line.startswith('XFAIL') and 'var=' not in line:
        c = re.search(r'cand=(\S+)', line).group(1)
        app, nok = ver[LP.ALIAS.get(c, c)]
        return app and nok == 0, summ
    v = re.search(r'var=(\S+)', line).group(1)
    a = int(re.search(r' a=(\d+)', line).group(1)) if ' a=' in line else None
    ok = False
    for b in ([a] if a is not None else range(inst.n)):
        if D[b]['W']: continue
        P = D[b]['part'].get(v, set()) - {b}
        if P and not any(D[x]['W'] for x in P):
            ok = True; summ += f"; first agent {b} not in K0 ∪ K1, partners {sorted(P)} not in K0 ∪ K1 either"
    return ok, summ


def main():
    args = sys.argv[1:]
    D = next((a for a in args if not a.startswith('--')), os.path.join(HERE, '..', 'results', 'k4_m_portfolio'))
    only = next((a.split('=', 1)[1].split(',') for a in args if a.startswith('--only=')), None)
    S = {}
    for f in sorted(glob.glob(os.path.join(D, '*.json'))):
        o = json.load(open(f)); k = os.path.splitext(os.path.basename(f))[0]
        if 'counters' in o: S[k] = o
    fails = {}                                   # name -> {dataset: (fails, applicable)}, smallest line
    for k, o in S.items():
        for nm, sm in o.get('smallest', {}).items():
            if nm.startswith(('C40VIOL', 'M1VIOL', 'KRVIOL', 'KROVIOL')): continue
            e = fails.setdefault(nm, {'where': {}, 'best': None})
            cnt = o['counters'].get(nm[len('partner:'):] if nm.startswith('partner:') else nm)
            if cnt and nm.startswith('partner:'): cnt = [cnt[0], cnt[0] - cnt[1] - cnt[2]]
            if cnt: e['where'][k] = cnt
            if e['best'] is None or tuple(sm['key']) < tuple(e['best'][0]): e['best'] = (sm['key'], sm['line'], k)
    for f in sorted(glob.glob(os.path.join(D, 'hunt*.json'))):
        o = json.load(open(f))
        for c, r in o.get('results', {}).items():
            if not r.get('smallest'): continue
            nm = LP.ALIAS.get(c, c)
            if nm in LP.VARS: nm = 'partner:' + nm
            e = fails.setdefault(nm, {'where': {}, 'best': None})
            e['where'][os.path.splitext(os.path.basename(f))[0]] = [None, r['failures'], None, None]
            key = LP.prof_key(r['smallest'])
            if e['best'] is None or tuple(key) < tuple(e['best'][0]): e['best'] = (list(key), r['smallest'], os.path.basename(f))
    for nm, e in sorted(fails.items()):
        if only and nm not in only and INV.get(nm) not in only: continue
        key, line, k = e['best']
        ok, summ = confirm(line)
        fn = 'FAILURES_' + (INV.get(nm, nm).replace('partner:', 'partner_').replace(':', '_').replace('|', 'or')) + '.md'
        title = nm + (f' ({INV[nm]})' if nm in INV else '')
        L = [f'# Failures of `{title}`', '',
             'Lemma M portfolio (`k4/lemmam_portfolio.c`, workstream compute/k4-m-portfolio). EVIDENCE: found by the '
             'first implementation (classes K0, K1 of `k4/rulef.c`, included unchanged; `-Y1`), confirmed below by the '
             'second (`k4/lemmam_xcheck.py`, PR #33\'s independent model `k4/c4_verify_H/lb4r.py` with Lemma K of '
             '`k4/rulef_model.py`, M1 and Lemma KR written from the text of `k4/rulef.md`).', '',
             '## Where it fails', '',
             '| dataset | (profile, first agent) pairs: a partner exists, none in K0 ∪ K1 | pairs with a not in K0 ∪ K1 |'
             if nm.startswith('partner:') else '| dataset | failures (profiles) | applicable |', '|---|---|---|']
        for d, c in e['where'].items():
            L.append(f'| `{d}` | {c[1]:,} | {c[0]:,} |' if c[0] is not None else f'| `{d}` (hunt) | {c[1]} annealing walks ended in a failure | – |')
        L += ['', f'## Smallest failure (dataset `{k}`, n = {key[0]}, m = {key[1]})', '', '```', line, '```', '',
              f'Second implementation: **{"CONFIRMED" if ok else "NOT CONFIRMED"}**. Per first agent (some policy): {summ}.', '',
              '## Reproduce', '', '```',
              "echo '" + json.dumps({'sets': XC.parse_line(line)[0], 'vals': XC.parse_line(line)[1]}) + "' > /tmp/p.jsonl",
              'python3 k4/lemmam_portfolio.py --profiles=/tmp/p.jsonl -Y1 --jobs=1     # first implementation',
              'python3 k4/lemmam_xcheck.py --fails=results/k4_m_portfolio/' + fn + '   # second implementation', '```', '']
        path = os.path.join(D, fn)
        if os.path.exists(path):                     # keep a hand-written Notes section
            old = open(path).read()
            if '## Notes' in old: L.append(old[old.index('## Notes'):].rstrip('\n'))
        open(path, 'w').write('\n'.join(L) + '\n')
        print(f'{fn}: {"CONFIRMED" if ok else "NOT CONFIRMED"} n={key[0]} m={key[1]}', flush=True)


if __name__ == '__main__':
    main()
