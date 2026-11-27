"""Reproduce K4.MATCH.RSD.BASE with this workstream's own code (bplib.py; nothing imported from k4/matching).

At every one-absorber-hard start of the three data files (multi 8,383 rows, Hall 2,071, PW 291; 8,539 distinct
starts), decide by brute force over every sequence of reduction steps whether pure reduction repairs it:
  (i)    RSD: one settlement per step, (L*) at the step, a lifted completion at once at the end (phantoms receive
         nothing);
  (iR)   ROUND-RSD: rounds of at most two settlements, (L*) at the round's end;
  (ii)   RSD with (L*) deferred to the final raw test;
  (i')   RSD with (L*) at the step, deleted agents may receive junk in the completion (any agent may own);
  (iii)  deferred and deleted agents receiving.
Every final allocation is checked raw EFX0 in the full instance.  Every start is first checked: the picks are a perfect
SD outcome (characterization and brute force over orders agree) and no one-absorber completion exists at the picks.

    python3 k4/base_phantom/base_census.py [FILES...]      (default: the three data files)
"""
import sys, os, json, collections, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bplib import Inst, State, start_state, rounds, lifted_completion, load_rows, row_key

DATA = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'results', 'k4_base_phantom', 'data')
DEFAULT = [os.path.join(DATA, f) for f in ('onemove_hard_multi.jsonl.gz', 'onemove_hard_hall2071.jsonl.gz',
                                           'onemove_hard_pw291.jsonl.gz')]
FORMS = {'(i)': dict(rmax=1, lstar=True, deadrecv=False),
         '(iR)': dict(rmax=2, lstar=True, deadrecv=False),
         '(ii)': dict(rmax=1, lstar=False, deadrecv=False),
         "(i')": dict(rmax=1, lstar=True, deadrecv=True),
         '(iii)': dict(rmax=1, lstar=False, deadrecv=True)}


def repairs(I, S, f, memo):
    k = S.key()
    if k in memo:
        return memo[k]
    X = lifted_completion(I, S, deadrecv=f['deadrecv'])
    if X is not None:
        assert I.efx0(X)
        memo[k] = True
        return True
    res = False
    for combo, S2 in rounds(I, S, rmax=f['rmax'], lstar=f['lstar'], p2=not f['deadrecv']):
        if repairs(I, S2, f, memo):
            res = True
            break
    memo[k] = res
    return res


def job(r):
    I = Inst(r['sets'], r['vals'])
    S = start_state(I, r['picks'])
    sd1 = I.is_sd(S.alive, S.goods, S.B)
    sd2 = I.is_sd_brute(S.alive, S.goods, S.B)
    hard = lifted_completion(I, S) is None
    out = {'sd': sd1, 'sdx': sd1 == sd2, 'hard': hard}
    for name, f in FORMS.items():
        out[name] = repairs(I, S, f, {})
    return r, out


if __name__ == '__main__':
    files = sys.argv[1:] or DEFAULT
    print('$ python3 k4/base_phantom/base_census.py', *[os.path.basename(f) for f in files])
    per_file = {}
    allrows = {}
    for fn in files:
        rows = list(load_rows(fn))
        per_file[fn] = rows
        for r in rows:
            allrows.setdefault(row_key(r), r)
    print('rows per file:', {os.path.basename(k): len(v) for k, v in per_file.items()}, '; distinct starts:', len(allrows))
    with mp.Pool(4) as pool:
        res = {row_key(r): o for r, o in pool.imap_unordered(job, list(allrows.values()), chunksize=8)}
    C = collections.Counter()
    for k, o in res.items():
        C['picks a perfect SD outcome: %s' % o['sd']] += 1
        C['SD characterization = brute force over orders: %s' % o['sdx']] += 1
        C['one-absorber-hard at the picks: %s' % o['hard']] += 1
    for k in sorted(C):
        print(' ', C[k], k)
    for name in FORMS:
        fails = [k for k, o in res.items() if not o[name]]
        pf = {os.path.basename(fn): len(set(row_key(r) for r in rows if not res[row_key(r)][name]))
              for fn, rows in per_file.items()}
        print('form %-6s fails at %4d distinct starts; per file (distinct) %s' % (name, len(fails), pf))
    six = sorted([allrows[k] for k, o in res.items() if not o['(iii)']], key=lambda r: (len(r['sets']), 1 + max(max(s) for s in r['sets']), r['name']))
    f35 = [k for k, o in res.items() if not o['(i)']]
    print('form (iii) failures:')
    for r in six:
        print('  %s n=%d m=%d sets=%s vals=%s picks=%s' % (r['name'], len(r['sets']), 1 + max(max(s) for s in r['sets']),
                                                       r['sets'], r['vals'], r['picks']))
    print('(iii) failures inside (i) failures:', all(row_key(r) in set(f35) for r in six))
    print('(i) and (iR) fail at the same starts:', set(f35) == set(k for k, o in res.items() if not o['(iR)']))
    sm = collections.Counter((len(allrows[k]['sets']), 1 + max(max(s) for s in allrows[k]['sets'])) for k in f35)
    print('(i) failures by (n, m):', dict(sorted(sm.items())))
    out = os.path.join(DATA, '..', 'base35.jsonl')
    with open(out, 'w') as fo:
        for k in sorted(f35, key=lambda k: (len(k[0]), k)):
            r = allrows[k]
            fo.write(json.dumps({'name': r['name'], 'sets': r['sets'], 'vals': r['vals'], 'picks': r['picks'],
                                 'forms': {nm: res[k][nm] for nm in FORMS}}) + '\n')
    print('wrote results/k4_base_phantom/base35.jsonl (%d rows)' % len(f35))
