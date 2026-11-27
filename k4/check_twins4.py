"""Independent re-check of the round-3 reduction certificates (k4/TWINS.md; written by k4/twins4.py with k4/reduce4.py).

The checking logic is k4/check_reductions4.py's, used unmodified through its functions (it shares no code with
reduce4.py, twins4.py or mincex4.py; see its docstring): its own type enumeration ([1, 16]^d, last grid point as
representative), its own local-state enumeration, the raw EFX0 definition, its gadget-legality check (smaller, <= 4
goods per gadget agent, all in I' + D, H' in C_beta for every way the rest connects the boundary goods) and its check of
every stored extension against Lemma M1 / M1(b). This file adds only the round-3 configurations, hard-coded below and
written here independently of twins4.py's builders: a record whose declared configuration (agents with their goods in
order, I, D) differs from the entry of the same name is rejected before its coverage is counted.

Configurations (k4/TWINS.md §2): dbl-K1-K2[-cC] (two agents of kinds K1, K2 sharing two goods g0, g1 that no other agent
values; C further shared goods, boundary).

Usage: check_twins4.py certs.json.gz [--jobs=J] [--expect=CONFIG:COUNT ...] [--uncovered-out=file.json]
       check_twins4.py certs.json.gz --selftest     (corrupted copies must be rejected)"""
import sys, json, gzip, copy
from multiprocessing import Pool
import check_reductions4 as CR

NEW = {
    # Q3 agent e on (g0, g1, a) next to f
    'dbl-Q3-Q3':    ({'e': ['g0', 'g1', 'a'], 'f': ['g0', 'g1', 'x']}, ['g0', 'g1'], ['a', 'x']),
    'dbl-Q3-Q3-c1': ({'e': ['g0', 'g1', 'a'], 'f': ['g0', 'g1', 'a']}, ['g0', 'g1'], ['a']),
    'dbl-Q3-P4':    ({'e': ['g0', 'g1', 'a'], 'f': ['g0', 'g1', 'x', 'pf']}, ['g0', 'g1', 'pf'], ['a', 'x']),
    'dbl-Q3-P4-c1': ({'e': ['g0', 'g1', 'a'], 'f': ['g0', 'g1', 'a', 'pf']}, ['g0', 'g1', 'pf'], ['a']),
    'dbl-Q3-Q4':    ({'e': ['g0', 'g1', 'a'], 'f': ['g0', 'g1', 'x', 'y']}, ['g0', 'g1'], ['a', 'x', 'y']),
    'dbl-Q3-Q4-c1': ({'e': ['g0', 'g1', 'a'], 'f': ['g0', 'g1', 'a', 'y']}, ['g0', 'g1'], ['a', 'y']),
    # P4 agent e on (g0, g1, a, pe) next to f
    'dbl-P4-P4':    ({'e': ['g0', 'g1', 'a', 'pe'], 'f': ['g0', 'g1', 'x', 'pf']}, ['g0', 'g1', 'pe', 'pf'], ['a', 'x']),
    'dbl-P4-P4-c1': ({'e': ['g0', 'g1', 'a', 'pe'], 'f': ['g0', 'g1', 'a', 'pf']}, ['g0', 'g1', 'pe', 'pf'], ['a']),
    'dbl-P4-Q4':    ({'e': ['g0', 'g1', 'a', 'pe'], 'f': ['g0', 'g1', 'x', 'y']}, ['g0', 'g1', 'pe'], ['a', 'x', 'y']),
    'dbl-P4-Q4-c1': ({'e': ['g0', 'g1', 'a', 'pe'], 'f': ['g0', 'g1', 'a', 'y']}, ['g0', 'g1', 'pe'], ['a', 'y']),
    # Q4 agent e on (g0, g1, a, b) next to a Q4 agent f
    'dbl-Q4-Q4':    ({'e': ['g0', 'g1', 'a', 'b'], 'f': ['g0', 'g1', 'x', 'y']}, ['g0', 'g1'], ['a', 'b', 'x', 'y']),
    'dbl-Q4-Q4-c1': ({'e': ['g0', 'g1', 'a', 'b'], 'f': ['g0', 'g1', 'a', 'y']}, ['g0', 'g1'], ['a', 'b', 'y']),
    'dbl-Q4-Q4-c2': ({'e': ['g0', 'g1', 'a', 'b'], 'f': ['g0', 'g1', 'a', 'b']}, ['g0', 'g1'], ['a', 'b']),
}
for _k in NEW: assert _k not in CR.CONFIGS, _k
CR.CONFIGS.update(NEW)


def check_one(rec):
    assert rec['config'] in NEW, 'not a round-3 configuration: %s' % rec['config']
    return CR.check_record(rec)


def run(recs, jobs):
    with Pool(jobs) as pool: return pool.map(check_one, recs)


def selftest(recs, jobs):
    """Corrupted copies of round-3 records must lose coverage or be flagged."""
    base = run(recs, jobs)
    cov0 = {}
    for r, res in zip(recs, base): cov0[(r['config'], r['name'])] = int(res[4].sum())
    pick = max(recs, key=lambda r: (r['reduced'], len(r['states'])))
    key = (pick['config'], pick['name'])
    tests = []
    r = copy.deepcopy(pick); r['states'] = r['states'][1:]; tests.append(('a state deleted', r))
    r = copy.deepcopy(pick)
    for k, Xl in r['states']:
        X = Xl[0]
        s = next((s for s in X['S'] if X['S'][s]), None)
        if s is not None: X['S'][s] = X['S'][s][1:]; break
    tests.append(('a good dropped from an extension', r))
    r = copy.deepcopy(pick); r['Sp'] = dict(r['Sp']); r['Sp']['x2'] = {'fix': {pick['D'][0]: 1}}
    tests.append(('an extra gadget agent (not smaller)', r))
    r = copy.deepcopy(pick); r['source'] = False; tests.append(('unenvied bundle dropped', r))
    gad = max((r for r in recs if r['Ip']), key=lambda r: r['reduced'])          # a gadget record with gadget goods
    r = copy.deepcopy(gad); r['Ip'] = []; tests.append(("gadget goods not declared in I' (%s)" % gad['name'], r))
    r = copy.deepcopy(gad); r['Sp'] = {'h': {'fix': dict(gad['Sp']['h']['fix'], u1=1, u2=1, u3=1)}}
    r['Ip'] = sorted(set(gad['Ip']) | {'u1', 'u2', 'u3'})
    tests.append(('a gadget agent valuing 5 goods', r))
    r = copy.deepcopy(pick); r['S'] = dict(r['S']); r['S']['e'] = list(reversed(r['S']['e']))
    tests.append(('a record whose agents differ from its configuration', r))
    r = copy.deepcopy(pick); r['I'] = r['I'][1:]; tests.append(('a record whose I differs from its configuration', r))
    r = copy.deepcopy(pick); r['config'] = 'dbl-Q4-Q4-c2' if pick['config'] != 'dbl-Q4-Q4-c2' else 'dbl-Q3-Q3'
    tests.append(('a record filed under another configuration', r))
    # an interior good moved from an S bundle into an outside bundle holding outside goods (not the unenvied one)
    r = copy.deepcopy(pick); hit = False
    for k, Xl in r['states']:
        _, blocks, sd = json.loads(k)
        for i, b in enumerate(blocks):
            if any(x in pick['D'] for x in b) and any(x.startswith('W:') for x in b) and sd != ['O', i]:
                for X in Xl:
                    g = next((x for B in X['S'].values() for x in B if x in pick['I']), None)
                    if g is None: continue
                    for B in X['S'].values():
                        if g in B: B.remove(g)
                    X['O'][i].append(g); hit = True
            if hit: break
        if hit: break
    if hit: tests.append(('interior good into a W bundle (domination)', r))
    good = True
    print('  selftest base record %s/%s: covered %d' % (key[0], key[1], cov0[key]))
    res = run([t[1] for t in tests], jobs)
    for (what, r), (cfg, name, problems, n_adm, covered, _, _) in zip(tests, res):
        k0 = (cfg, name)
        rejected = bool(problems) or (covered.sum() < cov0[k0] if k0 in cov0 else True)
        print('  selftest %-52s -> %s (problems: %s, covered %d)' % (what, 'rejected' if rejected else 'NOT REJECTED',
                                                                     problems, covered.sum()))
        good &= rejected
    return good


def main():
    path = sys.argv[1]
    opts = sys.argv[2:]
    jobs = next((int(a.split('=')[1]) for a in opts if a.startswith('--jobs=')), 4)
    expect = [a.split('=', 1)[1] for a in opts if a.startswith('--expect=')]
    fail_out = next((a.split('=', 1)[1] for a in opts if a.startswith('--uncovered-out=')), None)
    recs = json.load(gzip.open(path, 'rt'))
    print('check_twins4.py %s: %d records; types re-enumerated by check_reductions4: %d (3 goods), %d (4 goods)' % (
        path, len(recs), len(CR.TY[3]), len(CR.TY[4])))
    if '--selftest' in opts:
        ok = selftest(recs, jobs)
    else:
        ok = CR.summarize(run(recs, jobs), expect, fail_out)
    print('RESULT: %s' % ('OK' if ok else 'FAILED'))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
