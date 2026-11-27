"""Verify the counterexamples to the every-order form of Conjecture RF (K4.SDC.RF as amended: for every receiver u of an
OC1-failing maximum-matching SD start, every u-first order giving a maximum matching satisfies OC1) found by
rf_climb.py's walk (results/k4_rf_offexport/rf_walk_n5_stored_fails.jsonl.gz).  Workstream compute/k4-rf-offexport.

For each instance, three implementations must agree:
  (1) rf_oc1.c (the search used by the hunt);
  (2) rf_check.py_oc1 (pure Python: k4/d1/d1lib.py's one-absorber enumeration and raw EFX0, rf_check.check_chain);
  (3) brute(), written here from the definitions alone (k4/sdc.md section 29): raw EFX0 inline; the one-absorber
      completions as every map of the junk goods to agents with at most one agent receiving two or more; the improving
      chains as every sequence of distinct agents x_0..x_t (t >= 1) and every assignment of each candidate good to one
      of H_0..H_t or to no set.
Also checked: the core is the pure n = 5 core (m, idx) of results/k4_certs_5_pure.json.gz, every agent's values are
strict (all 16 subset sums distinct), Y and Y' are SD picks of the stated orders and maximum matchings, and u is a
receiver of Y.

    python3 k4/rf_indep/verify_rf_every_cex.py [--all]
"""
import sys, os, gzip, json, itertools, subprocess, tempfile
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import rf_check as R


def brute(sets, vals, m, Y):
    """OC1 at picks Y, from the definitions; returns 'P', 'C' or 'F'"""
    n = len(sets); v = [dict(zip(s, vv)) for s, vv in zip(sets, vals)]
    val = lambda i, S: sum(v[i].get(g, 0) for g in S)
    def efx0(X):
        for i in range(n):
            for j in range(n):
                if i == j: continue
                for g in X[j]:
                    if val(i, X[i]) < val(i, [h for h in X[j] if h != g]): return False
        return True
    def one_absorber(B):
        held = set(g for b in B for g in b); J = [g for g in range(m) if g not in held]
        for f in itertools.product(range(n), repeat=len(J)):
            cnt = [f.count(i) for i in range(n)]
            if sum(1 for c in cnt if c >= 2) > 1: continue
            X = [list(B[i]) + [g for g, a in zip(J, f) if a == i] for i in range(n)]
            if efx0(X): return True
        return False
    B = [[y] if y is not None else [] for y in Y]
    if one_absorber(B): return 'P'
    held = set(g for b in B for g in b); J = [g for g in range(m) if g not in held]
    for t in range(1, n):
        for seq in itertools.permutations(range(n), t + 1):
            cand = sorted(set(J) | set(B[seq[t]]))
            for f in itertools.product(range(-1, t + 1), repeat=len(cand)):
                H = [[g for g, a in zip(cand, f) if a == i] for i in range(t + 1)]
                if any(g not in J for i in range(1, t + 1) for g in H[i]): continue          # H_i within J for i >= 1
                if any(g not in v[seq[i]] for i in range(t + 1) for g in H[i]): continue     # inside R_{x_i}
                if not val(seq[0], H[0]) > val(seq[0], B[seq[0]]): continue
                if not all(val(seq[i], B[seq[i - 1]] + H[i]) > val(seq[i], B[seq[i]]) for i in range(1, t + 1)): continue
                NB = [list(b) for b in B]; NB[seq[0]] = H[0]
                for i in range(1, t + 1): NB[seq[i]] = B[seq[i - 1]] + H[i]
                if one_absorber(NB): return 'C'
    return 'F'


def c_answer(binpath, sets, vals, m, Y):
    line = R.task_line('x', sets, vals, m, [[y] if y is not None else [] for y in Y])
    out = subprocess.run([binpath], input=line + '\n', capture_output=True, text=True).stdout.split()
    return out[1]


def main():
    allrows = '--all' in sys.argv
    binpath = os.path.join(tempfile.gettempdir(), 'rf_oc1_verify'); subprocess.check_call(['gcc', '-O2', '-o', binpath, os.path.join(HERE, 'rf_oc1.c')])
    print('$ python3 k4/rf_indep/verify_rf_every_cex.py' + (' --all' if allrows else ''))
    cert = {(c['m'], c['idx']): c['sets'] for c in json.load(gzip.open(os.path.join(ROOT, 'results', 'k4_certs_5_pure.json.gz')))['cores']}
    rows = [json.loads(l) for l in gzip.open(os.path.join(ROOT, 'results', 'k4_rf_offexport', 'rf_walk_n5_stored_fails.jsonl.gz'), 'rt')]
    bad = [r for r in rows if any(not x['a'] for x in r['per_receiver'].values())]
    print('instances with an every-form failure in the walk dump: %d' % len(bad))
    todo = bad if allrows else bad[:3]
    ok_all = True
    for r in todo:
        sets, vals, Y = r['sets'], r['vals'], tuple(r['picks']); m = r['core_m']; n = len(sets)
        checks = {}
        checks['core is (m, idx) of the certified pure n = 5 list'] = cert.get((r['core_m'], r['core_idx'])) == sets
        checks['strict values'] = all(len(set(sum(vv[q] for q in range(len(vv)) if mk >> q & 1) for mk in range(1 << len(vv)))) == 1 << len(vv) for vv in vals)
        nu = R.nu_kuhn(sets); pref = R.prefs(sets, vals)
        allp = {o: R.sd(pref, o) for o in itertools.permutations(range(n))}
        giving = [o for o in allp if allp[o] == Y]
        checks['Y is the SD picks of some order, a maximum matching'] = bool(giving) and sum(1 for y in Y if y is not None) == nu
        ans_Y = (c_answer(binpath, sets, vals, m, Y), R.py_oc1(sets, vals, m, [[y] for y in Y]), brute(sets, vals, m, Y))
        checks['OC1 fails at Y (C, Python, brute)'] = ans_Y == ('F', 'F', 'F')
        rec = R.receivers(sets, vals, Y)
        for u in rec:
            if r['per_receiver'][str(u)]['a']: continue
            ufmm = sorted(set(allp[o] for o in allp if o[0] == u and sum(1 for y in allp[o] if y is not None) == nu), key=str)
            badY = []
            for Yp in ufmm:
                a3 = (c_answer(binpath, sets, vals, m, Yp), R.py_oc1(sets, vals, m, [[y] for y in Yp]), brute(sets, vals, m, Yp))
                if a3 == ('F', 'F', 'F'): badY.append((Yp, [o for o in allp if o[0] == u and allp[o] == Yp]))
                elif 'F' in a3: checks['implementations disagree at %s: %s' % (Yp, a3)] = False
            checks['receiver %d: some u-first maximum-matching order whose picks fail OC1 (all three agree)' % u] = bool(badY)
            print('core (m %d, idx %d) sets %s vals %s' % (r['core_m'], r['core_idx'], json.dumps(sets), json.dumps(vals)))
            print('  Y = %s (orders %s), receivers %s; OC1 at Y: C %s, Python %s, brute %s' % (Y, giving[:3], rec, *ans_Y))
            for Yp, ods in badY:
                tw = [i for i in range(n) if Y[i] != Yp[i]]
                print('  u = %d: u-first order %s gives the maximum matching Y\' = %s, OC1 fails there (all three); '
                      'changed agents %s, set-twins: %s' % (u, ods[0], Yp, tw, len(tw) == 2 and sets[tw[0]] == sets[tw[1]]))
        bad_checks = [k for k, x in checks.items() if not x]
        print('  checks: %s' % ('all pass' if not bad_checks else 'FAIL ' + '; '.join(bad_checks)))
        ok_all &= not bad_checks
    print('RESULT %d of %d instances verified as counterexamples to the every-order form of RF: %s'
          % (len(todo), len(bad), 'yes' if ok_all else 'NO'))


if __name__ == '__main__':
    main()
