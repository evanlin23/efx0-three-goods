"""Minimal-counterexample candidates with n agents and cyclomatic number beta after K4.MC8 (k4/TWINS.md).

The pipeline of k4/mincex_shapes.py (as the hunt session's mc_n.py runs it for one n: genbg's G' list, K4.MC3 and the
structural part of K4.MC5, the Q3/P4 expansion, the K4.MC5 px domain cuts, isomorphic cores merged), with K4.MC8's
double-edge exclusion added at the G' level (twins_filter.gamma_prune, equivalent to twins_filter.excluded on the
expanded cores). Optionally also the K4.MC8 domain cuts of the partial double edges.
Usage: twins_count.py N BETA [--write=OUT.json.gz] [--cuts] [--no-mc8] [--mc9]     (run from k4/; --no-mc8: without K4.MC8, the
       baseline count)"""
import sys, os, json, gzip, collections, pickle, time
import numpy as np
import mincex_shapes as MS
import twins_filter as TF


def main():
    n, beta = int(sys.argv[1]), int(sys.argv[2])
    opt = dict(a[2:].split('=', 1) for a in sys.argv[3:] if a.startswith('--') and '=' in a)
    cuts = '--cuts' in sys.argv
    t0 = time.time()
    fail = MS.px_uncovered()
    unc = {}
    if cuts:
        for p in ('../results/k4_twins/dbl_q3_uncovered.json', '../results/k4_twins/dbl_p4q4_uncovered.json'):
            unc.update(json.load(open(p)))
    orig_g, orig_sp = MS.gammas, MS.structural_prune
    MS.gammas = lambda b, nmin=5, nmax=None: orig_g(b, nmin=n, nmax=n)
    pruned = collections.Counter()
    def sp(nb):
        if orig_sp(nb): return True
        if '--no-mc8' not in sys.argv and TF.gamma_prune(nb): pruned['gamma'] += 1; return True
        if '--mc9' in sys.argv and TF.gamma_claw(nb): pruned['claw'] += 1; return True
        return False
    MS.structural_prune = sp
    recs, stat = [], collections.Counter()
    for nn, m, sets in MS.hypergraphs(beta, n):
        if '--no-mc8' not in sys.argv: assert not TF.excluded(sets)
        dom, kinds, rules = MS.restricted_domains(sets, m, fail)
        if cuts and any(len(d) for d in dom):
            dom, _ = TF.cut_domains(sets, dom, unc)
        size = int(np.prod([len(d) for d in dom], dtype=object))
        if size == 0: continue
        stat[m] += 1
        recs.append({'n': nn, 'm': m, 'beta': beta, 'sets': sets, 'kinds': kinds, 'profiles': size,
                     'dsizes': [len(d) for d in dom]})
    print('G\' graphs pruned by K4.MC8: %d, by K4.MC9: %d; expanded cores kept before merging isomorphs: %d (%.0f s)' % (
        pruned['gamma'], pruned['claw'], len(recs), time.time() - t0), flush=True)
    uniq = MS.unique([(r['n'], r['m'], r['sets']) for r in recs])
    keep = set(json.dumps(s) for _, _, s in uniq)
    recs = [r for r in recs if json.dumps(r['sets']) in keep]
    by = collections.Counter(r['m'] for r in recs)
    for m in sorted(by):
        left = [r['profiles'] for r in recs if r['m'] == m]
        print('beta=%d n=%d m=%d: %d left after K4.MC5 and K4.MC8%s (profiles max %d, total %d)' % (
            beta, n, m, by[m], ' (with the K4.MC8 domain cuts)' if cuts else '', max(left), sum(left)), flush=True)
    print('total: %d candidate cores (%.0f s)' % (len(recs), time.time() - t0))
    if 'write' in opt:
        with gzip.open(opt['write'], 'wt') as f: json.dump(recs, f)


if __name__ == '__main__':
    main()
