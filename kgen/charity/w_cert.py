"""Independent check of an UNSAT answer of w_synth.run (kgen/charity.md §6), from the cut list it dumps.

w_synth's outer problem asks for real values making the fixed stranded state X (bundles B, pool P) EFX0 with strong
charity, a robust stopping state (no pool good can be added to a bundle; >= |P| + 1 sources, each holding >= 2
goods), and strictly heavier than every allocation Y in the cut list that is EFX0.  The cut list is a finite set of
allocations, each leaving <= p - 1 goods out.  If the outer problem with these cuts is infeasible, then no values make
X a welfare maximum leaving |P| goods out against all allocations leaving fewer (the cuts are such allocations, and the
stopping-state conditions are implied, §6 and CH6).  This script re-encodes that outer problem from the dump, written
from scratch as SMT-LIB 2 text over QF_LIA/QF_LRA (no z3 code shared), and asks cvc5 (a second solver) for
satisfiability.  It also re-checks each cut: its bundles and pool partition the goods and the pool has <= p - 1 goods.

Encoding: v_i(g) real, = 0 off agent i's support and >= 1 on it (fixed support), or, with no fixed support, a Boolean
b_ig with b -> v >= 1, not b -> v = 0 and sum_g b_ig <= k; every pool good valued by someone; at most one good per
bundle worthless to all.  Strict inequalities are kept strict (QF_LRA).

    python3 kgen/charity/w_cert.py CUTFILE [CUTFILE ...]
    python3 kgen/charity/w_cert.py --core CUTFILE COREFILE [--min]
--core: also extract an unsat core of the cuts (cvc5), re-check the core alone, and write {"core": [indices]} to
COREFILE (for w_milp_cert.py); --min shrinks the core by deletion (one cvc5 call per cut)."""
import sys, json, time
import cvc5


def lin(terms):
    """terms: list of variable names (each with coefficient +1); returns an SMT-LIB sum."""
    if not terms:
        return '0.0'
    return terms[0] if len(terms) == 1 else '(+ %s)' % ' '.join(terms)


def encode(D, named=False, only=None):
    """named: name each cut assertion cut_<t> (for unsat cores); only: indices of the cuts to include."""
    n, k, p, B, P, m = D['n'], D['k'], D['p'], D['bundles'], D['pool'], D['m']
    sup = D['support']
    V = lambda i, g: 'v_%d_%d' % (i, g)
    val = lambda i, G: lin([V(i, g) for g in G if sup is None or g in sup[i]])
    out = (['(set-option :produce-unsat-cores true)'] if named else []) + ['(set-logic QF_LRA)']
    for i in range(n):
        for g in range(m):
            if sup is not None and g not in sup[i]:
                continue
            out.append('(declare-const %s Real)' % V(i, g))
            if sup is not None:
                out.append('(assert (>= %s 1.0))' % V(i, g))
            else:
                out.append('(declare-const b_%d_%d Bool)' % (i, g))
                out.append('(assert (ite b_%d_%d (>= %s 1.0) (= %s 0.0)))' % (i, g, V(i, g), V(i, g)))
        if sup is None:
            out.append('(assert (<= %s %d.0))' % (lin(['(ite b_%d_%d 1.0 0.0)' % (i, g) for g in range(m)]), k))
    pos = lambda i, g: ('true' if g in sup[i] else 'false') if sup is not None else 'b_%d_%d' % (i, g)
    for g in P:                                            # every pool good valued by someone
        out.append('(assert (or %s))' % ' '.join(pos(i, g) for i in range(n)))
    for j in range(n):                                     # at most one good worthless to all in each bundle
        for a in range(len(B[j])):
            for c in range(a + 1, len(B[j])):
                g, h = B[j][a], B[j][c]
                out.append('(assert (or %s))' % ' '.join([pos(i, g) for i in range(n)] + [pos(i, h) for i in range(n)]))
    for i in range(n):                                     # X EFX0 and strong charity
        for j in range(n):
            if i != j:
                for h in B[j]:
                    out.append('(assert (<= %s %s))' % (val(i, [g for g in B[j] if g != h]), val(i, B[i])))
        out.append('(assert (<= %s %s))' % (val(i, P), val(i, B[i])))
    for g in P:                                            # no pool good can be added to a bundle
        for j in range(n):
            C = B[j] + [g]
            out.append('(assert (or %s))' % ' '.join('(> %s %s)' % (val(i, [x for x in C if x != h]), val(i, B[i]))
                                                     for i in range(n) if i != j for h in C))
    src = []
    for j in range(n):
        s = '(and %s)' % ' '.join('(<= %s %s)' % (val(i, B[j]), val(i, B[i])) for i in range(n) if i != j)
        out.append('(define-fun src_%d () Bool %s)' % (j, s))
        if len(B[j]) < 2:
            out.append('(assert (not src_%d))' % j)
        src.append('(ite src_%d 1.0 0.0)' % j)
    out.append('(assert (>= %s %d.0))' % (lin(src), len(P) + 1))
    WX = lin([V(i, g) for i in range(n) for g in B[i] if sup is None or g in sup[i]])
    for t, Y in enumerate(D['cuts']):
        if only is not None and t not in only:
            continue
        assert len(Y) == n + 1 and sorted(g for Yi in Y for g in Yi) == list(range(m)) and len(Y[n]) <= p - 1, Y
        disj = ['(< %s %s)' % (lin([V(i, g) for i in range(n) for g in Y[i] if sup is None or g in sup[i]]), WX)]
        for i in range(n):
            for j in range(n):
                if i != j:
                    for h in Y[j]:
                        disj.append('(> %s %s)' % (val(i, [g for g in Y[j] if g != h]), val(i, Y[i])))
        out.append(('(assert (! (or %s) :named cut_%d))' % (' '.join(disj), t)) if named else
                   '(assert (or %s))' % ' '.join(disj))
    out.append('(check-sat)')
    if named:
        out.append('(get-unsat-core)')
    return '\n'.join(out)


def solve(text):
    tm = cvc5.TermManager(); s = cvc5.Solver(tm)
    s.setOption('produce-models', 'false')
    sm = cvc5.SymbolManager(tm); ip = cvc5.InputParser(s, sm)
    ip.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, text, 'cert')
    res = None; core = None
    while True:
        cmd = ip.nextCommand()
        if cmd.isNull():
            break
        r = cmd.invoke(s, sm).strip()
        if r in ('sat', 'unsat', 'unknown'):
            res = r
        elif r.startswith('('):
            core = sorted(int(x[4:]) for x in r.strip('()').split() if x.startswith('cut_'))
    return (res, core) if core is not None else res


if __name__ == '__main__':
    print('$ python3 kgen/charity/w_cert.py', *[a.split('/')[-1] for a in sys.argv[1:]], flush=True)
    if sys.argv[1] == '--core':
        f, out = sys.argv[2], sys.argv[3]; D = json.load(open(f)); t0 = time.time()
        r, core = solve(encode(D, named=True))
        assert r == 'unsat', r
        print('%s: %d cuts; cvc5 unsat, core of %d cuts (%.1f s)' % (f.split('/')[-1], len(D['cuts']), len(core),
                                                                      time.time() - t0), flush=True)
        if '--min' in sys.argv:
            keep = list(core)
            for t in list(core):
                trial = [x for x in keep if x != t]
                if solve(encode(D, only=set(trial))) == 'unsat':
                    keep = trial
            core = keep
            print('  deletion-minimal core: %d cuts (%.1f s)' % (len(core), time.time() - t0), flush=True)
        r2 = solve(encode(D, only=set(core)))
        print('  core alone: cvc5 says %s' % r2, flush=True)
        assert r2 == 'unsat'
        json.dump({'core': core}, open(out, 'w'))
        sys.exit(0)
    for f in sys.argv[1:]:
        D = json.load(open(f)); t0 = time.time()
        text = encode(D)
        r = solve(text)
        print('%s: n %d, m %d, k %d, X leaves %d out, cuts %d (each leaving <= %d out), fixed support %s: cvc5 says %s '
              '(%.1f s)' % (f.split('/')[-1], D['n'], D['m'], D['k'], len(D['pool']), len(D['cuts']), D['p'] - 1,
                            D['support'] is not None, r, time.time() - t0), flush=True)
