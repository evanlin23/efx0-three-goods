"""Unsat core of a dumped cut list (kgen/charity.md §6), found with z3 by assumption literals: each cut t is asserted
as g_t -> cut_t over the SMT-LIB text of w_cert.encode, and z3 is asked for satisfiability under all g_t.  The core's
provenance does not matter for the certificate: w_cert.py (cvc5) and w_milp_cert.py (HiGHS) then check the core
alone, and a subset of the cuts that is infeasible makes the whole list infeasible.

    python3 kgen/charity/w_core_z3.py CUTFILE COREFILE"""
import sys, json, time, gzip
import z3
from w_cert import encode

if __name__ == '__main__':
    print('$ python3 kgen/charity/w_core_z3.py', *[a.split('/')[-1] for a in sys.argv[1:]], flush=True)
    f, out = sys.argv[1], sys.argv[2]
    D = json.load(gzip.open(f, 'rt') if f.endswith('.gz') else open(f)); t0 = time.time()
    S = z3.Solver()
    S.from_string(encode(D, guard=True).replace('(check-sat)', ''))
    g = [z3.Bool('g_%d' % t) for t in range(len(D['cuts']))]
    r = S.check(*g)
    assert r == z3.unsat, r
    core = sorted(int(str(c)[2:]) for c in S.unsat_core())
    print('z3: unsat under all %d cuts; core of %d cuts (%.1f s)' % (len(g), len(core), time.time() - t0), flush=True)
    json.dump({'core': core}, open(out, 'w'))
