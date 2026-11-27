"""Shrink a certificate by keeping one allocation per orbit of the core's automorphism group.

The records get "orbits": true; the checkers (check.py, check_mc_n.py) then expand every listed allocation by the
automorphism group they compute themselves (networkx GraphMatcher on the incidence graph) before checking coverage.
Sound for any group: every image is an allocation like any other, judged by the raw definition.
Usage: orbits.py IN.json.gz OUT.json.gz   (run.py class certificates or run_mc.py lists; allocations as lists or base36)"""
import sys, os, json, gzip
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
import cegar
DIG = '0123456789abcdefghijklmnopqrstuvwxyz'

def main():
    src, dst = sys.argv[1], sys.argv[2]
    d = json.load(gzip.open(src, 'rt'))
    recs = d['cores'] if isinstance(d, dict) else d
    tot = kept = 0
    for r in recs:
        m = r.get('m') or d['m']
        auts = cegar.automorphisms(r['sets'], m, cap=10 ** 9)
        seen, out = set(), []
        for A in r['allocs']:
            A = [int(c, 36) for c in A] if isinstance(A, str) else A
            if tuple(A) in seen: continue
            out.append(''.join(DIG[j] for j in A))
            for ma, mg in auts:
                img = [0] * m
                for g in range(m): img[mg[g]] = ma[A[g]]
                seen.add(tuple(img))
        tot += len(r['allocs']); kept += len(out)
        r['allocs'] = out; r['orbits'] = True
    print(f'{len(recs)} cores: {tot} allocations -> {kept} orbit representatives')
    json.dump(d, gzip.open(dst, 'wt'), separators=(',', ':'))

if __name__ == '__main__':
    main()
