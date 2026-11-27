"""Sensitivity test of the OC1^max checkers (workstream compute/k4-oc1max-cert): thinned certificates must be rejected.
For K random certified hypergraphs of a certificate:
- drop one witness and run check.check_core, and also brute.cover_job when n <= 3.  The certificates are UNSAT cores,
  so most single drops leave a hole; a drop that is still covered is reported (a core need not be minimal);
- for every witness, move one random good of X to another agent (usually making it invalid at every matching); the
  certificate made of the perturbed witnesses should be rejected.
check.py uses the recorded picks of a witness as a filter (a sound restriction), brute.py does not, so the test
requires: covered for check.py implies covered for brute.py.

    python3 k4/oc1cert/test_check.py CERT.json.gz [K] [SEED]"""
import sys, os, gzip, json, random, copy, collections

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check, brute


def main():
    path = sys.argv[1]; K = int(sys.argv[2]) if len(sys.argv) > 2 else 20; rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
    print('$ python3 k4/oc1cert/test_check.py', *sys.argv[1:], flush=True)
    recs = [r for r in json.load(gzip.open(path))['cores'] if r['result'] == 'certified']
    C = collections.Counter()
    for r in rng.sample(recs, min(K, len(recs))):
        n = len(r['sets'])
        ok = check.check_core(copy.deepcopy(r))[2]
        assert ok is True, 'the full certificate must be accepted'
        C['full certificate accepted'] += 1
        r2 = copy.deepcopy(r); k = rng.randrange(len(r2['witnesses'])); del r2['witnesses'][k]
        res = check.check_core(copy.deepcopy(r2))[2]
        C['one witness dropped: sat checker %s' % ('still covered' if res is True else 'REJECTS')] += 1
        if n <= 3:
            resb = brute.cover_job(copy.deepcopy(r2))[2]
            C['one witness dropped: brute force %s' % ('still covered' if resb == 'covered' else 'REJECTS')] += 1
            # check.py skips witnesses whose recorded picks differ from Y (a sound restriction); brute.py does not, so
            # it may still cover through a move that is legal from other picks.  So: SAT-covered implies brute-covered.
            assert not (res is True and resb != 'covered'), 'the SAT checker accepts what the brute force rejects'
            if res is not True and resb == 'covered': C['one witness dropped: brute force covers through other picks'] += 1
        r3 = copy.deepcopy(r)
        for w in r3['witnesses']:
            X = list(w['X']); g = rng.randrange(len(X)); X[g] = str((int(X[g]) + 1 + rng.randrange(n - 1)) % n)
            w['X'] = ''.join(X)
        res3 = check.check_core(copy.deepcopy(r3))[2]
        C['every X perturbed: sat checker %s' % ('still covered' if res3 is True else 'REJECTS')] += 1
        if n <= 3:
            resb3 = brute.cover_job(copy.deepcopy(r3))[2]
            assert not (res3 is True and resb3 != 'covered'), 'the SAT checker accepts what the brute force rejects'
            C['every X perturbed: brute force %s' % ('still covered' if resb3 == 'covered' else 'REJECTS')] += 1
    for k in sorted(C): print(k, C[k])


if __name__ == '__main__':
    main()
