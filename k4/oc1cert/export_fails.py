"""Export every maximum-matching start where OC1^max fails (so that, by the OC2^max certificate, exactly two moves are
needed), for the hypergraphs of a certificate whose depth-1 run failed (workstream compute/k4-oc1max-cert).

For each such hypergraph, cegar.Cert(depth=1) is run to the end with every failing (type profile, picks) pair blocked
exactly, which enumerates all of them (single encoding; check.py --excluded re-checks that every other pair is
covered).  For every pair the record gives:
- explicit integer values (the type's representative: strict, balanced, (C4));
- the picks and every order whose SD picks they are;
- the receivers: pick holders whose pick no other agent prefers to its own (the unfrozen agents; for TTC Conjecture R2);
- Inst.check (raw: must be 'OC1 fails');
- for every SAMPLE-th pair, a raw two-move check (Inst.moves twice, Inst.one_absorber).
It also writes OUT_cert.json.gz: per hypergraph every witness the run added and the excluded (failing) pairs, so that
check.py can confirm independently that every other pair is repaired (the enumeration is complete).

    python3 k4/oc1cert/export_fails.py CERT_DEPTH1.json.gz OUT.json.gz [SAMPLE]"""
import sys, os, gzip, json, itertools, collections, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
from cegar import Cert
from oc1_mc2_rand import Inst


def receivers(I, Y):
    return [j for j in range(I.n) if Y[j] is not None and
            not any(i != j and Y[j] in I.v[i] and (Y[i] is None or I.v[i][Y[j]] > I.v[i][Y[i]]) for i in range(I.n))]


def main():
    src, out = sys.argv[1], sys.argv[2]; SAMPLE = int(sys.argv[3]) if len(sys.argv) > 3 else 50
    print('$ python3 k4/oc1cert/export_fails.py', *sys.argv[1:], flush=True)
    recs = json.load(gzip.open(src))['cores']
    res = []; cert = []; T = collections.Counter(); t0 = time.time()
    for r in recs:
        if r['result'] == 'certified': continue
        C = Cert(r['sets'], depth=1); st = C.run(max_fail=10 ** 9)
        assert st == 'FAIL'
        starts = []
        for k, (prof, Y) in enumerate(C.fails):
            vals = [list(C.dom[i][t]) for i, t in enumerate(prof)]
            I = Inst(r['sets'], vals)
            orders = [list(o) for o in itertools.permutations(range(I.n)) if I.sd(o) == tuple(Y)]
            raw = I.check(tuple(Y))
            rc = receivers(I, Y)
            e = {'vals': vals, 'picks': list(Y), 'orders': orders, 'receivers': rc, 'raw': raw}
            if k % SAMPLE == 0:
                base = [[p] if p is not None else [] for p in Y]
                two = set(s2 for s in I.moves(base) for s2 in I.moves([list(b) for b in s]))
                e['raw_two_moves'] = 'two moves repair' if any(I.one_absorber([list(b) for b in s]) for s in two) else 'two moves fail'
                T['sampled two-move raw check: %s' % e['raw_two_moves']] += 1
            T['raw: %s' % raw] += 1
            T['orders per start %d' % len(orders)] += 1
            T['receivers per start %d' % len(rc)] += 1
            starts.append(e)
        T['hypergraphs'] += 1; T['starts'] += len(starts)
        print(r['list'], r['idx'], 'failing starts', len(starts), 'distinct profiles', len(set(map(lambda s: json.dumps(s['vals']), starts))),
              'receivers', dict(collections.Counter(len(s['receivers']) for s in starts)), '%.0f s' % (time.time() - t0), flush=True)
        res.append({'list': r['list'], 'idx': r['idx'], 'sets': r['sets'], 'nu': C.nu, 'starts': starts})
        # certificate modulo the failing pairs: every witness the run added, and the pairs it blocked one by one
        cert.append({'list': r['list'], 'idx': r['idx'], 'sets': r['sets'], 'nu': C.nu, 'result': 'certified',
                     'witnesses': [w.to_json() for w in C.witnesses],
                     'excluded': [{'picks': s['picks'], 'vals': s['vals']} for s in starts]})
    with gzip.open(out, 'wt') as f:
        json.dump({'what': 'every (type profile, picks) pair of these core hypergraphs where the picks form a maximum '
                           'matching, are an SD outcome, and OC1^max fails (no one-absorber completion at the picks or '
                           'after one official move); by the OC2^max certificate (cert_4_depth2.json.gz) two moves '
                           'suffice at each; values are integer representatives of the strict balanced types',
                   'source': src, 'generator': 'k4/oc1cert/export_fails.py', 'hypergraphs': res}, f)
    cout = out.replace('.json.gz', '_cert.json.gz')
    with gzip.open(cout, 'wt') as f:
        json.dump({'statement': 'every (type profile, maximum-matching SD picks) pair of these hypergraphs is repaired by '
                                'a witness (OC1^max) except the listed excluded pairs; check with k4/oc1cert/check.py',
                   'generator': 'k4/oc1cert/export_fails.py', 'cores': cert}, f)
    for k in sorted(T): print(k, T[k])
    print('wrote', out, cout, '%.0f s' % (time.time() - t0))


if __name__ == '__main__':
    main()
