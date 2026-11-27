"""Which SD orders are good at the starts where OC1^max fails (the coordinator's request; workstream
compute/k4-oc1max-cert).  Raw code only (k4/sdc/oc1_mc2_rand.Inst), no SAT.

At each failing start (a strict profile `vals` and the picks `picks` of a maximum-matching SD order for which OC1
fails), every one of the n! SD orders is run.
- An order counts if it is maximum-matching: its picks number nu (the size of a maximum matching).
- The orders are grouped by their pick vectors. For each pick vector the record has:
  - the orders giving it;
  - OC1 by Inst.check ('picks complete', 'one move repairs' or 'OC1 fails');
  - the receivers (pick holders whose pick no other agent prefers to its own pick, an agent without a pick valuing
    its own pick at 0);
  - the frozen agents (the other pick holders);
  - the junk (goods nobody picked).
- Totals: the distribution of (number of good pick vectors, number of bad ones), receivers of good and of bad pick
  vectors, and a few candidate rules for choosing a good order, each counted over the starts.

Input: an n = 5 chunk summary (results/k4_oc1max/n5/*_summary.jsonl.gz: the stored OC1^max failures `oc1_fails`)
or an export of failing starts (export_fails.py's format: {"hypergraphs": [{"sets", "starts": [{"vals",
"picks"}]}]}).

    python3 k4/oc1cert/good_orders.py IN OUT.json.gz [--stride=K] [--jobs=4]"""
import sys, os, gzip, json, itertools, collections, time, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
from oc1_mc2_rand import Inst


def nu(I):
    """size of a maximum matching agents -> goods (augmenting paths)"""
    match = {}
    def aug(i, seen):
        for g in I.R[i]:
            if g in seen: continue
            seen.add(g)
            if g not in match or aug(match[g], seen): match[g] = i; return True
        return False
    return sum(aug(i, set()) for i in range(I.n))


def roles(I, P):
    val = lambda i, g: I.v[i].get(g, 0) if g is not None else 0
    rec = [j for j in range(I.n) if P[j] is not None and
           not any(i != j and val(i, P[j]) > val(i, P[i]) for i in range(I.n))]
    frozen = [j for j in range(I.n) if P[j] is not None and j not in rec]
    junk = [g for g in range(I.m) if g not in P]
    return rec, frozen, junk


def analyse(a):
    lst, idx, sets, vals, bad = a
    I = Inst(sets, vals); bad = tuple(bad); k = nu(I)
    by = collections.defaultdict(list)
    for o in itertools.permutations(range(I.n)):
        P = I.sd(o)
        if sum(p is not None for p in P) == k: by[P].append(list(o))
    assert bad in by, 'the failing picks are not a maximum-matching SD outcome'
    outs = []
    for P, ords in sorted(by.items(), key=lambda t: -len(t[1])):
        rec, frozen, junk = roles(I, P)
        outs.append({'picks': list(P), 'orders': ords, 'OC1': I.check(P), 'receivers': rec, 'frozen': frozen,
                     'junk': junk, 'is the failing start': P == bad})
    return {'list': lst, 'idx': idx, 'sets': sets, 'vals': vals, 'failing picks': list(bad), 'nu': k,
            'pick vectors': outs}


def rules(r):
    """candidate rules for a good order: True if the rule's choice is good, False if bad, None if it chooses nothing"""
    outs = r['pick vectors']; good = lambda o: o['OC1'] != 'OC1 fails'
    bad = next(o for o in outs if o['is the failing start'])
    res = {}
    mx = max(len(o['receivers']) for o in outs)
    top = [o for o in outs if len(o['receivers']) == mx]
    res['every pick vector with the most receivers is good'] = all(good(o) for o in top)
    res['some pick vector with the most receivers is good'] = any(good(o) for o in top)
    res['every pick vector with >= 2 receivers is good'] = all(good(o) for o in outs if len(o['receivers']) >= 2) \
        if any(len(o['receivers']) >= 2 for o in outs) else None
    mo = max(len(o['orders']) for o in outs)
    res['the most frequent pick vector is good'] = all(good(o) for o in outs if len(o['orders']) == mo)
    # an order starting with a receiver of the failing start
    st = [o for o in outs if any(od[0] in bad['receivers'] for od in o['orders'])]
    res['every order starting with a receiver of the failing start is good'] = all(
        good(o) for o in st if any(od[0] in bad['receivers'] for od in o['orders'])) if st else None
    # nearest good pick vector to the failing one (Hamming distance)
    d = [sum(a != b for a, b in zip(o['picks'], bad['picks'])) for o in outs if good(o)]
    res['Hamming distance from the failing picks to the nearest good picks'] = min(d) if d else None
    return res


def main():
    src, out = sys.argv[1], sys.argv[2]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[3:] if a.startswith('--') and '=' in a)
    stride = int(opt.get('stride', 1))
    print('$ python3 k4/oc1cert/good_orders.py', *sys.argv[1:], flush=True)
    tasks = []
    if src.endswith('.jsonl.gz'):
        for l in gzip.open(src, 'rt'):
            if not l.strip(): continue
            r = json.loads(l)
            for f in r.get('oc1_fails') or []:
                tasks.append((r['list'], r['idx'], r['sets'], f['vals'], f['picks']))
    else:
        d = json.load(gzip.open(src))
        for h in d['hypergraphs']:
            for s in h['starts']:
                tasks.append((h.get('list'), h.get('idx'), h['sets'], s['vals'], s['picks']))
    tasks = tasks[::stride]
    print('failing starts', len(tasks), 'hypergraphs', len({(t[0], t[1], len(t[2]), str(t[2])) for t in tasks}),
          flush=True)
    T = collections.Counter(); R = collections.defaultdict(collections.Counter); res = []; t0 = time.time()
    with mp.Pool(int(opt.get('jobs', 4))) as pool:
        for r in pool.imap(analyse, tasks, chunksize=4):
            outs = r['pick vectors']
            ng = sum(o['OC1'] != 'OC1 fails' for o in outs); nb = len(outs) - ng
            T['starts'] += 1; T['(good, bad) pick vectors %d, %d' % (ng, nb)] += 1
            if ng == 0: T['NO GOOD ORDER (OC1^exists-max fails)'] += 1; print('NO GOOD ORDER', json.dumps(r), flush=True)
            for o in outs:
                T['%s pick vectors with %d receivers' % ('good' if o['OC1'] != 'OC1 fails' else 'bad', len(o['receivers']))] += 1
                T['good pick vectors: %s' % o['OC1']] += o['OC1'] != 'OC1 fails'
            for k, v in rules(r).items(): R[k][v] += 1
            res.append(r)
            if len(res) % 500 == 0: print('... %d, %.0f s' % (len(res), time.time() - t0), flush=True)
    for k in sorted(T): print(k, T[k])
    print('candidate rules (True: the rule picks a good order; False: a bad one; None: it picks nothing):')
    for k in R: print('  ', k, dict(sorted(R[k].items(), key=str)))
    with gzip.open(out, 'wt') as f:
        json.dump({'what': 'SD orders and their pick vectors at the starts where OC1^max fails (%s)' % os.path.basename(src),
                   'generator': 'k4/oc1cert/good_orders.py (raw Inst code)', 'stride': stride, 'totals': dict(T),
                   'rules': {k: {str(a): b for a, b in v.items()} for k, v in R.items()}, 'starts': res}, f)
    print('wrote', out, '%.0f s' % (time.time() - t0))


if __name__ == '__main__':
    main()
