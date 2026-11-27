"""Lemma RF-B (k4/oc1_hall.md §24.8) on the n = 5 OC1^max-failure exports of compute/k4-oc1max-cert (§24.9).

Input: the certifier's two-move start exports (every failing (type profile, picks) pair of the listed hypergraphs,
with every order giving the picks), e.g.
    git show origin/compute/k4-oc1max-cert:results/k4_oc1max/n5/two_move_starts_n5_partial6.json.gz > partial6.json.gz
    git show origin/compute/k4-oc1max-cert:results/k4_oc1max/n5/two_move_starts_n5_sel2.json.gz > sel2.json.gz
and the stored failures of the certifier's summaries (oc1_fails fields, every order giving the picks recomputed here):
    git show origin/compute/k4-oc1max-cert:results/k4_oc1max/n5/5_pure_s5o0_summary.jsonl.gz > s5o0.jsonl.gz

For every failing order o with receiver u, the RF start Y' = SD(u, o - u) (distinct (profile, Y') pairs once) is
classified by (|U'|, |D_T'|).  At the DEMOTE-2 starts (|U'| = 1, |D_T'| = 2) every candidate k (a truly dangerous agent
whose pick d wants and the other one does not) is tested against Lemma RF-B's hypotheses (B1)-(B5), with S = the junk
goods k and k' share, and FULL(k, S) is tested for EFX0 (rf_b_facts.lemma_rfb: ohlib.efx0 and the raw checker's
Inst.efx0).  Tiers at each DEMOTE-2 start:
  1. some candidate meets (B1)-(B5) (then FULL(k, S) is checked EFX0);
  2. else the chain "k takes S, d takes Y'_k" (k in D_T', d wanting Y'_k) followed by ANY one-absorber completion
     (ohlib.absorb_brute, raw EFX0);
  3. else ANY canonical chain from k in D_T' (each agent wanting its predecessor's pick) with H0 = S, followed by any
     one-absorber completion;
  4. else the start is printed (first few) and checked for OC1 by the raw checker (k4/sdc/oc1_mc2_rand.Inst.check).
RF is run from EVERY receiver of the failing start (two-receiver failures exist at n = 5: R2 is refuted, K4.SDC.R2.N5),
and Lemma RF-PATH is checked at every RF start: the agents whose picks change form one ejection path u -> x1 -> ... -> d
in o-order, every x_i strictly loses, u gains, and the end d is unfrozen at Y' (girth, k4/girth.md §7).

    python3 k4/oc1_hall/rf_n5.py FILE [FILE ...]
"""
import sys, os, json, gzip, collections, itertools, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, threatened, base_of_picks, absorb_brute, bundles_of
from greedy_rules import apply_chain, canonical_paths
import rf_b_facts as RB
import _paths
sys.path.insert(0, os.path.join(_paths.ROOT, 'k4', 'sdc'))
from oc1_mc2_rand import Inst as RawInst


def job(task):
    sets, starts, tag = task
    m = 1 + max(max(s) for s in sets); C = collections.Counter(); bad = []
    seen = set()
    for st in starts:
        vals = st['vals']; I = Inst(sets, vals, m); Y = tuple(st['picks'])
        P0 = Picks(I, Y); U0 = [i for i in range(I.n) if i not in P0.F and Y[i] is not None]
        if 'orders' in st:
            orders = st['orders']
        else:
            orders = [o for o in itertools.permutations(range(I.n)) if picks(I, o) == Y]
            C['stored failure: receivers = %d' % len(U0)] += 1
        C['failing orders'] += 1 * len(orders)
        C['failing starts with %d receivers' % len(U0)] += 1
        for o, u in itertools.product(orders, U0):        # RF from EVERY receiver (R2 is refuted at n = 5)
            Y2 = picks(I, [u] + [x for x in o if x != u])
            # Lemma RF-PATH (any receiver moved to the front): one ejection path u -> x1 -> ... -> d in o-order,
            # every x_i strictly loses, u gains, d is unfrozen at Y'
            ch = [i for i in range(I.n) if Y2[i] != Y[i]]
            if ch:
                path = [u]; ok = True
                while True:
                    nxt = [i for i in ch if Y[i] is not None and Y[i] == Y2[path[-1]] and i not in path]
                    if not nxt: break
                    path.append(nxt[0])
                ok = set(path) == set(ch) and all(Y2[x] is None or I.v[x].get(Y2[x], 0) < I.v[x][Y[x]] for x in path[1:]) and I.v[u][Y2[u]] > I.v[u][Y[u]]
                pos = {a: i for i, a in enumerate(o)}
                ok = ok and all(pos[path[i]] < pos[path[i + 1]] for i in range(1, len(path) - 1))
                dd = path[-1]
                ok = ok and (Y2[dd] is None or all(not I.v[i].get(Y2[dd], 0) > I.v[i].get(Y2[i], 0) for i in range(I.n) if i != dd))
                C['RF-PATH (one ejection path in o-order, ejected agents lose, end unfrozen at Y\'): %s' % ok] += 1
            else:
                C['RF-PATH: Y\' = Y'] += 1
            key = (json.dumps(vals), Y2)
            if key in seen: continue
            seen.add(key)
            P = Picks(I, Y2)
            U2 = [i for i in range(I.n) if i not in P.F and Y2[i] is not None]
            DT = [k for k in P.D if threatened(I, k, P.pv[k], P.J)]
            C['RF starts'] += 1
            if any(y is None for y in Y2): C['RF starts with a pickless agent'] += 1; continue
            C['RF starts by (|U\'|, |D_T\'|) = (%d, %d)' % (len(U2), len(DT))] += 1
            if len(U2) != 1 or len(DT) != 2: continue
            d = U2[0]; k1, k2 = DT; other = {k1: k2, k2: k1}
            S = tuple(g for g in P.J if g in I.R[k1] and g in I.R[k2])
            C['DEMOTE-2: |S| = %d' % len(S)] += 1
            cand = [k for k in DT if RB.lab(I, P, Y2, k, other[k], d) == 'k<-d']
            C['DEMOTE-2: candidates k<-d: %d' % len(cand)] += 1
            res = []
            for k in cand:
                C2 = collections.Counter()
                res.append((k, RB.lemma_rfb(I, Y2, P, d, k, S, C2, ''), C2))
                C['DEMOTE-2 candidate %s the RF path: meets (B1)-(B5) %s' % ('on' if Y2[k] != Y[k] else 'off', res[-1][1][0])] += 1
            if len(cand) == 2:
                hi = max(cand, key=lambda k: I.v[d].get(Y2[k], 0))
                C['DEMOTE-2, two candidates: the one d values more meets (B1)-(B5): %s; the other: %s' % tuple(r[1][0] for r in sorted(res, key=lambda r: r[0] != hi))] += 1
            ok = [r for r in res if r[1][0]]
            C['DEMOTE-2: some candidate meets (B1)-(B5): %s' % bool(ok)] += 1
            if ok:
                C['DEMOTE-2: ... and FULL(k, S) is EFX0 for it: %s' % all(r[1][1] for r in ok)] += 1
                continue
            C['DEMOTE-2: FULL(k, S) EFX0 for some candidate anyway: %s' % any(r[1][1] for r in res)] += 1
            for k, (h, c), C2 in res:
                for key2, v in C2.items():
                    if 'hypothesis' in key2 and key2.endswith('False'): C['DEMOTE-2, no candidate: failed ' + key2.split('hypothesis ')[1]] += v
            if not cand: C['DEMOTE-2, no candidate at all'] += 1
            base = base_of_picks(I, Y2)
            # tier 2: k in D_T' takes S, d (wanting Y'_k) takes Y'_k; then ANY one-absorber completion
            t2 = set()
            for k in DT:
                if I.v[d].get(Y2[k], 0) > P.pv[d] and I.val(k, S) > P.pv[k]:
                    ab = absorb_brute(I, apply_chain(I, P, base, (k, d), S), witness=True)
                    if ab: t2.add('owner ' + ('d' if ab[0] == d else ('k' if ab[0] == k else 'other')))
            C['DEMOTE-2, tier 2 (chain k -> d with T = S, then any completion): %s' % bool(t2)] += 1
            if t2: continue
            # tier 3: any canonical chain from k in D_T' with H0 = S, then any completion
            t3 = set()
            for k in DT:
                if not I.val(k, S) > P.pv[k]: continue
                for path in canonical_paths(I, P, k):
                    ab = absorb_brute(I, apply_chain(I, P, base, path, S), witness=True)
                    if ab: t3.add('length %d, head %s' % (len(path) - 1, 'd' if path[-1] == d else 'frozen'))
            C['DEMOTE-2, tier 3 (a canonical chain from k with H0 = S, then any completion): %s' % bool(t3)] += 1
            for x in t3: C['DEMOTE-2, tier 3 kind: ' + x] += 1
            if not t3 and len(bad) < 2:
                R = RawInst(sets, vals); bad.append({'sets': sets, 'vals': vals, 'Y': list(Y), 'u': u, "Y'": list(Y2), 'd': d, 'DT': DT, 'S': list(S), 'OC1 at Y\'': R.check(Y2)})
    return tag, C, bad


def tasks_of(path):
    if path.endswith('.jsonl.gz'):
        for line in gzip.open(path):
            r = json.loads(line)
            if r.get('oc1_fails'):
                yield (r['sets'], [{'vals': f['vals'], 'picks': f['picks']} for f in r['oc1_fails']], 'stored ' + os.path.basename(path))
        return
    d = json.load(gzip.open(path))
    for hg in d['hypergraphs']:
        groups = collections.defaultdict(list)          # starts with the same profile stay in one task, so that
        for st in hg['starts']: groups[json.dumps(st['vals'])].append(st)   # (profile, Y') pairs are counted once
        chunk = []
        for g in groups.values():
            chunk += g
            if len(chunk) >= 4000: yield (hg['sets'], chunk, '%s#%d' % (hg['list'], hg['idx'])); chunk = []
        if chunk: yield (hg['sets'], chunk, '%s#%d' % (hg['list'], hg['idx']))


if __name__ == '__main__':
    print('$ python3 k4/oc1_hall/rf_n5.py', *[os.path.basename(p) for p in sys.argv[1:]], flush=True)
    T = collections.Counter(); per = collections.defaultdict(collections.Counter); shown = 0
    tasks = [t for p in sys.argv[1:] for t in tasks_of(p)]
    with mp.Pool() as pool:
        for tag, C, bad in pool.imap_unordered(job, tasks):
            T.update(C); per[tag].update(C)
            for b in bad:
                if shown < 12: shown += 1; print('DEMOTE-2 START OUTSIDE TIERS 1-3:', json.dumps(b), flush=True)
    for tag in sorted(per):
        c = per[tag]
        print('%s: RF starts %d, DEMOTE-2 %d, with a candidate meeting (B1)-(B5) %d' % (tag, c['RF starts'], sum(v for k, v in c.items() if k.startswith('DEMOTE-2: |S|')), c['DEMOTE-2: some candidate meets (B1)-(B5): True']))
    for k in sorted(T): print(k, T[k])
