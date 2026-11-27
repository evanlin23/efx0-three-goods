"""Referee check of k3-oc1's Lemma NA (k4/k3_oc1.md §13.5 on claude/k4-k3-oc1; k4/oc1_hall.md §24.13), written here from
the statement.  At every DEMOTE-0 RF start of the n = 5 exports (one receiver, no truly dangerous agent), every
injection f: J' -> agents is tried (each agent takes its pick and at most one junk good, no owner):
  - Lemma NA's criterion: every agent i that wants the pick of a receiving agent a != i has v_i(X_i) >= v_i(Y'_a);
  - raw EFX0 (ohlib.efx0 and the raw checker's Inst.efx0).
The two must agree on every assignment.  Also counted: the DEMOTE-0 starts with some no-owner completion, split by
whether Lemma RF-A1*'s owner-w completion (w takes W, d takes {g, h}) is EFX0 there.

    python3 k4/oc1_hall/rf_na_check.py N5_EXPORT [N5_EXPORT ...]
"""
import sys, os, json, gzip, collections, itertools, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, threatened, efx0
import _paths
sys.path.insert(0, os.path.join(_paths.ROOT, 'k4', 'sdc'))
from oc1_mc2_rand import Inst as RawInst


def job(task):
    sets, starts, tag = task
    m = 1 + max(max(s) for s in sets); C = collections.Counter(); seen = set(); bad = []
    for st in starts:
        vals = st['vals']; I = Inst(sets, vals, m); Y = tuple(st['picks']); u = st['receivers'][0]
        R = RawInst(sets, vals)
        for o in st['orders']:
            Y2 = picks(I, [u] + [x for x in o if x != u])
            if None in Y2 or (json.dumps(vals), Y2) in seen: continue
            seen.add((json.dumps(vals), Y2)); P = Picks(I, Y2)
            U2 = [i for i in range(I.n) if i not in P.F]
            if len(U2) != 1 or any(threatened(I, k, P.pv[k], P.J) for k in P.D): continue
            C['DEMOTE-0 starts'] += 1
            J = P.J; some = False
            for who in itertools.permutations(range(I.n), len(J)):
                X = [[y] for y in Y2]
                for g, a in zip(J, who): X[a].append(g)
                val = [I.val(i, X[i]) for i in range(I.n)]
                crit = all(not (I.v[i].get(Y2[a], 0) > P.pv[i]) or val[i] >= I.v[i].get(Y2[a], 0) for a in who for i in range(I.n) if i != a)
                raw = efx0(I, X); raw2 = R.efx0(X)
                C['assignments: criterion %s, ohlib %s, raw %s' % (crit, raw, raw2)] += 1
                if not (crit == raw == raw2) and len(bad) < 3: bad.append({'sets': sets, 'vals': vals, "Y'": list(Y2), 'X': X})
                some = some or raw
            C['DEMOTE-0 starts with a no-owner completion: %s' % some] += 1
            C['  ... on %s: %s' % (tag, some)] += 1
    return C, bad


def tasks_of(path):
    d = json.load(gzip.open(path))
    for hg in d['hypergraphs']:
        groups = collections.defaultdict(list)
        for st in hg['starts']: groups[json.dumps(st['vals'])].append(st)
        chunk = []
        for g in groups.values():
            chunk += g
            if len(chunk) >= 2000: yield (hg['sets'], chunk, '%s#%d' % (hg['list'], hg['idx'])); chunk = []
        if chunk: yield (hg['sets'], chunk, '%s#%d' % (hg['list'], hg['idx']))


if __name__ == '__main__':
    print('$ python3 k4/oc1_hall/rf_na_check.py', *[os.path.basename(p) for p in sys.argv[1:]], flush=True)
    T = collections.Counter(); shown = 0
    with mp.Pool() as pool:
        for C, bad in pool.imap_unordered(job, [t for p in sys.argv[1:] for t in tasks_of(p)]):
            T.update(C)
            for b in bad:
                if shown < 5: shown += 1; print('CRITERION DISAGREES WITH RAW EFX0:', json.dumps(b), flush=True)
    for k in sorted(T): print(k, T[k])
