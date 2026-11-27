"""The RF starts of the n = 5 failure exports where the per-order rotation leaves an agent pickless (k4/oc1_hall.md
§24.10; girth's question).  For each failing order o with receiver u and Y' = SD(u, o - u) not a maximum matching:
  - the RF path u = x0 -> x1 -> ... -> d (Lemma RF-PATH) and whether its end d is the pickless agent ("d gets nothing");
  - fix 1, "d just before its ejector": sigma' = (u, o - u) with d moved to just before x_{l-1}, the agent that took
    d's pick (for l = 1 the ejector is u, so d goes first);
  - fix 2, "d second": (u, d, o - u - d);
  - for each fix: are the picks a maximum matching, and does OC1 hold there (raw, k4/sdc/oc1_mc2_rand.Inst.check)?

    python3 k4/oc1_hall/rf_n5_pickless.py FILE [FILE ...]    (the exports two_move_starts_n5_partial6 / sel2)
"""
import sys, os, json, gzip, collections, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks
import _paths
sys.path.insert(0, os.path.join(_paths.ROOT, 'k4', 'sdc'))
from oc1_mc2_rand import Inst as RawInst


def rf_path(Y, Y2, u):
    path = [u]
    while True:
        nxt = [i for i in range(len(Y)) if Y[i] is not None and Y2[path[-1]] is not None and Y[i] == Y2[path[-1]] and i not in path]
        if not nxt: return path
        path.append(nxt[0])


def job(task):
    sets, starts, tag = task
    m = 1 + max(max(s) for s in sets); C = collections.Counter(); ex = []; seen = set()
    R = None
    for st in starts:
        vals = st['vals']; I = Inst(sets, vals, m); Y = tuple(st['picks']); u = st['receivers'][0]
        for o in st['orders']:
            sig = [u] + [x for x in o if x != u]; Y2 = picks(I, sig)
            if None not in Y2: continue
            key = (json.dumps(vals), Y2)
            if key in seen: continue
            seen.add(key); C['pickless RF starts'] += 1
            path = rf_path(Y, Y2, u); d = path[-1]
            C['the pickless agent is the RF path\'s end d: %s; path length %d' % (Y2[d] is None, len(path) - 1)] += 1
            ej = path[-2]
            f1 = [x for x in sig if x != d]; f1.insert(f1.index(ej), d)
            f2 = [u, d] + [x for x in sig if x not in (u, d)]
            R = RawInst(sets, vals)
            for name, od in (('fix 1 (d just before its ejector)', f1), ('fix 2 (d second)', f2)):
                Z = picks(I, od)
                if None in Z: C[name + ': not a maximum matching'] += 1; continue
                res = R.check(Z)
                C[name + ': maximum matching, OC1 %s' % res] += 1
                if res == 'OC1 fails' and len(ex) < 3: ex.append({'fix': name, 'sets': sets, 'vals': vals, 'Y': list(Y), 'o': list(o), 'order': od, 'picks': list(Z)})
            if len(ex) < 1: ex.append({'example': True, 'sets': sets, 'vals': vals, 'Y': list(Y), 'o': list(o), "Y'": list(Y2), 'path': path})
    return tag, C, ex


def tasks_of(path):
    d = json.load(gzip.open(path))
    for hg in d['hypergraphs']:
        groups = collections.defaultdict(list)
        for st in hg['starts']: groups[json.dumps(st['vals'])].append(st)
        chunk = []
        for g in groups.values():
            chunk += g
            if len(chunk) >= 4000: yield (hg['sets'], chunk, '%s#%d' % (hg['list'], hg['idx'])); chunk = []
        if chunk: yield (hg['sets'], chunk, '%s#%d' % (hg['list'], hg['idx']))


if __name__ == '__main__':
    print('$ python3 k4/oc1_hall/rf_n5_pickless.py', *[os.path.basename(p) for p in sys.argv[1:]], flush=True)
    T = collections.Counter(); per = collections.Counter(); shown = 0
    with mp.Pool() as pool:
        for tag, C, ex in pool.imap_unordered(job, [t for p in sys.argv[1:] for t in tasks_of(p)]):
            T.update(C); per[tag] += C['pickless RF starts']
            for e in ex:
                if shown < 4: shown += 1; print(json.dumps(e), flush=True)
    for k in sorted(per): print('pickless RF starts on', k, per[k])
    for k in sorted(T): print(k, T[k])
