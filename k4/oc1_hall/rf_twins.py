"""Twin receivers at RF starts.  A *set-twin* of u is an agent w with R_w = R_u (same goods); an *exact twin* also has
v_w = v_u on every good.  Both are counted (k4/oc1_hall.md §24.15; coordinator's question for Rule RF-rot).  At every failing order
o with receiver u, w = the holder of u's top good at Y: is w a twin of u (R_w = R_u), and is the RF rotation then a
pick swap (Y'_u = Y_w, Y'_w = Y_u)?  At k = 5 such a swap reproduces the failing start (ledger K4.SDC.RF.K5EVERY).
Data: the n = 4 export (main) and the n = 5 exports of compute/k4-oc1max-cert.  OC1 at the rotation is known from
rf_n5_all.py / receiver_first_check (every rotation satisfies OC1 on these data); here only the twin structure is counted.

    python3 k4/oc1_hall/rf_twins.py N4_EXPORT N5_EXPORT [N5_EXPORT ...]
"""
import sys, os, json, gzip, collections, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks


def job(task):
    sets, starts, tag = task
    m = 1 + max(max(s) for s in sets); C = collections.Counter()
    for st in starts:
        I = Inst(sets, st['vals'], m); Y = tuple(st['picks'])
        for u in st['receivers']:
            top = max(I.R[u], key=lambda g: I.key[u][g])
            w = [i for i in range(I.n) if Y[i] == top]
            for o in st['orders']:
                C[tag + 'failing (order, receiver) pairs'] += 1
                if not w: C[tag + "u's top good is junk at Y"] += 1; continue
                Y2 = picks(I, [u] + [x for x in o if x != u])
                twin = I.R[w[0]] == I.R[u]
                if twin: C[tag + '  set-twin; also exact twin (identical values on every good): %s' % (I.v[w[0]] == I.v[u])] += 1
                swap = Y2[u] == Y[w[0]] and Y2[w[0]] == Y[u]
                C[tag + 'w a twin of u: %s; rotation is the pick swap u <-> w: %s' % (twin, swap)] += 1
                if twin and swap:
                    C[tag + '  twin swap: Y\' equals Y up to swapping the twins: %s' % (sorted(zip(sets, Y2)) == sorted(zip(sets, Y)))] += 1
    return C


def tasks_of(path, tag):
    d = json.load(gzip.open(path))
    for hg in d['hypergraphs']:
        st = hg['starts']
        for a in range(0, len(st), 4000): yield (hg['sets'], st[a:a + 4000], tag)


if __name__ == '__main__':
    print('$ python3 k4/oc1_hall/rf_twins.py', *[os.path.basename(p) for p in sys.argv[1:]], flush=True)
    tasks = []
    for p in sys.argv[1:]: tasks += list(tasks_of(p, 'n=4 ' if 'n4' in os.path.basename(p) else 'n=5 '))
    T = collections.Counter()
    with mp.Pool() as pool:
        for C in pool.imap_unordered(job, tasks): T.update(C)
    for k in sorted(T): print(k, T[k])
