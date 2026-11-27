"""The RF starts of the n = 5 exports, by Hall's class (|U'|, |D_T'|) (k4/oc1_hall.md §24.10), regenerated with this
workstream's code, and the two classes of the coordinator's task dumped: (1, 3), and DEMOTE-0 = (1, 0) starts whose
picks do not complete (k4/ttc.md §14.8).

RF start: for a failing (profile, picks) pair of the certifier's export, every listed order o and every receiver u,
Y' = SD(u, o - u); distinct (profile, Y') pairs once; Y' leaving an agent pickless is counted separately.  U' = the
receivers of Y'; D_T' = the dangerous agents k (frozen, valuing junk) that the whole junk J' threatens at its pick value
(some h in J' with v_k(J' - h) > p_k).

    python3 k4/ttc/rf_classes_n5.py OUT.jsonl EXPORT.json.gz [EXPORT ...]"""
import sys, os, gzip, json, collections, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ttclib as T


def threatened(E, i, t, S):
    vs = [E.v[i].get(g, 0) for g in S]
    return len(S) >= 2 and sum(vs) - min(vs) > t


def job(args):
    sets, starts = args
    m = 1 + max(max(s) for s in sets); n = len(sets); C = collections.Counter(); dump = []
    seen = set()
    for st in starts:
        E = T.Enc(sets, st['vals'], m)
        for o in st['orders']:
            for u in st['receivers']:
                o2 = [u] + [a for a in o if a != u]
                Y = tuple(T.sd(E, o2)[0])
                key = (json.dumps(st['vals']), Y)
                if key in seen:
                    continue
                seen.add(key)
                if any(y is None for y in Y):
                    C['pickless rotation'] += 1; continue
                b = T.base_of(E, Y); F = T.frozen_set(E, b); U = [i for i in range(n) if i not in F]
                J = [g for g in range(m) if b[g] < 0]
                D = T.dangerous_set(E, b)
                DT = [k for k in sorted(D) if threatened(E, k, E.v[k][Y[k]], J)]
                cls = (len(U), len(DT)); C['class %s' % (cls,)] += 1
                if cls == (1, 3) or cls == (1, 0):
                    P = T.extends_A(E, b, 1)
                    if cls == (1, 0) and P:
                        C['class (1, 0): picks complete'] += 1; continue
                    if cls == (1, 3) and P:
                        C['class (1, 3): picks complete'] += 1; continue
                    dump.append({'sets': sets, 'vals': st['vals'], 'order': o2, 'picks': list(Y), 'class': list(cls),
                                 'U': U, 'DT': DT, 'J': J})
    return C, dump


if __name__ == '__main__':
    print('$ python3 k4/ttc/rf_classes_n5.py', *sys.argv[1:], flush=True)
    out = open(sys.argv[1], 'w'); tasks = []
    for fn in sys.argv[2:]:
        d = json.load(gzip.open(fn))
        for h in d['hypergraphs']:
            byp = collections.defaultdict(list)     # group by profile, so that de-duplication inside a job is global
            for st in h['starts']:
                byp[json.dumps(st['vals'])].append(st)
            grp = list(byp.values())
            for i in range(0, len(grp), 200):
                tasks.append((h['sets'], [st for g in grp[i:i + 200] for st in g]))
    Ctot = collections.Counter(); nd = 0
    with mp.Pool() as pool:
        for C, dump in pool.imap_unordered(job, tasks):
            Ctot.update(C)
            for r in dump:
                out.write(json.dumps(r) + '\n'); nd += 1
    out.close()
    for k in sorted(Ctot):
        print(k, Ctot[k])
    print('dumped', nd)
