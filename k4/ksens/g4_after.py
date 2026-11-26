"""Lemma candidate (K4-G4) on k = 4 data (k4/ksens.md §2): for every start whose picks have no one-absorber completion,
some state reached by one improving chain has a one-absorber completion AND leaves no dangerous frozen agent: no agent
whose base is wanted by someone (v_i(base_j) > v_i(base_i)) values the junk of that state above its base (GDT's (G4)
without the owner's good).  At k = 5 PW5 has no repairing chain at all.

    python3 k4/ksens/g4_after.py SEEDFILE [NMAX]"""
import sys, json, collections, time
import _paths
import ocsat, kchains
from climb import load_seeds


def dangerous_frozen(sets, vals, m, bases):
    n = len(sets); v = [dict(zip(s, vv)) for s, vv in zip(sets, vals)]
    val = lambda i, S: sum(v[i].get(g, 0) for g in S)
    J = [g for g in range(m) if not any(g in b for b in bases)]
    out = []
    for j in range(n):
        if not bases[j]: continue
        wanted = any(i != j and val(i, bases[j]) > val(i, bases[i]) for i in range(n))
        if wanted and val(j, J) > val(j, bases[j]): out.append(j)
    return out


if __name__ == '__main__':
    path = sys.argv[1]; NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    C = collections.Counter(); t0 = time.time(); seen = set()
    print('$ python3 k4/ksens/g4_after.py', *sys.argv[1:], flush=True)
    for idx, (sets, vals) in enumerate(load_seeds(path)):
        if idx % 200 == 0: print('progress', idx, dict(C), '%.0f s' % (time.time() - t0), flush=True)
        key = json.dumps((sets, vals))
        if key in seen or not (2 <= len(sets) <= NMAX) or max(map(len, sets)) > 4: continue
        seen.add(key); m = 1 + max(max(s) for s in sets); n = len(sets); O = ocsat.OC(sets, vals, m)
        C['instances'] += 1
        for Y in ocsat.starts(sets, vals, m):
            b = ocsat.bases_of(Y, n)
            if O.holds(b, chain='none', A=1): continue
            C['hard starts'] += 1
            L, _ = kchains.reach(O, b, 10 ** 6)
            # cheap test first, SAT only on states leaving no dangerous frozen agent, stop at the first success
            clean = next((s for s in L if not dangerous_frozen(sets, vals, m, s) and O.holds(s, chain='none', A=1)), None)
            C['... with a repairing state leaving no dangerous frozen agent'] += clean is not None
            if clean is None:
                rep = O.holds(b, chain='need', A=1)
                C['NO CLEAN REPAIR (repaired by one chain: %s)' % rep] += 1
                if C['shown'] < 5:
                    C['shown'] += 1
                    print('NO CLEAN REPAIR', json.dumps((sets, vals)), 'picks', Y, 'OC1 holds', rep, flush=True)
        O.close()
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
