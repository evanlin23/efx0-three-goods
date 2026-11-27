"""Which owners o make Conjecture NO's order work?  Compares candidate rules for o: the agent the plain neediest-first
order processes last anyway (LAST), the agent of least initial need (LEAST), the agent with the most private value
(PRIV), and reports how many o work.

    python3 k4/sdc/no_owner.py screen|suite"""
import sys, collections
import _paths
from sdclib import Enc
from sdc_orders import completable
from sdc_need import score, instances, rule_order
from sdc_need_owner import order_with_last

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); bad = collections.defaultdict(list)
    print('$ python3 k4/sdc/no_owner.py', *sys.argv[1:])
    for name, sets, vals, m in instances(src):
        E = Enc(sets, vals, m)
        work = [o for o in range(E.n) if completable(E, order_with_last(E, 'need2', False, o)[0])]
        C['instances'] += 1; C['owners that work: %d of %d' % (len(work), E.n) if E.n <= 5 else 'owners that work: fraction %.1f' % (len(work) / E.n)] += 1
        last = rule_order(E, 'need2', False)[1][-1]
        allg = set(range(E.m))
        least = min(range(E.n), key=lambda i: (score(E, i, allg, 'need2'), i))
        priv = max(range(E.n), key=lambda i: (sum(E.v[i][g] for g in E.R[i] if all(g not in E.R[j] for j in range(E.n) if j != i)), -i))
        for key, o in (('LAST', last), ('LEAST', least), ('PRIV', priv)):
            C[key + ' works'] += o in work
            if o not in work: bad[key].append(name)
    for k in sorted(C, key=str): print(k, C[k])
    for k, v in bad.items(): print('fails', k, len(v), v[:6])
