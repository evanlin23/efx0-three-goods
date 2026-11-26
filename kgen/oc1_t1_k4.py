"""Does the t = 0 move matter at k = 4?  k4/sdc/oc_absorb.py's OC1 test (one-absorber completion; chains of
k4/sdc/de_free.py, CHAIN_ONLY, its default caps DF_HMAX = DF_BMAX = 4) on the curated k = 4 sets, with the repairs split
by chain length: for every start whose picks have no one-absorber completion, is there a repairing chain with t >= 1
(at least two agents' bases change), or only t = 0 moves (one agent adds junk to its pick)?

    python3 kgen/oc1_t1_k4.py special|screen|suite|logs"""
import sys, os, itertools, collections, time, json
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
import _paths  # noqa
import de_free as DF
from sdclib import Enc
from oc_absorb import extends_A
from sdc_orders import sd
from sdc_need import instances
from nof_var import SPECIAL

DF.CHAIN_ONLY = True

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 kgen/oc1_t1_k4.py', *sys.argv[1:], flush=True)
    if src == 'special': items = SPECIAL
    elif src == 'logs':      # the hard profiles printed in results/k4_sdc/*.log, as in k4/sdc/oc_absorb.py
        import re, glob
        seen = set(); items = []
        for f in sorted(glob.glob(os.path.join(ROOT, 'results', 'k4_sdc', '*.log'))):
            for line in open(f, errors='ignore'):
                for mt in re.finditer(r'(\[\[\[[0-9, \[\]]+\]\], \[\[[0-9, \[\]]+\]\]\])', line):
                    try: sets, vals = json.loads(mt.group(1))
                    except Exception: continue
                    if not all(len(a) == len(b) for a, b in zip(sets, vals)) or max(len(a) for a in sets) > 4: continue
                    key = json.dumps((sets, vals))
                    if key in seen: continue
                    seen.add(key); items.append(('log%d' % len(items), sets, vals, 1 + max(max(a) for a in sets)))
    else: items = instances(src)
    for name, sets, vals, m in items:
        n = len(sets)
        if n > 5: continue
        E = Enc(sets, vals, m); C['instances'] += 1; done = {}
        for o in itertools.permutations(range(n)):
            Y = tuple(sd(E, list(o))[0])
            if Y not in done:
                base = [-1] * m
                for i, g in enumerate(Y):
                    if g is not None: base[g] = i
                base = tuple(base)
                if extends_A(E, base, 1): done[Y] = 'picks'
                else:
                    r1 = r0 = False
                    for b2 in DF.moves(E, base):
                        ch = sum(1 for i in range(n) if {g for g in range(m) if b2[g] == i} != {g for g in range(m) if base[g] == i})
                        if ch >= 2 and not r1: r1 = extends_A(E, b2, 1)
                        if ch == 1 and not r0: r0 = extends_A(E, b2, 1)
                        if r1 and r0: break
                    done[Y] = 't>=1' if r1 else ('only t=0' if r0 else 'none')
                    if done[Y] != 't>=1':
                        print(done[Y].upper(), name, json.dumps((sets, vals)), 'order', o, 'picks', Y, flush=True)
            C['starts: ' + done[Y]] += 1
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
