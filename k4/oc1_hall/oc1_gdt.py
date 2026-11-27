"""OC1 with the completion restricted to the GDT shape (k4/oc1_hall.md §2): junk goes only to one owner and, one good
each, to single-good holders that are not frozen (nobody else values their good above its own bundle); frozen agents
and multi-good holders take nothing.  Raw EFX0 check (ohlib.shaped_completion).  For every order:
  0 = picks complete in this shape; 1 = after one improving chain (k4/sdc/de_free.py moves) they do; None = neither.
Owner: 'unfrozen-single' (default) or 'any' (OWNERS=any).  Holders: HOLD=unfrozen-single (default), single, all.

    python3 k4/oc1_hall/oc1_gdt.py special|screen|suite|logs|cores:FILES N SEED
"""
import sys, os, itertools, collections, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, base_of_picks, gdt_shape
from sdclib import Enc
from min_frozen import load
import de_free as DF
DF.CHAIN_ONLY = True
NMAX = int(os.environ.get('NMAX', '5')); OWN = os.environ.get('OWNERS', 'unfrozen-single'); HOLD = os.environ.get('HOLD', 'unfrozen-single')

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/oc1_hall/oc1_gdt.py', *sys.argv[1:], '(OWNERS=%s HOLD=%s)' % (OWN, HOLD), flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > NMAX: continue
        I = Inst(sets, vals, m, name); E = Enc(sets, vals, m); seen = {}; C['instances'] += 1
        for od in itertools.permutations(range(n)):
            Y = picks(I, od)
            if Y not in seen:
                base = base_of_picks(I, Y)
                if gdt_shape(I, base, OWN, hold=HOLD): seen[Y] = 0
                elif any(gdt_shape(I, b2, OWN, hold=HOLD) for b2 in DF.moves(E, base)): seen[Y] = 1
                else:
                    seen[Y] = None
                    if C['shown'] < 8:
                        C['shown'] += 1; print('NOT REPAIRED', name, json.dumps((sets, vals)), 'order', od, 'picks', Y, flush=True)
            C['starts'] += 1; C['start: chains needed %s' % seen[Y]] += 1
        C['distinct starts'] += len(seen); C['distinct starts not repaired'] += sum(1 for d in seen.values() if d is None)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
