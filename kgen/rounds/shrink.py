"""Shrink one-round failures by deleting goods (kgen/rounds.md §3.5): for every failure in a JSONL file, try every
single-good deletion (and then recursively) and report the smallest m at which some start of the shrunk instance still
needs more than one round.  rnd.c only; any smaller failure found is a claim to confirm with verify_fail.py.
    python3 kgen/rounds/shrink.py results/kgen_rounds/fails.jsonl [CLASS]"""
import sys, os, json
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rndlib
CL = sys.argv[2] if len(sys.argv) > 2 else 'RND1'


def fails(V):
    res, _ = rndlib.analyze(V)
    return [r for r in res if r['counts'][CL] == 0]


best = None; seen = set()
for line in open(sys.argv[1]):
    V = json.loads(line)['vals']
    stack = [V]
    while stack:
        W = stack.pop()
        for g in range(len(W[0])):
            U = [[x for h, x in enumerate(row) if h != g] for row in W]
            k = json.dumps(U)
            if k in seen or len(U[0]) < len(U): continue
            seen.add(k)
            f = fails(U)
            if f:
                stack.append(U)
                if best is None or len(U[0]) < len(best[0][0]):
                    best = (U, f[0]['order']); print('smaller failure: n %d m %d' % (len(U), len(U[0])), json.dumps(U), 'order', f[0]['order'], flush=True)
print('smallest:', best and (len(best[0]), len(best[0][0])))
