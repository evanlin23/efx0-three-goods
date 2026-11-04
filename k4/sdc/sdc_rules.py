"""Selection rules over serial-dictatorship outcomes: do all selected outcomes extend to an EFX0 allocation?
Rules: RK = least total pick rank; UW = most unwanted agents; RK+UW lexicographic; VS = largest total pick value."""
import sys, os, json, itertools, collections, random
from sdclib import Enc
from sdc_orders import sd, completable
from sdc_feats import feats
def outcomes(E, r1, maxorders=5040, rng=None):
    res = set()
    it = itertools.permutations(range(E.n)) if E.n <= 7 else (rng.sample(range(E.n), E.n) for _ in range(maxorders))
    for order in it:
        res.add(tuple(sd(E, order, r1)[0]))
    return res
RULES = {'RK': lambda f: (-f['rksum'],), 'UW': lambda f: (f['unwanted'],), 'RKUW': lambda f: (-f['rksum'], f['unwanted']),
         'UWRK': lambda f: (f['unwanted'], -f['rksum']), 'VS': lambda f: (f['valsum'],)}
def check(sets, vals, m, r1, rng=None):
    E = Enc(sets, vals, m); outs = outcomes(E, r1, rng=rng)
    F = {Y: feats(E, list(Y)) for Y in outs}; ext = {}
    def ok(Y):
        if Y not in ext: ext[Y] = completable(E, list(Y))
        return ext[Y]
    res = {}
    for name, key in RULES.items():
        best = max(key(F[Y]) for Y in outs)
        sel = [Y for Y in outs if key(F[Y]) == best]
        res[name] = (all(ok(Y) for Y in sel), any(ok(Y) for Y in sel))
    return res, len(outs)
if __name__ == '__main__':
    src, r1 = sys.argv[1], sys.argv[2] == 'r1'
    C = collections.Counter(); bad = collections.defaultdict(list)
    def run(name, sets, vals, m):
        res, k = check(sets, vals, m, r1)
        C['inst'] += 1
        for r, (a, s) in res.items():
            C[(r, 'all')] += a; C[(r, 'some')] += s
            if not a and len(bad[r]) < 2: bad[r].append((name, sets, vals))
    if src == 'screen':
        import _paths; cwd = os.getcwd(); os.chdir(_paths.DE4)
        from ss_screen import screen_set
        S = screen_set(); os.chdir(cwd)
        for name, I in S:
            if I.n > 7: continue
            run(name, I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)], I.m)
    else:
        for line in open(src):
            if 'inst' not in line: continue
            sets, vals = json.loads(line.split('inst ', 1)[1].rsplit(' time', 1)[0])
            run('climb', sets, vals, 1 + max(max(s) for s in sets))
    for k in sorted(C, key=str): print(k, C[k])
    for r, b in bad.items():
        for x in b: print('BAD', r, json.dumps(x))
