"""Plain-Python analysis of level-sum maxima (the M lines of gm4_explore.c / gm4_run.py), from the raw definitions.

Independent of the C code: values, threats, EFX0, levels, sources and placements are recomputed here.
Usage: gm4_analyze.py FILE [--show=K] [--verify=K]
  --show=K    print K readable examples of maxima where some source fails the single dump
  --verify=K  re-check maximality of the first K records by enumerating all junk-free partial allocations
"""
import itertools, json, sys
from collections import Counter

def parse(line):
    body, meta = line.split(' # ')
    parts = body[2:].split(' | ')
    vals = [list(map(int, t.split(','))) for t in parts[0].split()]
    Y = [int(x) for x in parts[1].split()]
    U = int(parts[2])
    m = int(meta.split()[0][2:]); sets = json.loads(meta.split('sets=')[1])
    V = [dict(zip(S, vs)) for S, vs in zip(sets, vals)]
    Yb = [frozenset(g for g in range(m) if y >> g & 1) for y in Y]
    Ub = frozenset(g for g in range(m) if U >> g & 1)
    return m, sets, V, Yb, Ub

class Inst:
    def __init__(self, m, sets, V):
        self.m, self.sets, self.V, self.n = m, sets, V, len(sets)
        self.R = [frozenset(S) for S in sets]
    def val(self, i, S): return sum(self.V[i].get(g, 0) for g in S)
    def thr(self, i, B): return max(self.val(i, B - {g}) for g in B) if B else 0
    def lev(self, i, S):
        x = self.val(i, S); R = sorted(self.R[i])
        return sum(1 for k in range(len(R) + 1) for T in itertools.combinations(R, k) if self.val(i, T) < x)
    def efx0(self, X):
        return all(self.thr(i, X[j]) <= self.val(i, X[i]) for i in range(self.n) for j in range(self.n) if j != i and X[j])
    def sources(self, X):
        return [s for s in range(self.n) if all(self.val(i, X[s]) <= self.val(i, X[i]) for i in range(self.n) if i != s)]
    def envies(self, X):
        return {(i, j) for i in range(self.n) for j in range(self.n) if i != j and self.val(i, X[j]) > self.val(i, X[i])}
    def dump_ok(self, X, U, s):
        if self.R[s] & U: return False
        B = X[s] | U
        return all(self.thr(x, B) <= self.val(x, X[x]) for x in range(self.n) if x != s)
    def min_envied(self, X, B):
        """inclusion-minimal subsets E of B with val_h(E) > sigma_h for some h: list of (E, [h...])"""
        sig = [self.val(i, X[i]) for i in range(self.n)]
        env = []
        Bl = sorted(B)
        for k in range(1, len(Bl) + 1):
            for E in itertools.combinations(Bl, k):
                E = frozenset(E)
                if any(F <= E for F, _ in env): continue
                hs = [h for h in range(self.n) if self.val(h, E) > sig[h]]
                if hs: env.append((E, hs))
        return env
    def junk_free_states(self):
        choices = [[None] + [i for i in range(self.n) if g in self.R[i]] for g in range(self.m)]
        for c in itertools.product(*choices):
            X = [set() for _ in range(self.n)]
            for g, i in enumerate(c):
                if i is not None: X[i].add(g)
            yield [frozenset(x) for x in X]

def fmt(inst, X, U):
    out = []
    for i in range(inst.n):
        vs = ' '.join(f"{g}:{inst.V[i][g]}" for g in inst.sets[i])
        out.append(f"  agent {i} [{vs}] holds {sorted(X[i])} (val {inst.val(i, X[i])}, lev {inst.lev(i, X[i])})")
    out.append(f"  pool {sorted(U)}")
    return '\n'.join(out)

def main():
    f = [a for a in sys.argv[1:] if not a.startswith('--')][0]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[1:] if a.startswith('--'))
    show, verify = int(opt.get('show', 0)), int(opt.get('verify', 0))
    stats = Counter(); shown = 0; nrec = 0
    for line in open(f):
        if not line.startswith('M '): continue
        m, sets, V, Y, U = parse(line); inst = Inst(m, sets, V); nrec += 1
        assert inst.efx0(Y) and all(Y[i] <= inst.R[i] for i in range(inst.n)) and U
        if nrec <= verify:
            best = max(sum(inst.lev(i, X[i]) for i in range(inst.n)) for X in inst.junk_free_states() if inst.efx0(X))
            assert best == sum(inst.lev(i, Y[i]) for i in range(inst.n)), line
            stats['verified_max'] += 1
        src = inst.sources(Y)
        ok = [s for s in src if inst.dump_ok(Y, U, s)]
        stats[f'src={len(src)} dumpok={len(ok)}'] += 1
        if len(ok) < len(src) and shown < show:
            shown += 1
            print(f"--- m={m} sets={sets} sources={src} dump ok at {ok}; envy {sorted(inst.envies(Y))}")
            print(fmt(inst, Y, U))
            for s in src:
                if s in ok: continue
                why = [f"values pool goods {sorted(inst.R[s] & U)}"] if inst.R[s] & U else []
                env = inst.min_envied(Y, Y[s] | U)
                why += [f"{sorted(E)} envied by {hs}" for E, hs in env]
                print(f"  source {s} fails: " + '; '.join(why))
    print('records', nrec, dict(stats))

if __name__ == '__main__':
    main()
