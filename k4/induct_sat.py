"""SAT checks for k4/induct.md (an implementation independent of k4/induct.c and k4/induct_bf.py).

EFX0 is encoded per ordered pair (i, j) of agents from agent i's own relevant goods R_i (so it is exact for any
number of relevant goods, and small when |R_i| <= 4):
  - O = X_i ∩ R_i is fixed by the literals x[g][i] (g in R_i);
  - for every nonempty T ⊆ R_i ∖ O with v_i(T) - min_T v_i > v_i(O): not (T ⊆ X_j);
  - for every nonempty T ⊆ R_i ∖ O with v_i(T) > v_i(O): not (T ⊆ X_j and X_j contains a good outside R_i),
    where out[j][i] <-> OR_{g not in R_i} x[g][j].
Correctness: theta_i(X_j) = v_i(X_j ∩ R_i) - min_{X_j} v_i equals v_i(T) - min_T v_i with T = X_j ∩ R_i when X_j ⊆ R_i,
and v_i(T) otherwise; the clauses above exclude exactly theta_i(X_j) > v_i(X_i) (taking T = X_j ∩ R_i; clauses for
smaller T are implied by monotonicity of theta_i under inclusion, so they exclude nothing more).
"w unenvied": for every j != w, not (X_j ∩ R_j = O and T ⊆ X_w) whenever v_j(T) > v_j(O).
D2 (optional): at most one bundle of more than 2 goods.

Every allocation returned is re-checked by raw_efx0 (the definition, no encoding).

CLI:
  python3 k4/induct_sat.py ht T            PS and private insertion on the chain core H_T of k4/c4.md §7 (own builder)
  python3 k4/induct_sat.py ps 'SETS' 'PROF' [--d2]     PS for every agent of one instance
  python3 k4/induct_sat.py crosscheck N SEED FILE...   PS by SAT vs k4/induct.c's search (task Q) on N random strict
                                                        profiles of the cores in the k = 4 certificate files
"""
import itertools, sys, json
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool


def raw_efx0(V, own, agents):
    B = {a: [] for a in agents}
    for g, a in own.items(): B[a].append(g)
    for i in agents:
        mine = sum(V[i][g] for g in B[i])
        for j in agents:
            if j != i and B[j]:
                if mine < sum(V[i][g] for g in B[j]) - min(V[i][g] for g in B[j]): return False
    return True


def raw_enviers(V, own, w, agents):
    B = {a: [] for a in agents}
    for g, a in own.items(): B[a].append(g)
    return [j for j in agents if j != w and sum(V[j][g] for g in B[w]) > sum(V[j][g] for g in B[j])]


def subsets(S):
    S = list(S)
    for r in range(len(S) + 1):
        for T in itertools.combinations(S, r): yield T


class Model:
    def __init__(self, V, agents, goods, d2=False):
        self.V, self.agents, self.goods = V, list(agents), list(goods)
        vp = self.vp = IDPool()
        x = self.x = {(g, j): vp.id(('x', g, j)) for g in self.goods for j in self.agents}
        cl = self.cl = []
        for g in self.goods:
            lits = [x[g, j] for j in self.agents]
            cl.append(lits)
            for a, b in itertools.combinations(lits, 2): cl.append([-a, -b])
        R = self.R = {i: [g for g in self.goods if V[i][g] > 0] for i in self.agents}
        for i in self.agents:
            outside = [g for g in self.goods if V[i][g] == 0]
            for j in self.agents:
                if j == i: continue
                o = vp.id(('out', j, i))
                cl.append([-o] + [x[g, j] for g in outside])
                for g in outside: cl.append([-x[g, j], o])
                for O in subsets(R[i]):
                    vO = sum(V[i][g] for g in O)
                    pat = [-x[g, i] for g in O] + [x[g, i] for g in R[i] if g not in O]
                    rest = [g for g in R[i] if g not in O]
                    for T in subsets(rest):
                        if not T: continue
                        vT = sum(V[i][g] for g in T)
                        if vT - min(V[i][g] for g in T) > vO:
                            cl.append(pat + [-x[g, j] for g in T])
                        elif vT > vO:
                            cl.append(pat + [-x[g, j] for g in T] + [-o])
        if d2:
            bigs = []
            for j in self.agents:
                b = vp.id(('big', j)); bigs.append(b)
                enc = CardEnc.atmost([x[g, j] for g in self.goods], 2, vpool=vp, encoding=EncType.seqcounter)
                for c in enc.clauses: cl.append(c + [b])
            enc = CardEnc.atmost(bigs, 1, vpool=vp, encoding=EncType.seqcounter)
            cl.extend(enc.clauses)

    def unenvied(self, w):
        V, x, cl = self.V, self.x, []
        for j in self.agents:
            if j == w: continue
            for O in subsets(self.R[j]):
                vO = sum(V[j][g] for g in O)
                pat = [-x[g, j] for g in O] + [x[g, j] for g in self.R[j] if g not in O]
                rest = [g for g in self.R[j] if g not in O]
                for T in subsets(rest):
                    if T and sum(V[j][g] for g in T) > vO:
                        cl.append(pat + [-x[g, w] for g in T])
        return cl

    def solve(self, extra=(), assume=()):
        with Solver(name='cadical153', bootstrap_with=self.cl + list(extra)) as s:
            if not s.solve(assumptions=list(assume)): return None
            mdl = set(l for l in s.get_model() if l > 0)
            return {g: j for g in self.goods for j in self.agents if self.x[g, j] in mdl}


def ps(V, agents, goods, w, d2=False):
    """An EFX0 allocation (owner map) of the instance restricted to agents/goods in which nobody envies w, or None."""
    M = Model(V, agents, goods, d2)
    X = M.solve(M.unenvied(w))
    if X is not None:
        assert raw_efx0(V, X, agents) and not raw_enviers(V, X, w, agents), 'encoding error'
    return X


def exists(V, agents, goods, d2=False):
    X = Model(V, agents, goods, d2).solve()
    if X is not None: assert raw_efx0(V, X, agents), 'encoding error'
    return X


def build_ht(t):
    """H_t of k4/c4.md §7, rebuilt here from its description: l = {g_1, z, u, u'} (8, 6, 5, 4); per gadget j:
    x_{j,i} = {a_{j,i}, b_{j,i}, c_{j,i}, g_j} (8, 6, 4, 3), i = 1..3, and y_j = {a_{j,1}, a_{j,2}, a_{j,3}, e_j}
    (8, 6, 4, 3) with e_j = g_{j+1} (j < t), e_t = z."""
    names = []
    def new(nm): names.append(nm); return len(names) - 1
    g = [new(f'g{j + 1}') for j in range(t)]; z = new('z'); u = new('u'); u2 = new("u'")
    sets = [[g[0], z, u, u2]]; vals = [[8, 6, 5, 4]]; anames = ['l']
    for j in range(t):
        a = [new(f'a{j + 1}{i + 1}') for i in range(3)]; b = [new(f'b{j + 1}{i + 1}') for i in range(3)]
        c = [new(f'c{j + 1}{i + 1}') for i in range(3)]
        for i in range(3):
            sets.append([a[i], b[i], c[i], g[j]]); vals.append([8, 6, 4, 3]); anames.append(f'x{j + 1}{i + 1}')
        sets.append([a[0], a[1], a[2], g[j + 1] if j + 1 < t else z]); vals.append([8, 6, 4, 3]); anames.append(f'y{j + 1}')
    m = len(names)
    V = [[0] * m for _ in sets]
    for i, (S, t_) in enumerate(zip(sets, vals)):
        for gg, xv in zip(S, t_): V[i][gg] = xv
    return sets, V, names, anames


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    d2 = '--d2' in sys.argv
    if args[0] == 'ht':
        t = int(args[1])
        sets, V, names, anames = build_ht(t)
        n, m = len(sets), len(names)
        deg = [sum(g in S for S in sets) for g in range(m)]
        print(f'H_{t}: n = {n}, m = {m}')
        A = list(range(n))
        X = exists(V, A, range(m), d2)
        print('  EFX0 (D2)' if d2 else '  EFX0', 'exists:', X is not None)
        for w in A:
            X = ps(V, A, range(m), w, d2)
            print(f'  PS(H, {anames[w]}):', 'yes' if X else 'NO')
        for w in A:
            for p in sets[w]:
                if deg[p] != 1: continue
                goods = [g for g in range(m) if g != p]
                X = ps(V, A, goods, w, d2)
                ok = None
                if X is not None:
                    X2 = dict(X); X2[p] = w; ok = raw_efx0(V, X2, A)
                print(f'  private insertion {anames[w]} + {names[p]}: PS(H - p, w) =', 'yes' if X else 'NO',
                      '; X\' + (p -> w) EFX0 (raw):', ok)
    elif args[0] == 'crosscheck':
        import gzip, random, subprocess, os
        sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
        from induct_run import domain, build, BIN
        build()
        N, seed, files = int(args[1]), int(args[2]), args[3:]
        rng = random.Random(seed)
        cores = [c for f in files for c in json.load(gzip.open(f))['cores']]
        print('command: python3 k4/induct_sat.py ' + ' '.join(sys.argv[1:]))
        tests = mism = 0
        for _ in range(N):
            c = rng.choice(cores); sets, m = c['sets'], c['m']
            deg = [sum(g in S for S in sets) for g in range(m)]
            prof = [rng.choice(domain(S, deg)) for S in sets]
            V = [[0] * m for _ in sets]
            for i, (S, t_) in enumerate(zip(sets, prof)):
                for gg, xv in zip(S, t_): V[i][gg] = xv
            n = len(sets)
            T = [(w, -1) for w in range(n)] + [(w, p) for w, S in enumerate(sets) if len(S) == 4 for p in S if deg[p] == 1]
            inp = [f'{n} {m}'] + [' '.join(map(str, r)) for r in V] + [str(len(T))] + [f'Q {w} {p}' for w, p in T]
            out = [l for l in subprocess.run([BIN], input='\n'.join(inp) + '\n', capture_output=True, text=True,
                                             check=True).stdout.split('\n') if l.startswith('TASK')]
            for (w, p), line in zip(T, out):
                f = line.split('|')[1].split()
                goods = [g for g in range(m) if g != p]
                for d2, cval in ((False, int(f[1])), (True, int(f[3]))):
                    if d2 and not int(f[1]): continue          # the C search reports D2 only when PS holds
                    sat = ps(V, list(range(n)), goods, w, d2) is not None
                    tests += 1
                    if sat != bool(cval):
                        mism += 1; print('  MISMATCH', sets, prof, w, p, d2, sat, cval)
        print(f'{N} profiles, {tests} PS tests (SAT vs k4/induct.c task Q, with and without D2): {mism} mismatches')
    elif args[0] == 'ps':
        sets = json.loads(args[1]); prof = json.loads(args[2])
        m = 1 + max(g for S in sets for g in S)
        V = [[0] * m for _ in sets]
        for i, (S, t_) in enumerate(zip(sets, prof)):
            for gg, xv in zip(S, t_): V[i][gg] = xv
        for w in range(len(sets)):
            X = ps(V, list(range(len(sets))), range(m), w, d2)
            print('agent', w, 'PS:', 'yes' if X else 'NO', X)


if __name__ == '__main__':
    main()
