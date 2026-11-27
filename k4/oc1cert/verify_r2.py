"""Raw brute-force check of TTC's R2-M / R2* (k4/ttc.md §14.6 on claude/k4-ttc) at given starts, from the definitions,
with no SAT and no code from cegar.py (workstream compute/k4-oc1max-cert).

At a perfect SD start Y (picks y_i, junk J):
- frozen: some other agent prefers y_j to its own pick;
- receivers U: the agents that are not frozen;
- D: frozen agents valuing some junk good;
- hard: no one-absorber EFX0 completion of the picks (Inst.one_absorber).
- A canonical chain is an official chain (x_0, ..., x_t), t >= 1, with:
  - x_0 in D, and x_1 preferring y_{x_0} to y_{x_1};
  - x_t in U;
  - the official rules: H_0 within (J + B_{x_t}) and x_0's relevant goods, worth more than B_{x_0}; each x_i
    (i >= 1) takes B_{x_{i-1}} + H_i with H_i within J and its relevant goods, gaining; the H's disjoint.
- R2-M: the bases after some canonical chain have a complete EFX0 completion with these constraints:
  - nobody receives two or more junk goods;
  - agents other than x_0 holding two or more base goods receive none.
  (Lemma M^c's shape S^c with owner x_0 and max_rest = 1.)
- R2*: the same, with only "nobody receives two or more junk goods".
- R2-O: a one-absorber completion whose owner (the only agent allowed two or more junk goods) is a receiver not on the
  chain; such a receiver must exist.  R2-O generous: or a completion with no owner (nobody takes two junk goods).
  R2-O': the owner, if any, is a receiver other than the chain's end z (on or off the chain).
- R2-C: any one-absorber completion after a canonical chain.
- R2-E: for some SD order sigma giving Y, the earliest-wanter chain E(k) from some k in D, with k taking an improving
  T within (J + {Y_z}), then a one-absorber completion.
For each start: is it perfect, does it have |U| >= 2, is it hard, and do R2-M and R2* hold?

    python3 k4/oc1cert/verify_r2.py STARTS.jsonl     (one {"sets", "vals", "picks"} per line)"""
import sys, os, json, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
from oc1_mc2_rand import Inst


def subsets(xs):
    return itertools.chain.from_iterable(itertools.combinations(xs, r) for r in range(len(xs) + 1))


def canonical_states(I, Y):
    n = I.n; V = I.V; R = I.R
    base = [[y] for y in Y]; J = [g for g in range(I.m) if g not in Y]
    wants = lambda i, j: I.v[i].get(Y[j], 0) > I.v[i][Y[i]]
    frozen = [any(wants(i, j) for i in range(n) if i != j) for j in range(n)]
    D = [j for j in range(n) if frozen[j] and any(g in R[j] for g in J)]
    out = []
    def ext(path, used, Hs):
        xt = path[-1]
        if len(path) >= 2 and not frozen[xt]:
            x0 = path[0]
            for H0 in subsets([g for g in J if g not in used and g in R[x0]] + [g for g in base[xt] if g in R[x0]]):
                if H0 and V(x0, H0) > V(x0, base[x0]):
                    nb = [list(b) for b in base]; nb[x0] = list(H0)
                    for t in range(1, len(path)): nb[path[t]] = base[path[t - 1]] + list(Hs[t])
                    out.append((x0, nb, tuple(path)))
        if len(path) >= n: return
        for y in range(n):
            if y in path: continue
            if len(path) == 1 and not wants(y, path[0]): continue        # x_1 prefers y_{x_0} to its own pick
            for H in subsets([g for g in J if g not in used and g in R[y]]):
                if V(y, base[xt] + list(H)) > V(y, base[y]): ext(path + [y], used | set(H), Hs + [H])
    for x in D: ext([x], frozenset(), [()])
    return out, frozen


def one_absorber_owner(I, nb, owners):
    """a complete EFX0 completion of the bases in which some agent of `owners` may take any number of junk goods and
    every other agent at most one (owners=None: any agent; no owner taking two or more is also allowed)"""
    held = {g for b in nb for g in b}; J = [g for g in range(I.m) if g not in held]
    cands = [None] + (list(range(I.n)) if owners is None else list(owners))
    for a in cands:
        for r in range(0 if a is None else 2, len(J) + 1):
            if a is None and r: break
            for S in itertools.combinations(J, r):
                rest = [g for g in J if g not in S]; others = [i for i in range(I.n) if i != a]
                for recv in itertools.permutations(others, len(rest)):
                    X = [list(b) for b in nb]
                    if a is not None: X[a] += list(S)
                    for g, i in zip(rest, recv): X[i].append(g)
                    if I.efx0(X): return True
    return False


def shaped(I, nb, x0, mode):
    held = {g for b in nb for g in b}; J = [g for g in range(I.m) if g not in held]
    elig = [a for a in range(I.n) if mode == 'star' or a == x0 or len(nb[a]) <= 1]
    if len(J) > len(elig): return False
    for who in itertools.permutations(elig, len(J)):
        X = [list(b) for b in nb]
        for g, a in zip(J, who): X[a].append(g)
        if I.efx0(X): return True
    return False


def r2e(I, Y, variant='e'):
    """R2-E: for some SD order sigma giving Y, some k in D and some T within (J + {Y_z}) and R_k worth more to k than
    Y_k, the state after the earliest-wanter chain E(k) has a one-absorber completion ('e2': |T| = 2; 'eo': the
    owner, if any, is a receiver of Y)."""
    n = I.n; J = [g for g in range(I.m) if g not in Y]
    wants = lambda i, j: I.v[i].get(Y[j], 0) > I.v[i][Y[i]]
    frozen = [any(wants(i, j) for i in range(n) if i != j) for j in range(n)]
    U = [j for j in range(n) if not frozen[j]]
    D = [k for k in range(n) if frozen[k] and any(g in I.R[k] for g in J)]
    for sigma in itertools.permutations(range(n)):
        if I.sd(sigma) != Y: continue
        for k in D:
            path = [k]
            while True:
                ws = [i for i in sigma if i != path[-1] and wants(i, path[-1])]
                if not ws or ws[0] in path: break
                path.append(ws[0])
            if ws or len(path) < 2: continue          # a cycle (ws nonempty at the break): undefined
            z = path[-1]
            pool = [g for g in J if g in I.R[k]] + ([Y[z]] if Y[z] in I.R[k] else [])
            for T in subsets(pool):
                if not T or (variant == 'e2' and len(T) != 2) or I.V(k, T) <= I.v[k][Y[k]]: continue
                nb = [[y] for y in Y]; nb[k] = list(T)
                for l in range(1, len(path)): nb[path[l]] = [Y[path[l - 1]]]
                if variant == 'eo':
                    if one_absorber_owner(I, nb, U): return True
                elif I.one_absorber([list(b) for b in nb]): return True
    return False


if __name__ == '__main__':
    C = collections.Counter()
    for line in open(sys.argv[1]):
        if not line.strip(): continue
        d = json.loads(line); I = Inst(d['sets'], d['vals']); Y = tuple(d['picks'])
        perfect = all(y is not None for y in Y)
        orders = sum(I.sd(o) == Y for o in itertools.permutations(range(I.n)))
        sts, frozen = canonical_states(I, Y) if perfect else ([], [])
        U = [j for j in range(I.n) if perfect and not frozen[j]]
        hard = not I.one_absorber([[y] for y in Y])
        r2m = any(shaped(I, nb, x0, 'm') for x0, nb, p in sts)
        r2s = any(shaped(I, nb, x0, 'star') for x0, nb, p in sts)
        r2o = any([u for u in U if u not in p] and one_absorber_owner(I, nb, [u for u in U if u not in p]) for x0, nb, p in sts)
        r2og = any(one_absorber_owner(I, nb, [u for u in U if u not in p]) for x0, nb, p in sts)
        r2op = any(one_absorber_owner(I, nb, [u for u in U if u != p[-1]]) for x0, nb, p in sts)
        r2c = any(I.one_absorber([list(b) for b in nb]) for x0, nb, p in sts)
        r2e_ = r2e(I, Y, 'e') if perfect else False
        res = {'perfect': perfect, 'orders giving the picks': orders, 'receivers': U, 'hard': hard,
               'canonical chain states': len(sts), 'R2-M repairs': r2m, 'R2* repairs': r2s, 'R2-O repairs': r2o, 'R2-O generous repairs': r2og, "R2-O' repairs": r2op,
               'R2-C repairs': r2c, 'R2-E repairs': r2e_, 'OC1 (Inst.check)': I.check(Y)}
        verdict = 'R2-M FAILS' if (perfect and orders and len(U) >= 2 and hard and not r2m) else 'R2-M ok or n/a'
        C[verdict] += 1
        for nm, ok in (('R2*', r2s), ('R2-O', r2o), ('R2-O generous', r2og), ("R2-O'", r2op), ('R2-C', r2c), ('R2-E', r2e_)):
            C['%s %s' % (nm, 'FAILS' if (perfect and orders and len(U) >= 2 and hard and not ok) else 'ok or n/a')] += 1
        print(verdict, json.dumps({**{k: d[k] for k in ('sets', 'vals', 'picks')}, **res}), flush=True)
    print(dict(C))
