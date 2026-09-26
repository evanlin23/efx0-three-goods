"""Core sources for the C4min hunt (k4/c4min_hunt.md §3-§4): random connected k = 4 cores, and structured families
of 4-good agents.

Families (every one is checked to be a k = 4 core by k4/check4.py's is_core):
  ht T                H_T of k4/c4.md §7 (branch proof/k4-c4, PR #33): head l = {g_1, z, u, u'}, gadgets j = 1..T
                      of three x_{j,i} = {a_{j,i}, b_{j,i}, c_{j,i}, g_j} and y_j = {a_{j,1}, a_{j,2}, a_{j,3}, e_j},
                      e_j = g_{j+1} (j < T), e_T = z; ht_values(T) gives §7's values (8, 6, 5, 4) and (8, 6, 4, 3).
  chain T H, cycle T, tree T, pure N M
                      the generators of k4/d_stress.py (branch compute/k4-d-stress, PR #42), imported from that file
                      if present, else loaded with `git show origin/compute/k4-d-stress:k4/d_stress.py`.
  ht2 T               H_T with two x's per gadget: y_j = {a_{j,1}, a_{j,2}, p_j, e_j} (p_j private to y_j).
  htx T               H_T whose x's share their lower goods around the gadget: x_{j,i} = {a_{j,i}, b_{j,i},
                      b_{j,i+1 mod 3}, g_j} (no private goods).
  htc T               T gadgets in a cycle without a head: e_j = g_{j+1}, e_T = g_1.
  glue (function)     two cores joined by a shared good ('merge') or a connector agent ('link': 4 goods, two of them
                      private; 'link3': 3 goods, one private).
  lt R C              agent (i, j) = row i's three lower goods + column j's top (R x C agents; lt 2 2 is the m = 8 core
                      of attempts/k4-c4min-w0-owner-base.md)
  ltp R C             lt with one private good per agent instead of a third lower good
  grid R C            gadgets on an R x C grid: gadget (r, c)'s y links to the g of (r, c+1) (or of (r+1, 0) at the end
                      of a row), and one extra 4-good agent per row joins the g's of consecutive rows.
"""
import importlib.util, itertools, os, random, subprocess, sys
import c4min_common as cc

HERE = cc.HERE


def _d_stress():
    p = os.path.join(HERE, 'd_stress.py')
    if not os.path.exists(p):
        src = subprocess.run(['git', '-C', cc.ROOT, 'show', 'origin/compute/k4-d-stress:k4/d_stress.py'],
                             capture_output=True, check=True).stdout
        p = os.path.join(cc.tempfile.gettempdir(), 'd_stress_' + cc.hashlib.sha1(src).hexdigest()[:12] + '.py')
        if not os.path.exists(p):
            with open(p, 'wb') as f: f.write(src)
    spec = importlib.util.spec_from_file_location('d_stress', p)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


class Goods:
    def __init__(self): self.k = 0
    def __call__(self):
        self.k += 1
        return self.k - 1


def ht(t):
    """H_t of k4/c4.md §7 with its agent order (l, then x_{j,1..3}, y_j per gadget); goods numbered in creation
    order: g_1..g_t, z, u, u', then a, b, c per x."""
    G = Goods()
    g = [G() for _ in range(t)]
    z, u, u2 = G(), G(), G()
    sets = [[g[0], z, u, u2]]
    for j in range(t):
        a = []
        for i in range(3):
            aa, bb, c = G(), G(), G()
            a.append(aa)
            sets.append([aa, bb, c, g[j]])
        sets.append(a + [g[j + 1] if j + 1 < t else z])
    return sets


def ht_values(t):
    """§7's values: l (8, 6, 5, 4), every x and y (8, 6, 4, 3), in the order of each good list."""
    return [(8, 6, 5, 4)] + [(8, 6, 4, 3)] * (4 * t)


def ht2(t):
    G = Goods()
    g = [G() for _ in range(t)]
    z, u, u2 = G(), G(), G()
    sets = [[g[0], z, u, u2]]
    for j in range(t):
        a = []
        for i in range(2):
            aa, bb, c = G(), G(), G()
            a.append(aa)
            sets.append([aa, bb, c, g[j]])
        sets.append(a + [G(), g[j + 1] if j + 1 < t else z])
    return sets


def htx(t):
    G = Goods()
    g = [G() for _ in range(t)]
    z, u, u2 = G(), G(), G()
    sets = [[g[0], z, u, u2]]
    for j in range(t):
        a = [G() for _ in range(3)]
        b = [G() for _ in range(3)]
        for i in range(3):
            sets.append([a[i], b[i], b[(i + 1) % 3], g[j]])
        sets.append(a + [g[j + 1] if j + 1 < t else z])
    return sets


def htc(t):
    G = Goods()
    g = [G() for _ in range(t)]
    sets = []
    for j in range(t):
        a = []
        for i in range(3):
            aa, bb, c = G(), G(), G()
            a.append(aa)
            sets.append([aa, bb, c, g[j]])
        sets.append(a + [g[(j + 1) % t]])
    return sets


def grid(r, c):
    G = Goods()
    t = r * c
    g = [G() for _ in range(t)]
    z, u, u2 = G(), G(), G()
    sets = [[g[0], z, u, u2]]
    for j in range(t):
        a = []
        for i in range(3):
            aa, bb, cc_ = G(), G(), G()
            a.append(aa)
            sets.append([aa, bb, cc_, g[j]])
        sets.append(a + [g[j + 1] if j + 1 < t else z])
    for row in range(r - 1):
        sets.append([g[row * c], g[(row + 1) * c], G(), G()])
    return sets


def lt(r, c):
    """R x C grid: row i has three 'lower' goods L_i, column j a top T_j; agent (i, j) = L_i ∪ {T_j}. For R = C = 2 this
    is the pure n = 4, m = 8 core where C4min with the owner's needs from its base fails
    (attempts/k4-c4min-w0-owner-base.md). n = R C, m = 3 R + C."""
    G = Goods()
    L = [[G(), G(), G()] for _ in range(r)]
    T = [G() for _ in range(c)]
    return [L[i] + [T[j]] for i in range(r) for j in range(c)]


def ltp(r, c):
    """lt with one private good per agent: agent (i, j) = {p_ij} ∪ (two lower goods of row i) ∪ {T_j};
    m = R C + 2 R + C, sigma = R C - 2 R - C."""
    G = Goods()
    L = [[G(), G()] for _ in range(r)]
    T = [G() for _ in range(c)]
    return [[G()] + L[i] + [T[j]] for i in range(r) for j in range(c)]


def lt_values(r, c):
    """the type of the w0 instance for every agent: lower goods 2, 3, 4 (in list order), top 8 (a > b + c)"""
    return [(2, 3, 4, 8)] * (r * c)


def family(name, args, rng=None):
    """the good lists of a family member (k4/c4min_hunt.c handles at most 64 goods: H_t up to t = 6)"""
    rng = rng or random.Random(1)
    if name == 'ht': return ht(int(args[0]))
    if name == 'ht2': return ht2(int(args[0]))
    if name == 'htx': return htx(int(args[0]))
    if name == 'htc': return htc(int(args[0]))
    if name == 'grid': return grid(int(args[0]), int(args[1]))
    if name == 'lt': return lt(int(args[0]), int(args[1]))
    if name == 'ltp': return ltp(int(args[0]), int(args[1]))
    ds = _d_stress()
    if name == 'chain': return ds.chain(int(args[0]), int(args[1]) if len(args) > 1 else 1)
    if name == 'cycle': return ds.cycle(int(args[0]))
    if name == 'tree': return ds.tree(int(args[0]))
    if name == 'pure': return ds.pure(int(args[0]), int(args[1]), rng)
    raise ValueError(name)


def glue(A, mA, Bs, mB, rng, mode):
    """Two cores joined: mode 'merge' identifies a random good of A with a random good of B; mode 'link' adds a
    connector agent {a, b, p, q} (a of A, b of B, p and q new private goods); mode 'link3' a 3-good connector
    {a, b, p}. Returns (sets, m) or None if the result is not a k = 4 core."""
    B = [[g + mA for g in S] for S in Bs]
    if mode == 'merge':
        a, b = rng.randrange(mA), rng.randrange(mB) + mA
        B = [[a if g == b else g for g in S] for S in B]
        sets = [list(S) for S in A] + B
    elif mode == 'link':
        sets = [list(S) for S in A] + B + [[rng.randrange(mA), rng.randrange(mB) + mA, mA + mB, mA + mB + 1]]
    else:
        sets = [list(S) for S in A] + B + [[rng.randrange(mA), rng.randrange(mB) + mA, mA + mB]]
    sets, m = normalize(sets)
    return (sets, m) if check_core(sets, m) else None


def normalize(sets):
    """relabel goods 0..m-1 in order of first appearance; returns (sets, m)"""
    lab = {}
    out = []
    for S in sets:
        out.append([lab.setdefault(g, len(lab)) for g in S])
    return out, len(lab)


def random_core(rng, n, m, n4, tries=100000):
    """a random connected k = 4 core with n agents (n4 of them with 4 goods) and m goods (k4/check4.py is_core)."""
    for _ in range(tries):
        sizes = [4] * n4 + [3] * (n - n4)
        sets = [sorted(rng.sample(range(m), d)) for d in sizes]
        if cc.is_core(n, m, sets, False)[0]: return sets
    return None


def check_core(sets, m):
    ok, _ = cc.is_core(len(sets), m, sets, False)
    return ok
