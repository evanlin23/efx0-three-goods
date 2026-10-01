"""Shared code of workstream proof/k4-thetab (k4/thetab.md): the T3-stage states of k4/dl13.md §6 item 2 and the
other-needer swap.

Builds on k4/dl13_stuck.py (Profile: the min-frozen class of a profile with exact deficits, Lemma H1 of k4/hall.md) and
k4/dl13_lemmas.py (Ctx: one state with its best owners, admissible sets, swaps), both from PR #75, and on
k4/suite/model.py. Nothing here changes those files.

Objects (k4/thetab.md §1):
- the *targets*: T1-stuck state records of PR #75's dumps (results/k4_dl13_stuck/stuck_*.jsonl.gz) that are at the T3
  stage (no (T1), (T2) or (T4) move lowers the deficit) and that none of the structural repairs C1, C2, C3 of
  k4/dl13.md §4 certifies; `targets()` yields them with their class: 'S1 theta-b', 'S1 theta-a' or 'noS1';
- setting (H): f = 1, the frozen agent x holds g, the needers of g are exactly two agents y1, y2, both big-top with
  top g;
- the swap sigma(i, A): y_i takes {g}, x takes A ⊆ (J ∪ B_{y_i}) ∩ R_x admissible (N_x(A) ⊆ {g}); P' is min-frozen
  by Lemma 6 of k4/dl2.md;
- `swap_bound`: Lemma G of k4/thetab.md §2, the hitting-set bound for an unmoved owner o of P' (o = y_j, the other
  needer, by default): def(P') <= |C| - cap'(x) - S_rest - kappa for every C ⊆ J' meeting every threat edge inside
  W'_o; computed exactly (least C) over the edges the lemma lists.
"""
import collections, gzip, itertools, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, 'suite'))
import model as M                                   # noqa: E402
from model import bits, pc, mask                    # noqa: E402
from dl2_classify import best_owners, bigtop        # noqa: E402
from dl13_stuck import Profile                      # noqa: E402
from dl13_lemmas import Ctx, tup, regime            # noqa: E402

DUMPS = os.path.join(ROOT, 'results', 'k4_dl13_stuck')
GAP = os.path.join(HERE, 'suite', '.cache', 'gapbench', 'results', 'k4_gap')


# ------------------------------------------------------------------ the targets of k4/dl13.md §6 item 2
def dump_files():
    return sorted(os.path.join(DUMPS, f) for f in os.listdir(DUMPS) if f.startswith('stuck_') and f.endswith('.jsonl.gz'))


def t3_stage(ctx):
    """no (T1) or (T2) move lowers the deficit (def(P) is the least deficit of P's key) and no (T4) move does"""
    return ctx.key_optimal() and ctx.t4_stuck()


def target_class(ctx):
    """None if C1, C2 or C3 of k4/dl13.md certifies the state; otherwise 'S1 theta-b' / 'S1 theta-a' / 'noS1'
    (the S1 shape with every triple theta-failing, of the kinds listed, or no S1 shape)"""
    trip = ctx.s1_triples()
    c1, kinds = ctx.C1()
    if c1: return None
    if ctx.C2(): return None
    if ctx.C3(): return None
    return ('S1 ' + '/'.join(sorted(k for k in kinds))) if trip else 'noS1'


def targets(files=None, fpred=None):
    """yield (record, Profile, Ctx, class) for every target state record of the dumps (records, not distinct states:
    a state found by two runs counts twice, as in k4/dl13.md)"""
    cache = {}
    for fn in files or dump_files():
        for r in (json.loads(l) for l in gzip.open(fn, 'rt')):
            if fpred and not fpred(r): continue
            key = json.dumps([r['sets'], r['vals']])
            if key not in cache:
                cache.clear(); cache[key] = Profile({'sets': r['sets'], 'vals': r['vals'], 'm': r['m']})
            pr = cache[key]; ctx = Ctx(pr, tup(r['Bs']))
            if not t3_stage(ctx): continue
            cls = target_class(ctx)
            if cls is None: continue
            r['file'] = os.path.basename(fn)
            yield r, pr, ctx, cls


# ------------------------------------------------------------------ setting (H) and the swaps
def ntype(I, y):
    return 'BT' if bigtop(I, y) else ('4' if len(I.sets[y]) == 4 else '3')


def setting(ctx):
    """(x, g, needers, third agents) at f = 1, else None"""
    P = ctx.P
    if sum(P.frozen) != 1: return None
    x = P.frozen.index(True)
    nd = ctx.needers(x)
    third = [w for w in P.free if w not in nd]
    return x, ctx.Bs[x], nd, third


def in_H(ctx):
    s = setting(ctx)
    if s is None: return False
    x, g, nd, third = s
    return len(nd) == 2 and all(bigtop(ctx.I, y) for y in nd)


def minimal_edges(I, w, U, hold_val):
    """the minimal subsets Z of U ∩ R_w with v_w(Z) > hold_val (a set Y with a good outside R_w threatens w holding a
    base of value hold_val iff Y ∩ R_w contains one of them)"""
    goods = list(bits(U & I.R[w]))
    out = []
    for k in range(1, len(goods) + 1):
        for Z in itertools.combinations(goods, k):
            Zm = mask(Z)
            if I.val(w, Zm) > hold_val and not any((e & Zm) == e for e in out):
                out.append(Zm)
    return out


def least_hitting(edges, allowed):
    """least |C| with C ⊆ allowed meeting every edge; (None, None) if some edge misses allowed"""
    if not edges: return 0, 0
    if any(not (e & allowed) for e in edges): return None, None
    U = 0
    for e in edges: U |= e
    cand = list(bits(allowed & U))
    for k in range(len(cand) + 1):
        for Cl in itertools.combinations(cand, k):
            C = mask(Cl)
            if all(e & C for e in edges): return k, C
    return None, None


def swap_bound(ctx, z, A, o=None):
    """Lemma G (k4/thetab.md §2) for the swap (z takes {g}, x takes A) and an unmoved free owner o (default: the other
    needer when there are exactly two). Returns a dict with the edges by kind and the bound
    best = min over kappa in {0, 1} of |C| - cap'(x) - S_rest - kappa, or None if the edges cannot be met."""
    I, P, Bs = ctx.I, ctx.P, ctx.Bs
    x, g, nd, third = setting(ctx)
    if o is None:
        o = [w for w in nd if w != z][0]
    Jn = (P.J | Bs[z]) & ~A                             # J'
    U = Bs[o] | Jn                                      # W'_o
    allowed = Jn
    rest = [w for w in P.free if w not in (o, z)]       # free agents other than o and z (x is frozen in P)
    S_rest = sum(2 - pc(Bs[w]) for w in rest)
    capx = 2 - pc(A)
    Lz = I.R[z] & ~g
    e_z = minimal_edges(I, z, U, I.val(z, g))          # z holding g (big-top: the single edge L_z, if inside U)
    e_x = minimal_edges(I, x, U, I.val(x, A))           # x holding A
    e_w = {w: minimal_edges(I, w, U, P.bv[w]) for w in rest}
    edges = e_z + e_x + [e for w in rest for e in e_w[w]]
    h0, C0 = least_hitting(edges, allowed)
    out = dict(o=o, z=z, A=A, U=U, capx=capx, S_rest=S_rest, ez=len(e_z), ex=len(e_x),
               ew={w: len(e) for w, e in e_w.items()}, h0=h0, kappa_h=None)
    bounds = []
    if h0 is not None: bounds.append(h0 - capx - S_rest)
    # kappa = 1 (z counted in u'_o(Y)): v_x(A) > v_x(g), no agent other than o, z needs g in P, and g ∉ N_o(Y): automatic
    # if o does not value g; for a big-top o on g we require L_o ⊆ Y (the removed set C misses L_o, and L_o ⊆ U)
    others_need_g = any(P.N[w] & g for w in range(I.n) if w not in (o, z, x))
    Lo = I.R[o] & ~g
    if I.val(x, A) > I.val(x, g) and not others_need_g:
        hk = None
        if not (g & I.R[o]):
            hk = h0
        elif bigtop(I, o) and not (Lo & ~U):
            hk, Ck = least_hitting(edges, allowed & ~Lo)
        out['kappa_h'] = hk
        if hk is not None: bounds.append(hk - capx - S_rest - 1)
    out['best'] = min(bounds) if bounds else None
    # per-agent quietness of the agents in `rest`: their edges can be met by at most their own slots
    out['quiet'] = all((least_hitting(e_w[w], allowed)[0] is not None and
                        least_hitting(e_w[w], allowed)[0] <= 2 - pc(Bs[w])) for w in rest)
    return out


def swaps(ctx, z):
    """the admissible A for x after z takes g: A ⊆ (J ∪ B_z) ∩ R_x, 1 or 2 goods, N_x(A) ⊆ NA"""
    x = setting(ctx)[0]
    return ctx.admissible(x, ctx.P.J | ctx.Bs[z])


def fmt(Bs):
    return '(' + ', '.join('{' + ','.join(map(str, bits(B))) + '}' for B in Bs) + ')'


def show(r, ctx, out=sys.stdout):
    I = ctx.I; P = ctx.P
    print('src', r.get('src'), 'n=%d m=%d f=%d def=%s omega=%d V=%s' % (I.n, I.m, I.f, ctx.D, ctx.omega, ctx.V), file=out)
    for i in range(I.n):
        gs = sorted(I.sets[i], key=lambda q: -I.v[i][q])
        print('  agent %d: %s%s base %s %s needs %s' % (i, ' '.join('%d:%d' % (q, I.v[i][q]) for q in gs),
              ' BT' if bigtop(I, i) else '', sorted(bits(ctx.Bs[i])), 'FROZEN' if P.frozen[i] else 'free',
              sorted(bits(P.N[i]))), file=out)
    print('  J', sorted(bits(P.J)), 'best owners', ctx.best, file=out)
