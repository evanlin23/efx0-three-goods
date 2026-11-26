"""Alternating-tree search in the happy-set model (k4/haxell.md §2-§3), after Annamalai's layers (arXiv 1509.07007
Def. 2.3-2.4) with AKS's collapse-and-discard rule.

Dictionary (Haxell / Annamalai  ->  here):
  matching M, matched player  ->  the current complete allocation, a happy agent (raw EFX0, ht_lib.happy_vec)
  unmatched root a_0          ->  an unhappy agent p_0
  edge of a player            ->  a move of the catalogue (junk transfer T, improving chain C, re-base D) that serves
                                  the player: for p_0, p_0 is happy after it; for a blocker b of a tree edge f, b
                                  would no longer be a victim of f after it
  blocking edges of e         ->  the victims of e: agents happy now and unhappy after e
  immediately addable         ->  an edge without victims
  B-disjointness              ->  an edge is addable only if the goods it touches are disjoint from the goods touched
                                  by the edges already in the tree, and its victims are not tree agents
  layer (X_i, Y_i)            ->  X_i the edges added in round i, Y_i their victims
  signature                   ->  (-|X_1|, |Y_1|, ..., -|X_l|, |Y_l|, inf), compared lexicographically (Annamalai's
                                  eq. (4) without the logarithmic scaling, which only matters for running time)

Loop (for one root): BUILD adds, for each player of the newest Y (the root at the start), the first addable edge
(fewest victims first); if no player of the newest Y has one, players of every layer are tried (Haxell's original
rule); none at all = STUCK.  COLLAPSE: while some tree edge has no victims and still serves its purpose, take the one in
the lowest layer, apply it, discard every layer above it, recompute the victims of the rest, and repeat; the root is
done when its own edge is applied.  The signature is recorded at every iteration and every non-decrease is counted
(the construction does not force it: a collapse may create victims for lower edges; such an event is logged).

The outer loop roots a tree at an unhappy agent until every agent is happy (an EFX0 allocation) or every unhappy
agent's tree is stuck.

Model G (MODEL=G): the junk starts in the pool, every state is a partial EFX0 allocation, and the root of each tree
is a pool good, whose purpose is to be allocated; an augmentation allocates at least one pool good and keeps every
agent happy, so at most |J| augmentations.

    python3 k4/haxell/ht_tree.py SRC [MOVES=TC] [NMAX=4] [ABS=last|all] [ITMAX=400] [MODEL=A|G]"""
import sys, os, json, itertools, collections, time
from ht_lib import (Inst, happy_vec, start_state, apply, chain_moves, transfer_moves, rebase_moves, touched,
                    instances)

INF = float('inf')


def catalogue(I, st, kinds):
    if 'T' in kinds:
        yield from transfer_moves(I, st)
    if 'C' in kinds:
        yield from chain_moves(I, st)
    if 'D' in kinds:
        yield from rebase_moves(I, st)


class Edge:
    __slots__ = ('player', 'mv', 'parent', 'layer', 'victims', 'goods')

    def __init__(self, player, mv, parent, layer, victims, goods):
        self.player = player; self.mv = mv; self.parent = parent; self.layer = layer
        self.victims = victims; self.goods = goods


def victims_of(I, st, h, mv):
    st2 = apply(I, st, mv)
    h2 = happy_vec(I, st2[0])
    return frozenset(i for i in range(I.n) if h[i] and not h2[i]), st2, h2


def serves(I, st, h, e):
    """does e (in state st) still serve its purpose?"""
    st2 = apply(I, st, e.mv)
    h2 = happy_vec(I, st2[0])
    if e.parent is None:
        if isinstance(e.player, tuple):          # Model G: the root is a pool good, which must be allocated
            return st2[0][e.player[1]] >= 0
        return h2[e.player]
    # e.player must not be a victim of the parent edge after e
    st3 = apply(I, st2, e.parent.mv)
    return happy_vec(I, st3[0])[e.player]


def signature(layers):
    s = []
    for X, Y in layers[1:]:
        s += [-len(X), len(Y)]
    return tuple(s) + (INF,)


def grow(I, st, p0, kinds, itmax, stats):
    """one alternating tree rooted at p0; returns the new state or None (stuck)"""
    h = happy_vec(I, st[0])
    layers = [([], {p0})]          # L_0 = (empty, {p0})
    tree_goods = set()
    last_sig = None; it = 0
    while it < itmax:
        it += 1
        # ---- collapse phase: an edge without victims that still serves its purpose is swapped in; as in
        # Annamalai (Lemma 5.1) the whole layer of that edge and every layer above it are discarded, so the
        # first coordinate that changes is |Y| of the layer below, which loses the edge's player.
        while True:
            cand = [e for X, Y in layers for e in X if not e.victims and serves(I, st, h, e)]
            if not cand:
                break
            e = min(cand, key=lambda x: x.layer)
            st = apply(I, st, e.mv); h2 = happy_vec(I, st[0])
            if any(a and not b for a, b in zip(h, h2)):
                stats['collapse with a victim (bug)'] += 1
            h = h2; stats['collapses'] += 1
            if e.parent is None:
                stats['iterations'] += it
                return st
            L = e.layer
            layers = layers[:L]
            before = set().union(*[set(Y) for _, Y in layers])
            tree_goods = set()
            for li in range(1, len(layers)):
                Xl, Yl = layers[li]
                newX = []
                for x in Xl:
                    v, _, _ = victims_of(I, st, h, x.mv)
                    if v - x.victims:
                        stats['collapse created new victims for a lower edge'] += 1
                    x.victims = v; x.goods = touched(I, st, x.mv); tree_goods |= x.goods
                    newX.append(x)
                layers[li] = (newX, set().union(*[x.victims for x in newX]) if newX else set())
        # ---- build phase
        tree_agents = set().union(*[set(Y) for _, Y in layers])
        newest = sorted(layers[-1][1], key=str)
        added = build(I, st, h, layers, newest, tree_agents, tree_goods, kinds) if newest else False
        if not added:
            added = build(I, st, h, layers, sorted(tree_agents, key=str), tree_agents, tree_goods, kinds)
            if added:
                stats['build needed an older player'] += 1
        if not added:
            stats['iterations'] += it
            stats['stuck tree: layers %d' % (len(layers) - 1)] += 1
            return None
        stats['layers max'] = max(stats['layers max'], len(layers) - 1)
        sig = signature(layers)
        if last_sig is not None and not sig < last_sig:
            stats['signature did not decrease'] += 1
        stats['signature checks'] += 1
        last_sig = sig
    stats['itmax hit'] += 1
    return None


def build(I, st, h, layers, players, tree_agents, tree_goods, kinds):
    """add one new layer with, for each player, its first addable edge (fewest victims)"""
    newX = []; newY = set(); used = set(tree_goods)
    parents = {}
    # the edge that each blocker blocks (its purpose): the tree edge whose victim it is
    for li, (X, Y) in enumerate(layers):
        for e in X:
            for b in e.victims:
                parents.setdefault(b, e)
    for p in players:
        parent = parents.get(p)  # None for the root
        best = None
        for mv in catalogue(I, st, kinds):
            g = touched(I, st, mv)
            if not g or g & used:
                continue
            v, st2, h2 = victims_of(I, st, h, mv)
            if v & (tree_agents | newY):
                continue
            e = Edge(p, mv, parent, len(layers), v, g)
            if not serves(I, st, h, e):
                continue
            if best is None or len(v) < len(best.victims):
                best = e
                if not v:
                    break
        if best is not None:
            newX.append(best); newY |= best.victims; used |= best.goods
    if not newX:
        return False
    layers.append((newX, newY))
    tree_goods |= used
    return True


def solve(I, st, kinds, itmax, stats, model='A'):
    rounds = 0
    while True:
        h = happy_vec(I, st[0])
        if model == 'G':
            P = [g for g in range(I.m) if st[0][g] < 0]
            if not P:
                return st, rounds
            done = False
            for g0 in P:
                st2 = grow(I, st, ('good', g0), kinds, itmax, stats)
                if st2 is not None:
                    if not all(happy_vec(I, st2[0])):
                        stats['augmentation left an unhappy agent (bug)'] += 1
                    st = st2; rounds += 1; done = True
                    break
            if not done:
                return None, rounds
            continue
        U = [i for i in range(I.n) if not h[i]]
        if not U:
            return st, rounds
        done = False
        for p0 in U:
            st2 = grow(I, st, p0, kinds, itmax, stats)
            if st2 is not None:
                h2 = happy_vec(I, st2[0])
                if h2.count(False) >= len(U):
                    stats['augmentation did not reduce the unhappy count'] += 1
                st = st2; rounds += 1; done = True
                break
        if not done:
            return None, rounds
        if rounds > 4 * I.n:
            stats['too many augmentations'] += 1
            return None, rounds


if __name__ == '__main__':
    args = dict(a.split('=') for a in sys.argv[2:] if '=' in a)
    src = sys.argv[1]; kinds = args.get('MOVES', 'TC'); nmax = int(args.get('NMAX', '4'))
    absmode = args.get('ABS', 'last'); itmax = int(args.get('ITMAX', '400'))
    model = args.get('MODEL', 'A')
    if model == 'G':
        absmode = 'last'
    print('$ python3 k4/haxell/ht_tree.py', *sys.argv[1:], flush=True)
    t0 = time.time(); C = collections.Counter(); shown = 0
    for name, sets, vals, m in instances(src):
        n = len(sets)
        if n > nmax:
            continue
        I = Inst(sets, vals, m, name); C['instances'] += 1; res = {}
        for o in itertools.permutations(range(n)):
            absorbers = [o[-1]] if absmode == 'last' else list(range(n))
            Y = None; ok = False
            for ab in absorbers:
                st, Y = start_state(I, o, ab, pool=(model == 'G'))
                key = (Y, ab if model == 'A' else None)
                if key not in res:
                    fin, rounds = solve(I, st, kinds, itmax, C, model)
                    if fin is not None and model == 'G':
                        assert min(fin[0]) >= 0
                    if fin is not None:
                        assert all(happy_vec(I, fin[0]))
                    res[key] = (fin is not None, rounds)
                if res[key][0]:
                    ok = True; C['start: augmentations %d' % res[key][1]] += 1
                    break
            C['starts'] += 1
            if not ok:
                C['start: STUCK'] += 1
                if shown < 6:
                    shown += 1
                    print('STUCK', name, json.dumps((sets, vals)), 'order', list(o), 'picks', list(Y), flush=True)
    for k in sorted(C, key=str):
        print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
