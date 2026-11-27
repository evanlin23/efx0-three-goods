"""Composite alternating tree (k4/haxell.md §3.3).  ht_tree.py follows AKS literally: a blocker's new edge must be
victim-free on its own, and edges are swapped in one at a time.  In Santa Claus that is enough, because blocking is
resource overlap: a blocker that vacates hurts nobody.  Envy is not monotone in that way.  The trap of §3.2 (C127)
is escaped only by two transfers made *together*, each of which alone creates a victim.  So here a branch of the
tree is swapped in as one composite move.

Tree: layers L_1, L_2, ...; every edge is a move of the catalogue (ht_lib: T, C, D), and the edges of the tree are
pairwise disjoint in the goods they touch (so they commute).  S(T) is the state with every tree edge applied.
  - layer 1: one edge for the root (Model G: a pool good, which the edge allocates; Model A: an unhappy agent, whom
    the edge makes happy);
  - layer i+1: for each victim b of S(T) (an agent unhappy in S(T); in Model A other than agents already unhappy at
    the start), one edge, disjoint from the tree, after which b is happy in S(T + edge), chosen to leave the fewest
    victims (ties: the catalogue order);
  - collapse: when S(T) has no victim (and the root is served), S(T) becomes the new state (one composite move);
  - partial collapse (AKS): before building, if some edge e of the tree is victim-free alone, still serves its
    player alone, and is not the root edge, it is applied alone, and the layers from its own up are discarded
    (COLLAPSE=1, default 0);
  - stuck: no needy player has an edge.
Termination of a tree: the edges are good-disjoint, so at most m edges; the signature recorded is
(-|X_1|, |Y_1|, -|X_2|, |Y_2|, ..., inf), Y_i = the victims after layer i.  An augmentation never makes a happy
agent unhappy: in Model G it allocates the root good, so at most |J| augmentations; in Model A the unhappy set
shrinks.  Nothing here uses agents' values except the EFX0 test itself.

    python3 k4/haxell/ht_ctree.py SRC [MODEL=G] [MOVES=TC] [NMAX=5] [ROOT=first|all] [COLLAPSE=0]"""
import sys, os, json, itertools, collections, time
from ht_lib import (Inst, happy_vec, start_state, apply, chain_moves, transfer_moves, rebase_moves, touched,
                    instances, bundles)

INF = float('inf')


def catalogue(I, st, kinds):
    if 'T' in kinds:
        yield from transfer_moves(I, st)
    if 'C' in kinds:
        yield from chain_moves(I, st)
    if 'D' in kinds:
        yield from rebase_moves(I, st)


def compose(I, st, mvs):
    for mv in mvs:
        st = apply(I, st, mv)
    return st


def root_ok(I, S, root, base_unhappy):
    if root[0] == 'good':
        return S[0][root[1]] >= 0
    return happy_vec(I, S[0])[root[1]]


def victims(I, S, base_unhappy):
    h = happy_vec(I, S[0])
    return frozenset(i for i in range(I.n) if not h[i] and i not in base_unhappy)


def grow(I, st, root, kinds, stats, collapse=False, lmax=None):
    """returns the new state, or None if stuck"""
    h0 = happy_vec(I, st[0])
    base_unhappy = frozenset(i for i in range(I.n) if not h0[i])
    if root[0] == 'agent':
        base_unhappy = base_unhappy - {root[1]}
    layers = []          # each: list of (player, mv, goods)
    sigs = []
    lmax = lmax or (I.m + 2)
    while True:
        mvs = [e[1] for L in layers for e in L]
        S = compose(I, st, mvs)
        V = victims(I, S, base_unhappy)
        ok = root_ok(I, S, root, base_unhappy) if layers else False
        if layers and ok and not V:
            stats['layers at collapse %d' % len(layers)] += 1
            return S
        if collapse and len(layers) >= 2:
            # an edge of layer >= 2 that is victim-free alone and still serves its player alone
            done = False
            for li in range(1, len(layers)):
                for e in layers[li]:
                    S1 = apply(I, st, e[1])
                    if victims(I, S1, base_unhappy) <= set() and happy_vec(I, S1[0])[e[0]]:
                        st = S1; h0 = happy_vec(I, st[0])
                        layers = layers[:li]
                        # the moves of the remaining edges are re-validated by recomputing on the new state
                        stats['partial collapses'] += 1
                        done = True; break
                if done:
                    break
            if done:
                continue
        if len(layers) >= lmax:
            stats['layer limit'] += 1
            return None
        used = set().union(*[e[2] for L in layers for e in L]) if layers else set()
        need = [root] if not ok else [('agent', b) for b in sorted(V)]
        newL = []; Scur = S; mvs_cur = list(mvs)
        for p in need:
            best = None
            for mv in catalogue(I, Scur, kinds):
                g = touched(I, Scur, mv)
                if not g or g & used:
                    continue
                S2 = apply(I, Scur, mv)
                if p[0] == 'good':
                    if S2[0][p[1]] < 0:
                        continue
                else:
                    if not happy_vec(I, S2[0])[p[1]]:
                        continue
                nv = len(victims(I, S2, base_unhappy))
                if best is None or nv < best[0]:
                    best = (nv, mv, g, S2)
                    if nv == 0:
                        break
            if best is not None:
                newL.append((p[1] if p[0] == 'agent' else p, best[1], best[2]))
                used |= best[2]; Scur = best[3]; mvs_cur.append(best[1])
        if not newL:
            stats['stuck tree: layers %d' % len(layers)] += 1
            return None
        layers.append(newL)
        Vn = victims(I, Scur, base_unhappy)
        sigs.append((-len(newL), len(Vn)))
        stats['layers max'] = max(stats['layers max'], len(layers))


def solve(I, st, kinds, stats, model, rootmode, collapse):
    rounds = 0
    while True:
        h = happy_vec(I, st[0])
        if model == 'G':
            roots = [('good', g) for g in range(I.m) if st[0][g] < 0]
        else:
            roots = [('agent', i) for i in range(I.n) if not h[i]]
        if not roots:
            return st, rounds
        if rootmode == 'first':
            roots = roots[:1]
        nxt = None
        for r in roots:
            nxt = grow(I, st, r, kinds, stats, collapse)
            if nxt is not None:
                break
        if nxt is None:
            return None, rounds
        h2 = happy_vec(I, nxt[0])
        if any(a and not b for a, b in zip(h, h2)):
            stats['augmentation with a victim (bug)'] += 1
        st = nxt; rounds += 1
        if rounds > I.m + I.n:
            stats['too many augmentations'] += 1
            return None, rounds


if __name__ == '__main__':
    args = dict(a.split('=') for a in sys.argv[2:] if '=' in a)
    src = sys.argv[1]; kinds = args.get('MOVES', 'TC'); nmax = int(args.get('NMAX', '5'))
    model = args.get('MODEL', 'G'); rootmode = args.get('ROOT', 'all'); collapse = args.get('COLLAPSE', '0') == '1'
    print('$ python3 k4/haxell/ht_ctree.py', *sys.argv[1:], flush=True)
    t0 = time.time(); C = collections.Counter(); shown = 0
    for name, sets, vals, m in instances(src):
        n = len(sets)
        if n > nmax:
            continue
        I = Inst(sets, vals, m, name); C['instances'] += 1; res = {}; bad = None
        for o in itertools.permutations(range(n)):
            st, Y = start_state(I, o, pool=(model == 'G'))
            key = (Y, None if model == 'G' else o[-1])
            if key not in res:
                fin, rounds = solve(I, st, kinds, C, model, rootmode, collapse)
                if fin is not None:
                    assert all(happy_vec(I, fin[0])) and min(fin[0]) >= 0
                res[key] = (fin is not None, rounds)
            C['starts'] += 1
            if res[key][0]:
                C['start: augmentations %d' % res[key][1]] += 1
            else:
                C['start: STUCK'] += 1
                if bad is None:
                    bad = (list(o), list(Y))
        C['instances with a stuck start'] += bad is not None
        if bad is not None and shown < 6:
            shown += 1
            print('STUCK', name, json.dumps((sets, vals)), 'order', bad[0], 'picks', bad[1], flush=True)
    for k in sorted(C, key=str):
        print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
