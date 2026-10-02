#!/usr/bin/env python3
"""How much of Theorem Z′'s maximality ZMOVE needs (workstream proof/k4-zmove-hall; k4/zmove_hall.md §2). EVIDENCE
tooling, k4/zmh_lib.py's model.

For every key κ with def*(κ) > 0 and every state P of κ, `move(P)` says whether some (T3⁺) move with at most one helper
from P reaches a state of deficit <= 0. The states are grouped by how much of Theorem Z′'s potential they carry:
  all      every min-frozen state of κ;
  cfg      the states P_Q of configurations (free bases nonempty unless U_y = ∅, fillers exist);
  po       those with a pool-optimal configuration over them (no free y has a pair S ⊆ Q_y ∪ L worth more than Q_y);
  forest   pool-optimal, and the threats among the free agents of that configuration have no cycle;
  rmax     cfg states maximizing r′ alone;
  zmax     the Z′-maxima (r′, then Λ′).
For each class it counts the keys at which SOME state of the class has a move and those at which EVERY state does.
ZMOVE is "zmax: some"; the strong form found on the data is "zmax: every".

usage: python3 k4/zmh_classes.py [--every=E] [--max=N] [--maxn=N] [--show=K] INPUT ..."""
import collections, json, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zmh_lib import Prof, load_inputs, show, pc, bits

CLASSES = ('all', 'cfg', 'po', 'forest', 'rmax', 'zmax')


def has_move(pr, P, good):
    for Q in good:
        if 'T3+' in pr.move_kind(P, Q)[0]: return True
    return False


def pool_optimal(pr, key, Q, L):
    F, NN, U = pr.key_data(key)
    for y, q in Q.items():
        vq = pr.val(y, q)
        pool = list(bits((q | L) & U[y]))
        for i in range(len(pool)):
            for j in range(i + 1, len(pool)):
                if pr.val(y, (1 << pool[i]) | (1 << pool[j])) > vq: return False
            if pr.val(y, 1 << pool[i]) > vq: return False
    return True


def acyclic(pr, key, Q, L):
    free = [y for y in range(pr.n) if key[y] is None]
    adj = {o: [w for w in free if w != o and pr.threat(w, Q[o] | L, pr.val(w, Q[w]))] for o in free}
    col = {}

    def dfs(u):
        col[u] = 1
        for w in adj[u]:
            if col.get(w) == 1: return False
            if w not in col and not dfs(w): return False
        col[u] = 2
        return True
    return all(dfs(u) for u in free if u not in col)


def main(argv):
    opts = {}; ins = []
    for a in argv:
        if a.startswith('--'):
            kk, _, vv = a[2:].partition('='); opts[kk] = vv
        else: ins.append(a)
    every = int(opts.get('every', 1)); mx = int(opts.get('max', 10 ** 9)); maxn = int(opts.get('maxn', 99))
    showk = int(opts.get('show', 2))
    cnt = collections.Counter(); idx = 0; shown = collections.Counter(); seen = set()
    for path in ins:
        for rec in load_inputs(path):
            idx += 1
            if (idx - 1) % every or len(rec['sets']) > maxn: continue
            sig = json.dumps([rec['sets'], rec['vals']])
            if sig in seen: continue
            seen.add(sig)
            if cnt['profiles'] >= mx: break
            cnt['profiles'] += 1
            pr = Prof(rec['sets'], rec['vals'], rec.get('m'))
            if pr.omega < 1: continue
            good = [Q for Q in pr.states if pr.D[Q] <= 0]
            for key, ds in pr.dstar.items():
                if ds <= 0: continue
                cnt['keys'] += 1
                cls = {c: [] for c in CLASSES}
                cfg = pr.config_states(key)
                pot = {P: pr.potential(P, key) for P in cfg}
                rbest = max((p[0] for p in pot.values()), default=None)
                zbest = max(pot.values(), default=None)
                for P in pr.keys[key]:
                    m = has_move(pr, P, good)
                    cls['all'].append(m)
                    if P not in pot: continue
                    cls['cfg'].append(m)
                    cf = pr.configs_over(P, key)
                    po = [(Q, L) for Q, L in cf if pool_optimal(pr, key, Q, L)]
                    if po:
                        cls['po'].append(m)
                        if any(acyclic(pr, key, Q, L) for Q, L in po): cls['forest'].append(m)
                    if pot[P][0] == rbest: cls['rmax'].append(m)
                    if pot[P] == zbest: cls['zmax'].append(m)
                for c in CLASSES:
                    L_ = cls[c]
                    cnt['%-6s states' % c] += len(L_)
                    cnt['%-6s states without a move' % c] += L_.count(False)
                    if L_ and not any(L_): cnt['%-6s keys: NO state of the class has a move' % c] += 1
                    if L_ and not all(L_): cnt['%-6s keys: some state of the class has none' % c] += 1
                    if not L_: cnt['%-6s keys: class empty' % c] += 1
                if cls['po'] and not all(cls['po']) and shown['po'] < showk:
                    shown['po'] += 1
                    bad = [P for P in pr.keys[key] if P in pot and not has_move(pr, P, good)]
                    print('pool-optimal state without a move:', json.dumps({'sets': pr.sets, 'vals': [[pr.v[i][h] for h in pr.sets[i]] for i in range(pr.n)], 'm': pr.m}),
                          'key', [None if b is None else list(bits(b)) for b in key], 'def*', ds,
                          'states without', [show(P) for P in bad][:4], 'zmax potential', zbest,
                          'their potentials', [pot[P] for P in bad][:4], flush=True)
    for kk in sorted(cnt): print('%-60s %d' % (kk, cnt[kk]))


if __name__ == '__main__':
    main(sys.argv[1:])
