"""Viability of the happy-set model (k4/haxell.md §3.1).  Haxell-type trees (Annamalai; AKS; DRZ) never unmatch a
matched player: every swap they perform is applied only when it is unblocked.  In the happy-set model of ht_lib.py
the analogue is a *victim-free* move: no agent that is happy before the move is unhappy after it.  An alternating
tree can only ever apply victim-free moves, so if no sequence of victim-free moves leads from the start to an EFX0
allocation, no such tree succeeds from that start, whatever its signature.

This script searches (breadth first, capped) the graph of victim-free moves from the serial-dictatorship start of
every order (the absorber is the last agent of the order), for the move catalogue MOVES:
  T  junk transfers;  C  improving chains of k4/sdc.md §29 (released goods to any agent);  D  re-bases.
MODE=strict: victim-free (happy set never shrinks); MODE=count: the number of unhappy agents never rises.
MODEL=A: junk starts with the absorber, goal every agent happy; MODEL=G: junk starts in the pool, every state is a
partial EFX0 allocation (strict mode keeps every agent happy), goal: the pool is empty.

    python3 k4/haxell/ht_bfs.py SRC [MOVES=TC] [MODE=strict] [CAP=20000] [NMAX=4] [MODEL=A|G]
SRC: special | screen | suite | logs | cores:FILES:N:SEED (see ht_lib.instances)."""
import sys, os, json, itertools, collections, time
from ht_lib import Inst, happy_vec, start_state, apply, chain_moves, transfer_moves, rebase_moves, instances


def neighbours(I, st, kinds):
    if 'T' in kinds:
        yield from transfer_moves(I, st)
    if 'C' in kinds:
        yield from chain_moves(I, st)
    if 'D' in kinds:
        yield from rebase_moves(I, st)


def done(I, st, h):
    return all(h) and min(st[0]) >= 0


def bfs(I, st0, kinds, mode, cap):
    h0 = happy_vec(I, st0[0])
    if done(I, st0, h0):
        return 0, 1
    seen = {st0: h0}; frontier = [st0]; d = 0
    while frontier:
        d += 1; nxt = []
        for st in frontier:
            h = seen[st]
            for mv in neighbours(I, st, kinds):
                st2 = apply(I, st, mv)
                if st2 in seen:
                    continue
                h2 = happy_vec(I, st2[0])
                if mode == 'strict':
                    if any(a and not b for a, b in zip(h, h2)):
                        continue
                else:
                    if h2.count(False) > h.count(False):
                        continue
                if done(I, st2, h2):
                    return d, len(seen)
                seen[st2] = h2; nxt.append(st2)
                if len(seen) > cap:
                    return 'cap', len(seen)
        frontier = nxt
    return None, len(seen)


if __name__ == '__main__':
    args = dict(a.split('=') for a in sys.argv[2:] if '=' in a)
    src = sys.argv[1]; kinds = args.get('MOVES', 'TC'); mode = args.get('MODE', 'strict')
    cap = int(args.get('CAP', '20000')); nmax = int(args.get('NMAX', '4'))
    model = args.get('MODEL', 'A')
    print('$ python3 k4/haxell/ht_bfs.py', *sys.argv[1:], flush=True)
    t0 = time.time(); C = collections.Counter(); shown = 0
    for name, sets, vals, m in instances(src):
        n = len(sets)
        if n > nmax:
            continue
        I = Inst(sets, vals, m, name); C['instances'] += 1; res = {}
        for o in itertools.permutations(range(n)):
            st, Y = start_state(I, o, pool=(model == 'G'))
            key = (Y, o[-1])
            if key not in res:
                res[key] = bfs(I, st, kinds, mode, cap)[0]
            r = res[key]
            C['starts'] += 1
            C['start: %s' % ('stuck' if r is None else 'cap' if r == 'cap' else 'depth %d' % r)] += 1
        bad = [k for k, r in res.items() if r is None]
        C['instances with a stuck start'] += bool(bad)
        if bad and shown < 6:
            shown += 1
            print('STUCK', name, json.dumps((sets, vals)), 'picks', bad[0][0], 'absorber', bad[0][1], flush=True)
    for k in sorted(C, key=str):
        print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
