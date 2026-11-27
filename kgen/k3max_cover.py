"""OC1 at maximum-matching starts at k = 3 (k4/k3_oc1.md §10 on branch claude/k4-k3-oc1): which hard perfect
drafts do the proved theorems already cover?  For every hard perfect draft (every agent picks; no one-absorber
completion by lbtest.lb2), classify it:
  - R1-compatible: Theorem R1C covers it (r1compat.r1_compatible);
  - Theorem B* applies (thm_bstar.bstar), and its rotations complete;
  - neither: the gap a proof of OC1^max at k = 3 must close.  Features of these drafts are recorded: |T|, the least
    deficit h(E_t) - (|T| - 1) over terminal owners t, and the shape of a repairing DE trade.
Needs the code of k4/k3oc1/ (branch claude/k4-k3-oc1): set K3OC1 to its directory (default: a worktree of that
branch, see below), run from anywhere.

    K3OC1=/path/to/k4/k3oc1 python3 kgen/k3max_cover.py small:4|certs:5 [SHARD NSHARDS]"""
import sys, os, json, collections, time
K = os.environ.get('K3OC1', os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'k4', 'k3oc1'))
sys.path.insert(0, K)
from k3lib import base_of
from de_moves import de_trades
from lbtest import lb2, parts, exposed, upgrade
from oc1_fast import drafts
from oc1_k3 import hypergraphs, profiles
from oc1_max import nu
from r1compat import r1_compatible
from thm_bstar import bstar, mh

if __name__ == '__main__':
    src = sys.argv[1]; shard, nsh = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (0, 1)
    C = collections.Counter(); t0 = time.time(); shown = 0
    print('$ python3 kgen/k3max_cover.py', *sys.argv[1:], flush=True)
    for ci, (sets, m) in enumerate(hypergraphs(src, None)):
        if ci % nsh != shard: continue
        n = len(sets); v = nu(sets); C['hypergraphs'] += 1
        for rk in profiles(sets, 0, None):
            for Y in drafts(rk, n):
                if sum(1 for g in Y if g is not None) != n: continue
                C['perfect drafts'] += 1
                b = base_of(Y, m)
                if lb2(rk, m, b): continue
                C['perfect, hard'] += 1
                r1 = r1_compatible(rk, Y)
                ub0 = upgrade(rk, m, b); T0 = parts(rk, m, ub0)[5]; C['hard: |T| = %d (after upgrades)' % len(T0)] += 1
                bs, found = bstar(rk, m, Y)
                okb = bool(found) and any(f[3] for f in found)
                C['hard: R1-compatible'] += r1
                C['hard: B* applies (some rotation completes)'] += okb
                C['hard: B* applies but no rotation completes (contradicts B*)'] += bool(found) and not okb
                if r1 or okb:
                    C['hard: |T| = %d, covered' % len(T0)] += 1; continue
                C['hard: covered by neither R1C nor B*'] += 1
                ub = upgrade(rk, m, b); B, J, U, NA, F, T = parts(rk, m, ub)
                pi = lambda x: [g for g in (rk[x][1], rk[x][2]) if g in J]
                defs = [mh([pi(x) for x in exposed(rk, ub, t, B, J, U)]) - (len(T) - 1) for t in T]
                C['  gap: |T| = %d' % len(T)] += 1
                C['  gap: least deficit %s' % (min(defs) if defs else 'none')] += 1
                mv = de_trades(rk, m, b); rep = [d for nb, d in mv if lb2(rk, m, nb)]
                C['  gap: some DE trade repairs %s' % bool(rep)] += 1
                if rep:
                    kinds = collections.Counter(str(d.get('kind', d) if isinstance(d, dict) else d)[:12] for d in rep)
                if shown < 4:
                    shown += 1; print('GAP', json.dumps([list(r) for r in rk]), m, 'picks', Y, '|T| =', len(T), 'deficits', defs, 'repairing trades:', len(rep), flush=True)
    for k in sorted(C): print(C[k], k)
    print('time %.0f s' % (time.time() - t0))
