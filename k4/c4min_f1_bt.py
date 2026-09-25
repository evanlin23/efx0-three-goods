#!/usr/bin/env python3
"""c4min_f1_bt: the big-top case of k4/c4min_f1.md (Lemma 8 and Theorem F1*), on the independent Python implementation.
For every (r, Lambda)-maximal configuration c without a valid owner (f = 1, omega >= 1; its frozen agent x is then
big-top by Theorem F1), for every terminal tau and every threat path tau -> ... -> x: the path move c'_tau
(k4/c4min_f1_proof.py) and
  - the potentials of c and c'_tau, t and t',
  - whether tau is big-top, whether c'_tau is completable, whether x is a valid owner of c'_tau with C = {},
  - whether tau is a valid owner of c with the unfreezing clause.
usage: python3 k4/c4min_f1_bt.py FILE [--rand=N] [--seed=S] [--ex=K]"""
import collections, os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from c4min_lib import needs, fmt_profile
from c4min_cfg import configs
from c4min_f1 import f1_profiles, frozen_of, xtype, t_of
from c4min_f1_proof import psi, kind, threat_digraph, path_move


def main():
    files = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict((a[2:].split('=') + [''])[:2] for a in sys.argv[1:] if a.startswith('--'))
    rand = int(opt.get('rand', 0) or 0); seed = int(opt.get('seed', 1) or 1); nex = int(opt.get('ex', 3) or 3)
    for fn in files:
        C = collections.Counter(); ex = collections.defaultdict(list); t0 = time.time()
        for ci, pr, ks in f1_profiles(fn, rand, seed):
            n = pr.n; C['profiles'] += 1
            cfs = [c for NA, phi in ks for c in configs(pr, NA, phi)]
            K = [psi(c) for c in cfs]; mx = max(K)
            Kt = [(k[0], k[1], -t_of(c)) for k, c in zip(K, cfs)]; mxt = max(Kt)
            comp = [bool(c.owners()) for c in cfs]
            if any(comp[a] for a in range(len(cfs)) if K[a] == mx): C['profiles with a completable (r, Lambda)-maximum'] += 1
            else: C['PROFILES WITHOUT A COMPLETABLE (r, Lambda)-MAXIMUM'] += 1
            if any(comp[a] for a in range(len(cfs)) if Kt[a] == mxt): C['profiles with a completable (r, Lambda, -t)-maximum'] += 1
            else: C['PROFILES WITHOUT A COMPLETABLE (r, Lambda, -t)-MAXIMUM'] += 1
            for a, c in enumerate(cfs):
                if K[a] != mx or comp[a]: continue
                x = frozen_of(c)[0]; g = next(iter(c.NA))
                assert xtype(pr, x, g) == 'BT', 'Theorem F1'
                kinds = {y: kind(c, y) for y in c.free}; T = threat_digraph(c)
                term = [z for z in range(n) if z != x and g in needs(pr.vals[z], c.H(z))]
                paths = []
                def walk(u, path):
                    for w in T[u]:
                        if w == x: paths.append(list(path))
                        elif w not in path: path.append(w); walk(w, path); path.pop()
                for tau in term: walk(tau, [tau])
                tag = f'max t={t_of(c)} ({"(r,L,-t)-max" if Kt[a] == mxt else "not (r,L,-t)-max"}), terminals {len(term)} ({sum(xtype(pr, z, g) == "BT" for z in term)} big-top)'
                C[tag] += 1
                for P in paths:
                    tau = P[0]; c2, case = path_move(c, P, x, kinds, 'BT')
                    rel = 'up' if psi(c2) > mx else 'tie' if psi(c2) == mx else 'DOWN'
                    key = (f'  path move [{case}] {rel}: tau big-top {xtype(pr, tau, g) == "BT"}, t\'={t_of(c2)}, '
                           f'c\' completable {bool(c2.owners())}, x owns c\' (C={{}}) {c2.owner_ok(x, unfreeze=False)}, '
                           f'tau owns c (unfreezing) {c.owner_ok(tau)}, T[tau]={"{x}" if T[tau] == [x] else "more"}')
                    C[key] += 1
                    if len(ex[key]) < nex:
                        ex[key].append(f'core {ci} {fmt_profile(pr)} frozen {x} pairs {dict((i, sorted(q)) for i, q in c.Q.items())} pool {sorted(c.L)}; tau {tau}')
        print(f'FILE {fn} rand={rand} seed={seed} ({time.time() - t0:.0f} s)')
        for k in sorted(C): print(f'  {k}: {C[k]}')
        for k in sorted(ex):
            for e in ex[k]: print(f'  example ({k.strip()}): {e}')
        sys.stdout.flush()


if __name__ == '__main__':
    main()
