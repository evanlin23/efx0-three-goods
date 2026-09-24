"""Reproduces attempts/beta3-restricted-qplans.md: Q-plans (proofs/beta3.md section 3) with a restricted toolbox.
For every connected beta = 3 core with the given n and every order of its Q-agents, decides whether a Q-plan exists
when only some roles are allowed and/or dump targets are forbidden. The search is exact: spares can only sit in the
components with excess -1 before spares (one each), since (P2) forbids them in active components, so trying every
role assignment, every spare choice and every dump target decides existence (the plans found are re-checked with
beta3.check_plan).
Usage (from the repository root): python attempts/beta3_restricted_qplans.py n [n ...]"""
import sys, os, itertools, collections
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'src'))
import beta3
from frontier import PERMS
from cores_nauty import gen_cores_nauty

VARIANTS = {                                   # allowed roles, dump targets allowed
    'a-pins only':               (('a',), False),
    'a-pins, b-pins':            (('a', 'b'), False),
    'a-pins, b-pins, dump':      (('a', 'b'), True),
    'a-pins, 2-holders, dump':   (('a', 'ab', 'ac', 'bc'), True),
    'all roles, no dump':        (('a', 'b', 'ab', 'ac', 'bc'), False),
    'all roles, dump (full)':    (('a', 'b', 'ab', 'ac', 'bc'), True),
}


def exists(core, qrank, roles_allowed, dump):
    for roles in itertools.product(roles_allowed, repeat=len(core.Q)):
        Y = {z: beta3.role_goods(r, qrank[z]) for z, r in zip(core.Q, roles)}
        held = [g for gs in Y.values() for g in gs]
        if len(set(held)) != len(held): continue
        eps = beta3.plan_eps(core, Y, ())
        needy = [k for k, e in enumerate(eps) if e == -1]
        if min(eps, default=0) < -1: continue
        for Z in itertools.product(*[[v for v in core.comps[k] if v not in held] for k in needy]):
            cands = [None]
            if Z and dump and not any(e >= 1 for e in eps):
                cands = [tuple(Y[z]) for z in core.Q if len(Y[z]) == 2] + \
                        [(v,) for v in core.shared if v not in held and v not in Z]
            for T in cands:
                if beta3.check_plan(core, qrank, (Y, tuple(Z), T)) is None: return True
    return False


if __name__ == '__main__':
    for n in map(int, sys.argv[1:]):
        m = 2 * n - 2
        fails, example = collections.defaultdict(collections.Counter), {}
        total = collections.Counter()
        for pi, sets in gen_cores_nauty(n, m):
            core = beta3.Core(n, m, sets); q = len(core.Q)
            for qp in itertools.product(range(6), repeat=q):
                qrank = {z: tuple(sets[z][k] for k in PERMS[p]) for z, p in zip(core.Q, qp)}
                total[q] += 1
                for name, (roles, dump) in VARIANTS.items():
                    if not exists(core, qrank, roles, dump):
                        fails[name][q] += 1
                        example.setdefault(name, (sets, {z: qrank[z] for z in core.Q}))
        print(f"n={n} m={m}: Q-orders by q {dict(sorted(total.items()))}")
        for name in VARIANTS:
            print(f"  {name:26s} fails by q: {dict(sorted(fails[name].items()))}"
                  + (f"  e.g. core {example[name][0]}, Q-orders (a, b, c) {example[name][1]}" if name in example else ""))
        sys.stdout.flush()
