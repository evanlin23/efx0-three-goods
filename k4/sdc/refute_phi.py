"""Independent replay (no shared code) of the counterexamples to PHI (k4/sdc.md §20, §21): n = 3, m = 7, agents valuing
2, 6 and 6 goods (strict; general valuations), and a strict k = 4 core with n = 3, m = 7 (agents valuing 3, 4, 4 goods),
which refutes PHI4.  Enumerates every allocation, keeps the EFX0 ones (raw definition),
takes the maximum of Phi = sum of the values of each agent's favourite held good, and checks that a maximizer holds
no serial-dictatorship outcome (for every order, some agent's pick is outside its bundle).

    python3 k4/sdc/refute_phi.py"""
import itertools

CASES = {'general (2, 6, 6 valued goods)': [[0, 0, 55, 57, 0, 0, 0], [50, 1, 0, 58, 76, 75, 70], [0, 11, 58, 68, 41, 26, 21]],
         'k = 4 core (3, 4, 4 valued goods)': [[25, 0, 0, 50, 55, 0, 0], [63, 0, 23, 0, 16, 62, 0], [0, 31, 44, 0, 61, 0, 49]]}
VAL = None
n, m = 3, 7


def is_efx0(X):
    for i in range(n):
        own = sum(VAL[i][g] for g in X[i])
        for j in range(n):
            if j == i: continue
            for h in X[j]:
                if sum(VAL[i][g] for g in X[j] if g != h) > own: return False
    return True


def phi(X):
    return sum(max([VAL[i][g] for g in X[i] if VAL[i][g] > 0], default=0) for i in range(n))


def sd(order):
    left = set(range(m)); Y = {}
    for i in order:
        av = [g for g in left if VAL[i][g] > 0]
        Y[i] = max(av, key=lambda g: VAL[i][g]) if av else None
        if Y[i] is not None: left.discard(Y[i])
    return Y


def run():
    print('strict:', all(len(set(v for v in r if v)) == len([v for v in r if v]) for r in VAL), 'valued goods per agent:', [sum(1 for v in r if v) for r in VAL])
    E = [X for a in itertools.product(range(n), repeat=m) for X in [[[g for g in range(m) if a[g] == i] for i in range(n)]] if is_efx0(X)]
    best = max(phi(X) for X in E); M = [X for X in E if phi(X) == best]
    print('EFX0 allocations:', len(E), 'max Phi:', best, 'maximizers:', M)
    outs = {o: sd(o) for o in itertools.permutations(range(n))}
    for X in M:
        holds = [o for o, Y in outs.items() if all(Y[i] is None or Y[i] in X[i] for i in range(n))]
        print('maximizer', X, 'holds the SD outcome of orders:', holds)
    cons = [X for X in E if any(all(Y[i] is None or Y[i] in X[i] for i in range(n)) for Y in outs.values())]
    print('SD-consistent EFX0 allocations:', len(cons), 'their max Phi:', max(phi(X) for X in cons))


if __name__ == '__main__':
    print('$ python3 k4/sdc/refute_phi.py')
    for name, v in CASES.items():
        VAL = v
        print('==', name)
        run()
