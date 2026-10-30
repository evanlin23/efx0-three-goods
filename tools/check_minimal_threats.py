"""Independent raw checks for proofs/minimal_threats.md and the Lean shape example.

Run from the repository root: python tools/check_minimal_threats.py.
No third-party packages; all allocation checks are exhaustive within each named profile.
The random profiles are reproducible samples, not coverage of all profiles.
"""
import itertools
import json
import random


def raw(v, bundles):
    return all(sum(v[i][g] for g in bundles[i]) >=
               sum(v[i][g] for g in bundles[j] if g != h)
               for i in range(len(v)) for j in range(len(v)) if i != j
               for h in bundles[j])


def minimal_threats(row, threshold):
    support = [g for g, x in enumerate(row) if x > 0]
    out = []
    for r in range(1, len(support) + 1):
        for t in itertools.combinations(support, r):
            value = sum(row[g] for g in t)
            if value > threshold and all(value - row[g] <= threshold for g in t):
                out.append(frozenset(t))
    return out


def hypergraph(v, bundles):
    return all(not any(t < bundles[j] for j in range(len(v)) if i != j)
               for i, row in enumerate(v)
               for t in minimal_threats(row, sum(row[g] for g in bundles[i])))


def allocations(n, m):
    for owners in itertools.product(range(n), repeat=m):
        yield [frozenset(g for g, o in enumerate(owners) if o == i) for i in range(n)]


def family(k):
    # Even k: identical supports. Odd k: k-1 common goods and one private good each.
    m = k if k % 2 == 0 else k + 1
    supports = [list(range(k)), list(range(k))] if k % 2 == 0 else [
        list(range(k - 1)) + [k - 1], list(range(k - 1)) + [k]]
    base = 2 ** (k + 2)
    v = [[0] * m for _ in range(2)]
    for i, s in enumerate(supports):
        for p, g in enumerate(s):
            v[i][g] = base + 2 ** p
    return v


def main():
    checked = 0
    for k in range(3, 9):
        v = family(k)
        for row in v:
            s = [x for x in row if x]
            sums = [sum(t) for r in range(len(s) + 1) for t in itertools.combinations(s, r)]
            assert len(sums) == len(set(sums))
        valid = []
        for b in allocations(2, len(v[0])):
            verdict = raw(v, b)
            assert verdict == hypergraph(v, b)
            checked += 1
            if verdict:
                valid.append(b)
        lower = (k + 1) // 2
        assert valid
        assert min(min(map(len, b)) for b in valid) == lower
        d2 = sum(min(map(len, b)) <= 2 for b in valid)
        print(json.dumps(dict(k=k, m=len(v[0]), valuations=v,
                              allocations=2 ** len(v[0]), efx0=len(valid), d2=d2,
                              minimum_smaller_bundle=lower,
                              witness=[sorted(x) for x in valid[0]])))
    v = [[96, 80, 72, 68, 66, 0], [96, 80, 72, 68, 0, 65]]
    valid = []
    for b in allocations(2, 6):
        verdict = raw(v, b)
        assert verdict == hypergraph(v, b)
        checked += 1
        if verdict:
            assert list(map(len, b)) == [3, 3]
            valid.append(b)
    assert valid
    assert raw(v, [frozenset([0, 1, 4]), frozenset([2, 3, 5])])
    print(json.dumps(dict(example="Lean five", allocations=64, efx0=len(valid),
                          all_bundle_sizes=[3, 3], d2=0)))
    rng = random.Random(20261030)
    for _ in range(40):
        v = [[rng.randrange(5) for _ in range(5)] for _ in range(3)]
        for b in allocations(3, 5):
            assert raw(v, b) == hypergraph(v, b)
            checked += 1
    print(f'PASS: raw EFX0 and minimal-threat hypergraphs agree on {checked} allocations')
    extension_checks = 0
    for row in itertools.product(range(4), repeat=3):
        for t in range(7):
            for g in range(3):
                rest = [x for x in range(3) if x != g]
                for mask in range(4):
                    s = frozenset(rest[j] for j in range(2) if mask >> j & 1)
                    added = s | {g}
                    safe = all(sum(row[x] for x in added if x != h) <= t for h in added)
                    condition = sum(row[x] for x in s) <= t and all(
                        row[g] + sum(row[x] for x in s if x != h) <= t for h in s)
                    assert safe == condition
                    extension_checks += 1
    print(f'PASS: exact extension rule on {extension_checks} bundle/threshold checks')


if __name__ == '__main__':
    main()
