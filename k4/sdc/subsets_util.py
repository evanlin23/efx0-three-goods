import itertools


def subsets(xs):
    xs = list(xs)
    for r in range(len(xs) + 1):
        yield from itertools.combinations(xs, r)
