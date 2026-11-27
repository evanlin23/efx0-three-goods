"""Every n-agent instance of DE's core case up to relabelling (each agent values exactly three goods; any number of
private goods; connected or not): agents' sets are sorted triples, goods are numbered by first appearance, and the
sequence of sets is non-decreasing.  This is a superset of the isomorphism classes (some classes repeat), which is
enough for an exhaustive test.
    gen(n) yields (sets, m)"""
import itertools

def gen(n):
    out = []
    def rec(sets, m):
        if len(sets) == n:
            out.append(([list(s) for s in sets], m)); return
        # next set: 3 goods from the m used ones plus up to 3 new ones (numbered m, m+1, ...)
        for k_new in range(0, 4):
            for old in itertools.combinations(range(m), 3 - k_new):
                s = tuple(sorted(old + tuple(range(m, m + k_new))))
                if sets and s < sets[-1]: continue
                rec(sets + [s], m + k_new)
    rec([], 0)
    return out

if __name__ == '__main__':
    import sys
    for n in range(1, int(sys.argv[1]) + 1): print(n, len(gen(n)))
