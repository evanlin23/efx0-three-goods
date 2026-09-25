"""Example construction for k4/frontier/tester.py --pipe: the same serial dictatorship as sd.c, in Python.
Reads one instance per line ("n m" then per agent "d g_1..g_d v_1..v_d"), writes one line of m owners.
Run: python3 k4/frontier/tester.py --pipe='python3 k4/frontier/plugins/sd_pipe.py' --n=2 --jobs=1"""
import sys
for line in sys.stdin:
    x = list(map(int, line.split()))
    n, m, p, agents = x[0], x[1], 2, []
    for i in range(n):
        d = x[p]; agents.append((x[p + 1:p + 1 + d], x[p + 1 + d:p + 1 + 2 * d])); p += 1 + 2 * d
    owner, taken = [n - 1] * m, set()
    for i, (goods, vals) in enumerate(agents):
        free = [(v, g) for g, v in zip(goods, vals) if g not in taken]
        if free:
            g = max(free)[1]; taken.add(g); owner[g] = i
    print(' '.join(map(str, owner)), flush=True)
