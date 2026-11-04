import sys, json
from p1_brute import analyse, efx0
for line in open(sys.argv[1]):
    if not line.startswith('BAD'): continue
    name = line.split()[1]; sets, vals, asg = json.loads(line.split(' ', 2)[2])
    n = len(sets); m = 1 + max(max(s) for s in sets)
    v = [[0] * m for _ in range(n)]
    for i in range(n):
        for g, x in zip(sets[i], vals[i]): v[i][g] = x
    comp, npm, bad, badut, badlm = analyse(n, m, v)
    u = tuple(sum(v[i][g] for g, a in enumerate(asg) if a == i) for i in range(n))
    print(name, 'completeEFX0', comp, '#paretoMax', npm, 'bad', bad, 'u', u, 'utilBad', badut, 'leximinBad', badlm)
