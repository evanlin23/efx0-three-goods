"""n = 6 test hypergraphs for the portfolio (compute/k4-portfolio): random n = 5 cores with three or more 4-good agents
(results/k4_certs_5_n4_3, _n4_4, _pure) extended by a sixth agent. EVIDENCE tooling.

The certificate files have n = 6 cores with one 4-good agent only (results/k4_certs_6_n4_1.json.gz), and on those no
profile has a state with f >= 1 (results/k4_portfolio/n6_1.log). Here a sixth agent with 3 or 4 goods is added to a
random n = 5 core: at least one old good, 0, 1 or 2 new goods (each new good is valued by the sixth agent only). The
result is kept when it satisfies the k = 4 core conditions that k4/suite/model.py's core_violations checks on the
hypergraph: every agent has 3 or 4 goods, at most d - 2 private goods, connected, every good valued (strict balanced
types and the private-pair condition come from check4.core_domains when the profiles are drawn). The hypergraphs are
not reduced up to isomorphism.

  python3 k4/portfolio_ext6.py OUT.json.gz N SEED       (N hypergraphs; then: python3 k4/portfolio.py certs OUT.json.gz ...)"""
import gzip, json, os, random, sys
HERE = os.path.dirname(os.path.abspath(__file__))


def is_core(sets, m):
    n = len(sets)
    deg = [sum(g in S for S in sets) for g in range(m)]
    if any(d == 0 for d in deg): return False
    for S in sets:
        if not 3 <= len(S) <= 4: return False
        if sum(deg[g] == 1 for g in S) + 2 > len(S): return False
    seen, st = {0}, [0]
    while st:
        i = st.pop()
        for j in range(n):
            if j not in seen and set(sets[i]) & set(sets[j]): seen.add(j); st.append(j)
    return len(seen) == n


def main():
    out, N, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    base = []
    for f in ('k4_certs_5_n4_3.json.gz', 'k4_certs_5_n4_4.json.gz', 'k4_certs_5_pure.json.gz'):
        base += [(f, c) for c in json.load(gzip.open(os.path.join(HERE, '..', 'results', f), 'rt'))['cores'] if c['m'] <= 11]
    res, seen = [], set()
    while len(res) < N:
        f, c = rng.choice(base)
        m = c['m']; deg = rng.choice([3, 4]); new = rng.choice([0, 1, 1, 2]) if deg == 4 else rng.choice([0, 1])
        S6 = sorted(rng.sample(range(m), deg - new) + list(range(m, m + new)))
        sets = [list(S) for S in c['sets']] + [S6]
        key = json.dumps(sets)
        if key in seen or not is_core(sets, m + new): continue
        seen.add(key)
        res.append({'n': 6, 'm': m + new, 'idx': len(res), 'sets': sets, 'from': f'{f}#{c.get("idx")}+{S6}'})
    json.dump({'cores': res, 'note': 'n = 6 extensions of n = 5 cores, k4/portfolio_ext6.py ' + ' '.join(sys.argv[1:])},
              gzip.open(out, 'wt'))
    print(f'{len(res)} hypergraphs -> {out}')


if __name__ == '__main__':
    main()
