"""Structure of level-sum maxima and of near-misses (k4/gm4.md §5).  Plain Python from the raw definitions, on the
M lines of gm4_explore.c (-DOUT) or the GAP lines of gm4_climb.c (-DSHOWGAP), via gm4_analyze.py's parser.
Usage: gm4_structure.py rules FILE    selection rules for the dump source, champions of failing sources
       gm4_structure.py gap FILE      smallest level-sum-raising re-division of each GAP state
EVIDENCE only."""
import sys
from collections import Counter
from gm4_analyze import parse, Inst

def reach(E, s):
    R, st = {s}, [s]
    while st:
        a = st.pop()
        for (x, y) in E:
            if x == a and y not in R: R.add(y); st.append(y)
    return R

def rules(f):
    st = Counter()
    for line in open(f):
        if not line.startswith('M '): continue
        m, sets, V, Y, U = parse(line); I = Inst(m, sets, V)
        src = I.sources(Y); E = I.envies(Y)
        if len(src) < 2: continue
        ok = {s: I.dump_ok(Y, U, s) for s in src}
        if all(ok.values()): st['maxima with >= 2 sources, all admit the dump'] += 1; continue
        st['maxima with >= 2 sources, some source fails'] += 1
        RS = {s: reach(E, s) for s in src}
        feats = {
            'fewest goods': lambda s: len(Y[s]),
            'lowest level': lambda s: I.lev(s, Y[s]),
            'most reachable agents': lambda s: -len(RS[s]),
            'most out-edges': lambda s: -sum(1 for (a, b) in E if a == s),
            'fewest other agents valuing its goods': lambda s: sum(1 for x in range(I.n) if x != s and I.R[x] & Y[s]),
        }
        for name, fn in feats.items():
            b = min(fn(s) for s in src); ch = [s for s in src if fn(s) == b]
            st[(name, 'all chosen admit the dump' if all(ok[s] for s in ch) else
                ('some chosen admit it' if any(ok[s] for s in ch) else 'NONE chosen admits it'))] += 1
        for s in src:
            if ok[s]: continue
            champs = {h for Ee, hs in I.min_envied(Y, Y[s] | U) if Ee != (Y[s] | U) for h in hs}
            for h in champs: st['champion (minimal envied set) is ' + ('a source' if h in src else 'a non-source')] += 1
            if I.R[s] & U: continue
            tgt = {t for h in champs for t in src if h in RS[t]}
            st['failing source valuing no pool good: sources reaching its champions are ' +
               ('all working' if all(ok[t] for t in tgt) else 'not all working')] += 1
    for k, v in sorted(st.items(), key=str): print(k, v)

def gap(f):
    st = Counter()
    for line in open(f):
        if not line.startswith('GAP '): continue
        m, sets, V, Y, U = parse('M ' + line[4:]); I = Inst(m, sets, V)
        L = lambda X: [I.lev(i, X[i]) for i in range(I.n)]
        ly = L(Y)
        better = [(X, L(X)) for X in I.junk_free_states() if I.efx0(X) and sum(L(X)) > sum(ly)]
        mins = min(sum(X[i] != Y[i] for i in range(I.n)) for X, l in better)
        st[f'smallest escape changes {mins} agent(s)'] += 1
        st['Pareto improvement exists' if any(all(l[i] >= ly[i] for i in range(I.n)) for X, l in better) else 'no Pareto improvement'] += 1
    for k, v in sorted(st.items(), key=str): print(k, v)

if __name__ == '__main__':
    {'rules': rules, 'gap': gap}[sys.argv[1]](sys.argv[2])
