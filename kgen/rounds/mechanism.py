"""For every one-round failure in the given JSONL files: does every value-dominating EFX allocation have a starved agent
(kgen/rounds.md §1, Corollary)?  EFX allocations are listed by rnd.c and re-checked here against the raw definition;
starvation is computed here.  Any MD allocation without a starved agent is printed (it fails one round for another
reason of Lemma RC: two passers into one agent, a cycle, or a gain).

    python3 kgen/rounds/mechanism.py results/kgen_rounds/fails.jsonl [more.jsonl ...]
"""
import sys, os, json, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rndlib


def efx(V, X):
    for i in range(len(X)):
        o = sum(V[i][g] for g in X[i])
        for j in range(len(X)):
            if i != j and X[j] and sum(V[i][g] for g in X[j]) - min(V[i][g] for g in X[j]) > o: return False
    return True


def starved(V, X, y):
    J = set(range(len(V[0]))) - set(y); picks = set(y); out = []
    for a in range(len(X)):
        if y[a] in X[a]: continue
        jv = sum(V[a][g] for g in X[a] if g in J)
        best = jv + max([V[a][f] for f in X[a] if f in picks] + [0])
        if best <= V[a][y[a]]: out.append(a)
    return out


C = collections.Counter(); seen = set()
for fn in sys.argv[1:]:
    for line in open(fn):
        x = json.loads(line); V = x['vals']; y = x['picks']
        key = json.dumps([V, y])
        if key in seen: continue
        seen.add(key)
        n, m = len(V), len(V[0])
        L, cnt = rndlib.list_efx(V)
        md = 0; st = 0
        for own in L:
            X = [[g for g in range(m) if own[g] == i] for i in range(n)]
            assert efx(V, X)
            if all(sum(V[i][g] for g in X[i]) >= V[i][y[i]] for i in range(n)):
                md += 1
                if starved(V, X, y): st += 1
                else: print('NOT STARVED', x.get('class', 'RND1'), json.dumps(V), y, X, flush=True)
        C[(x.get('class', 'RND1'), n, m, 'all MD starved' if st == md else 'some MD not starved')] += 1
for k in sorted(C): print(k, C[k])
print('distinct failing starts', len(seen))
