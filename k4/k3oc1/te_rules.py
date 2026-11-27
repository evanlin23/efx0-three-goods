"""Choice rules for T-E (k4/k3_oc1.md §12.1): over the valid Rule E rotations of a hard perfect draft, does the rotation
chosen by a rule complete under LE with owner nobody, e or k?  Rules: some; every; sigma-first k; sigma-last k; every
least-omega'; every most-T'; every longest chain; every k whose chain ends at a terminal t with k in E_t and
{b_k, c_k} not inside J (pair arrow); every k with {b_k, c_k} inside J (chain).  sigma = the order on GAP lines, the
least-index topological order of the need DAG on sources.
    python3 k4/k3oc1/te_rules.py gapfile:FILE... | source:SOURCE [PROFILES SEED [SHARD NSHARDS]]"""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines
from lbtest import upgrade, parts, _owner_test, lb2
from t2k_e import valid_rotations, le_test, topo


def results(rk, m, order, Y):
    out = []
    pos = {a: i for i, a in enumerate(order)}
    for k, p, nb in valid_rotations(rk, m, order, Y):
        bu = upgrade(rk, m, nb); B, J, U, NA, F, T = parts(rk, m, bu)
        ok = bool(le_test(rk, m, nb, k, p[-1])) or bool(_owner_test(rk, m, bu, B, J, U, T, [i == k for i in range(len(rk))], {k}))
        out.append(dict(k=k, pos=pos[k], len=len(p), ok=ok, om=len(J) - len(T), T=len(T),
                        arrow=not {rk[k][1], rk[k][2]} <= set(g for g in range(m) if base_of(Y, m)[g] < 0)))
    return out


def count(R, C, tag):
    if not R: C[tag + 'no valid Rule E rotation'] += 1; return
    C[tag + 'drafts'] += 1
    def ev(name, sel):
        if sel: C[tag + name + ' ' + str(all(r['ok'] for r in sel))] += 1
    C[tag + 'some ' + str(any(r['ok'] for r in R))] += 1
    ev('every', R)
    ev('sigma-first', [min(R, key=lambda r: r['pos'])])
    ev('sigma-last', [max(R, key=lambda r: r['pos'])])
    mo = min(r['om'] for r in R); ev('every least-omega', [r for r in R if r['om'] == mo])
    mT = max(r['T'] for r in R); ev('every most-T', [r for r in R if r['T'] == mT])
    mL = max(r['len'] for r in R); ev('every longest', [r for r in R if r['len'] == mL])
    mS = min(r['len'] for r in R); ev('every shortest', [r for r in R if r['len'] == mS])
    ev('every pair-arrow k', [r for r in R if r['arrow']])
    ev('every junk-pair k', [r for r in R if not r['arrow']])


if __name__ == '__main__':
    C = collections.Counter()
    if sys.argv[1].startswith('source:'):
        import random
        from oc1_fast import drafts
        from oc1_k3 import hypergraphs, profiles
        argv = [sys.argv[1][7:]] + sys.argv[2:]
        src = argv[0]; P, seed = (int(argv[1]), int(argv[2])) if len(argv) > 2 else (0, 0)
        shard, nsh = (int(argv[3]), int(argv[4])) if len(argv) > 4 else (0, 1)
        rng = random.Random(seed)
        print('$ python3 k4/k3oc1/te_rules.py', *sys.argv[1:], flush=True)
        for ci, (sets, m) in enumerate(hypergraphs(src, rng)):
            if ci % nsh != shard: continue
            for rk in profiles(sets, P, rng):
                for Y in drafts(rk, len(sets)):
                    if any(g is None for g in Y) or lb2(rk, m, base_of(Y, m)): continue
                    T = parts(rk, m, upgrade(rk, m, base_of(Y, m)))[5]
                    R = results(rk, m, topo(rk, Y), Y); count(R, C, '|T| %d: ' % len(T))
                    if R and not any(r['ok'] for r in R): print('NOSOME', json.dumps([list(r) for r in rk]), m, 'picks', Y, flush=True)
                    if not R: print('NOROT', json.dumps([list(r) for r in rk]), m, 'picks', Y, flush=True)
    else:
        for a in sys.argv[1:]:
            for line in read_lines(a[8:] if a.startswith('gapfile:') else a):
                mt = re.search(r'GAP (\[\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+)', line)
                if not mt: continue
                rk = [tuple(r) for r in json.loads(mt.group(1))]
                R = results(rk, int(mt.group(2)), ast.literal_eval(mt.group(3)), ast.literal_eval(mt.group(4)))
                count(R, C, '|T| %s: ' % mt.group(5))
    for k in sorted(C): print(k, C[k])
