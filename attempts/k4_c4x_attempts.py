#!/usr/bin/env python3
"""Replay the smallest failing instances of attempts/k4-c4x-*.md with two independent implementations.

For each recorded instance (a strict profile given by explicit integer values) and potential Φ, it checks the claim
("some Φ-maximum is not completable" = the every-form fails; "no Φ-maximum is completable" = the some-form fails)
- with k4/c4x_check.py (plain Python from the definitions: every base map, validity, every completion literally as
  lean/EFX/PreAllocK.lean's Completion with the owner's needs from its bundle, (OC4); every completion found is
  re-checked EFX0 from the raw definition), and
- with k4/c4x.c (the enumerator used for the exhaustive runs), on the same profile.
Prints one line per instance and potential; exits 1 if a claim is not confirmed by both.

usage: python3 attempts/k4_c4x_attempts.py"""
import os, sys, subprocess, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'k4'))
import c4x_check, c4x_run

def lev_vec(sets, vl, B):
    out = []
    for i, S in enumerate(sets):
        bv = sum(vl[i][g] for g in B[i])
        out.append(sum(1 for T in range(1 << len(S)) if sum(vl[i][S[k]] for k in range(len(S)) if T >> k & 1) < bv))
    return out

def py_potential(name, sets, vl, B, feats):
    lv = lev_vec(sets, vl, B)
    if name == 'sumlev': return sum(lv)
    if name == 'sum2lev': return sum(2 ** l for l in lv)
    if name == 'leximax': return tuple(sorted(lv, reverse=True))
    if name == 'leximin': return tuple(sorted(lv))
    if name == 'sumval': return sum(sum(vl[i][g] for g in B[i]) for i in range(len(sets)))
    if name == 'sumlev3,sumlev4': return (sum(l for l, S in zip(lv, sets) if len(S) == 3), sum(l for l, S in zip(lv, sets) if len(S) == 4))
    return feats[name]      # '-frozen', '(-frozen,sumlev)', '(-frozen,leximin)', '(-frozen,slots)', '(-frozen,-rodef)'

C_FEATS = {'sumlev3,sumlev4': '18,19', 'sumlev': '0', 'sum2lev': '1', 'leximax': '2', 'leximin': '3', 'sumval': '4', '-frozen': '6',
           '(-frozen,sumlev)': '6,0', '(-frozen,leximin)': '6,3', '(-frozen,slots)': '6,8', '(-frozen,-rodef)': '6,17'}

FLAGS_C = {'w0': '-w0', 'ef': '-E', 'big': '-3'}

def py_results(sets, vl, flags):
    m = 1 + max(max(S) for S in sets)
    return c4x_check.analyse(sets, m, vl, w0='w0' in flags, ef='ef' in flags, big='big' in flags)

def py_check(sets, vl, pot, flags=()):
    res = py_results(sets, vl, flags)
    vals = [py_potential(pot, sets, vl, B, feats) for (B, comp, feats) in res]
    best = max(vals)
    mx = [r for r, v in zip(res, vals) if v == best]
    return all(r[1] for r in mx), any(r[1] for r in mx), len(res), sum(r[1] for r in res)

def pareto_check(sets, vl):
    """(every Pareto-maximum completable, some Pareto-maximum completable, number of Pareto maxima)"""
    res = py_results(sets, vl, ())
    vs = [tuple(sum(vl[i][g] for g in B[i]) for i in range(len(sets))) for (B, _, _) in res]
    pm = [k for k in range(len(res)) if not any(all(vs[q][i] >= vs[k][i] for i in range(len(sets))) and vs[q] != vs[k] for q in range(len(res)))]
    return all(res[k][1] for k in pm), any(res[k][1] for k in pm), len(pm)

def c_run(sets, vl, opts):
    m = 1 + max(max(S) for S in sets)
    lines = [f'{len(sets)} {m}']
    for i, S in enumerate(sets):
        lines.append(f'{len(S)} ' + ' '.join(map(str, S)) + ' 1')
        lines.append(' '.join(str(vl[i][g]) for g in S))
    lines.append('0 1')
    return subprocess.run([c4x_run.binary()] + opts, input='\n'.join(lines) + '\n', capture_output=True, text=True, check=True).stdout

def c_check(sets, vl, pot, flags=()):
    opts = ['-p', C_FEATS[pot]] + (['-R'] if '17' in C_FEATS[pot] else []) + [FLAGS_C[f] for f in flags]
    w = [l for l in c_run(sets, vl, opts).splitlines() if l.startswith('PHI')][0].split()
    return w[3] == '0', w[5] == '0'

def c_result(sets, vl, opts, key):
    w = [l for l in c_run(sets, vl, opts).splitlines() if l.startswith('RESULT')][0].split()
    return int(w[w.index(key) + 1])

# (attempts file, name, sets, values per agent in the order of its set, claim, ...):
#   claim 'pot', potential, 'every' | 'some' [, flags]: the every-form fails (some maximum is not completable) or the
#     some-form fails (no maximum is completable), in the space given by flags ('w0', 'ef', 'big'; default 𝒫);
#   claim 'nocomp', flags: no pre-allocation of the variant space is completable;
#   claim 'pareto': some Pareto-maximal pre-allocation of 𝒫 is not completable;
#   claim 'paretosome': no Pareto-maximal pre-allocation of 𝒫 is completable.
INSTANCES = [
    ('k4-c4x-frozen-first', 'n = 2, m = 5', [[0, 2, 3, 4], [1, 2, 3, 4]], [(1, 4, 6, 8), (1, 4, 8, 6)], 'pot', '-frozen', 'every'),
    ('k4-c4x-frozen-first', 'n = 2, m = 5', [[0, 2, 3, 4], [1, 2, 3, 4]], [(1, 4, 6, 8), (2, 4, 5, 8)], 'pot', '(-frozen,slots)', 'every'),
    ('k4-c4x-frozen-first', 'n = 3, m = 6', [[0, 2, 4, 5], [1, 3, 5], [3, 4, 5]], [(2, 3, 4, 8), (2, 4, 3), (4, 2, 3)], 'pot', '(-frozen,sumlev)', 'every'),
    ('k4-c4x-frozen-first', 'n = 4, m = 7 (some-form)', [[0, 2, 3, 6], [1, 5, 6], [3, 4, 5, 6], [4, 5, 6]], [(2, 6, 3, 10), (2, 4, 3), (3, 10, 8, 6), (4, 3, 2)], 'pot', '(-frozen,slots)', 'some'),
    ('k4-c4x-frozen-first', 'n = 3, m = 8 (some-form)', [[0, 2, 6, 7], [1, 4, 6, 7], [3, 5, 6, 7]], [(3, 4, 2, 8), (3, 4, 2, 8), (3, 4, 2, 8)], 'pot', '(-frozen,sumlev)', 'some'),
    ('k4-c4x-pareto-potentials', 'n = 3, m = 6, one 4-good agent', [[0, 2, 4, 5], [1, 3, 5], [3, 4, 5]], [(2, 3, 4, 8), (2, 4, 3), (4, 2, 3)], 'pot', 'sumlev', 'every'),
    ('k4-c4x-pareto-potentials', 'n = 3, m = 6, one 4-good agent', [[0, 2, 4, 5], [1, 3, 5], [3, 4, 5]], [(2, 3, 4, 8), (2, 3, 4), (3, 2, 4)], 'pot', 'sum2lev', 'some'),
    ('k4-c4x-pareto-potentials', 'n = 3, m = 6, one 4-good agent', [[0, 2, 4, 5], [1, 3, 5], [3, 4, 5]], [(2, 3, 4, 8), (2, 3, 4), (3, 2, 4)], 'pot', 'leximax', 'some'),
    ('k4-c4x-pareto-potentials', 'n = 3, m = 6, one 4-good agent', [[0, 2, 4, 5], [1, 3, 5], [3, 4, 5]], [(2, 3, 4, 8), (2, 3, 4), (3, 2, 4)], 'pareto'),
    ('k4-c4x-pareto-potentials', 'n = 3, m = 8, two 4-good agents', [[0, 2, 5, 6], [1, 4, 5, 7], [3, 6, 7]], [(2, 3, 8, 4), (3, 4, 8, 2), (3, 2, 4)], 'pot', 'leximin', 'every'),
    ('k4-c4x-pareto-potentials', 'n = 3, m = 8, pure', [[0, 2, 6, 7], [1, 4, 6, 7], [3, 5, 6, 7]], [(3, 4, 2, 8), (3, 4, 2, 8), (3, 4, 2, 8)], 'pot', 'leximin', 'some'),
    ('k4-c4x-pareto-potentials', 'n = 3, m = 8, pure', [[0, 2, 6, 7], [1, 4, 6, 7], [3, 5, 6, 7]], [(3, 4, 2, 8), (3, 4, 2, 8), (3, 4, 2, 8)], 'pot', 'sumlev', 'some'),
    ('k4-c4x-pareto-potentials', 'n = 3, m = 8, pure', [[0, 2, 6, 7], [1, 4, 6, 7], [3, 5, 6, 7]], [(3, 4, 2, 8), (3, 4, 2, 8), (3, 4, 2, 8)], 'paretosome'),
    ('k4-c4x-pareto-potentials', 'n = 3, m = 6, two 4-good agents', [[0, 1, 2, 5], [2, 3, 4, 5], [3, 4, 5]], [(2, 3, 4, 8), (1, 4, 8, 6), (2, 4, 3)], 'pot', 'sumlev3,sumlev4', 'every'),
    ('k4-c4x-variant-spaces', 'n = 2, m = 5, owner needs from base', [[0, 2, 3, 4], [1, 2, 3, 4]], [(2, 3, 4, 8), (2, 3, 4, 8)], 'nocomp', ('w0',)),
    ('k4-c4x-variant-spaces', 'n = 3, m = 6, envy-free two-good bases only', [[0, 3, 4, 5], [1, 3, 4, 5], [2, 3, 4, 5]], [(3, 5, 6, 7), (4, 6, 5, 8), (5, 4, 6, 8)], 'nocomp', ('ef',)),
    ('k4-c4x-variant-spaces', 'n = 3, m = 5, owner bases of 3-4 goods, -frozen', [[0, 1, 2, 4], [1, 3, 4], [2, 3, 4]], [(2, 10, 6, 3), (4, 3, 2), (3, 4, 2)], 'pot', '-frozen', 'some', ('big',)),
]

def main():
    bad = 0
    for inst in INSTANCES:
        att, name, sets, values, claim = inst[:5]
        vl = [dict(zip(S, v)) for S, v in zip(sets, values)]
        if claim == 'pareto':
            ev, so, npm = pareto_check(sets, vl)
            cfail = c_result(sets, vl, ['-Q', '-p', '3'], 'paretofail')
            ok = (not ev) and cfail == 1
            print(f'{att}: {name}: {npm} Pareto maxima; some Pareto maximum not completable: py {not ev}, c {cfail == 1} -> {"confirmed" if ok else "NOT confirmed"}')
        elif claim == 'paretosome':
            ev, so, npm = pareto_check(sets, vl)
            cfail = c_result(sets, vl, ['-Q', '-p', '3'], 'paretosomefail')
            ok = (not so) and cfail == 1
            print(f'{att}: {name}: {npm} Pareto maxima; no Pareto maximum completable: py {not so}, c {cfail == 1} -> {"confirmed" if ok else "NOT confirmed"}')
        elif claim == 'nocomp':
            flags = inst[5]
            res = py_results(sets, vl, flags)
            cn = c_result(sets, vl, ['-a', '-p', '6'] + [FLAGS_C[f] for f in flags], 'nocomp')
            ok = not any(r[1] for r in res) and cn == 1
            print(f'{att}: {name}: space {"+".join(flags)}: {len(res)} valid, {sum(r[1] for r in res)} completable (py); no completable pre-allocation (c): {cn == 1} -> {"confirmed" if ok else "NOT confirmed"}')
        else:
            pot, form = inst[5], inst[6]
            flags = inst[7] if len(inst) > 7 else ()
            ev, so, nv, nc = py_check(sets, vl, pot, flags)
            cev, cso = c_check(sets, vl, pot, flags)
            claim_py = (not ev) if form == 'every' else (not so)
            claim_c = (not cev) if form == 'every' else (not cso)
            ok = claim_py and claim_c
            print(f'{att}: {name}: {pot}{" [" + "+".join(flags) + "]" if flags else ""}: {nv} valid, {nc} completable; every max completable: py {ev} c {cev}; '
                  f'some max completable: py {so} c {cso} -> {form}-form failure {"confirmed" if ok else "NOT confirmed"}')
        bad += not ok
    print('ALL CONFIRMED' if not bad else f'{bad} NOT CONFIRMED')
    sys.exit(1 if bad else 0)

if __name__ == '__main__':
    main()
