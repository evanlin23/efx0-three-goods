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
    return feats[name]      # '-frozen', '(-frozen,sumlev)', '(-frozen,leximin)', '(-frozen,slots)', '(-frozen,-rodef)'

C_FEATS = {'sumlev': '0', 'sum2lev': '1', 'leximax': '2', 'leximin': '3', 'sumval': '4', '-frozen': '6',
           '(-frozen,sumlev)': '6,0', '(-frozen,leximin)': '6,3', '(-frozen,slots)': '6,8', '(-frozen,-rodef)': '6,17'}

def py_check(sets, vl, pot):
    m = 1 + max(max(S) for S in sets)
    res = c4x_check.analyse(sets, m, vl)
    vals = [py_potential(pot, sets, vl, B, feats) for (B, comp, feats) in res]
    best = max(vals)
    mx = [r for r, v in zip(res, vals) if v == best]
    return all(r[1] for r in mx), any(r[1] for r in mx), len(res), sum(r[1] for r in res)

def pareto_check(sets, vl):
    """(every Pareto-maximum completable, number of Pareto maxima)"""
    m = 1 + max(max(S) for S in sets)
    res = c4x_check.analyse(sets, m, vl)
    vs = [tuple(sum(vl[i][g] for g in B[i]) for i in range(len(sets))) for (B, _, _) in res]
    pm = [k for k in range(len(res)) if not any(all(vs[q][i] >= vs[k][i] for i in range(len(sets))) and vs[q] != vs[k] for q in range(len(res)))]
    return all(res[k][1] for k in pm), len(pm)

def c_check(sets, vl, pot):
    m = 1 + max(max(S) for S in sets)
    lines = [f'{len(sets)} {m}']
    for i, S in enumerate(sets):
        lines.append(f'{len(S)} ' + ' '.join(map(str, S)) + ' 1')
        lines.append(' '.join(str(vl[i][g]) for g in S))
    lines.append('0 1')
    opts = ['-p', C_FEATS[pot]] + (['-R'] if '17' in C_FEATS[pot] else [])
    out = subprocess.run([c4x_run.binary()] + opts, input='\n'.join(lines) + '\n', capture_output=True, text=True, check=True).stdout
    w = [l for l in out.splitlines() if l.startswith('PHI')][0].split()
    return w[3] == '0', w[5] == '0'

# (file, name, sets, values per agent in the order of sets, potential, claim) with claim 'every' (the every-form
# fails: some maximum is not completable) or 'some' (no maximum is completable)
INSTANCES = [
]

def main():
    bad = 0
    for (att, name, sets, values, pot, claim) in INSTANCES:
        vl = [dict(zip(S, v)) for S, v in zip(sets, values)]
        if pot == 'pareto':
            ev, npm = pareto_check(sets, vl)
            ok_py = not ev
            print(f'{att}: {name}: pareto: {npm} Pareto maxima, every completable: {ev} -> claim {"confirmed" if ok_py else "NOT confirmed"} (python)')
            bad += not ok_py
            continue
        ev, so, nv, nc = py_check(sets, vl, pot)
        cev, cso = c_check(sets, vl, pot)
        claim_py = (not ev) if claim == 'every' else (not so)
        claim_c = (not cev) if claim == 'every' else (not cso)
        print(f'{att}: {name}: {pot}: {nv} valid, {nc} completable; every max completable: py {ev} c {cev}; '
              f'some max completable: py {so} c {cso} -> {claim}-form failure {"confirmed" if claim_py and claim_c else "NOT confirmed"}')
        bad += not (claim_py and claim_c)
    print('ALL CONFIRMED' if not bad else f'{bad} NOT CONFIRMED')
    sys.exit(1 if bad else 0)

if __name__ == '__main__':
    main()
