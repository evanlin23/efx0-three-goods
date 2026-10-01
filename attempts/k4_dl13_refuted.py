#!/usr/bin/env python3
"""Replays the counterexample(s) to Conjecture DL13 (k4/dl2.md §3, ledger K4.DL2.T13) of attempts/k4-dl13-refuted.md
with three implementations, and prints every min-frozen P' with a smaller deficit and the shape of the move.

  A: k4/dl2_relations.py on k4/suite/model.py (the proof workstream's tool; relation R13 = R_13, RTr = R_T);
  B: main's k4/c4x_check.py (its own enumeration of every base map good -> agent or junk with (V1), (V2), and its own
     removal-only deficit `rodef`) with the membership tests of k4/dl2_relations_xcheck.py (rel_B, written separately
     from A);
  C: k4/dl13.c (compute/k4-dl13; a copy of k4/dl2.c's enumeration and deficit with the R_13 test added), its per-state
     line (-s): the branch flags t1, t3p, t3h.
Each instance must be a connected k = 4 core with strict values (model.py's core_violations, strict, connected) with
fewest frozen agents f >= 1 and omega >= 1, and at the listed P all three must find def(P) > 0 and no R_13 move to a
min-frozen P' with a smaller deficit. Also checked: whether R_T (DL_T's relation: R_13 plus rotations of free agents)
has an improving move at P (A and B), as listed per instance.
usage: python3 attempts/k4_dl13_refuted.py"""
import hashlib, os, subprocess, sys, tempfile
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, 'k4', 'suite'))
sys.path.insert(0, os.path.join(ROOT, 'k4'))
import model as M
import dl2_relations as DR
from dl2_classify import PA, INF
import c4x_check as CX
from dl2_relations_xcheck import rel_B

INSTANCES = [
    # (id, source, sets, vals, m, P, whether R_T (DL_T's relation) has an improving move at P)
    ('dl13-n4m9-rot', "#53's gap_n4_pure_s4000 catalogue: core 123 (m = 9, idx 0) of results/k4_certs_4_pure.json.gz, "
                      'profile 7,196,164,44',
     [[0, 1, 2, 7], [2, 4, 5, 8], [3, 4, 5, 6], [3, 6, 7, 8]], [[2, 3, 6, 10], [7, 4, 8, 2], [6, 5, 3, 7], [3, 2, 8, 4]], 9,
     [[7], [2, 8], [4, 5], [3, 6]], True),
    ('dl13-n4m7-fswap', 'k4/dl13_hunt.py (climb 42 of results/k4_dl13/hunt_n4_3_m8.log): core 58 of '
                        'results/k4_certs_4_n4_3.json.gz (m = 7), profile 34,22,122,3',
     [[0, 2, 5, 6], [1, 4, 5, 6], [3, 4, 5, 6], [4, 5, 6]], [[3, 2, 4, 8], [2, 6, 10, 3], [4, 10, 2, 7], [3, 4, 2]], 7,
     [[5], [4], [3], [6]], False),
]

ok_all = True


def say(name, ok, detail=''):
    global ok_all
    ok_all &= ok
    print('  %-58s %s  %s' % (name, 'confirmed' if ok else 'NOT REPRODUCED', detail), flush=True)


def c_tool():
    src = os.path.join(ROOT, 'k4', 'dl13.c')
    sha = hashlib.sha256(open(src, 'rb').read()).hexdigest()
    b = os.path.join(tempfile.gettempdir(), 'k4_dl13_attempt_' + sha[:16])
    if not os.path.exists(b):
        subprocess.run(['gcc', '-O2', '-o', b + '.tmp', src], check=True); os.replace(b + '.tmp', b)
    return b, sha


def run_c(binary, sets, vals, m):
    inp = [f'{len(sets)} {m} 0'] + [f"{len(S)} {' '.join(map(str, S))}" for S in sets] + [' '.join('1' for _ in sets)]
    inp += [' '.join(map(str, V)) for V in vals] + ['0']
    out = subprocess.run([binary, '-s'], input='\n'.join(inp) + '\n', capture_output=True, text=True, check=True).stdout
    st = {}
    for l in out.splitlines():
        w = l.split()
        if w[0] != 'S': continue
        n = len(sets)
        Bs = tuple(tuple(g for g in range(32) if int(x) >> g & 1) for x in w[2:2 + n])
        x = list(map(int, w[2 + n:2 + n + 6]))
        st[Bs] = {'f': int(w[1]), 'def': x[0], 'k': x[1], 't1': x[3], 't3p': x[4], 't3h': x[5]}
    return st


def main():
    binary, sha = c_tool()
    print(f'# k4/dl13.c sha256 {sha}')
    for iid, src, sets, vals, m, P0, rt in INSTANCES:
        print(f'{iid}: n = {len(sets)}, m = {m}; {src}')
        print(f'  sets {sets}\n  vals {vals}\n  P = {P0}')
        I = M.Inst(sets, vals, m); I.preallocs()
        say('connected k = 4 core, strict values (model.py)', I.core_violations() == [] and I.strict() and I.connected())
        say('f >= 1 and omega >= 1 (model.py)', I.f >= 1 and I.omega >= 1, f'f = {I.f}, omega = {I.omega}')
        key = tuple(tuple(b) for b in P0)
        # A
        recA = {tuple(tuple(b) for b in r['Bs']): r for r in DR.profile({'sets': sets, 'vals': vals, 'm': m})}
        a = recA.get(key)
        say('A: P is min-frozen with def(P) > 0', a is not None, f"def {a['def']}, nearest smaller deficit at distance {a['k']}" if a else '')
        say('A: no R_13 move lowers the deficit (DL13 fails)', a is not None and not a['holds']['R13'])
        if rt: say('A: an R_T move does (DL_T holds)', a is not None and a['holds']['RTr'])
        else: say('A: no R_T move does either (DL_T fails)', a is not None and not a['holds']['RTr'])
        # B
        vl = [dict(zip(S, V)) for S, V in zip(sets, vals)]
        res = CX.analyse(sets, m, vl)
        mf = max(r[2]['-frozen'] for r in res)
        mp = [(tuple(frozenset(B) for B in r[0]), r[2]['rodef']) for r in res if r[2]['-frozen'] == mf]
        P = next((Q for Q, d in mp if tuple(tuple(sorted(B)) for B in Q) == key), None)
        dP = next((d for Q, d in mp if Q == P), None)
        better = [Q for Q, d in mp if dP is not None and d < dP]
        dist = lambda Q: sum(1 for x, y in zip(P, Q) if x != y)
        say('B: P is min-frozen with def(P) > 0', P is not None and dP > 0,
            f'def {dP}, {len(mp)} min-frozen P, {len(better)} with a smaller deficit' if P is not None else '')
        say('B: no R_13 move lowers the deficit (DL13 fails)', P is not None and not any(rel_B('R13', sets, vals, P, Q) for Q in better))
        if rt: say('B: an R_T move does (DL_T holds)', P is not None and any(rel_B('RTr', sets, vals, P, Q) for Q in better))
        else: say('B: no R_T move does either (DL_T fails)', P is not None and not any(rel_B('RTr', sets, vals, P, Q) for Q in better))
        print(f'  B: nearest other min-frozen P\': distance {min(dist(Q) for Q, _ in mp if Q != P)}; nearest with a smaller '
              f'deficit: distance {min(dist(Q) for Q in better)}' if P is not None else '')
        # C
        st = run_c(binary, sets, vals, m)
        c = st.get(key)
        say('C: P is a state (def > 0) with f >= 1', c is not None and c['def'] > 0 and c['f'] >= 1,
            f"def {c['def']}, k {c['k']}" if c else '')
        say('C: t1 = t3p = t3h = 0 (DL13 fails)', c is not None and (c['t1'], c['t3p'], c['t3h']) == (0, 0, 0))
        say('A, B, C agree on every def > 0 state of the profile (def, DL13)',
            set(recA) == set(st) and all(recA[s]['def'] == st[s]['def'] and recA[s]['holds']['R13'] == bool(st[s]['t1'] or st[s]['t3p'] or st[s]['t3h']) for s in st),
            f'{len(st)} states')
        # the improving moves
        Ia = PA(I, tuple(M.mask(b) for b in P0))
        D = {Bs: (INF if I.deficit(Bs) is None else I.deficit(Bs)) for Bs, _ in I.minP}
        print(f'  frozen agents of P: {[i for i in range(len(sets)) if Ia.frozen[i]]}; J = {sorted(M.bits(Ia.J))}; '
              f'needs: {[sorted(M.bits(x)) for x in Ia.N]}')
        print('  every min-frozen P\' with def(P\') < def(P), by distance (A\'s shapes: U unfrozen, Z newly frozen, Y the '
              'free agents that change, with their kind):')
        rows = []
        for Bs, d in D.items():
            if d >= D[tuple(M.mask(b) for b in P0)]: continue
            s = DR.shape(Ia, PA(I, Bs))
            rows.append((s['k'], d, [sorted(M.bits(B)) for B in Bs], s))
        for k, d, bs, s in sorted(rows, key=lambda r: (r[0], r[1], r[2])):
            kind = ('need transfer' if s['nt'] else
                    'rotation of free agents' if s['U'] == 0 and s['Z'] == 0 and s['W'] == 0 else
                    f"role swap with a needer and {len(s['Y'])} helpers" if s['swap'] and s['needer'] else
                    f"frozen goods move: {s['U']} unfreeze, {s['Z']} freeze, {s['W']} frozen agents change their good, "
                    f"{len(s['Y'])} free agents change" + (' (a chain ending at a free agent)' if s['chain'] else ''))
            print(f"    k = {k}  def {d:>2}  {bs}  {kind}; free changed agents {list(s['Y'])}")
    print('ALL CONFIRMED' if ok_all else 'SOMETHING WAS NOT REPRODUCED')


if __name__ == '__main__':
    main()
