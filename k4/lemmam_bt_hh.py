"""The two instances of k4/lemmam_bt.md: H_t + q (a single big-top agent first needs two rotations, §2) and HH_t (two
copies of H_t: no first agent works with at most one rotation, so Lemma M and rule F with one rotation are false, §3).

Instances (H_t is k4/c4.md §7, built by k4/adaptive_H.py as in k4/rulef_H.py):
  Hq<T>  H_t plus a big-top agent q = {p, b_11, c_11, u} with values (8, 4, 3, 2), p a new good; q has the last index
  HH<T>  two copies A, B of H_t; l_B's good u is l_A's u; agents l_A, l_B, A's gadgets, B's gadgets (in H_t's order)

Usage:
  python3 k4/lemmam_bt_hh.py core NAME                   connected k = 4 core, strict profile, big-top agents
  python3 k4/lemmam_bt_hh.py classes NAME [A,B,..]       Lemma K classes of every first agent (k4/lemmam_bt.py):
                                                         least deficit at the Phase 1 + upgrade state (K0) and after
                                                         every single RotStep (K1), each policy; C40's hypothesis
  python3 k4/lemmam_bt_hh.py rk NAME                     the same classes by k4/rulef.c (-A41 -E1 -Y1 -N1, single
                                                         profile; LB4r itself is skipped: its owner search enumerates
                                                         subsets of the junk, out of reach at m = 65). Needs the
                                                         source of k4/rulef.c (PR #72): k4/rulef.c or $RULEF_SRC
  python3 k4/lemmam_bt_hh.py exact NAME A|B [A,B,..]     LB4r(tau_a) with at most one rotation, exactly: every policy,
                                                         every state one RotStep away, every owner and no owner, Lean's
                                                         Output with the owner's needs from its bundle; encoding A
                                                         (k4/c4_verify_H/lb4r.py) or B (k4/c4_verify_H/enc_b.py)
  python3 k4/lemmam_bt_hh.py d2 NAME                     K4.D on the instance: a two-step insertion sequence whose
                                                         state has an Output (encoding A), checked by the raw EFX0
                                                         definition
"""
import json, os, subprocess, sys, tempfile, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import adaptive_H as AH
import adaptive_run as AR
import check4
import lemmam_bt as L
import lb4r as M
from enc_b import output_b


def build_hq(t):
    sets, vals, m = AH.build(t)
    u, b11, c11 = t + 1, t + 3 + 3, t + 3 + 6       # adaptive_H.build: g_1..g_t, z, u, u', then a, b, c per gadget
    return sets + [[m, b11, c11, u]], vals + [[8, 4, 3, 2]], m + 1


def build_hh(t):
    S, V, m = AH.build(t)
    u = t + 1
    SA = [list(s) for s in S]
    SB = [[g + m for g in s] for s in S]
    SB[0] = [u if g == u + m else g for g in SB[0]]
    sets = [SA[0], SB[0]] + SA[1:] + SB[1:]
    vals = [V[0], V[0]] + V[1:] + V[1:]
    used = sorted(set(g for s in sets for g in s))
    ren = {g: i for i, g in enumerate(used)}
    return [[ren[g] for g in s] for s in sets], vals, len(used)


def build(name):
    t = int(name[2:])
    return build_hq(t) if name.startswith('Hq') else build_hh(t)


def core(name):
    sets, vals, m = build(name)
    ok, _ = check4.is_core(len(sets), m, sets, False)
    doms = check4.core_domains(sets, m, False)        # strict balanced types (with the two-private-goods condition)
    strict = all(any(all(dv[g] == x for g, x in zip(S, V)) for dv in dom) for S, V, dom in zip(sets, vals, doms))
    inst = L.make_inst(sets, vals)
    print(f'{name}: n = {len(sets)}, m = {m}, connected k = 4 core: {ok}, every type a strict balanced core type: '
          f'{strict}, big-top agents: {L.bigtops(inst)}')
    print(json.dumps({'sets': sets, 'vals': vals}))


def c40(inst, a):
    """Corollary C4^0's hypothesis fails when, after envy-free upgrades, omega >= 1 and some 4-good agent is exposed
    w.r.t. r (or r is frozen); returns (omega, exposed 4-good agents)."""
    s, run, _ = L.run_state(inst, a, 'envyFree')
    A = L.analyse_r(inst, s, run)
    return M.omega(inst, s), [x for x in A['E'] if len(inst.R[x]) == 4], A['frozen_r']


def classes(name, agents=None):
    sets, vals, m = build(name)
    inst = L.make_inst(sets, vals)
    print(f'# classes {name}: n = {inst.n}, m = {inst.m} (k4/lemmam_bt.py, Lemma K with Remark 4)', flush=True)
    bad = 0
    for a in (agents if agents is not None else range(inst.n)):
        t0 = time.time()
        res, inK = [], False
        for pol in L.POLS:
            s, run, _ = L.run_state(inst, a, pol)
            d0 = L.kdef_best(inst, s)
            d1, nrot = L.INF, 0
            if d0 > 0:
                for s2 in M.rot_steps(inst, s):
                    nrot += 1
                    d1 = min(d1, L.kdef_best(inst, s2))
                    if d1 <= 0:
                        break
            inK |= d0 <= 0 or d1 <= 0
            res.append(f'{pol}: K0 deficit {d0}, {nrot} RotSteps, least deficit after one {d1}')
        om, e4, rfz = c40(inst, a)
        isc40 = om <= 0 or (not e4 and not rfz)
        bad += not inK and not isc40
        print(f'first {a}: ' + ' | '.join(res) + f' | C40: omega {om}, exposed 4-good {len(e4)}, r frozen {rfz}'
              f' -> {"in K0/K1/C40" if inK or isc40 else "in no class"} ({time.time() - t0:.0f}s)', flush=True)
    print(f'RESULT classes {name}: first agents in no class (K0, K1, RK3 policies; C40): {bad}')


def rk(name):
    src = os.environ.get('RULEF_SRC') or os.path.join(HERE, 'rulef.c')
    code = open(src).read()
    old = 'static int lb4r(int maxrot) {\n'
    assert code.count(old) == 1
    code = code.replace(old, old + '    if (getenv("RULEF_NOLB4R")) return 0;\n')
    d = tempfile.mkdtemp()
    open(os.path.join(d, 'r.c'), 'w').write(code)
    subprocess.run(['gcc', '-O2', '-o', os.path.join(d, 'r'), os.path.join(d, 'r.c')], check=True)
    sets, vals, m = build(name)
    env = dict(os.environ, RULEF_NOLB4R='1')
    p = subprocess.run([os.path.join(d, 'r'), '-A41', '-E1', '-Y1', '-N1', '-r1', '-T1', '-D7'],
                       input=AR.encode_profile(sets, vals), capture_output=True, text=True, env=env)
    idx = [l for l in p.stdout.split('\n') if l.startswith('IDX')]
    print(f'# rk {name}: k4/rulef.c ({src}) -A41 -E1 -Y1 -N1 -r1 -T1 -D7, LB4r skipped')
    if not idx:
        print('no IDX line: the first agent of rule RK is in K0;', p.stdout[-500:])
        return
    fa = [list(map(int, x.split(':')[1].split(','))) for x in idx[0].split('fa=')[1].strip().split(';')]
    bad = 0
    for a, (kN, kE, c, om, k1) in enumerate(fa):
        ok = kN <= 0 or kE <= 0 or k1 == 1 or c == 1
        bad += not ok
        print(f'first {a}: Lemma K deficit need-shrinking {kN}, envy-free/none {kE}, K1 {k1}, C40 {c} -> '
              f'{"in a class" if ok else "in no class"}')
    print(f'RESULT rk {name}: first agents in no class: {bad} of {len(fa)}')


def exact(name, enc, agents=None):
    sets, vals, m = build(name)
    inst = L.make_inst(sets, vals)
    print(f'# exact {name}: encoding {enc}, n = {inst.n}, m = {inst.m}', flush=True)
    nok = 0
    for a in (agents if agents is not None else range(inst.n)):
        t0 = time.time()
        st = {}
        for pol in L.POLS:
            s, _, _ = L.run_state(inst, a, pol)
            st.setdefault(s, ('rot0', pol))
        for pol in L.POLS:
            s, _, _ = L.run_state(inst, a, pol)
            for s2, desc in M.rot_steps(inst, s).items():
                st.setdefault(s2, ('rot1', pol, desc))
        found = None
        for s, tag in st.items():
            for o in [None] + list(range(inst.n)):
                ok = M.output_sat(inst, s, o, 'bundle')[0] if enc == 'A' else output_b(inst.v, s, o, 'bundle')
                if ok:
                    found = (tag, o)
                    break
            if found:
                break
        nok += found is not None
        print(f'first {a}: {len(st)} states (<= 1 rotation, 3 policies): '
              f'{"output " + str(found) if found else "no output"} ({time.time() - t0:.0f}s)', flush=True)
    print(f'RESULT exact {name} encoding {enc}: first agents with an output after <= 1 rotation: {nok}')


def d2(name):
    sets, vals, m = build(name)
    inst = L.make_inst(sets, vals)
    t = int(name[2:])
    # first agent x_{1,2} of copy A (index 3); at the second insertion step x_{1,2} of copy B, whose position among
    # the unprocessed agents is found by trying them
    for h in range(inst.n):
        s, run = M.phase1_state(inst, (3, h))
        ins = [x for x, f, k in run if k == 'I']
        if len(ins) >= 2 and ins[1] == 2 + 4 * t + 1:
            break
    for pol in L.POLS:
        s2, _ = M.up_run(inst, s, pol)
        for o in [None] + list(range(inst.n)):
            ok, X = M.output_sat(inst, s2, o, 'bundle', want_model=True)
            if ok:
                bund = [[g for g in range(inst.m) if X[g] == i] for i in range(inst.n)]
                efx = all(check4.efx0_safe(i, {g: inst.v[i][g] for g in range(inst.m)}, bund) for i in range(inst.n))
                big = sum(len(b) > 2 for b in bund)
                print(f'd2 {name}: insertion sequence {ins[:2]}, policy {pol}, owner {o}: Output, raw EFX0 {efx}, '
                      f'bundles above two goods {big}')
                return
    print(f'd2 {name}: no Output at that state')


if __name__ == '__main__':
    mode, name = sys.argv[1], sys.argv[2]
    rest = sys.argv[3:]
    ag = lambda s: [int(x) for x in s.split(',')]
    if mode == 'core':
        core(name)
    elif mode == 'classes':
        classes(name, ag(rest[0]) if rest else None)
    elif mode == 'rk':
        rk(name)
    elif mode == 'exact':
        exact(name, rest[0], ag(rest[1]) if len(rest) > 1 else None)
    elif mode == 'd2':
        d2(name)
