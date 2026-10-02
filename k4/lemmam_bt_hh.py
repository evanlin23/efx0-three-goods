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
  python3 k4/lemmam_bt_hh.py rk NAME                     k4/rulef.c's first big-top agent (-A42 -Q0) and rule RK
                                                         (-A41) with the class of the agent each chooses
  python3 k4/lemmam_bt_hh.py rkall NAME [A,B,..]         the classes K0, K1, C40 of every first agent by k4/rulef.c
                                                         (-A41 -E1 -Y1 -N1, single profile), one first agent per run;
                                                         LB4r itself is skipped (its owner search enumerates subsets
                                                         of the junk, out of reach at m = 65). Both need the source
                                                         of k4/rulef.c (PR #72): k4/rulef.c or $RULEF_SRC
  python3 k4/lemmam_bt_hh.py exact NAME A|B [A,B,..]     LB4r(tau_a) with at most one rotation, exactly: every policy,
                                                         every state one RotStep away, every owner and no owner, Lean's
                                                         Output with the owner's needs from its bundle; encoding A
                                                         (k4/c4_verify_H/lb4r.py) or B (k4/c4_verify_H/enc_b.py)
  python3 k4/lemmam_bt_hh.py d2 NAME                     K4.D on the instance: a two-step insertion sequence whose
                                                         state has an Output (encoding A), checked by the raw EFX0
                                                         definition
  python3 k4/lemmam_bt_hh.py suite NAME                  write the suite record k4/suite/instances/lmbt-NAME.json
                                                         (core and strictness by k4/suite/model.py; witness: an EFX0
                                                         allocation with one large bundle from LB4r without rotation
                                                         on a sequence that chooses the right agents)
With --log=FILE, classes, rkall and exact append their lines to FILE and skip the first agents FILE already has (resumable);
one worker process throughout.
"""
import hashlib, json, os, subprocess, sys, tempfile, time
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


LOG = None


def out(line):
    print(line, flush=True)
    if LOG:
        with open(LOG, 'a') as f:
            f.write(line + '\n')


def done_agents():
    """first agents already in the log (resumable runs)"""
    if not LOG or not os.path.exists(LOG):
        return {}
    res = {}
    for l in open(LOG):
        if l.startswith('first '):
            res[int(l.split()[1].rstrip(':'))] = l
    return res


def finished(n):
    return len(done_agents()) == n if LOG else True


def classes(name, agents=None):
    sets, vals, m = build(name)
    inst = L.make_inst(sets, vals)
    done = done_agents()
    if not done:
        out(f'# classes {name}: n = {inst.n}, m = {inst.m} (k4/lemmam_bt.py, Lemma K with Remark 4)')
    bad = sum('in no class' in l for l in done.values())
    for a in (agents if agents is not None else range(inst.n)):
        if a in done:
            continue
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
        out(f'first {a}: ' + ' | '.join(res) + f' | C40: omega {om}, exposed 4-good {len(e4)}, r frozen {rfz}'
            f' -> {"in K0/K1/C40" if inK or isc40 else "in no class"} ({time.time() - t0:.0f}s)')
    N = len(agents) if agents is not None else inst.n
    if finished(N):
        out(f'RESULT classes {name}: first agents in no class (K0, K1, RK3 policies; C40): {bad} of {N}')


def rulef_bin():
    """k4/rulef.c (PR #72) with two switches added for these instances: RULEF_NOLB4R skips LB4r itself (its owner
    search enumerates subsets of the junk, out of reach at m = 65), RULEF_ONLY=a evaluates rule RK's classes for the
    first agent a only (so the run can go one first agent at a time). Returns (binary, sha256 prefix of the source)."""
    src = os.environ.get('RULEF_SRC') or os.path.join(HERE, 'rulef.c')
    code = open(src).read()
    sha = hashlib.sha256(code.encode()).hexdigest()[:16]
    old = 'static int lb4r(int maxrot) {\n'
    assert code.count(old) == 1
    code = code.replace(old, old + '    if (getenv("RULEF_NOLB4R")) return 0;\n')
    loop = 'for (int a = 0; a < n && (rk_choice < 0 || FULL41); a++) {'
    assert code.count(loop) == 3
    code = code.replace(loop, loop + ' if (only_a() >= 0 && a != only_a()) continue;')
    head = 'static void rulef_leaf41(void) {'
    code = code.replace(head, 'static int only_a(void) { const char *s = getenv("RULEF_ONLY"); return s ? atoi(s) : -1; }\n'
                        + head)
    d = tempfile.mkdtemp()
    open(os.path.join(d, 'r.c'), 'w').write(code)
    subprocess.run(['gcc', '-O2', '-o', os.path.join(d, 'r'), os.path.join(d, 'r.c')], check=True)
    return os.path.join(d, 'r'), sha


def rk_agents(name, agents=None):
    """Rule RK's classes K0, K1, C40 of each first agent by k4/rulef.c, one first agent per process (resumable)."""
    binary, sha = rulef_bin()
    sets, vals, m = build(name)
    n = len(sets)
    done = done_agents()
    opts = ['-A41', '-E1', '-Y1', '-N1', '-r1', '-T1', '-D7']
    if not done:
        out(f'# rk {name}: k4/rulef.c (sha256 {sha}) {" ".join(opts)}, one first agent per run (RULEF_ONLY), '
            f'LB4r skipped; fields: Lemma K deficit after need-shrinking upgrades, after envy-free or no upgrades, '
            f'K1, C40')
    bad = sum('in no class' in l for l in done.values())
    for a in (agents if agents is not None else range(n)):
        if a in done:
            continue
        t0 = time.time()
        p = subprocess.run([binary] + opts, input=AR.encode_profile(sets, vals), capture_output=True, text=True,
                           env=dict(os.environ, RULEF_NOLB4R='1', RULEF_ONLY=str(a)))
        idx = [l for l in p.stdout.split('\n') if l.startswith('IDX')]
        if not idx:
            out(f'first {a}: no IDX line (rule RK chose an agent in K0): in a class ({time.time() - t0:.0f}s)')
            continue
        kN, kE, c, om, k1 = [list(map(int, x.split(':')[1].split(',')))
                             for x in idx[0].split('fa=')[1].strip().split(';')][a]
        ok = kN <= 0 or kE <= 0 or k1 == 1 or c == 1
        bad += not ok
        out(f'first {a}: {kN}, {kE}, K1 {k1}, C40 {c} -> {"in a class" if ok else "in no class"} '
            f'({time.time() - t0:.0f}s)')
    N = len(agents) if agents is not None else n
    if finished(N):
        out(f'RESULT rk {name}: first agents in no class: {bad} of {N}')


def rk(name):
    binary, sha = rulef_bin()
    sets, vals, m = build(name)
    env = dict(os.environ, RULEF_NOLB4R='1')
    # the first big-top agent q (-A42 -Q0), then rule RK (-A41)
    modes = [['-A42', '-Q0'], ['-A41']]
    for mo in modes:
        opts = mo + ['-Y1', '-N1', '-r1', '-T1', '-D7', '-v']
        p = subprocess.run([binary] + opts, input=AR.encode_profile(sets, vals), capture_output=True,
                           text=True, env=env)
        print(f'# rk {name}: k4/rulef.c (sha256 {sha}) {" ".join(opts)}, LB4r skipped')
        rk41 = [l for l in p.stdout.split('\n') if l.startswith('RK41')]
        cls = '?'
        if rk41:
            w = rk41[0].split()
            for c, nm in enumerate(['K0', 'K1', 'C40', 'open']):
                i = w.index('c%d' % c)
                if sum(map(int, w[i + 1:i + 4])):
                    cls = nm
        run = [l for l in p.stdout.split('\n') if l.startswith('RUN')]
        tau = run[0].split('tau=')[1].split()[0] if run and 'tau=' in run[0] else '?'
        print(f'rule {" ".join(mo)}: chosen first agent {tau.split(",")[0]}, its class {cls}')


def exact(name, enc, agents=None):
    sets, vals, m = build(name)
    inst = L.make_inst(sets, vals)
    done = done_agents()
    if not done:
        how = ('A (k4/c4_verify_H/lb4r.py build_model, HiGHS backend)' if enc == 'A'
               else 'B (k4/c4_verify_H/enc_b.py output_b, HiGHS)')
        out(f'# exact {name}: encoding {how}, Output with the owner\'s needs from its bundle, every owner and none, '
            f'n = {inst.n}, m = {inst.m}')
    nok = sum('no output' not in l for l in done.values())
    for a in (agents if agents is not None else range(inst.n)):
        if a in done:
            continue
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
                # encoding A with its MILP backend (HiGHS): on these states Glucose needs up to half a minute per
                # owner (the infeasibility is a counting argument), HiGHS a tenth of a second; PR #33 ran H_4 and
                # H_5 the same way (k4/c4_verify_H/README.md)
                ok = (M.output_sat(inst, s, o, 'bundle', backend='milp')[0] if enc == 'A'
                      else output_b(inst.v, s, o, 'bundle'))
                if ok:
                    found = (tag, o)
                    break
            if found:
                break
        nok += found is not None
        out(f'first {a}: {len(st)} states (<= 1 rotation, 3 policies): '
            f'{"output " + str(found) if found else "no output"} ({time.time() - t0:.0f}s)')
    N = len(agents) if agents is not None else inst.n
    if finished(N):
        out(f'RESULT exact {name} encoding {enc}: first agents with an output after <= 1 rotation: {nok} of {N}')


def lemmas(name):
    """Lemmas 1 and 2 of k4/lemmam_bt.md §3 on HH_t: for every first agent and policy, the bases of every gadget (as
    ranks in the agent's order: 0 = a, 1 = b, ...) are those the lemmas state."""
    sets, vals, m = build(name)
    t = int(name[2:])
    inst = L.make_inst(sets, vals)

    def role(i):
        if i < 2:
            return ('l', 'AB'[i], 0, 0)
        c = 'A' if i < 2 + 4 * t else 'B'
        k = (i - 2) % (4 * t)
        j, r = k // 4 + 1, k % 4
        return ('y', c, j, 0) if r == 3 else ('x', c, j, r + 1)
    idx = {role(i): i for i in range(inst.n)}
    bad = checked = 0
    for a in range(inst.n):
        ra = role(a)
        D = ra[1]
        C = 'B' if D == 'A' else 'A'
        for pol in L.POLS:
            s, _, _ = L.run_state(inst, a, pol)
            B = L.bases(inst, s)

            def conf(cp, j):
                ag = [idx[('y', cp, j, 0)]] + [idx[('x', cp, j, i)] for i in (1, 2, 3)]
                return [sorted(L.ranking(inst, x).index(g) for g in B[x]) for x in ag]
            for j in range(1, t + 1):
                checked += 2
                if conf(C, j) != [[3], [0], [0], [0]]:
                    bad += 1
                    print('copy C, first agent', a, pol, 'gadget', j, conf(C, j))
                if ra[0] == 'l' or j < ra[2]:
                    exp = [[3], [0], [0], [0]]                                            # (alpha)
                elif j == ra[2] and ra[0] == 'y' or ra[3] in (2, 3) and j == ra[2]:
                    exp = [[0], [1, 2], [0], [0]] if pol == 'shrink' else [[0], [1], [0], [0]]   # (beta1)
                else:
                    exp = [[1, 3], [0], [1, 2], [0]] if pol == 'shrink' else [[1], [0], [1], [0]]  # (beta2)
                if conf(D, j) != exp:
                    bad += 1
                    print('copy D, first agent', a, pol, 'gadget', j, conf(D, j), 'expected', exp)
    print(f'lemmas {name}: {checked} gadget states checked (every first agent, every policy), {bad} mismatches')


def witness(name):
    """An EFX0 allocation with at most one bundle above two goods: LB4r without rotation on the insertion sequence
    (x^A_{1,2}, x^B_{1,2}) for HH_t, (x_{1,1}) for H_t + q (rule RK's agent); encoding A, checked by the raw definition."""
    sets, vals, m = build(name)
    inst = L.make_inst(sets, vals)
    t = int(name[2:])
    if name.startswith('HH'):
        for h in range(inst.n):
            s0, run = M.phase1_state(inst, (3, h))
            ins = [x for x, f, k in run if k == 'I']
            if len(ins) >= 2 and ins[1] == 2 + 4 * t + 1:
                break
    else:
        s0, run = M.phase1_state(inst, (1,))
        ins = [x for x, f, k in run if k == 'I']
    for pol in L.POLS:
        s2, _ = M.up_run(inst, s0, pol)
        for o in [None] + list(range(inst.n)):
            ok, X = M.output_sat(inst, s2, o, 'bundle', want_model=True)
            if ok:
                bund = [[g for g in range(inst.m) if X[g] == i] for i in range(inst.n)]
                efx = all(check4.efx0_safe(i, {g: inst.v[i][g] for g in range(inst.m)}, bund) for i in range(inst.n))
                return dict(sequence=ins[:2] if name.startswith('HH') else ins[:1], policy=pol, owner=o,
                            allocation=bund, efx0=efx, large=sum(len(b) > 2 for b in bund))
    return None


SUITE_TEXT = {
    'Hq3': dict(
        refutes=[{'statement': 'Step (a) of the big-top programme for Lemma M (k4/rulef.md §6, PR #72): with exactly one '
                  'big-top agent q, the run of tau_q = (q, then index order) is in class K0 or K1 of rule RK (q first '
                  'needs at most one rotation)', 'ledger': 'K4.LMBT.A', 'smallest': False}],
        notes='H_3 (k4/c4.md §7, built by k4/adaptive_H.py) plus agent 13 = q = {p, b_11, c_11, u} with values '
              '(8, 4, 3, 2), p = good 33 private; q is the only big-top agent. q takes p and nobody loses a good, so the '
              'rest of tau_q is H_3\'s index run (Proposition Q of k4/lemmam_bt.md §2): LB4r(tau_q) has no output with '
              'at most one rotation (PR #33\'s encodings A and B, results/k4_lemmam_bt/exactA_Hq3.log, exactB_Hq3.log; '
              'the referee\'s model R, indep_exactR_Hq3.log); '
              'Lemma K deficit 5, >= 2 after every RotStep; rule RK takes x_11 (agent 1) in K0. Smallest of its family '
              '(H_2 + q allows one rotation); n <= 4 data satisfy the statement. Too large for the exhaustive '
              'predicates of predicates.py; replay: python3 k4/lemmam_bt_hh.py exact Hq3 A 13. Witness: LB4r without '
              'rotation on rule RK\'s sequence (x_11 first), an EFX0 allocation with one large bundle.'),
    'HH3': dict(
        refutes=[{'statement': 'Lemma M (k4/rulef.md §4, K4.RF.M): some first agent a is in class K0 or K1 of rule RK; '
                  'and rule F with at most one rotation (K4.AD.F; Lean EFX.LB4R.TheoremRuleF, RuleFConn): some a with '
                  'LB4r(tau_a), tau_a = (a, then index order), succeeding with at most one rotation',
                  'ledger': 'K4.LMBT.M', 'smallest': False}],
        notes='Two copies A, B of H_3 (k4/c4.md §7) with l_B\'s good u identified with l_A\'s good u (good 4); agents '
              'l_A, l_B, A\'s gadget agents, B\'s gadget agents (H_3 order); every agent has four goods, none big-top. '
              'Every first agent leaves one copy to index order (Proposition HH of k4/lemmam_bt.md §3): for each of the '
              '26 first agents, LB4r(tau_a) has no output with at most one rotation (PR #33\'s encodings A and B, '
              'results/k4_lemmam_bt/exactA_HH3.log, exactB_HH3.log; the PR #83 referee\'s model R, '
              'k4/lemmam_bt_indep.py, indep_exactR_HH3.log), and Lemma K puts none in K0 or K1 (k4/lemmam_bt.py, '
              'classes_HH3.log). Smallest known (two copies of H_2 have outputs with one rotation, '
              'indep_exactR_HH2.log). Too large for the exhaustive predicates of predicates.py; replay: python3 '
              'k4/lemmam_bt_hh.py exact HH3 A. Witness (K4.D holds): LB4r without rotation on the insertion sequence '
              '(x^A_12, x^B_12) = agents (3, 15).'),
}


def suite_record(name):
    sets, vals, m = build(name)
    from suite import model as SM          # k4/suite/model.py: the suite's own core and strictness checks
    I = SM.Inst(sets, vals, m)
    w = witness(name)
    rec = {'id': 'lmbt-' + name, 'n': len(sets), 'm': m, 'sets': sets, 'vals': vals,
           'is_core': not I.core_violations(), 'strict': I.strict(), 'core_ref': None,
           'source': {'pr': 83, 'branch': 'proof/k4-lemmam-bt',
                      'files': ['k4/lemmam_bt.md', 'k4/lemmam_bt_hh.py', 'results/k4_lemmam_bt/'],
                      'replay': 'bash k4/lemmam_bt_runs.sh'},
           'refutes': SUITE_TEXT[name]['refutes'],
           'witness': {'allocation': w['allocation'], 'insertion_sequence': w['sequence'], 'policy': w['policy'],
                       'owner': w['owner'], 'raw_efx0': w['efx0'], 'bundles_above_two': w['large']},
           'expect_fail': [], 'notes': SUITE_TEXT[name]['notes']}
    path = os.path.join(HERE, 'suite', 'instances', rec['id'] + '.json')
    with open(path, 'w') as f:
        json.dump(rec, f, ensure_ascii=False)
        f.write('\n')
    print(path, 'is_core', rec['is_core'], 'strict', rec['strict'], 'witness EFX0', w['efx0'], 'large', w['large'])


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
    LOG = next((x.split('=', 1)[1] for x in sys.argv if x.startswith('--log=')), None)
    argv = [x for x in sys.argv if not x.startswith('--log=')]
    mode, name = argv[1], argv[2]
    rest = argv[3:]
    ag = lambda s: [int(x) for x in s.split(',')]
    if mode == 'core':
        core(name)
    elif mode == 'classes':
        classes(name, ag(rest[0]) if rest else None)
    elif mode == 'rk':
        rk(name)
    elif mode == 'rkall':
        rk_agents(name, ag(rest[0]) if rest else None)
    elif mode == 'exact':
        exact(name, rest[0], ag(rest[1]) if len(rest) > 1 else None)
    elif mode == 'd2':
        d2(name)
    elif mode == 'lemmas':
        lemmas(name)
    elif mode == 'suite':
        suite_record(name)
