"""Failed candidates of the workstream proof/k4-rulef (k4/rulef.md §5.3; attempts/k4-rulef-*.md), reproduced.

1. attempts/k4-rulef-least-count.md: the first agent minimizing a count (A4+N's or A4+(o)'s deficit, the refined
   counts, Lemma K's deficit, omega; ties by index or by frozen / exposed 4-good agents; also "a 4-good agent first").
   On the recorded profile, for each rule of k4/rulef.c -A40 (-Q selects the rule): LB4r on the rule's sequence fails
   with at most one rotation (-r1) and succeeds with two (-r2); independently, in PR #33's model of LB4r
   (k4/c4_verify_H/lb4r.py, written from lean/EFX/LB4R.lean) the least number of rotations on tau = [a] is 2, under
   every policy and both owner-needs conventions (attempts/k4_adaptive_attempts.least_rotations); rule RK (-A41) needs
   one; and k4/lb4_brute.py finds EFX0 allocations with at most one large bundle (the rule fails, not K4.D).
2. attempts/k4-rulef-frozen-free-owner.md: "a state of LB4r after Phase 1 and need-shrinking upgrades with no frozen
   agent and omega >= 1 has a valid owner (no rotation)". On the recorded n = 2 profile, first agent 0: in PR #33's
   model the state has no frozen agent, omega = 1, and no Output (no owner, every owner, both conventions).
3. attempts/k4-rulef-bigtop-first.md: "a big-top agent first (four goods, top worth more than the next two together),
   else index order" (k4/rulef.c -A42 -Q0; -Q1: else an agent whose least good is another agent's top). On the
   recorded profile (no big-top agent) the rule's sequence needs two rotations, in rulef.c and in PR #33's model.
4.-5. (same file) the first big-top agent fails when two or more agents are big-top (n = 4, m = 8, with rule RK as the
   fallback, -Q2), and the static refinements -Q3 / -Q4 (a shared top, fewest private goods) fail at n = 4, m = 7.
6. attempts/k4-rulef-keptout-in-R.md: Lemma K with kept-out sets restricted to goods the served agent values (the
   default of k4/rulef.c; -Y1 lifts it) leaves a suite core in no class of rule RK; with the full Lemma K every first
   agent is in K0. Checked in k4/rulef.c (-A41 with and without -Y1) and in k4/rulef_model.py (XKEEP False / True,
   every first agent and policy, every single RotStep of PR #33's model, completions checked with output_check and the
   raw EFX0 definition).
7. attempts/k4-rulef-kr-superset-needs.md: Lemma KR for a valid pre-allocation whose needs are only a superset of the
   value-based ones (without hypothesis (iii)): on the recorded n = 2 state every hypothesis holds and the rotated
   state violates (V1); with value-based needs the need chain does not exist.
Usage: python3 attempts/k4_rulef_attempts.py"""
import os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, 'k4'))
import k4_adaptive_attempts as AA
import rulef_run as RR
import adaptive_run as AR
from lb4r import Inst, phase1_state, up_run, any_output, all_needs, NA_of, frozen_pre, omega

RULES = {3: 'least A4+N deficit', 4: 'least A4+(o) deficit (envy-free)', 5: 'least of the two', 6: 'least refined (H) deficit, need-shrinking',
         7: 'least refined (H) deficit', 9: 'least omega after need-shrinking upgrades', 10: 'least refined deficit, then fewest frozen',
         11: 'a 4-good agent first', 12: 'least refined deficit, then fewest exposed 4-good agents', 13: 'least refined-with-kept-set deficit, need-shrinking',
         14: 'least refined-with-kept-set deficit', 16: 'least Lemma K deficit, need-shrinking', 17: 'least Lemma K deficit', 0: 'index order'}
P1 = ([[0, 1, 4, 5], [2, 3, 4, 5], [2, 3, 4, 5]], [[1, 4, 6, 8], [2, 3, 4, 8], [2, 7, 8, 4]])
FF = ([[0, 2, 3, 4], [1, 2, 3, 4]], [[2, 4, 7, 8], [2, 4, 5, 8]])
BT = ([[0, 1, 4, 5], [2, 3, 4, 5], [2, 3, 4, 5]], [[1, 4, 6, 8], [3, 5, 7, 6], [2, 4, 5, 8]])
BT2 = ([[0, 1, 3, 4], [2, 3, 6, 7], [2, 5, 7], [4, 5, 6, 7]], [[2, 3, 10, 6], [2, 8, 3, 4], [2, 4, 3], [4, 8, 2, 3]])
BT3 = ([[0, 2, 5, 6], [1, 4, 5, 6], [2, 3, 5], [3, 4, 6]], [[2, 8, 4, 5], [2, 8, 5, 4], [4, 2, 3], [2, 4, 3]])
ONB = ([[0, 2, 4, 6], [0, 2, 5, 6], [1, 3, 4, 7], [1, 3, 5, 7]], [[2, 3, 8, 4]] * 4)   # suite: lb4-owner-needs-from-base-n4m8
CLASSES = ['K0', 'K1', 'C40', 'open']


def rk_class(sets, vals, opts):
    p = subprocess.run([RR.BIN, '-A41', '-r1', '-T1'] + opts, input=AR.encode_profile(sets, vals), capture_output=True, text=True)
    t = next(l for l in p.stdout.split('\n') if l.startswith('RK41')).split()
    for c in range(4):
        i = t.index('c%d' % c)
        if sum(map(int, t[i + 1:i + 4])):
            return CLASSES[c]


def part7():
    # goods 0..3; agent 0 values (7, 6, 5, 3) on 0..3, agent 1 values (0, 4, 3, 2)
    v = [[7, 6, 5, 3], [0, 4, 3, 2]]
    R = [{g for g in range(4) if v[i][g] > 0} for i in range(2)]
    val = lambda i, S: sum(v[i][g] for g in S)
    def thr(i, L, H):
        L = list(L)
        return bool(L) and max(val(i, L) - v[i][h] for h in L) > val(i, H)
    vb = lambda i, B: {g for g in R[i] - B if v[i][g] > val(i, B)}
    B = [{0}, {1}]
    J = {2, 3}
    N = [{1}, set()]                                     # N_0 = {1}: a superset of agent 0's value-based needs (none)
    print("7. Lemma KR without (iii); state B = [{0}, {1}], J = {2, 3}, N = [{1}, {}], k = 1, o = 0, O = {2, 3}")
    ok = all(vb(i, B[i]) <= N[i] <= R[i] - B[i] for i in range(2))
    NA = N[0] | N[1]
    frz = [len(B[i]) == 1 and B[i] <= NA for i in range(2)]
    ok &= not (J & NA) and frz == [False, True]
    k, o, O = 1, 0, {2, 3}
    W = B[o] | J
    ok &= 1 in N[o] and O <= R[k] & W and val(k, O) > val(k, B[k])
    E = [x for x in range(2) if x != o and thr(x, W, B[x])]
    D = {2}
    kappa = sum(0 if frz[x] else 2 - len(B[x]) for x in range(2) if x != o)
    ok &= E == [1] and not thr(1, W - D, B[1]) and kappa == 0
    B2 = [{1}, O]
    J2 = W - O
    N2 = [vb(0, B2[0]), vb(1, B2[1])]
    NA2 = N2[0] | N2[1]
    o_free = not (B2[o] <= N2[k])
    v1 = not (J2 & NA2)
    print(f"  P valid: {ok}; E = {E}, served by the kept-out set {sorted(D)} (kappa = {kappa}, delta = 1); (i) holds; (ii) o "
          f"not frozen in P': {o_free}; P': J' = {sorted(J2)}, NA' = {sorted(NA2)}, (V1) holds: {v1}")
    chain_vb = 1 in vb(0, B[0])
    print(f"  with value-based needs agent 0 needs good 1: {chain_vb} (so the chain 1 -> 0 does not exist)")
    return ok and o_free and not v1 and not chain_vb


def part6():
    import rulef_model as RM
    from lb4r import output_check
    sets, vals = ONB
    print(f"6. Lemma K with kept-out sets inside R_x; profile sets={sets} vals={vals}")
    c0, c1 = rk_class(sets, vals, []), rk_class(sets, vals, ['-Y1'])
    print(f"  rulef.c -A41: class {c0} (kept-out sets inside R_x), {c1} with -Y1")
    ok = c0 == 'open' and c1 == 'K0'
    inst = RM.make_inst(sets, vals)
    for xk in (False, True):
        RM.XKEEP = xk
        row = []
        for a in range(inst.n):
            for pol in ('shrink', 'envyFree'):
                s, _ = RM.run_state(inst, a, pol)
                d = RM.deficit_K(inst, s)
                if d > 0:
                    dr = RM.rot_deficit_K(inst, s)[0]
                    row.append(f"a={a} {pol}: deficit {d}, after one RotStep {dr}")
                    ok &= (not xk) and dr > 0
                else:
                    o, X = RM.witness_K(inst, s)
                    good = output_check(inst, s, o, X, 'bundle') and RM.check_efx0(inst, X)
                    row.append(f"a={a} {pol}: deficit {d}, owner {o}, completion {'checked' if good else 'FAILS'}")
                    ok &= xk and good
        print(f"  k4/rulef_model.py XKEEP={xk}: " + '; '.join(row))
    RM.XKEEP = False
    ind = AA.least_rotations(AA.dense(sets, vals), [0])
    print(f"  LB4r on index order (independent model): least rotations {ind}; brute force: {AA.brute_d2(sets, vals)}")
    return ok and ind == 0


def tool(sets, vals, opts):
    p = subprocess.run([RR.BIN] + opts + ['-T1', '-v'], input=AR.encode_profile(sets, vals), capture_output=True, text=True)
    run = [l for l in p.stdout.split('\n') if l.startswith('RUN')][0]
    tau = [int(x) for x in run.split('tau=')[1].split()[0].split(',') if x]
    return run.split()[1], tau


def main():
    RR.build()
    print('# attempts/k4_rulef_attempts.py # rulef.c sha256', RR.SHA, flush=True)
    allok = True
    sets, vals = P1
    v = AA.dense(sets, vals)
    print(f"1. least-count rules; profile sets={sets} vals={vals}")
    for r, name in RULES.items():
        s1, tau = tool(sets, vals, ['-A40', '-C3', f'-Q{r}', '-r1'])
        s2, _ = tool(sets, vals, ['-A40', '-C3', f'-Q{r}', '-r2'])
        ind = AA.least_rotations(v, [tau[0]])
        ok = s1 == 'fail' and s2 == 'rot=2' and ind == 2
        allok &= ok
        print(f"  rule {r:2d} ({name}): first agent {tau[0]}; rulef.c -r1: {s1}, -r2: {s2}; independent model: least "
              f"rotations {ind} -> {'OK' if ok else 'MISMATCH'}")
    srk, tauk = tool(sets, vals, ['-A41', '-r1'])
    indk = AA.least_rotations(v, [tauk[0]])
    print(f"  rule RK: first agent {tauk[0]}, {srk}; independent model: least rotations {indk}")
    allok &= srk in ('rot=0', 'rot=1') and indk is not None and indk <= 1
    print('  brute force:', AA.brute_d2(sets, vals))
    sets, vals = FF
    inst = Inst(AA.dense(sets, vals))
    s, _ = up_run(inst, phase1_state(inst, [0])[0], 'shrink')
    needs = all_needs(inst, s)
    nfz = sum(frozen_pre(inst, s, NA_of(needs)))
    om = omega(inst, s, needs)
    outs = [o for conv in ('bundle', 'base') for o in any_output(inst, s, conv)]
    ok = nfz == 0 and om >= 1 and not outs
    allok &= ok
    print(f"2. frozen-free state without owner; profile sets={sets} vals={vals}, first agent 0, need-shrinking upgrades: "
          f"frozen agents {nfz}, omega {om}, outputs (any owner or none, both conventions) {outs} -> {'OK' if ok else 'MISMATCH'}")
    print('  brute force:', AA.brute_d2(sets, vals))
    sets, vals = BT
    v = AA.dense(sets, vals)
    print(f"3. a big-top agent first, else index order (also: else an agent whose least good is another's top); profile sets={sets} vals={vals}")
    for q in (0, 1):
        s1, tau = tool(sets, vals, ['-A42', f'-Q{q}', '-r1'])
        s2, _ = tool(sets, vals, ['-A42', f'-Q{q}', '-r2'])
        ind = AA.least_rotations(v, [tau[0]])
        ok = s1 == 'fail' and s2 == 'rot=2' and ind == 2
        allok &= ok
        print(f"  -Q{q}: first agent {tau[0]}; rulef.c -r1: {s1}, -r2: {s2}; independent model: least rotations {ind} -> {'OK' if ok else 'MISMATCH'}")
    big = [i for i, V in enumerate(vals) if len(V) == 4 and sorted(V)[3] > sorted(V)[2] + sorted(V)[1]]
    print(f"  big-top agents: {big}")
    srk, tauk = tool(sets, vals, ['-A41', '-r1'])
    indk = AA.least_rotations(v, [tauk[0]])
    print(f"  rule RK: first agent {tauk[0]}, {srk}; independent model: least rotations {indk}")
    allok &= srk in ('rot=0', 'rot=1') and indk is not None and indk <= 1 and not big
    print('  brute force:', AA.brute_d2(sets, vals))
    for label, (sets, vals), q in (
            ('4. the first big-top agent (else rule RK), two or more big-top agents', BT2, 2),
            ('5. a big-top agent with the fewest private goods, else a shared-top agent with the fewest private goods', BT3, 4)):
        v = AA.dense(sets, vals)
        print(f"{label}; profile sets={sets} vals={vals}")
        s1, tau = tool(sets, vals, ['-A42', f'-Q{q}', '-r1'])
        s2, _ = tool(sets, vals, ['-A42', f'-Q{q}', '-r2'])
        ind = AA.least_rotations(v, [tau[0]])
        ok = s1 == 'fail' and s2 == 'rot=2' and ind == 2
        allok &= ok
        big = [i for i, V in enumerate(vals) if len(V) == 4 and sorted(V)[3] > sorted(V)[2] + sorted(V)[1]]
        print(f"  -Q{q}: first agent {tau[0]} (big-top agents {big}); rulef.c -r1: {s1}, -r2: {s2}; independent model: least "
              f"rotations {ind} -> {'OK' if ok else 'MISMATCH'}")
        srk, tauk = tool(sets, vals, ['-A41', '-r1'])
        indk = AA.least_rotations(v, [tauk[0]])
        print(f"  rule RK: first agent {tauk[0]}, {srk}; independent model: least rotations {indk}")
        allok &= srk in ('rot=0', 'rot=1') and indk is not None and indk <= 1
        print('  brute force:', AA.brute_d2(sets, vals))
    allok &= part6()
    allok &= part7()
    print('ALL AS RECORDED' if allok else 'MISMATCH')


if __name__ == '__main__':
    main()
