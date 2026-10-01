"""Which single rotation repairs the runs that Lemma K does not certify (k4/rulef.md §4).

Reads DATA lines of k4/rulef.c -A40 -D4, or IDX lines of -A41 -D7 (leaf representatives where no first agent's run
has Lemma K deficit <= 0; rule F's rotations are known only for DATA lines, -1 otherwise) and,
on PR #33's independent model of LB4r (k4/c4_verify_H/lb4r.py), for every first agent a and both upgrade policies:
the Lemma K deficit of the state P after Phase 1(tau_a) and upgrades, and of every state one RotStep reaches from P
(rulef_model.rot_deficit_K). For the rotations that bring the deficit to <= 0 it records the shape: the rotated agent
k (3 or 4 goods; big-top a > b + c; exposed w.r.t. r, i.e. threatened by W = B_r ∪ J with its base), the chain end
(r, the last-processed agent that is not marked, or another agent), and the base O (O = R_k ∩ W, {b_k, c_k}, other).
Usage: rulef_rot.py DATAFILE [--max=N]"""
import collections, json, re, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rulef_model as RM
import lb4r as M


def last_unmarked(inst, s, run):
    marked = s[2]
    r = None
    for x, f, kind in run:
        if not marked[x]:
            r = x
    return r


def shape(inst, s, run, c, O):
    k, t = c[0], c[-1]
    r = last_unmarked(inst, s, run)
    base = s[0]
    J = [g for g in range(inst.m) if base[g] == -1]
    Br = M.base_of(inst, s, r) if r is not None else []
    W = set(J) | set(Br)
    Rk = sorted(inst.R[k], key=lambda g: -inst.v[k][g])
    vk = inst.v[k]
    bigtop = len(Rk) == 4 and vk[Rk[0]] > vk[Rk[1]] + vk[Rk[2]]
    exposed = RM.threatened(inst, k, W, M.base_of(inst, s, k))
    Oset = set(O)
    if Oset == set(Rk) & W:
        osh = 'O=R_k∩W'
    elif len(Rk) >= 3 and Oset == {Rk[1], Rk[2]}:
        osh = 'O={b,c}'
    else:
        osh = 'O other(%d)' % len(O)
    up = 'up' if RM.val(inst, k, O) > RM.val(inst, k, M.base_of(inst, s, k)) else 'down'
    return (('4' if len(Rk) == 4 else '3') + ('bigtop' if bigtop else ''), 'exposed' if exposed else 'not exposed',
            'end=r' if t == r else 'end≠r', osh, up)


def kr_certified(inst, s):
    """Lemma KR (k4/rulef.md §3) applies to s: some owner o (not frozen, |B_o| <= 1) has ∅-deficit delta <= 1, and some
    frozen k with a need chain to o and O ⊆ R_k ∩ W_o, v_k(O) > v_k(B_k), and some least ∅-service sigma satisfy
    (i), (ii), and o is not threatened after the rotation (or has a slot good outside sigma's slot goods and c_k >= 1).
    Returns a description or None."""
    import itertools
    needs = M.all_needs(inst, s)
    NA = M.NA_of(needs)
    fr = M.frozen_pre(inst, s, NA)
    base = s[0]
    J = [g for g in range(inst.m) if base[g] == -1]
    chains = M.chains(inst, s, needs, NA)
    for o in range(inst.n):
        Bo = M.base_of(inst, s, o)
        if fr[o] or len(Bo) > 1:
            continue
        delta, sigmas, capK, E = RM.all_min_services(inst, s, o, needs)
        if delta > 1 or not sigmas:
            continue
        W = set(Bo) | set(J)
        for c in chains:
            if c[-1] != o:
                continue
            k = c[0]
            Bk = M.base_of(inst, s, k)
            pool = [g for g in W if inst.v[k][g] > 0]
            for r_ in range(1, len(pool) + 1):
                for O in itertools.combinations(pool, r_):
                    if RM.val(inst, k, O) <= RM.val(inst, k, Bk):
                        continue
                    s2 = M.rotate(s, c, O)
                    if not M.rot_checks(inst, s2):
                        continue
                    n2 = M.all_needs(inst, s2)
                    if M.frozen_pre(inst, s2, M.NA_of(n2))[o]:
                        continue                                       # (ii) fails
                    Bo2 = M.base_of(inst, s2, o)
                    o_thr = RM.threatened(inst, o, W, Bo2)
                    J2 = [g for g in range(inst.m) if s2[0][g] == -1]
                    for sg in sigmas:
                        other = set().union(*[S for x, kind, S in sg if x != k]) if sg else set()
                        if set(O) & other:
                            continue                                   # (i) fails
                        mine = set().union(*[S for x, kind, S in sg if x == k]) if any(x == k for x, _, _ in sg) else set()
                        ck = len(mine - other)
                        if not o_thr and delta - 1 - ck <= 0:
                            return ('o not threatened', o == c[-1], len(c) - 1, len(O))
                        if o_thr and ck >= 1 and delta - ck <= 0:
                            G = set().union(*[S for x, kind, S in sg if kind == 's' and x != k]) if sg else set()
                            if any(not RM.threatened(inst, o, W - {g}, Bo2 + [g]) for g in J2 if g not in G):
                                return ('o served by a slot good', True, len(c) - 1, len(O))
    return None


def main():
    path = sys.argv[1]
    mx = int(next((a.split('=')[1] for a in sys.argv[2:] if a.startswith('--max=')), 10 ** 9))
    F = ['rot', 'cov', 'dN', 'dE', 'hN', 'hE', 'omN', 'omE', 'fz', 'e4', 'r', 'uN', 'uE', 'kN', 'kE', 'c40']
    nprof = 0
    W = collections.Counter(); S = collections.Counter(); per = collections.Counter(); KRs = collections.Counter()
    for line in open(path):
        if not (line.startswith('DATA') or line.startswith('IDX')): continue
        if nprof >= mx: break
        nprof += 1
        w = int(re.search(r'w=(\d+)', line).group(1))
        sets = json.loads(re.search(r'sets=(\[\[.*?\]\])', line).group(1))
        vals = json.loads(re.search(r'vals=(\[\[.*?\]\])', line).group(1))
        names = F if line.startswith('DATA') else ['kN', 'kE', 'c40', 'omN', 'k1']
        fa = [dict(zip(names, map(int, x.split(':')[1].split(',')))) for x in line.split('fa=')[1].strip().split(';')]
        for f in fa: f.setdefault('rot', -1)
        inst = RM.make_inst(sets, vals)
        anyK1 = False; k1s = []; anyKR = False
        for a in range(inst.n):
            best = RM.INF; shp = set()
            for pol in ('shrink', 'envyFree'):
                s, run = RM.run_state(inst, a, pol)
                kr = kr_certified(inst, s)
                if kr:
                    anyKR = True; KRs[kr[0]] += w
                d0 = RM.deficit_K(inst, s)
                if d0 <= 0:
                    print('NOTE: Python Lemma K <= 0 where C has > 0', a, pol, sets, vals)
                for s2, (c, O) in M.rot_steps(inst, s).items():
                    d = RM.deficit_K(inst, s2)
                    if d <= 0:
                        shp.add(shape(inst, s, run, c, O))
                    best = min(best, d)
            k1s.append(best)
            if best <= 0:
                anyK1 = True
                for sh in shp: S[sh] += w
            per[(fa[a]['rot'], best <= 0)] += w
        W[('some first agent: one rotation then Lemma K' if anyK1 else 'no first agent: one rotation then Lemma K',
           'rule F min rotations %d' % min(f['rot'] for f in fa))] += w
        W[('Lemma KR applies for some first agent and policy' if anyKR else 'Lemma KR applies for no first agent',)] += w
    print(f'{path}: leaves {nprof}')
    for k in sorted(W): print('  ', k, W[k])
    print('  per first agent (LB4r rotations, Lemma K after one rotation <= 0):')
    for k in sorted(per): print('    ', k, per[k])
    print('  Lemma KR certificates by case (profile, first agent and policy counted once each):', dict(KRs))
    print('  shapes of the repairing rotations (weighted by profiles, a profile counted once per shape and first agent):')
    for k, v in S.most_common(): print('    ', k, v)


if __name__ == '__main__':
    main()
