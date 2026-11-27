"""One-receiver sigma-maximal starts at n = 5 (the RKMAX analogue of the DEMOTE classes; coordinator's request after
oc1-hall's census, k4/oc1_hall.md §24.14 on claude/k4-oc1-hall).  Independent regeneration: random strict balanced
order types (k4/girth/sources.domains, the types of k4/check4.py) on every pure n = 5 core
(results/k4_certs_5_pure.json.gz); per profile all n! SD orders, the maximum-matching vectors, sigma = (#rank 1..4)
(as k4/sdc/extremal_rank_check.py), the sigma-maximal ones; for those with exactly one receiver d:
  - raw OC1 (k4/sdc/oc1_mc2_rand.Inst.check);
  - NA: a completion with no owner, every junk good to a different agent (k3-oc1's Lemma NA form);
  - "virtual RF": for an order tau giving Y* with first picker u0, Y = SD(tau minus u0, then u0); if u0 is a
    receiver of Y and Y != Y*, then Y* is the RF start of (Y, u0) and the RF path (u0, w, ..., d') is defined
    (Lemma RF-PATH); then DEMOTE's uniform statement (k4/girth/oc1_residue.check_one), and for the trade case
    Lemma RF-T's explicit X and Corollary RF-T''s facts (F1)-(F3);
  - the SINK form with a in {w, d} (k4/girth/oc1_sink.check), under a virtual RF path.
EVIDENCE.

    [RKMAX_OUT=FILE.jsonl.gz] python3 k4/girth/oc1_rkmax_rand.py PROFILES_PER_CORE SEED [JOBS]
                                         (with RKMAX_OUT: every vector that needs a move, with its repairing moves)
    python3 k4/girth/oc1_rkmax_rand.py --from LOG [JOBS]      (the profiles of the JSON lines of oc1-hall's
                                                               results/k4_oc1_hall/rf_rkmax_rand.log)
"""
import collections
import itertools
import json
import multiprocessing as mp
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
from oc1_mc2_rand import Inst  # noqa: E402
from oc1_cycles import roles  # noqa: E402
from oc1_recvfirst import sd  # noqa: E402
from oc1_r2n5 import path_from  # noqa: E402
from oc1_rf_owner import owner_ok  # noqa: E402
from oc1_rkmax import sigma  # noqa: E402


def profiles(task):
    """(vals, v) per profile: K random ones of the core, or the one given"""
    from sources import domains
    idx, sets, m, K, seed = task[:5]
    if len(task) > 5:
        vals = task[5]
        yield vals, [dict(zip(sets[i], vals[i])) for i in range(len(sets))]
        return
    rng = random.Random(seed * 100003 + idx)
    doms = domains(sets, m)
    for t in range(K):
        ds = [rng.choice(D) for D in doms]
        yield [[d[g] for g in sorted(d)] for d in ds], [dict(d) for d in ds]


def virtual_rfs(sets, v, Ystar, orders):
    """every (Y, u0, path): tau an order giving Ystar with first picker u0, Y = SD(tau - u0, then u0) perfect, != Ystar,
    with u0 a receiver of Y; then Ystar is the RF start of (Y, u0) (the setting of RF-PATH, DEMOTE, RF-T)"""
    R = [set(s) for s in sets]
    vals = [[v[i][g] for g in sorted(sets[i])] for i in range(len(sets))]
    out = {}
    for tau in orders:
        u0 = tau[0]
        Y = sd(R, v, list(tau[1:]) + [u0])
        if Y == Ystar or None in Y or (Y, u0) in out:
            continue
        rl, J = roles(sets, vals, list(Y))
        if rl[u0] != 'U':
            continue
        out[(Y, u0)] = path_from(Y, Ystar, J, u0)
    return [(Y, u0, p) for (Y, u0), p in out.items()]


def rft_cert(I, Y, Y2, u, path, J, J2):
    """Lemma RF-T + Corollary RF-T': some valid trade (p pick-dangerous at Y2 with its own pick, j in J valued by p,
    v_p({Y2_d, j}) > v_p(Y_p), v_d(Y_p) > v_d(Y2_d)) with J2 - {j} = {Y_u, z}, (F1)-(F3), and the canonical X EFX0"""
    n = len(Y)
    v = I.v
    d = path[-1]
    if len(path) < 3 or Y2[d] not in J:
        return False
    rl2, _ = roles(I.sets, I.vals, list(Y2))
    for p in range(n):
        if rl2[p] != 'Dp' or Y2[p] != Y[p]:
            continue
        for j in J2:
            if j not in v[p] or j not in J:
                continue
            if not (I.V(p, [Y2[d], j]) > I.V(p, [Y2[p]]) and I.V(d, [Y2[p]]) > I.V(d, [Y2[d]])):
                continue
            rest = [g for g in J2 if g != j]
            if len(rest) != 2 or Y[u] not in rest:
                continue
            z = [g for g in rest if g != Y[u]][0]
            F1 = v[d].get(Y[p], 0) > v[d][Y[d]]
            F2 = all(not (v[i].get(Y[d], 0) > v[i].get(Y[i], 0)) for i in range(n) if i not in path)
            F3 = all(i in (p, d, u) for i in range(n) if Y[p] in v[i])
            if not (F1 and F2 and F3):
                continue
            X = [[g] for g in Y2]
            X[p] = [Y2[d], j]
            X[d] = [Y2[p], Y[u]]
            X[path[-2]] = [Y2[path[-2]], z]
            assert I.efx0(X), 'RF-T\' gives a non-EFX0 X'
            return True
    return False


def ring3_cert(I, Y2, J2, d):
    """the 3-ring certificate (k4/girth/oc1_tstar.py): an official 3-ring c1 takes {Y2_d, j}, c2 takes Y2_c1, d takes
    Y2_c2, then d absorbs every remaining junk good; EFX0"""
    n = len(Y2)
    v = I.v
    rl2, _ = roles(I.sets, I.vals, list(Y2))
    for c1 in range(n):
        if c1 == d or rl2[c1] != 'Dp':
            continue
        for c2 in range(n):
            if c2 in (d, c1):
                continue
            for j in J2:
                if j not in v[c1]:
                    continue
                if not (I.V(c1, [Y2[d], j]) > I.V(c1, [Y2[c1]]) and I.V(c2, [Y2[c1]]) > I.V(c2, [Y2[c2]])
                        and I.V(d, [Y2[c2]]) > I.V(d, [Y2[d]])):
                    continue
                B = [[g] for g in Y2]
                B[c1] = [Y2[d], j]
                B[c2] = [Y2[c1]]
                B[d] = [Y2[c2]] + [g for g in J2 if g != j]
                if I.efx0(B):
                    return True
    return False


def sink_form(I, Ys, rl, J2, absorbers):
    from oc1_sink import demote_moves, sink_ok
    base = [[p] for p in Ys]
    for a in absorbers:
        if sink_ok(I, base, J2, a):
            return 'at the picks'
    for kind, st, left in demote_moves(I, Ys, rl, J2, -1):
        for a in absorbers:
            if sink_ok(I, st, left, a):
                return 'after ' + kind.replace("(C')", '(C)')
    return 'FAILS'


def rfb_form(I, Ys, rl, J2):
    """(C) with head h: k (truly dangerous) takes an improving junk set H, h takes {Ys_k} plus junk Hh (improving),
    then h also absorbs its old pick and every junk good left (the RF-B shape); EFX0"""
    from oc1_sink import subsets
    n = len(Ys)
    v = I.v
    for k in range(n):
        if rl[k] != 'DT':
            continue
        for H in subsets([g for g in J2 if g in v[k]], 1):
            if not I.V(k, H) > I.V(k, [Ys[k]]):
                continue
            for h in range(n):
                if h == k:
                    continue
                for Hh in subsets([g for g in J2 if g not in H and g in v[h]]):
                    if I.V(h, [Ys[k]] + list(Hh)) > I.V(h, [Ys[h]]):
                        B = [[p] for p in Ys]
                        B[k] = list(H)
                        B[h] = [Ys[k], Ys[h]] + [g for g in J2 if g not in H]
                        if I.efx0(B):
                            return 'holds'
    return 'no'


def intrinsic(I, Ys, rl, J):
    """the first form that completes Ys: NA / an owner (by role) at the picks; else a DEMOTE move form ((T), (T*),
    (C) with any head) followed by a one-absorber completion; else another official move; else OC1 fails"""
    from oc1_sink import demote_moves
    n = len(Ys)
    base = [[p] for p in Ys]
    if owner_ok(I, base, None):
        return 'picks: NA (no owner)'
    owners = [a for a in range(n) if len(J) >= 2 and owner_ok(I, base, a)]
    if owners:
        return 'picks: owner ' + '/'.join(sorted({rl[a] for a in owners}))
    J = sorted(J)
    for kind, st, left in demote_moves(I, Ys, rl, J, -1):
        if I.one_absorber([list(b) for b in st]):
            return 'move: ' + kind.replace("(C')", '(C)')
    from oc1_sink import subsets
    v = I.v
    for k in range(n):                        # (C) with a pick-dangerous tail k (seen at |J| = 2)
        if rl[k] != 'Dp':
            continue
        for H in subsets([g for g in J if g in v[k]], 1):
            if not I.V(k, H) > I.V(k, [Ys[k]]):
                continue
            for h in range(n):
                if h == k:
                    continue
                for Hh in subsets([g for g in J if g not in H and g in v[h]]):
                    if I.V(h, [Ys[k]] + list(Hh)) > I.V(h, [Ys[h]]):
                        st = [list(b) for b in base]
                        st[k] = list(H)
                        st[h] = [Ys[k]] + list(Hh)
                        if I.one_absorber(st):
                            return 'move: (C) with a pick-dangerous tail, |J| = %d, head %s' % (len(J), rl[h])
    for st in I.moves(base):
        if I.one_absorber([list(b) for b in st]):
            return 'move: another official move'
    return 'OC1 fails'


def job(task):
    idx, sets = task[0], task[1]
    n = len(sets)
    R = [set(s) for s in sets]
    C = collections.Counter()
    ex = []
    allo = list(itertools.permutations(range(n)))
    for vals, v in profiles(task):
        vec = collections.defaultdict(list)
        for o in allo:
            vec[sd(R, v, o)].append(o)
        nu = max(sum(x is not None for x in p) for p in vec)
        mm = [p for p in vec if sum(x is not None for x in p) == nu]
        C['profiles'] += 1
        if nu < n:
            C['profiles with no perfect vector'] += 1
            continue
        best = max(sigma(sets, v, p) for p in mm)
        for Ys in [p for p in mm if sigma(sets, v, p) == best]:
            rl, J = roles(sets, vals, list(Ys))
            if rl.count('U') != 1:
                continue
            cls = '(1, %d) |J|=%d' % (rl.count('DT'), len(J))
            I = Inst(sets, vals)
            C[(cls, 'one-receiver sigma-maximal vectors')] += 1
            raw = I.check(Ys)
            C[(cls, 'raw OC1: ' + raw)] += 1
            iv = intrinsic(I, Ys, rl, J)
            C[(cls, 'first form: ' + iv)] += 1
            d0 = rl.index('U')
            vrs = virtual_rfs(sets, v, Ys, vec[Ys])
            C[(cls, 'a virtual RF start whose path ends at the receiver: %s' % bool(
                [1 for Y, u0, p in vrs if p[-1] == d0]))] += 1
            J2 = sorted(J)
            base = [[p] for p in Ys]
            cert = []
            if owner_ok(I, base, None):
                cert.append('NA')
            if len(J2) >= 2 and owner_ok(I, base, d0):
                cert.append('owner d = the receiver (DEMOTE (i))')
            for Y, u0, path in vrs:
                _, JY = roles(sets, vals, list(Y))
                w = path[1] if len(path) > 1 else path[-1]
                if len(J2) >= 2 and w != d0 and owner_ok(I, base, w):
                    cert.append('owner w of a virtual RF (RF-A1* form)')
                if rft_cert(I, Y, Ys, u0, path, JY, J2):
                    cert.append("RF-T' (canonical X, F1-F3, virtual RF)")
            if ring3_cert(I, Ys, J2, d0):
                cert.append('3-ring certificate')
            if rfb_form(I, Ys, rl, J2) == 'holds':
                cert.append('RF-B form')
            cov = ', '.join(sorted(set(cert))) or 'NONE of the forms'
            C[(cls, iv + ' | covered by: ' + cov)] += 1
            if not iv.startswith('picks'):
                from oc1_demote import describe_move
                mv = sorted({describe_move(base, [list(b) for b in st], rl, J2, [d0])
                             for st in I.moves(base) if I.one_absorber([list(b) for b in st])})
                ex.append(dict(idx=idx, sets=sets, vals=vals, picks=list(Ys), cls=cls, raw=raw, first=iv,
                               covered_by=cov, repairing_moves=mv))
            ends = sorted({p[-1] for Y, u0, p in vrs} | {p[1] for Y, u0, p in vrs if len(p) > 1})
            C[(cls, iv + ' | SINK form (absorber w or d of a virtual RF): %s' % sink_form(I, Ys, rl, J2, ends))] += 1
            if raw == 'OC1 fails':
                ex.append(dict(idx=idx, sets=sets, vals=vals, picks=list(Ys), cls=cls, raw=raw, first=iv))
    return C, ex


def main():
    print('$ python3 k4/girth/oc1_rkmax_rand.py', *sys.argv[1:], flush=True)
    if sys.argv[1] == '--from':
        jobs = int(sys.argv[3]) if len(sys.argv) > 3 else 2
        tasks, seen = [], set()
        for line in open(sys.argv[2]):
            if 'ONE-RECEIVER' in line:
                r = json.loads(line[line.index('{'):])
                k = json.dumps([r['sets'], r['vals']])
                if k not in seen:
                    seen.add(k)
                    tasks.append((r['idx'], r['sets'], None, 1, 0, r['vals']))
    else:
        K, seed = int(sys.argv[1]), int(sys.argv[2])
        jobs = int(sys.argv[3]) if len(sys.argv) > 3 else 2
        from sources import cores
        tasks = [(idx, sets, m, K, seed) for f, idx, sets, m in cores(5, pure=True)]
    C = collections.Counter()
    E = []
    with mp.Pool(jobs) as pool:
        for c, e in pool.imap_unordered(job, tasks, chunksize=20):
            C.update(c)
            E += e
    print('profiles %d (with no perfect vector: %d)' % (C['profiles'], C['profiles with no perfect vector']))
    for k in sorted(k for k in C if isinstance(k, tuple)):
        print('   %-8s %-100s %6d' % (k[0], k[1], C[k]))
    for e in E:
        if e['raw'] == 'OC1 fails':
            print('OC1 FAILURE', json.dumps(e))
    out = os.environ.get('RKMAX_OUT')
    if out:
        import gzip
        with gzip.open(out, 'wt') as f:
            for e in sorted(E, key=lambda e: (e['idx'], e['vals'], e['picks'])):
                f.write(json.dumps(e) + '\n')
        print('wrote %d one-move vectors to %s' % (len(E), os.path.basename(out)))
    sys.stdout.flush()


if __name__ == '__main__':
    main()
