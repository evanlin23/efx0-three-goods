"""Which single rotation repairs the runs that Lemma K does not certify (k4/rulef.md §4).

Reads DATA lines of k4/rulef.c -A40 -D4 (leaf representatives where no first agent's run has Lemma K deficit <= 0) and,
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
    return (('4' if len(Rk) == 4 else '3') + ('bigtop' if bigtop else ''), 'exposed' if exposed else 'not exposed',
            'end=r' if t == r else 'end≠r', osh)


def main():
    path = sys.argv[1]
    mx = int(next((a.split('=')[1] for a in sys.argv[2:] if a.startswith('--max=')), 10 ** 9))
    F = ['rot', 'cov', 'dN', 'dE', 'hN', 'hE', 'omN', 'omE', 'fz', 'e4', 'r', 'uN', 'uE', 'kN', 'kE', 'c40']
    nprof = 0
    W = collections.Counter(); S = collections.Counter(); per = collections.Counter()
    for line in open(path):
        if not line.startswith('DATA'): continue
        if nprof >= mx: break
        nprof += 1
        w = int(re.search(r'w=(\d+)', line).group(1))
        sets = json.loads(re.search(r'sets=(\[\[.*?\]\])', line).group(1))
        vals = json.loads(re.search(r'vals=(\[\[.*?\]\])', line).group(1))
        fa = [dict(zip(F, map(int, x.split(':')[1].split(',')))) for x in line.split('fa=')[1].strip().split(';')]
        inst = RM.make_inst(sets, vals)
        anyK1 = False; k1s = []
        for a in range(inst.n):
            best = RM.INF; shp = set()
            for pol in ('shrink', 'envyFree'):
                s, run = RM.run_state(inst, a, pol)
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
    print(f'{path}: leaves {nprof}')
    for k in sorted(W): print('  ', k, W[k])
    print('  per first agent (LB4r rotations, Lemma K after one rotation <= 0):')
    for k in sorted(per): print('    ', k, per[k])
    print('  shapes of the repairing rotations (weighted by profiles, a profile counted once per shape and first agent):')
    for k, v in S.most_common(): print('    ', k, v)


if __name__ == '__main__':
    main()
