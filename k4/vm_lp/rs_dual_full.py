"""Full run of the two RS-dual tests over every profile of the export, in parallel (exploration for k4/vm_lp/)."""
import sys, os, gzip, json, collections, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rklib_copy as R
from rs_dual import beta_min, tight_in


DANGER = ['DT']                      # 'DT': rklib's truly dangerous; 'Dstar': frozen with v_x(junk) > p_x


def one(args):
    sets, vals, tag = args
    P = R.Prof(sets, vals); nu, Ms = P.max_matchings(); C = collections.Counter(); bad = []
    if nu != P.n: C['nu < n'] += 1; return C, bad
    rs = {M: sum(P.ranks(M)) for M in Ms}; best = min(rs.values())
    for Y in [M for M in Ms if rs[M] == best]:
        beta = beta_min(P, Y); assert beta is not None
        oc = P.oc1(Y); ro = P.roles(Y); J_ = set(ro['J'])
        pv = [P.val[i][Y[i]] for i in range(P.n)]
        dang = ro['DT'] if DANGER[0] == 'DT' else [x for x in ro['F'] if P.u(x, J_) > pv[x]]
        slack = {x: min(P.rank(x, g) - P.rank(x, Y[x]) for g in P.rel[x] if g in J_) - beta[Y[x]] for x in dang}
        tight = [x for x, s in slack.items() if s == 0]
        C[('RS-optimal', oc)] += 1
        C[('D1', oc, 'all dangerous slack' if not tight else 'some dangerous tight')] += 1
        if oc == 'F': bad.append(('F', tag, vals, Y))
        if not tight and oc != 'P': bad.append(('D1 fails', tag, vals, Y))
        if oc == 'M':
            B = [frozenset([g]) for g in Y]
            clos = set(tight); grew = True                 # backward closure along tight wants-arcs
            while grew:
                grew = False
                for x in list(clos):
                    for j in tight_in(P, Y, beta, x):
                        if j not in clos: clos.add(j); grew = True
            ok2 = False
            for nb in P.moves(B):
                ch = [i for i in range(P.n) if nb[i] != B[i]]
                if clos and set(ch) <= clos and P.one_absorber(list(nb)) is not None: ok2 = True; break
            C[('D2wide', 'a repair inside the tight closure' if ok2 else 'NO repair inside the tight closure')] += 1
            if not ok2: bad.append(('D2wide fails', tag, vals, Y))
            ok = False
            for nb in P.moves(B):
                ch = [i for i in range(P.n) if nb[i] != B[i]]
                if not any(i in tight and not (nb[i] & set(Y)) for i in ch): continue
                if not all(i in tight or any(i in tight_in(P, Y, beta, x) for x in tight) for i in ch): continue
                if P.one_absorber(list(nb)) is not None: ok = True; break
            C[('D2', 'canonical tight chain repairs' if ok else 'NO canonical tight chain')] += 1
            if not ok: bad.append(('D2 fails', tag, vals, Y))
    return C, bad


if __name__ == '__main__':
    if len(sys.argv) > 2: DANGER[0] = sys.argv[2]
    J = json.load(gzip.open(sys.argv[1])); jobs = []
    for h in J['hypergraphs']:
        seen = set()
        for st in h['starts']:
            k = json.dumps(st['vals'])
            if k in seen: continue
            seen.add(k); jobs.append((h['sets'], st['vals'], '%s#%d' % (h['list'], h['idx'])))
    print('$ python3 rs_dual_full.py', sys.argv[1]); print('profiles', len(jobs), flush=True)
    T = collections.Counter(); B = []
    with mp.Pool(4) as pool:
        for C, bad in pool.imap_unordered(one, jobs, chunksize=50):
            T.update(C); B += bad
    for k, v in sorted(T.items(), key=str): print(' ', v, k)
    print('violations:', len(B))
    for b in B[:10]: print('  ', b)
