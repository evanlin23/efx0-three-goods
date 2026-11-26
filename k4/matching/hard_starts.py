"""Free-slot deficiency at the one-absorber-hard maximum-matching starts (k4/matching.md §2).

Data as in the Hall session's ed_check.py with MAX=1 (k4/oc1_hall/ed_check.py on claude/k4-oc1-hall): every order of
every instance with n <= NMAX, distinct pick vectors, picks forming a maximum matching.  For each start:
  - S*-hard / one-absorber-hard at the picks (raw, mlib.complete with d = 0);
  - for the one-absorber-hard ones: delta_oa and delta_ss at the picks (least number of dummy slots), the per-owner
    values, and over all states one official move reaches (k4/sdc/oc1_mc2_rand.Inst.moves: additions, chains, rings):
    the least delta_oa and delta_ss after one move, and the number of moves with delta_oa = 0 (OC1 repairs).
One JSON line per hard start goes to OUT (default results/k4_matching/hard_<src>.jsonl).

    python3 k4/matching/hard_starts.py SRC [N SEED]       (NMAX=5, PROCS, OUT; SRC = cex: k4/matching/cex_deficiency.py;
                                                           SRC = pw:SEED:T: k4/matching/pwdesign.py)"""
import sys, os, itertools, collections, time, json, multiprocessing as mp
import _mpaths  # noqa: F401
from mlib import M, INF
from min_frozen import load

NMAX = int(os.environ.get('NMAX', '5'))


def job(item):
    name, sets, vals, m = item
    I = M(sets, vals, m, name); n = I.n; NU = I.nu(); C = collections.Counter(); rows = []
    for Y in sorted(set(I.sd(o) for o in itertools.permutations(range(n))), key=str):
        if sum(1 for y in Y if y is not None) != NU: C['non-max starts (skipped)'] += 1; continue
        C['max starts'] += 1
        if NU < sum(1 for s in sets if s): C['max starts with a pickless agent'] += 1
        base = [[g] if g is not None else [] for g in Y]
        ss = I.complete(base, 0, 'ss') is not None
        oa = ss or I.complete(base, 0, 'oa') is not None
        if oa:
            C['complete at the picks' + ('' if ss else ' (one absorber, not S*)')] += 1
            continue
        C['one-absorber-hard'] += 1
        doa = I.deficiency(base, 'oa'); dss = I.deficiency(base, 'ss')
        own = I.owner_deficiency(base, 'oa')
        mv = I.moves(base)
        after_oa = [I.deficiency(b, 'oa', dmax=doa) for b in mv]
        after_ss = [I.deficiency(b, 'ss', dmax=dss) for b in mv]
        rep = sum(1 for x in after_oa if x == 0)
        row = dict(name=name, sets=sets, vals=vals, m=m, picks=Y, J=I.junk(base), frozen=I.frozen(base),
                   D=I.dangerous(base), d_oa=doa, d_ss=dss, own_oa=[own[o] for o in range(n)], moves=len(mv),
                   best_after_oa=min(after_oa) if mv else None, best_after_ss=min(after_ss) if mv else None,
                   repairs_oa=rep, repairs_ss=sum(1 for x in after_ss if x == 0))
        rows.append(row)
        C['hard: delta_oa = %d' % doa] += 1; C['hard: delta_ss = %d' % dss] += 1
        C['hard: delta_oa = %d, OC1 %s' % (doa, 'holds' if rep else 'FAILS')] += 1
        if mv: C['hard: delta_oa = %d -> best after one move %d' % (doa, min(after_oa))] += 1
    return C, rows


if __name__ == '__main__':
    src = sys.argv[1]
    tag = src if not src.startswith('cores:') else 'cores_%s_%s' % (sys.argv[2], sys.argv[3])
    out = os.environ.get('OUT', os.path.join(_mpaths.ROOT, 'results', 'k4_matching', 'hard_%s.jsonl' % tag))
    print('$ python3 k4/matching/hard_starts.py', *sys.argv[1:], '(NMAX=%d)' % NMAX, flush=True)
    if src == 'cex':   # PW4, RD4, B<, B>, the 39 core counterexamples (k = 4 only), k4/matching/cex_deficiency.py
        from cex_deficiency import instances
        items = [(nm, st, vl, 1 + max(max(x) for x in st)) for nm, st, vl in instances() if max(map(len, st)) <= 4]
    elif src.startswith('pw:'):   # PW design space, k4/matching/pwdesign.py; SRC = pw:SEED:T
        from pwdesign import instances as pwi
        _, sd, tt = src.split(':'); items = pwi(int(sd), int(tt)); tag = 'pw_%s_%s' % (sd, tt)
        out = os.environ.get('OUT', os.path.join(_mpaths.ROOT, 'results', 'k4_matching', 'hard_%s.jsonl' % tag))
    else:
        items = load(src, sys.argv)
    items = [it for it in items if len(it[1]) <= NMAX]
    T = collections.Counter(); t0 = time.time()
    with open(out, 'w') as fo, mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for C, rows in pool.imap_unordered(job, items, chunksize=4):
            T['instances'] += 1; T.update(C)
            for r in rows:
                fo.write(json.dumps(r) + '\n')
                if r['repairs_oa'] == 0: print('OC1 FAILS', json.dumps(r), flush=True)
    for k in sorted(T): print(k, T[k])
    print('rows written to', os.path.relpath(out, _mpaths.ROOT))
    print('time %.0f s' % (time.time() - t0))
