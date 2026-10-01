"""Cross-check of k4/dl2.c against k4/suite/deficit_local.py and k4/suite/model.py (compute/k4-dl2). EVIDENCE only.

For each instance (one strict profile): k* from deficit_local.kstar (the suite's own Python, written from the
definitions independently of dl2.c) and from dl2.c; and, per min-frozen pre-allocation P, the bases, def(P), the
distance to the nearest min-frozen P' with smaller deficit and (def > 0) to the nearest other min-frozen P', and
(def > 0) Pareto-maximality, computed here over all of 𝒫 (dl2.c scans the min-frozen class only), model.py (the
suite's model) against dl2.c's "W" lines.
Every disagreement is printed; the exit status is nonzero if there is one.

  python3 k4/dl2_check.py suite [--maxn=N]                       every complete suite instance with n <= N (default 6)
  python3 k4/dl2_check.py catalog FILE [--every=E] [--max=N]     catalogue records of k4/gap_run.py
  python3 k4/dl2_check.py random CERTFILE [--per=P] [--seed=S]   P random strict profiles of every core of a cert file
Options: --jobs=J (default 2)."""
import gzip, glob, json, os, random, sys
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, 'suite'))
import check4
import dl2_run as DR
import deficit_local as DL
import model as M

INF = 10 ** 9


def py_side(d):
    I = M.Inst(d['sets'], d['vals'], d.get('m'))
    I.preallocs()
    k, det = DL.kstar(d)
    if I.omega <= 0: return k, None
    mp = [Bs for Bs, NA in I.minP]
    df = {Bs: (INF if x is None else x) for Bs, x in ((Bs, I.deficit(Bs)) for Bs in mp)}
    per = {}
    for Bs in mp:
        if df[Bs] <= 0: per[Bs] = (df[Bs], -1, -1, -1); continue
        dist = min((sum(1 for a, b in zip(Bs, B2) if a != b) for B2 in mp if df[B2] < df[Bs]), default=99)
        near = min((sum(1 for a, b in zip(Bs, B2) if a != b) for B2 in mp if B2 != Bs), default=99)
        # Pareto-maximal over all of the space P (not only the min-frozen class)
        vs = [I.val(i, Bs[i]) for i in range(I.n)]
        pm = int(not any(all(I.val(i, B2[i]) >= vs[i] for i in range(I.n)) and any(I.val(i, B2[i]) > vs[i] for i in range(I.n))
                         for B2, NA2 in I._P))
        per[Bs] = (df[Bs], dist, near, pm)
    return k, per


def one(d):
    m = d.get('m') or 1 + max(g for S in d['sets'] for g in S)
    doms = [[dict(zip(S, V))] for S, V in zip(d['sets'], d['vals'])]
    b = DR.run_blocks(DR.block(d['sets'], m, doms, 0, 0), ['-w'])[0]
    V = b['V'][0]; n = len(d['sets'])
    ck = V[n + 1]
    ck = None if ck == -2 else (float('inf') if ck == -1 else ck)
    cper = {}
    for w in b['W'][0]:
        Bs = tuple(w[:n]); dfv = w[n]; dist = w[n + 1]; near = w[n + 2]; pm = w[n + 3]
        cper[Bs] = ((INF if dfv >= 999999 else dfv), dist, near, pm)
    pk, pper = py_side(d)
    bad = []
    if pk != ck: bad.append(f'k*: python {pk} C {ck}')
    if pper is not None or cper:
        pp = pper or {}
        if set(pp) != set(cper):
            bad.append(f'min-frozen P sets differ: python {len(pp)}, C {len(cper)}, only python {sorted(set(pp) - set(cper))[:3]}, only C {sorted(set(cper) - set(pp))[:3]}')
        for Bs in set(pp) & set(cper):
            if pp[Bs] != cper[Bs]: bad.append(f'P {Bs}: python (def, dist, nn, pm) {pp[Bs]}, C {cper[Bs]}')
    return d.get('id'), n, ck, len(cper), bad


def main():
    argv = sys.argv[1:]
    mode = argv[0]
    args = [a for a in argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in argv[1:] if a.startswith('--'))
    print('# command: python3 k4/dl2_check.py ' + ' '.join(argv), flush=True)
    print(f'# dl2.c sha256 {DR.SHA}', flush=True)
    DR.build()
    insts = []
    if mode == 'suite':
        for fn in sorted(glob.glob(os.path.join(HERE, 'suite', 'instances', '*.json'))):
            d = json.load(open(fn))
            if 'kind' in d or len(d['sets']) > int(opt.get('maxn', 6)): continue
            insts.append(d)
    elif mode == 'catalog':
        recs = json.load(gzip.open(args[0], 'rt'))['records'][::int(opt.get('every', 1))]
        if 'max' in opt: recs = recs[:int(opt['max'])]
        insts = [{'id': f"{os.path.basename(args[0])}#{r['core']['pos']}:{r['prof']}", 'sets': r['core']['sets'],
                  'm': r['core']['m'], 'vals': r['vals']} for r in recs]
    elif mode == 'random':
        rng = random.Random(int(opt.get('seed', 1)))
        cores = json.load(gzip.open(args[0], 'rt'))['cores']
        for k, c in enumerate(cores):
            doms = check4.core_domains(c['sets'], c['m'], False)
            for _ in range(int(opt.get('per', 10))):
                p = [rng.randrange(len(D)) for D in doms]
                insts.append({'id': f"{os.path.basename(args[0])}#{k}:{p}", 'sets': c['sets'], 'm': c['m'],
                              'vals': [[D[q][g] for g in S] for S, D, q in zip(c['sets'], doms, p)]})
    nbad = 0; hist = {}; nP = 0
    with Pool(int(opt.get('jobs', 2))) as pool:
        for iid, n, ck, np_, bad in pool.imap(one, insts, chunksize=4):
            hist[ck] = hist.get(ck, 0) + 1; nP += np_
            if mode == 'suite': print(f'{iid:<44} n={n}  k*={ck}  {np_} min-frozen P  {"AGREE" if not bad else "DISAGREE"}', flush=True)
            if bad:
                nbad += 1
                print(f'DISAGREE {iid}: ' + '; '.join(bad[:5]), flush=True)
    print(f'instances {len(insts)}, min-frozen P compared {nP}, k* histogram (C) '
          f'{dict(sorted(hist.items(), key=lambda x: (x[0] is None, x[0] if x[0] is not None else 0)))}, disagreements {nbad}', flush=True)
    sys.exit(1 if nbad else 0)


if __name__ == '__main__':
    main()
