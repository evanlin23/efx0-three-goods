"""Second implementation for k4/lemmam_x.md (workstream proof/k4-lemmam-x), written from the text on PR #33's model
of LB4r (k4/c4_verify_H/lb4r.py, a transcription of lean/EFX/LB4R.lean) and Lemma K's count of PR #72
(k4/rulef_model.py), without code from k4/lemmam_x.c.

For a profile it computes, for every first agent a (tau_a = (a, then index order), LB's P-step key):
  the class of a: K0 (Lemma K deficit <= 0, or omega <= 0, after need-shrinking or envy-free upgrades), K1 (one
  RotStep from one of those states reaches Lemma K deficit <= 0), or bad; Lemma K with the kept-out sets of
  k4/rulef.md §2 Remark 4 (XKEEP), as k4/lemmam_x.c -Y1;
  for a bad a, the candidates a' of k4/lemmam_x.md §2, read off the envy-free run of tau_a;
  the class of the run (k4/c4.md's cases: A4, B4, (G2), one exposed 4-good agent frozen / free, two or more).
Usage: lemmam_x_check.py --profiles=FILE [--max=N]   (FILE: {"sets", "vals"} lines, or tagged lines with sets=/vals=)
       lemmam_x_check.py 'sets' 'vals'
k4/rulef_model.py is imported from the working tree when PR #72 is merged, else read from the branch head
origin/proof/k4-rulef with git show into the temporary directory."""
import json, os, re, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, 'c4_verify_H'))
if not os.path.exists(os.path.join(HERE, 'rulef_model.py')):
    cache = os.path.join(tempfile.gettempdir(), 'lemmam_x_cache')
    os.makedirs(cache, exist_ok=True)
    dst = os.path.join(cache, 'rulef_model.py')
    if not os.path.exists(dst):
        src = subprocess.run(['git', 'show', 'origin/proof/k4-rulef:k4/rulef_model.py'], cwd=HERE,
                             capture_output=True, text=True, check=True).stdout
        open(dst, 'w').write(src)
    sys.path.insert(1, cache)
import rulef_model as RM
RM.XKEEP = True
M = RM.M

CANDS = ['r', 'endEF_early', 'endEF_idx', 'endEF_maxload', 'end_of_minidx_EF', 'EF4_minidx', 'end_of_earliest_EF',
         'freenottop_early']


def state(inst, a, pol):
    s0, run = M.phase1_state(inst, (a,))
    s, _ = M.up_run(inst, s0, pol)
    return s, run


def klass(inst, a):
    for pol in ('shrink', 'envyFree'):
        if RM.deficit_K(inst, state(inst, a, pol)[0]) <= 0:
            return 0
    for pol in ('shrink', 'envyFree'):
        if RM.rot_deficit_K(inst, state(inst, a, pol)[0])[0] <= 0:
            return 1
    return 2


def chain_ends(inst, s, needs, frz, x):
    """ends of the need chains from x (k4/c4.md (A4)): unmarked successors needing the predecessor's pick, frozen
    agents continue the chain, a non-frozen agent ends it"""
    pick, marked = s[1], s[2]
    ends = set()

    def ext(chain):
        y = pick[chain[-1]]
        if y < 0:
            return
        for j in range(inst.n):
            if j in chain or marked[j] or y not in needs[j]:
                continue
            if frz[j]:
                ext(chain + [j])
            else:
                ends.add(j)
    ext([x])
    return ends


def envyfree_view(inst, a):
    s, run = state(inst, a, 'envyFree')
    order = [x for x, f, t in run]
    pos = {x: i for i, x in enumerate(order)}
    blk, b = {}, -1
    for x, f, t in run:
        if t == 'I':
            b += 1
        blk[x] = b
    needs = M.all_needs(inst, s)
    NA = M.NA_of(needs)
    frz = [f and not s[2][i] for i, f in enumerate(M.frozen_pre(inst, s, NA))]
    r = [x for x in order if not s[2][x]][-1]
    J = [g for g in range(inst.m) if s[0][g] == -1]
    W = set(M.base_of(inst, s, r)) | set(J)
    E = [x for x in range(inst.n) if x != r and not s[2][x] and RM.threatened(inst, x, W, M.base_of(inst, s, x))]
    return dict(s=s, run=run, pos=pos, blk=blk, needs=needs, frz=frz, r=r, W=W, E=E, J=J)


def candidates(inst, a):
    v = envyfree_view(inst, a)
    s, pos, frz, E, needs = v['s'], v['pos'], v['frz'], v['E'], v['needs']
    EF = [x for x in E if frz[x]]
    ends = {x: chain_ends(inst, s, needs, frz, x) for x in EF}
    load = {}
    for x in EF:
        for e in ends[x]:
            load[e] = load.get(e, 0) + 1
    allends = sorted(load)
    c = {k: None for k in CANDS}
    c['r'] = v['r']
    if allends:
        c['endEF_early'] = min(allends, key=lambda e: pos[e])
        c['endEF_idx'] = min(allends)
        c['endEF_maxload'] = min(allends, key=lambda e: (-load[e], pos[e]))
    if EF:
        x = min(EF)
        if ends[x]:
            c['end_of_minidx_EF'] = min(ends[x], key=lambda e: pos[e])
        x = min(EF, key=lambda y: pos[y])
        if ends[x]:
            c['end_of_earliest_EF'] = min(ends[x], key=lambda e: pos[e])
    EF4 = [x for x in EF if len(inst.R[x]) == 4]
    if EF4:
        c['EF4_minidx'] = min(EF4)
    fnt = [x for x in range(inst.n) if not frz[x] and not s[2][x] and s[1][x] != max(inst.R[x], key=lambda g: inst.v[x][g])]
    if fnt:
        c['freenottop_early'] = min(fnt, key=lambda e: pos[e])
    return c, v


def runclass(inst, a):
    """0 omega <= 0, 1 A4, 2 B4, 3 (G2), 4 one exposed 4-good agent frozen, 5 free, 6 two or more"""
    v = envyfree_view(inst, a)
    s = v['s']
    if M.omega(inst, s) <= 0:
        return 0
    E, frz, r, W, pos, blk, needs = v['E'], v['frz'], v['r'], v['W'], v['pos'], v['blk'], v['needs']
    e4 = [x for x in E if len(inst.R[x]) == 4]
    if len(e4) >= 2:
        return 6
    if len(e4) == 1:
        return 4 if frz[e4[0]] else 5
    ks = min((x for x in range(inst.n) if blk[x] == blk[r]), key=lambda x: pos[x])
    bad = ks in E and ks != r and frz[ks]
    if bad:
        ends = chain_ends(inst, s, needs, frz, ks)
        bad = bool(ends) and ends == {r}
    if bad:
        J = set(v['J'])
        for x in E:
            for y in E:
                if x < y and set(inst.R[x]) & set(inst.R[y]) & J:
                    bad = False
    if not bad:
        return 1
    # (G2): every last frozen agent before r on a need chain from ks leaves r a 4-good agent exposed
    pick = s[1]
    preds = set()

    def ext(chain):
        y = pick[chain[-1]]
        for j in range(inst.n):
            if j in chain or s[2][j] or y not in needs[j]:
                continue
            if j == r:
                preds.add(chain[-1])
            elif frz[j]:
                ext(chain + [j])
    ext([ks])
    for p in preds:
        if not (len(inst.R[r]) == 4 and RM.threatened(inst, r, W, [pick[p]])):
            return 2
    return 3


def rho(inst, s, x, W, J):
    """least size of a kept-out set D of junk goods with x not threatened by W - D with its base"""
    import itertools
    B = M.base_of(inst, s, x)
    for k in range(len(J) + 1):
        for D in itertools.combinations(J, k):
            if not RM.threatened(inst, x, W - set(D), B):
                return k
    return float('inf')


def lemma_checks(inst, a):
    """the conclusions of Lemmas 1, 2, 3 of k4/lemmam_x.md for a bad first agent a; returns a list of failures"""
    import itertools
    v = envyfree_view(inst, a)
    s, E, frz, r, W, J, needs, pos = v['s'], v['E'], v['frz'], v['r'], v['W'], v['J'], v['needs'], v['pos']
    bad = []
    if M.omega(inst, s) <= 0:
        bad.append('L1a')
    X = [x for x in E if frz[x]]
    if not X:
        bad.append('L1b')
    rc = runclass(inst, a)
    if rc in (0, 1, 2):
        bad.append('L1c')
    # Lemma 3: a Hall violator among the exposed frozen agents
    Dx = {x: {e for e in chain_ends(inst, s, needs, frz, x) if e != r and e not in E} for x in X}
    rh = {x: rho(inst, s, x, W, J) for x in X}
    found = False
    for k in range(1, len(X) + 1):
        for Xp in itertools.combinations(X, k):
            U = set().union(*(Dx[x] for x in Xp))
            if sum(rh[x] for x in Xp) > len(U):
                found = True
                break
        if found:
            break
    if not found:
        bad.append('L3')
    if rc == 3:   # Lemma 2 on a longest chain from k*
        blk = v['blk']
        ks = min((x for x in range(inst.n) if blk[x] == blk[r]), key=lambda x: pos[x])
        pick = s[1]
        best = []

        def ext(chain):
            nonlocal best
            y = pick[chain[-1]]
            for j in range(inst.n):
                if j in chain or s[2][j] or y not in needs[j]:
                    continue
                if j == r:
                    if len(chain) + 1 > len(best):
                        best = chain + [j]
                elif frz[j]:
                    ext(chain + [j])
        ext([ks])
        Yp = pick[best[-2]]
        rk = sorted(inst.R[r], key=lambda g: -inst.v[r][g])
        rks = sorted(inst.R[ks], key=lambda g: -inst.v[ks][g])
        O = set(rks[1:])
        L = set(inst.R[r]) & W
        ok = (Yp == rk[1] and O == {rk[2], rk[3]}) or (Yp == rk[0] and O <= set(rk[1:]) and L <= O | {rk[3]})
        others = [z for z in range(inst.n) if z != r and Yp in needs[z]]
        if not ok:
            bad.append('L2b')
        if others:
            bad.append('L2a')
    return bad


def analyse(sets, vals):
    inst = RM.make_inst(sets, vals)
    cls = [klass(inst, a) for a in range(inst.n)]
    out = []
    for a in range(inst.n):
        if cls[a] == 2:
            c, v = candidates(inst, a)
            out.append((a, runclass(inst, a), c, lemma_checks(inst, a)))
    return cls, out


def main():
    args = sys.argv[1:]
    prof = next((x.split('=', 1)[1] for x in args if x.startswith('--profiles=')), None)
    mx = int(next((x.split('=')[1] for x in args if x.startswith('--max=')), 10 ** 9))
    expect = {}      # classes reported by k4/lemmam_x.c (BAD lines with cls=), compared below
    if prof:
        P = []
        for line in open(prof):
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            if line.startswith('{'):
                o = json.loads(line); P.append((o['sets'], o['vals'])); continue
            ms = re.search(r'sets=(\[\[.*?\]\])', line); mv = re.search(r'vals=(\[\[.*?\]\])', line)
            if ms and mv:
                P.append((json.loads(ms.group(1)), json.loads(mv.group(1))))
                mc = re.search(r'cls=(\d+)', line)
                if mc:
                    expect[json.dumps(P[-1])] = mc.group(1)
    else:
        P = [(json.loads(args[0]), json.loads(args[1]))]
    mism = 0
    seen = set(); tot = {'profiles': 0, 'nogood': 0, 'bad': 0}
    good = {k: 0 for k in CANDS}; undef = {k: 0 for k in CANDS}; lfail = {}; rcs = {}
    for sets, vals in P:
        key = json.dumps([sets, vals])
        if key in seen:
            continue
        seen.add(key)
        if tot['profiles'] >= mx:
            break
        tot['profiles'] += 1
        cls, out = analyse(sets, vals)
        ce = expect.get(json.dumps([sets, vals]))
        if ce is not None and ce != ''.join(map(str, cls)):
            # K0 and K1 can both hold; compare good/bad only
            if [c == '2' for c in ce] != [c == 2 for c in cls]:
                mism += 1
                print('MISMATCH lemmam_x.c', ce, 'here', ''.join(map(str, cls)), json.dumps({'sets': sets, 'vals': vals}))
        if all(c == 2 for c in cls):
            tot['nogood'] += 1
            print('NOGOOD', json.dumps({'sets': sets, 'vals': vals}))
        for a, rc, c, lf in out:
            tot['bad'] += 1
            for k in CANDS:
                if c[k] is None:
                    undef[k] += 1
                elif cls[c[k]] <= 1:
                    good[k] += 1
            for f in lf:
                lfail[f] = lfail.get(f, 0) + 1
            rcs[rc] = rcs.get(rc, 0) + 1
            print('BAD', 'cls=' + ''.join(map(str, cls)), 'a=%d' % a, 'runclass=%d' % rc,
                  'cand=' + ','.join('-1' if c[k] is None else str(c[k]) for k in CANDS),
                  'lemmafail=' + (','.join(lf) or '-'), json.dumps({'sets': sets, 'vals': vals}))
    print('profiles', tot['profiles'], 'with no good first agent', tot['nogood'], 'bad pairs', tot['bad'],
          'good/bad disagreements with lemmam_x.c', mism, 'of', len(expect))
    print('  bad pairs by run class (0 omega<=0, 1 A4, 2 B4, 3 G2, 4 one exposed 4-good frozen, 5 free, 6 two or more):',
          dict(sorted(rcs.items())))
    print('  conclusions of Lemmas 1-3 that fail (must be none):', lfail or 'none')
    for k in CANDS:
        print(f"  candidate {k:20s} good {good[k]} undefined {undef[k]} of {tot['bad']}")


if __name__ == '__main__':
    main()
