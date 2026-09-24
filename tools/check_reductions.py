"""Independent re-check of reducibility certificates written by src/reduce.py (proofs/min_counterexample.md, Lemma M1).

Written separately from src/reduce.py, sharing no code with it:
  1. local states of Y are enumerated differently: every map from the local goods to labels (agents of S' or outside
     bundle numbers 0..k-1) is generated with itertools.product, then canonicalized and deduplicated;
  2. agents of S (ranked, balanced, three goods) are judged by the case table T/P/B/C/E of L5, not by the raw
     definition; agents of S' (explicit additive valuations, possibly not balanced) by the raw EFX0 definition written
     as v(own) >= v(B - {g}) for every other bundle B and every g in B;
  3. the gadget is a legal reduction (smaller, supported on I' + D, at most three goods per agent, and H' stays in the
     class C_k whenever H does; see gadget_problems);
  4. every admissible state must have a stored extension, and each extension is checked against the rules of Lemma M1:
     goods conserved, outside bundles keep their goods outside I', moved items go to agents of S or to outside bundles
     worth 0 to their owner, all agents of S safe, every new or modified bundle dominated by a bundle of Y or (with
     the option 'source', M1(b)) made, outside I and I', of goods of the unenvied bundle of Y.
Certificate: gzip JSON list of records {name, S, I, D, Ddel, Sp, Ip, states: [[Ykey, X], ...]}; Ykey and X as written
by reduce.canon_state and reduce.export_ext.
With --cover, also checks that the verified reductions cover all 36 ranking profiles of each configuration of
proofs/min_counterexample.md, section 4 (pair and loop), and the 12 profiles of Lemma M6 (pq: the P-agent ranks its
private good last), reading each profile from the record's agents, not from its name.
Usage: check_reductions.py certs.json.gz [--jobs N] [--cover]
       check_reductions.py certs.json.gz --selftest   (corrupted copies of the first records must be rejected)"""
import sys, json, gzip, itertools, os, multiprocessing

MARK = ('w:', 'W:')


def is_marker(x):
    return x.startswith(MARK[0]) or x.startswith(MARK[1])


def safe_L5(rank, own, bundles):
    """rank = (a, b, c); own = set of goods held; bundles = the other bundles (lists). Case table of L5."""
    a, b, c = rank
    home = {}
    for k, B in enumerate(bundles):
        for g in B: home[g] = k
    def alone(g): return g in home and len(bundles[home[g]]) == 1
    def together_big(g, h): return g in home and h in home and home[g] == home[h] and len(bundles[home[g]]) >= 3
    if a in own and (b in own or c in own or not together_big(b, c)): return True      # T
    if b in own and c in own: return True                                               # P
    if b in own and alone(a): return True                                               # B
    if c in own and alone(a) and alone(b): return True                                  # C
    return alone(a) and alone(b) and alone(c)                                           # E


def safe_raw(val, own, bundles):
    mine = sum(val.get(g, 0) for g in own)
    for B in bundles:
        tot = sum(val.get(g, 0) for g in B)
        for g in B:
            if tot - val.get(g, 0) > mine + 1e-9: return False
    return True


def key_of(spb, blocks, src):
    """Canonical key: S' bundles in agent order, outside blocks sorted (markers already renamed by canonical position),
    and the unenvied bundle (None, ['sp', agent], or ['O', position of the block])"""
    blocks = sorted(tuple(sorted(b)) for b in blocks)
    return json.dumps([[sorted(spb[s]) for s in sorted(spb)], [list(b) for b in blocks], src])


def states(rec):
    """All local states: labels for each local good, then marker flags."""
    sp = sorted(rec['Sp'])
    L = sorted(set(rec['Ip']) | (set(rec['D']) - set(rec['Ddel'])))
    seen = set()
    nlab = len(sp) + len(L)
    for lab in itertools.product(range(nlab), repeat=len(L)):
        # outside labels must be used in order of first appearance (restricted growth), to skip relabelings
        nxt, ok = len(sp), True
        for x in lab:
            if x >= len(sp):
                if x > nxt: ok = False; break
                if x == nxt: nxt += 1
        if not ok: continue
        spb = {s: [g for g, x in zip(L, lab) if x == i] for i, s in enumerate(sp)}
        raw = [[g for g, x in zip(L, lab) if x == k] for k in range(len(sp), nxt)]
        for wf in itertools.product((0, 1), repeat=len(sp)):
            for Wf in itertools.product((0, 1), repeat=len(raw)):
                sb = {s: spb[s] + (['w:' + s] if wf[i] else []) for i, s in enumerate(sp)}
                base = [b + (['W'] if Wf[k] else []) for k, b in enumerate(raw)]
                # with an unenvied bundle: it is an S' bundle, one of the blocks, or an extra outside bundle holding
                # no local good (empty, or outside goods only)
                variants = [(base, None)]
                if rec.get('source'):
                    variants = [(base, ('sp', s)) for s in sp] + [(base, ('O', k)) for k in range(len(base))] + \
                               [(base + [[]], ('O', len(base))), (base + [['W']], ('O', len(base)))]
                for blocks0, src in variants:
                    tag = [(tuple(sorted(b)), k) for k, b in enumerate(blocks0)]
                    order = [k for _, k in sorted(tag)]
                    blk = [[('W:%d' % i if g == 'W' else g) for g in sorted(blocks0[k])] for i, k in enumerate(order)]
                    sd = None if src is None else (['sp', src[1]] if src[0] == 'sp' else ['O', order.index(src[1])])
                    key = key_of(sb, blk, sd)
                    if key in seen: continue
                    seen.add(key)
                    yield key, sb, blk, sd


def partitions(items):
    if not items: yield []; return
    first, rest = items[0], items[1:]
    for part in partitions(rest):
        for k in range(len(part)): yield part[:k] + [[first] + part[k]] + part[k + 1:]
        yield [[first]] + part


def components(edges, vertices):
    parent = {v: v for v in vertices}
    def find(v):
        while parent[v] != v: parent[v] = parent[parent[v]]; v = parent[v]
        return v
    for a, b in edges: parent[find(a)] = find(b)
    comp = {}
    for v in vertices: comp.setdefault(find(v), set()).add(v)
    return list(comp.values())


def gadget_problems(rec):
    """The gadget (S', I') must be a legal reduction (Lemma M1): smaller than (S, I); each agent of S' values at most
    three goods, all in I' + D; I' disjoint from D; and H' stays in the class C_k whenever H does. The last is
    checked exactly, for every way the rest of the instance can connect the boundary goods D: with the rest modelled by
    one tree per block of a partition of D, every component of (rest + gadget) must lie, by its rest-part, inside one
    component of (rest + configuration), with cyclomatic number no larger; components of the gadget touching no
    boundary good must be forests."""
    S, Sp, I, D, Ip = rec['S'], rec['Sp'], set(rec['I']), set(rec['D']), set(rec['Ip'])
    out = []
    if not (len(Sp) < len(S) or (len(Sp) == len(S) and len(Ip) < len(I))): out.append('gadget not smaller')
    if Ip & D: out.append("I' meets D")      # I' may reuse a name of I: a good the gadget keeps (deleted, then re-added)
    for a, val in Sp.items():
        supp = {g for g, x in val.items() if x > 0}
        if len(supp) > 3: out.append('gadget agent %s values more than three goods' % a)
        if not supp <= Ip | D: out.append('gadget agent %s values a good outside I\' + D' % a)
    L = [(('a', a), ('g', g)) for a, R in S.items() for g in R]
    Lp = [(('b', a), ('g', g)) for a, val in Sp.items() for g, x in val.items() if x > 0]
    for P in partitions(sorted(D)):
        star = [(('r', k), ('g', g)) for k, blk in enumerate(P) for g in blk]
        def graph(edges):
            V = {v for e in edges + star for v in e} | {('g', g) for g in D} | {('r', k) for k in range(len(P))}
            comps = components(edges + star, V)
            beta = lambda C: sum(1 for e in edges + star if e[0] in C) - len(C) + 1
            return [(C, beta(C)) for C in comps]
        GH, GHp = graph(L), graph(Lp)
        for C, b in GHp:
            roots = {v for v in C if v[0] == 'r'}
            if not roots:
                if b > 0: out.append("gadget component with a cycle and no boundary good")
                continue
            host = [(C2, b2) for C2, b2 in GH if roots <= C2]
            if not host: out.append("H' joins parts of the instance that H keeps apart (partition %s)" % P)
            elif b > host[0][1]: out.append("H' has a component with a larger cyclomatic number (partition %s)" % P)
    return sorted(set(out))


def check_record(rec):
    S, Sp = rec['S'], rec['Sp']
    I, D, Ddel, Ip = set(rec['I']), set(rec['D']), set(rec['Ddel']), set(rec['Ip'])
    wit = dict((k, x) for k, x in rec['states'])
    U = lambda B: frozenset(x for x in B if x in D or is_marker(x))
    inner = lambda B: any(x in I or x in Ip for x in B)
    problems, n_adm = gadget_problems(rec), 0
    for key, sb, blk, sd in states(rec):
        Ybund = [sb[s] for s in sorted(sb)] + blk
        if not all(safe_raw(Sp[s], sb[s], [sb[t] for t in sorted(sb) if t != s] + blk) for s in sorted(sb)):
            continue
        Ysrc = None if sd is None else (sb[sd[1]] if sd[0] == 'sp' else blk[sd[1]])
        if Ysrc is not None and any(sum(Sp[s].get(g, 0) for g in Ysrc) > sum(Sp[s].get(g, 0) for g in sb[s]) + 1e-9
                                    for s in sb):
            continue                                            # an agent of S' envies the supposedly unenvied bundle
        n_adm += 1
        if key not in wit: problems.append('no extension for state ' + key); continue
        X = wit[key]
        Xs, Xo = X['S'], X['O']
        if sorted(Xs) != sorted(S) or len(Xo) != len(blk): problems.append('malformed extension ' + key); continue
        moved = sorted([x for s in sb for x in sb[s] if x not in Ip] + sorted(Ddel))
        placed = [x for s in Xs for x in Xs[s]]
        extra = []
        for k, (b, nb) in enumerate(zip(blk, Xo)):
            keep = [x for x in b if x not in Ip]
            if sorted(x for x in nb if x in keep) != sorted(keep): problems.append('outside bundle changed ' + key)
            add = [x for x in nb if x not in keep]
            free = bool(b) and all(x in Ip for x in b)
            if any(not (x in I or (free and x in moved)) for x in add): problems.append('illegal addition ' + key)
            extra += add
        placed += extra
        if sorted(placed) != sorted(list(I) + moved): problems.append('goods not conserved ' + key); continue
        others = lambda s: [Xs[t] for t in sorted(Xs) if t != s] + Xo
        for s in sorted(S):
            if not safe_L5(tuple(S[s]), set(Xs[s]), others(s)): problems.append('agent %s unsafe in extension %s' % (s, key))
        changed = [Xs[s] for s in sorted(Xs)] + [nb for b, nb in zip(blk, Xo) if sorted(b) != sorted(nb)]
        for B in changed:
            if len(B) <= 1 or not U(B): continue
            if Ysrc is not None and U(B) <= U(Ysrc): continue      # worth at most the unenvied bundle to outsiders
            if not any(U(B) <= U(B2) and (not inner(B) or inner(B2) or U(B) != U(B2)) for B2 in Ybund):
                problems.append('bundle %s not dominated in %s' % (B, key))
    return rec['name'], n_adm, problems


# Configurations of proofs/min_counterexample.md, section 4: two P-agents e, f sharing a good g of degree 2.
CONFS = {'pair': ({'gl', 'g', 'p'}, {'g', 'y', 'pf'}, {'g', 'p', 'pf'}, {'gl', 'y'}),
         'loop': ({'G', 'g', 'p'}, {'g', 'G', 'pf'}, {'g', 'p', 'pf'}, {'G'}),
         'pq': ({'gl', 'g', 'p'}, {'g', 'y1', 'y2'}, {'g', 'p'}, {'gl', 'y1', 'y2'})}
# profiles each configuration must have covered: all of them for pair and loop (Theorem M3); for pq (Lemma M6) those in
# which e ranks its private good p last
MUST = {'pair': lambda e, f: True, 'loop': lambda e, f: True, 'pq': lambda e, f: e[2] == 'p'}


def configuration(rec):
    S = rec['S']
    if sorted(S) != ['e', 'f']: return None
    for name, (ge, gf, I, D) in CONFS.items():
        if set(S['e']) == ge and set(S['f']) == gf and set(rec['I']) == I and set(rec['D']) == D: return name
    return None


def selftest(recs):
    """Corrupted copies of the first records must be rejected: a missing state, a bundle emptied, a good moved."""
    import copy, random
    rng, caught, tried = random.Random(1), 0, 0
    for rec in recs[:40]:
        for kind in ('drop', 'empty', 'move'):
            r = copy.deepcopy(rec); st = r['states']
            if not st: continue
            k = rng.randrange(len(st)); X = st[k][1]
            if kind == 'drop': del st[k]
            elif kind == 'empty':
                a = rng.choice(sorted(X['S'])); X['S'][a] = [] if X['S'][a] else ['p', 'g']
            else:
                src = [a for a in X['S'] if X['S'][a]]
                if not src: continue
                a = rng.choice(src); b = rng.choice([x for x in sorted(X['S']) if x != a])
                x = X['S'][a].pop(rng.randrange(len(X['S'][a]))); X['S'][b].append(x)
            tried += 1; caught += bool(check_record(r)[2])
    return tried, caught


if __name__ == '__main__':
    args = sys.argv[1:]; jobs = os.cpu_count()
    if '--selftest' in args:
        tried, caught = selftest(json.load(gzip.open([a for a in args if a != '--selftest'][0], 'rt')))
        print('selftest: %d corrupted certificates, %d rejected (a moved good can leave a valid extension)' % (tried, caught))
        sys.exit(0)
    if '--jobs' in args: k = args.index('--jobs'); jobs = int(args[k + 1]); del args[k:k + 2]
    cover = '--cover' in args; args = [a for a in args if a != '--cover']
    recs = json.load(gzip.open(args[0], 'rt'))
    total, bad, covered = 0, 0, {c: set() for c in CONFS}
    with multiprocessing.Pool(jobs) as pool:
        for rec, (name, n_adm, probs) in zip(recs, pool.imap(check_record, recs, chunksize=2)):
            total += n_adm
            if probs:
                bad += 1; print(name, 'PROBLEMS:', len(probs)); [print('  ', p) for p in probs[:5]]
            elif configuration(rec):
                covered[configuration(rec)].add((tuple(rec['S']['e']), tuple(rec['S']['f'])))
    print('checked %d reductions, %d admissible local states; reductions with problems: %d' % (len(recs), total, bad))
    if cover:
        # every ranking profile of the two agents must be covered by a reduction that passed
        for c, (ge, gf, I, D) in CONFS.items():
            allp = {(e, f) for e in itertools.permutations(sorted(ge)) for f in itertools.permutations(sorted(gf))
                    if MUST[c](e, f)}
            miss = allp - covered[c]
            print('%s: %d of the %d required ranking profiles covered by a verified reduction (%d covered in all)'
                  % (c, len(allp) - len(miss), len(allp), len(covered[c])))
            if miss: bad += 1; print('  not covered:', sorted(miss)[:10])
    sys.exit(1 if bad else 0)
