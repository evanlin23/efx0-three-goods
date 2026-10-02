#!/usr/bin/env python3
"""T3-stage states with f >= 2 and their repairs (workstream proof/k4-f2; k4/f2.md §1, §2). EVIDENCE tooling.

For every distinct strict profile in the inputs whose fewest frozen agents is f >= 2 (omega >= 1), the tool builds the
min-frozen class (k4/f2_lib.py: main's k4/suite/model.py and k4/dl2_classify.py), and for every min-frozen P with
def(P) > 0 decides whether P is at the *T3 stage* (k4/dl13.md §2.3: def(P) is the least deficit of its key and no (T4)
move lowers it; the stage is the same for R_T4 = T1 ∪ T2 ∪ T3 ∪ T4 and for R_C = T1 ∪ T2 ∪ T3⁺ ∪ T4, k4/f2_lib.py).
At each T3-stage state it records
  * the obstruction: for every best owner o, optimal X and c ∈ J \\ X, the blockers of c (agents w != o threatened by
    X ∪ {c} holding B_w); the state's *case*:
      A-S1  some junk good of a best owner o has a single blocker x that is frozen and o needs x's good (the S1 shape of
            k4/dl13.md Corollary 9.1), with its theta kinds (ok / theta-a / theta-b, k4/dl13.md Lemma 10);
      A-z   otherwise, some single frozen blocker has a free needer (not the owner);
      B     single frozen blockers occur and every one has only frozen needers (the frozen-needer case); recorded:
            the least number of frozen agents on a need path from a free agent to such a blocker (k4/f2.md Lemma P),
            and whether the owner o of the block is the free end of a need path to it ('B-S1c': the S1 shape through a
            chain);
      C     no single frozen blocker (single free blockers only, or no single blocker);
  * every improving (T3⁺) move: x unfreezes, z takes a frozen good it needs, the agents W (frozen in both) pass frozen
    goods along, at most one helper h gives up a good; (T3) when W = ∅. Described by its kind ('t3' or 't3c'), its
    chain (the path z -> a_1 -> ... -> x of frozen goods, extra cycles, whether every path agent takes a good it needs),
    x's role (single frozen blocker 'SB', a blocker 'BL', exposed 'EX', or none '-'), whether z is a best owner of P, the
    source of x's new base A (J, B_z, B_h), the helper's change, and who is a best owner of P' (x, h, an unmoved best
    owner of P 'O*', another unmoved free agent 'O');
  * the structural certificates C1 (Corollary 9.1), C2 (Corollary 11.1), C3 (Corollary 8.2) of k4/dl13.md (plain role
    swaps), evaluated at any f, each conclusion asserted against the exact deficits;
  * DL on the key graph (k4/dl13.md §2.3, Remark), per key with def* > 0: whether some single (T3) or (T4) move
    (RT4's edges), and whether some single (T3⁺) or (T4) move (R_C's edges), from some state of the key reaches a key
    with a smaller def*.
Every move also asserts that it keeps the key iff it is a (T1) or (T2) move, and that dl2_relations.py's (T3) test
agrees with the T3⁺ test at W = ∅.

usage: python3 k4/f2_shapes.py SOURCE ... [--every=E] [--max=N] [--out=FILE.jsonl.gz] [--chunk=K/C]
  SOURCE: a catalogue (#53's results/k4_gap/*.json.gz, 'records'), a dump (*.jsonl.gz records with sets/vals or
  core/vals), an instance list (*.json: [{"sets", "vals", "m"}]), or 'suite'. Only records with f >= 2 are read (a
  record without 'f' is read and filtered after the class is built); profiles are deduplicated across all sources.
  --chunk=K/C keeps the K-th of C equal slices of the deduplicated list (for runs of bounded length).
Output: the counts, the smallest example of each cell, and (--out) one JSON line per T3-stage state."""
import collections, glob, gzip, itertools, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from f2_lib import Prof, bits, pc, mask, tup, lst, counted, bigtop, kind, t3plus, INF, profile_items, chain_shape


# ------------------------------------------------------------------ inputs
def read_source(src):
    """yield (d, f or None, label) for every record of a source"""
    if src == 'suite':
        for fn in sorted(glob.glob(os.path.join(HERE, 'suite', 'instances', '*.json'))):
            d = json.load(open(fn))
            if 'kind' in d or not d.get('is_core', True): continue
            yield profile_items(d), None, 'suite:' + d['id']
        return
    base = os.path.basename(src)
    if src.endswith('.json'):
        for r in json.load(open(src)):
            yield profile_items(r), None, r.get('id', base)
        return
    if src.endswith('.jsonl.gz'):
        for l in gzip.open(src, 'rt'):
            r = json.loads(l)
            if 'vals' not in r or ('sets' not in r and 'core' not in r): continue
            yield profile_items(r), r.get('f'), base
    else:
        for r in json.load(gzip.open(src, 'rt')).get('records', []):
            yield profile_items(r), r.get('f'), base + ':' + ','.join(map(str, r.get('prof', [])))


def collect(sources, opt):
    seen = collections.OrderedDict()
    skip = set(opt['exclude-ids'].split(',')) if 'exclude-ids' in opt else set()
    for src in sources:
        k = 0
        for d, f, label in read_source(src):
            if f is not None and f < 2: continue
            if label.startswith('suite:') and label[6:] in skip: continue
            k += 1
            if 'every' in opt and (k - 1) % int(opt['every']): continue
            key = json.dumps([d['sets'], d['vals']])
            if key not in seen: seen[key] = (d, label)
    items = list(seen.values())
    if 'chunk' in opt:
        a, b = map(int, opt['chunk'].split('/'))
        L = len(items); items = items[L * a // b: L * (a + 1) // b]
    if 'max' in opt: items = items[:int(opt['max'])]
    return items


# ------------------------------------------------------------------ need paths (k4/f2.md Lemma P)
def need_paths(pr, Bs, w):
    """(k, ends): the least number k of frozen agents strictly between a free agent and w on a need path
    (z -> y_k -> ... -> y_1 -> w: z free needs B_{y_k}, each y needs the next good, y_1 needs B_w), and the free agents
    at that distance; (None, []) if no free agent reaches w (then the frozen agents reaching w contain a need cycle)"""
    P = pr.PA[Bs]; I = pr.I
    layer, seen, k = [w], {w}, 0
    while layer:
        nxt = []
        for y in layer:
            for i in range(I.n):
                if P.N[i] & Bs[y] and i not in seen:
                    seen.add(i); nxt.append(i)
        ends = [i for i in nxt if not P.frozen[i]]
        if ends: return k, sorted(ends)
        layer = [i for i in nxt if P.frozen[i]]; k += 1
    return None, []


def path_ends_all(pr, Bs, w):
    """every free agent with a need path to w"""
    P = pr.PA[Bs]; I = pr.I
    stack, seen, ends = [w], {w}, set()
    while stack:
        y = stack.pop()
        for i in range(I.n):
            if P.N[i] & Bs[y] and i not in seen:
                seen.add(i)
                if P.frozen[i]: stack.append(i)
                else: ends.add(i)
    return ends


# ------------------------------------------------------------------ one T3-stage state
class State:
    def __init__(self, pr, Bs):
        self.pr, self.Bs, self.I = pr, Bs, pr.I
        self.P = pr.PA[Bs]; self.D = pr.D[Bs]
        self.best = pr.best(Bs); self.V = pr.V(Bs)
        self.omega = pc(self.P.J) - self.P.S

    def thr(self, w, Z, hold): return self.I.threat(w, Z, self.I.val(w, hold))

    def admissible(self, i, pool):
        I, P = self.I, self.P
        return [mask(A) for k in (1, 2) for A in itertools.combinations(list(bits(pool & I.R[i])), k)
                if not (I.needs(i, mask(A)) & ~P.NA)]

    def new(self, x, z, A, h=None, Bh=None):
        b = list(self.Bs); b[z] = self.Bs[x]; b[x] = A
        if h is not None: b[h] = Bh
        return tuple(b)

    def theta_kind(self, o, Z, g):
        """Lemma 10 of k4/dl13.md at theta_o(Z) > v_o(g): 'a' or 'b' (asserted)"""
        I, P = self.I, self.P
        vg = I.val(o, g); Q = list(bits(Z & I.R[o]))
        if any(I.val(o, mask(q)) > vg for k in (1, 2) for q in itertools.combinations(Q, k)):
            assert any(P.N[i] & g for i in range(I.n) if i != o), ('Lemma 10(a)', self.Bs, o)
            return 'a'
        assert len(I.sets[o]) == 4 and bigtop(I, o) and max(I.sets[o], key=lambda q: I.v[o][q]) == next(bits(g)) \
            and not (I.R[o] & ~g & ~Z), ('Lemma 10(b)', self.Bs, o)
        return 'b'

    def case(self):
        """the case (module doc) and the details of the single blocks"""
        pr, P, Bs = self.pr, self.P, self.Bs
        sb = pr.single_blocks(Bs)
        det = collections.Counter(); fz_free = False; fz_any = False; thetas = set(); paths = set(); s1c = False
        for o, X, c, w in sb:
            if not P.frozen[w]:
                det['single free blocker'] += 1; continue
            fz_any = True
            fn = pr.free_needers(Bs, w)
            if fn:
                fz_free = True
                if o in fn:
                    g = Bs[w]; Z = X | (1 << c)
                    thetas.add('ok' if not self.thr(o, Z, g) else 'theta-' + self.theta_kind(o, Z, g))
                    det['S1'] += 1
                else:
                    det['frozen blocker, free needer != o'] += 1
            else:
                det['frozen blocker, frozen needers only'] += 1
                k, ends = need_paths(pr, Bs, w)
                paths.add(-1 if k is None else k)
                if o in path_ends_all(pr, Bs, w): s1c = True
        if fz_free:
            cs = 'A-S1' if det['S1'] else 'A-z'
        elif fz_any:
            cs = 'B-S1c' if s1c else 'B'
        else:
            cs = 'C'
        return cs, det, thetas, sb, sorted(paths)

    # ------------------------------------------------------------ the structural certificates at any f
    def C1(self, sb):
        """Corollary 9.1: S1 shape, theta-ok; def(P') <= def(P) - 1 - iota for every admissible A ⊆ X ∪ {c}"""
        I, P, Bs = self.I, self.P, self.Bs
        out = []
        for o, X, c, x in sb:
            if not P.frozen[x] or not (P.N[o] & Bs[x]): continue
            g = Bs[x]; Z = X | (1 << c)
            if self.thr(o, Z, g): continue
            As = self.admissible(x, Z)
            assert As, ('Corollary 9.1: no admissible A', Bs)
            iota = 0 if any(P.N[i] & g for i in range(I.n) if i not in (o, x)) else 1
            for A in As:
                b2 = self.new(x, o, A)
                assert b2 in self.pr.D and self.pr.D[b2] <= self.D - 1 - iota, ('Corollary 9.1', Bs, b2)
            out.append((o, x, c))
        return out

    def C2(self, sb):
        """Corollary 11.1: the single blocker is a free z needing the good g of a frozen x; z holding g and x holding
        A ⊆ (J ∪ B_z) minus (X ∪ {c}) are not threatened; e* = 0 (no counted good in N_x(A))"""
        I, P, Bs = self.I, self.P, self.Bs
        out = []
        for o, X, c, z in sb:
            if P.frozen[z]: continue
            cnt = counted(P, o, X); Y = X | (1 << c)
            for x in range(I.n):
                if not P.frozen[x] or not (P.N[z] & Bs[x]): continue
                g = Bs[x]
                if self.thr(z, Y, g): continue
                for A in self.admissible(x, (P.J | Bs[z]) & ~Y):
                    if self.thr(x, Y, A): continue
                    if any(Bs[w] & I.needs(x, A) for w in cnt): continue
                    b2 = self.new(x, z, A)
                    assert b2 in self.pr.D and self.pr.D[b2] <= self.D - 1, ('Corollary 11.1', Bs, b2)
                    out.append((o, x, z, c))
        return out

    def C3(self):
        """Corollary 8.2: x big-top frozen on its top g, z the only needer (free), L_x inside J ∪ B_z ∪ B_h, a safe
        bundle Z ⊇ L_x of x in P' with |Z| + 1 > V"""
        I, P, Bs = self.I, self.P, self.Bs
        pr = self.pr
        for x in range(I.n):
            if not P.frozen[x] or not bigtop(I, x): continue
            g = Bs[x]
            if max(I.sets[x], key=lambda q: I.v[x][q]) != next(bits(g)): continue
            L = I.R[x] & ~g
            nd = pr.needers(Bs, x)
            if len(nd) != 1 or P.frozen[nd[0]]: continue
            z = nd[0]
            for h in [None] + [h for h in P.free if h != z]:
                G = P.J | Bs[z] | (Bs[h] if h is not None else 0)
                if L & ~G: continue
                hs = [None]
                if h is not None:
                    hs = [mask(B) for k in range(3) for B in itertools.combinations(list(bits((G & ~L) & I.R[h])), k)
                          if (Bs[h] & ~mask(B)) and not (I.needs(h, mask(B)) & ~P.NA) and not (I.needs(h, mask(B)) & g)]
                for Bh in hs:
                    hold = {z: g}
                    if h is not None: hold[h] = Bh
                    W = G & ~(Bh or 0)
                    if pr.blockers(Bs, x, L, hold): continue
                    rest = list(bits(W & ~L)); bestZ = None
                    for k in range(len(rest), -1, -1):
                        for K in itertools.combinations(rest, k):
                            if not pr.blockers(Bs, x, L | mask(K), hold): bestZ = L | mask(K); break
                        if bestZ is not None: break
                    if pc(bestZ) + 1 <= self.V: continue
                    for A in self.admissible(x, L):
                        b2 = self.new(x, z, A, h, Bh)
                        assert b2 in pr.D and pr.D[b2] <= self.omega + 1 - pc(bestZ) and pr.D[b2] < self.D, \
                            ('Corollary 8.2', Bs, b2)
                    return [(x, z, h)]
        return []

    # ------------------------------------------------------------ the repairs
    def describe(self, B2, x, z, W, h, sb):
        I, P, Bs, pr = self.I, self.P, self.Bs, self.pr
        g = Bs[x]; A = B2[x]
        sbx = [t for t in sb if t[3] == x]
        blk = any(x in pr.blockers(Bs, o, X | (1 << c)) for o in self.best for X in pr.OWN[Bs][o][1]
                  for c in bits(P.J & ~X))
        exp = any(I.threat(x, P.W(o), P.bv[x]) for o in P.free)
        xr = 'SB' if sbx else ('BL' if blk else ('EX' if exp else '-'))
        src = ''.join(sorted(set(('J' if P.J >> q & 1 else ('Z' if Bs[z] >> q & 1 else 'H')) for q in bits(A))))
        hk = '-'
        if h is not None:
            gave = Bs[h] & ~B2[h]; took = B2[h] & ~Bs[h]
            hk = 'gives%d' % pc(gave)
            if gave & I.R[x] & ~g: hk += '/Lx'
            if took & Bs[z]: hk += '/takesZ'
            elif took: hk += '/takesJ'
        best2 = pr.best(B2); who = set()
        for o2 in best2:
            who.add('x' if o2 == x else ('h' if o2 == h else ('O*' if o2 in self.best else 'O')))
        zb = 'z=best' if z in self.best else 'z'
        nz = 'z-only' if pr.needers(Bs, x) == [z] else 'needers-%d' % len(pr.needers(Bs, x))
        path, cyc, needp = chain_shape(P, pr.PA[B2], x, z, W)
        return {'x': x, 'z': z, 'h': h, 'W': W, 'k': len(path) - 2, 'cyc': cyc, 'needp': needp,
                'xrole': xr, 'zb': zb, 'nz': nz, 'src': src or '0', 'hk': hk,
                'best2': ''.join(sorted(who)), 'def2': pr.D[B2], 'Bs2': lst(B2)}


def edge_kind(P, P2):
    """'t3', 't3c', 't4' or None for a move between min-frozen states (the (T3⁺) and (T4) tests of k4/f2_lib.py, without
    the shape computation; both keep NA)"""
    if P.NA != P2.NA: return None
    tp = t3plus(P, P2)
    if tp is not None: return 't3' if not tp[2] else 't3c'
    n = P.I.n
    ch = [i for i in range(n) if P.Bs[i] != P2.Bs[i]]
    if len(ch) >= 2 and all(P.frozen[i] and P2.frozen[i] for i in ch) \
            and sorted(P.Bs[i] for i in ch) == sorted(P2.Bs[i] for i in ch):
        return 't4'
    return None


def keygraph(pr):
    """per key κ with def*(κ) > 0: (some state of κ has a (T3) or (T4) move (RT4's edges) to some state of a key with a
    smaller def*, the same with (T3⁺) or (T4) moves (R_C's edges)): DL on the key graph, k4/dl13.md §2.3, Remark"""
    out = {}
    lower = {}
    for k, states in pr.bykey.items():
        ds = pr.dstar[k]
        if ds <= 0: continue
        if ds not in lower:
            lower[ds] = [B2 for B2 in pr.mp if pr.dstar[pr.key[B2]] < ds]
        rt4 = rc = False
        for Bs in states:
            P = pr.PA[Bs]
            for B2 in lower[ds]:
                kd = edge_kind(P, pr.PA[B2])
                if kd in ('t3', 't4'): rt4 = True
                if kd in ('t3', 't3c', 't4'): rc = True
                if rt4 and rc: break
            if rt4 and rc: break
        out[k] = (rt4, rc)
    return out


def run_profile(d):
    pr = Prof(d, fmin=2)
    if not pr.ok: return None
    res = {'f': pr.I.f, 'n': pr.I.n, 'm': pr.I.m, 'states': [], 'def>0': 0, 'keys': keygraph(pr)}
    for Bs in pr.mp:
        if pr.D[Bs] <= 0: continue
        res['def>0'] += 1
        if not pr.t3_stage(Bs): continue
        st = State(pr, Bs)
        cs, det, thetas, sb, paths = st.case()
        t3 = pr.t3_moves(Bs)
        c1 = st.C1(sb); c2 = st.C2(sb); c3 = st.C3() if not (c1 or c2) else []
        reps = [st.describe(B2, x, z, W, h, sb) for B2, x, z, W, h in t3]
        res['states'].append({'Bs': lst(Bs), 'def': pr.D[Bs], 'V': st.V, 'omega': st.omega, 'best': st.best,
                              'frozen': [i for i in range(pr.I.n) if st.P.frozen[i]], 't4opt': pr.t4_optimal(Bs),
                              'case': cs, 'det': dict(det), 'thetas': sorted(thetas), 'paths': paths,
                              'C1': bool(c1), 'C2': bool(c2), 'C3': bool(c3), 'reps': reps})
    return res


def sig(r):
    """coarse signature of a repair: chain length, x's role, z a best owner or not, helper or not, new best owners"""
    return 'k=%d%s %s %s %s best\'=%s' % (r['k'], '+cyc' if r['cyc'] else '', r['xrole'], r['zb'],
                                         'h' if r['h'] is not None else '-', r['best2'])


def main(argv):
    if not argv: print(__doc__); return
    srcs = [a for a in argv if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in argv if a.startswith('--'))
    print('# command: python3 k4/f2_shapes.py ' + ' '.join(argv), flush=True)
    items = collect(srcs, opt)
    print('# distinct profiles read: %d' % len(items), flush=True)
    fo = gzip.open(opt['out'], 'wt') if 'out' in opt else None
    cnt = collections.Counter(); ex = {}
    for d, label in items:
        res = run_profile(d)
        cnt['profiles'] += 1
        if res is None: continue
        cnt['profiles f>=2, omega>=1'] += 1
        cnt['profiles f=%d n=%d' % (res['f'], res['n'])] += 1
        cnt['def>0 states'] += res['def>0']
        for k, (rt4, rc) in res['keys'].items():
            cnt['keys def*>0'] += 1
            if not rt4: cnt['key graph: no single T3/T4 edge to a smaller def* (RT4)'] += 1
            if not rc:
                cnt['KEY-GRAPH FAILURE: no single T3+/T4 edge to a smaller def* (R_C)'] += 1
                print('KEYFAIL', label, json.dumps(d), k, flush=True)
        for s in res['states']:
            cnt['T3-stage'] += 1; cnt['T3-stage f=%d' % res['f']] += 1
            tag = (res['n'], res['m'])

            def note(key):
                cur = ex.get(key)
                if cur is None or tag < cur[0]: ex[key] = (tag, label, d, s['Bs'])
            cnt['case ' + s['case']] += 1; note('case ' + s['case'])
            if s['case'] == 'A-S1':
                cnt['case A-S1 thetas ' + '/'.join(s['thetas'])] += 1; note('case A-S1 thetas ' + '/'.join(s['thetas']))
            if s['case'].startswith('B'):
                cnt['case %s, frozen agents on the shortest need paths %s' % (s['case'], s['paths'])] += 1
            if not s['t4opt']: cnt['T3-stage not T4-optimal'] += 1
            kinds = set('t3' if r['k'] == 0 else 't3c' for r in s['reps'])
            if not s['reps']:
                cnt['FAILURE of DL_RC (T3 stage, no improving T3+ move)'] += 1
                print('FAILURE', label, json.dumps(d), s['Bs'], flush=True)
            elif 't3' not in kinds:
                cnt['DL_RT4 fails (only chains, W != {}) | case %s' % s['case']] += 1; note('chain only, case ' + s['case'])
                print('CHAINONLY', label, json.dumps(d), s['Bs'], flush=True)
            cert = 'C1' if s['C1'] else ('C2' if s['C2'] else ('C3' if s['C3'] else 'none'))
            cnt['cert %s | case %s' % (cert, s['case'])] += 1
            if cert == 'none': note('uncertified case ' + s['case'])
            xr = sorted(set(r['xrole'] for r in s['reps'] if r['k'] == 0))
            cnt['case %s | x roles of the plain T3 repairs %s' % (s['case'], '/'.join(xr) or '(none)')] += 1
            if s['reps'] and all(r['h'] is not None for r in s['reps']):
                cnt['case %s | every repair has a helper' % s['case']] += 1
            for sg in sorted(set(sig(r) for r in s['reps'])): cnt['repair sig | case %s | %s' % (s['case'], sg)] += 1
            if fo:
                fo.write(json.dumps(dict(s, src=label, sets=d['sets'], vals=d['vals'], m=d['m'], f=res['f']),
                                    separators=(',', ':')) + '\n')
    if fo: fo.close()
    for k in sorted(cnt): print('%-100s %d' % (k, cnt[k]))
    for k in sorted(ex):
        tag, label, d, Bs = ex[k]
        print('smallest %-40s n=%d m=%d %s sets=%s vals=%s P=%s' % (k, tag[0], tag[1], label, d['sets'], d['vals'], Bs))
    print('# done')
    sys.stdout.flush()


if __name__ == '__main__':
    main(sys.argv[1:])
