#!/usr/bin/env python3
"""Theorem ZMOVE on data: the uniform repair statement, at EVERY key with def* > 0 (workstream compute/k4-zmove).
EVIDENCE tooling.

The statement (the coordinator's; ZMOVE ⟹ DL on the key graph ⟹ TARGET₄, Lean on main): for every strict profile of
every connected k = 4 core with f >= 1 and ω >= 1, and every key κ with def*(κ) > 0, at least one of
  (Z)  at SOME Z′-maximum Q of κ, one (T3⁺) move from P_Q with at most one helper (the helper gives up a good of its
       base) reaches a min-frozen state P′ with def(P′) <= 0;
  (T4) κ has a (T4) edge to a key with smaller def* (from some state of κ).
Definitions used (k4/sx.md §1–2, §6 Lemma F⁺, and k4/c4min_reduce.md §2 on main):
  - a configuration at κ = (𝒩, φ): the frozen agents hold their goods φ(w); every free y holds a pair Q_y ⊆ M ∖ 𝒩, the
    pairs disjoint, with admissible part H_y = Q_y ∩ U_y (U_y = R_y ∖ 𝒩); the pool L is the rest of M ∖ 𝒩;
  - a Z′-maximum maximizes (r′, Λ′) lexicographically: r′ = #{free y : v_y(Q_y) >= v_y(U_y ∖ Q_y)} (robust),
    Λ′ = Σ_free ℓ_y(H_y) with ℓ_y(S) = #{T ⊆ R_y : v_y(T) < v_y(S)} (k4/sx.md §2);
  - P_Q: frozen w on {φ(w)}, free y on H_y (a min-frozen state of κ, Lemma 0);
  - (T3⁺): main's lean/EFX/MovesC.lean MoveT3plus (ledger K4.DL2.RC): NA′ = NA; exactly one changed x frozen in P and
    free in P′; exactly one changed z free in P and frozen in P′, B′_z = {g′} with g′ ∈ N_z(B_z); the changed agents
    free in both are at most one (the helper) and it gives up a good of its base; W = the changed agents frozen in both;
    the bases of W ∪ {z} in P′ are those of W ∪ {x} in P;
  - (T4): every changed agent frozen in P and in P′, NA′ = NA.
The machinery is the one compute/k4-cover's k4/cover_check.py uses: main's k4/suite/model.py (𝒫 and the min-frozen
class), k4/dl2_classify.py (Lemma H1's deficit; --verify checks it against model.py's direct removal-only deficit),
PR #82's k4/f2_cc.maxima (the Z′-maxima, the configurations of model.Inst.configs) and PR #80's
KeyProfile.t3plus_moves / t4_moves (k4/suite/.cache/sx/k4/sx_keygraph.py: every (T3⁺) move with at most one helper,
generated and looked up among the min-frozen states). --indep=E compares every E-th profile with k4/zmove_indep.py (a
second implementation: k4/rt4_n5_indep.py's deficits, its own configurations, maxima and (T3⁺)/(T4) predicates).

Per key with def* > 0 the record has: the number of configurations and of maxima; per maximum P_Q, def(P_Q) and
best = the least def(P′) over the (T3⁺) moves (<= 1 helper) from P_Q ("inf" if none), with one best move (target, x,
z, W, helper) and the number of moves to def <= 0 split by kind; the MARGIN = min over maxima of best; t4 = the least
def* of a key reached by a (T4) edge from a state of κ (or null), t4edge = that value < def*(κ); pass = margin <= 0 or
t4edge. Diagnostics: margin_U, the margin over the maxima of (r′, Λ′_U) with the level ℓ over the subsets of U_y
instead of R_y (k4/c4min_reduce.md §2 allows any strictly increasing level), and margin_all, the least best over every
configuration at κ (with --all).

Inputs: gzip JSON lines with sets, vals, m (dumps of k4/sx_keygraph.py, k4/cover_screen_run.py, k4/cover_hunt.py, or
k4/cover_check.py outputs), inst:LIST.json ({sets, vals, m} records), catalog:FILE.json.gz (#53-style).
Output: gzip JSON lines, one per profile; also the run's checkpoint (a rerun skips the input positions already in it).
Summaries: k4/zmove_summary.py.

usage: python3 k4/zmove_check.py OUT.jsonl.gz [--part=i/N] [--fmin=F] [--fmax=F] [--max=N] [--maxn=N] [--minn=N]
           [--verify=E] [--indep=E] [--all] [--nodedup] INPUT ...
--verify=E checks Lemma H1's deficits against model.py on every E-th profile (default 1; 0 = never).

Requires PR #80's files in k4/suite/.cache/sx/ (as k4/cover_check.py):
  for f in $(git ls-tree -r --name-only origin/proof/k4-sx | grep -v ^lean/); do mkdir -p k4/suite/.cache/sx/$(dirname $f);
    git show origin/proof/k4-sx:$f > k4/suite/.cache/sx/$f; done"""
import collections, gzip, itertools, json, os, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, 'suite'))
if not os.path.exists(os.path.join(HERE, 'suite', '.cache', 'sx', 'k4', 'sx_keygraph.py')):
    sys.exit('k4/suite/.cache/sx/ is missing PR #80\'s files; see the usage note in this file')
import f2_cc                                     # PR #82's tool (imports PR #80's sx_keygraph from the cache)
from f2_lib import Prof, lst
from model import bits, pc, mask
from dl2_classify import INF
from sx_keygraph import keyof


def jv(x): return 'inf' if x is None or x >= INF else x


def levelU(I, y, S, U):
    """ℓ over the subsets of U_y (the diagnostic level of margin_U)"""
    s = I.val(y, S); gs = [g for g in I.sets[y] if U >> g & 1]
    return sum(1 for k in range(len(gs) + 1) for T in itertools.combinations(gs, k) if sum(I.v[y][g] for g in T) < s)


def best_from(kp, Bs, memo):
    """least def(P′) over the (T3⁺) moves (<= 1 helper) from Bs, with one best move and the kinds of the moves to <= 0"""
    if Bs in memo: return memo[Bs]
    best = INF; bm = None; kinds = collections.Counter()
    for b2, x, z, W, h in kp.t3plus_moves(Bs):
        d2 = kp.D[b2]
        if d2 <= 0:
            kinds[('T3' if not W else 'T3+W%d' % len(W)) + ('+h' if h is not None else '')] += 1
        if bm is None or d2 < best or (d2 == best and (len(W), h is not None) < (len(bm[3]), bm[4] is not None)):
            best = d2; bm = (b2, x, z, W, h)
    out = {'best': best, 'kinds': dict(kinds),
           'move': None if bm is None else {'to': lst(bm[0]), 'x': bm[1], 'z': bm[2], 'W': list(bm[3]), 'helper': bm[4]}}
    memo[Bs] = out
    return out


def config_states(kp, k):
    """every configuration at k with (r′, Λ′, Λ′_U) and its P_Q"""
    I = kp.I
    free = [i for i in range(I.n) if k[i] is None]
    Nm = mask(k[i] for i in range(I.n) if k[i] is not None)
    U = {y: I.R[y] & ~Nm for y in range(I.n)}
    out = []
    for c in I.configs([k]):
        Bs = tuple((1 << k[i]) if k[i] is not None else (c.Q[i] & U[i]) for i in range(I.n))
        rob = sum(1 for y in free if c.robust(y))
        lam = sum(I.level(y, c.Q[y] & I.R[y]) for y in free)
        lamU = sum(levelU(I, y, c.Q[y] & U[y], U[y]) for y in free)
        out.append((c, Bs, rob, lam, lamU))
    return out


def t4_best(kp, k):
    """the least def* of a key reached by a (T4) edge from a state of k (other key), or None"""
    if kp.I.f < 2: return None
    best = None
    for Bs in kp.K[k]:
        for b2 in kp.t4_moves(Bs):
            k2 = keyof(kp.PA[b2])
            if k2 == k: continue
            if best is None or kp.dstar[k2] < best: best = kp.dstar[k2]
    return best


def check_profile(d, opt):
    pr = Prof(d, fmin=1)
    rec = {'sets': d['sets'], 'vals': d['vals'], 'm': d['m']}
    if 'src' in d: rec['src'] = d['src']
    if not pr.ok:
        rec.update(f=getattr(pr.I, 'f', None), skip='f = 0 or omega <= 0'); return rec, None
    I = pr.I
    rec.update(n=I.n, f=I.f, omega=I.omega)
    if not opt['fmin'] <= I.f <= opt['fmax']:
        rec['skip'] = 'f outside the range'; return rec, None
    if opt.get('verify_now'):
        for Bs in pr.mp:
            ref = I.deficit(Bs)
            assert pr.D[Bs] == (INF if ref is None else ref), ('deficit mismatch (dl2_classify vs model.py)', lst(Bs))
        rec['verified'] = 1
    kp = f2_cc.keyprofile(pr)
    memo = {}
    keys = []
    for k in sorted(kp.K, key=lambda k: [(-1 if g is None else g) for g in k]):
        ds = kp.dstar[k]
        if ds <= 0: continue
        cs = config_states(kp, k)
        assert cs, ('a key with no configuration', k)
        top = max((r, l) for _, _, r, l, _ in cs)
        topU = max((r, l) for _, _, r, _, l in cs)
        mx = [(c, Bs) for c, Bs, r, l, _ in cs if (r, l) == top]
        # the same maxima as f2_cc.maxima (PR #82), which k4/cover_check.py uses
        assert sorted(Bs for _, Bs, _, _ in f2_cc.maxima(kp, k)) == sorted(Bs for _, Bs in mx), ('maxima differ', k)
        kr = {'key': [g for g in k], 'dstar': ds, 'states': len(kp.K[k]), 'nconf': len(cs), 'maxima': []}
        margin = INF
        seen = set()
        for c, Bs in mx:
            assert Bs in kp.S and keyof(kp.PA[Bs]) == k, ('P_Q is not a min-frozen state of the key', k, lst(Bs))
            b = best_from(kp, Bs, memo)
            margin = min(margin, b['best'])
            if Bs in seen: continue                 # two maxima with the same P_Q (they differ in the pool part)
            seen.add(Bs)
            kr['maxima'].append({'PQ': lst(Bs), 'defPQ': jv(kp.D[Bs]), 'best': jv(b['best']), 'kinds': b['kinds'],
                                 'move': b['move']})
        kr['nmax'] = len(mx)
        kr['margin'] = jv(margin)
        mU = min(best_from(kp, Bs, memo)['best'] for c, Bs, r, _, l in cs if (r, l) == topU)
        kr['margin_U'] = jv(mU)
        if opt['all']:
            kr['margin_all'] = jv(min(best_from(kp, Bs, memo)['best'] for _, Bs, _, _, _ in cs))
        t4 = t4_best(kp, k)
        kr['t4'] = t4
        kr['t4edge'] = t4 is not None and t4 < ds
        kr['pass'] = margin <= 0 or kr['t4edge']
        keys.append(kr)
    rec['keys'] = keys
    return rec, kp


def compare_indep(d, rec):
    """k4/zmove_indep.py on the profile: f, and per key def*, the maxima's P_Q, the margin and the (T4) verdict"""
    import zmove_indep as Z
    res = Z.zmove(d['sets'], d['vals'], d['m'])
    assert res['f'] == rec['f'], ('indep: f', res['f'], rec['f'])
    mine = {tuple(kr['key']): kr for kr in rec['keys']}
    theirs = {k: v for k, v in res['keys'].items() if v['dstar'] > 0}
    assert set(mine) == set(theirs), ('indep: the keys with def* > 0 differ', sorted(map(str, mine)), sorted(map(str, theirs)))
    for k, kr in mine.items():
        t = theirs[k]
        assert kr['dstar'] == jv(t['dstar']), ('indep: def*', k, kr['dstar'], t['dstar'])
        assert sorted(map(json.dumps, (m['PQ'] for m in kr['maxima']))) == sorted(map(json.dumps, t['PQs'])), \
            ('indep: the maxima differ', k)
        assert kr['margin'] == jv(t['margin']), ('indep: margin', k, kr['margin'], t['margin'])
        assert kr['margin_U'] == jv(t['margin_U']), ('indep: margin_U', k, kr['margin_U'], t['margin_U'])
        assert kr['t4edge'] == t['t4edge'], ('indep: t4 edge', k, kr['t4edge'], t['t4edge'])
        assert kr['nconf'] == t['nconf'], ('indep: number of configurations', k, kr['nconf'], t['nconf'])
    return 'agree (%d keys)' % len(mine)


# ---------------------------------------------------------------------------- inputs
def read_inputs(args):
    out = []
    for a in args:
        if a.startswith('inst:'):
            fn = a[5:]
            for i, e in enumerate(json.load(gzip.open(fn, 'rt') if fn.endswith('.gz') else open(fn))):
                out.append({'sets': e['sets'], 'vals': e['vals'], 'm': e.get('m') or 1 + max(map(max, e['sets'])),
                            'src': '%s:%s' % (os.path.basename(fn), e.get('id', i))})
        elif a.startswith('catalog:'):
            fn = a[8:]
            for r in json.load(gzip.open(fn, 'rt'))['records']:
                out.append({'sets': r['core']['sets'], 'vals': r['vals'], 'm': r['core']['m'],
                            'src': '%s:%s' % (os.path.basename(fn), r.get('prof'))})
        else:
            op = gzip.open if a.endswith('.gz') else open
            with op(a, 'rt') as fh:
                try:
                    for line in fh:
                        if not line.strip(): continue
                        r = json.loads(line)
                        if 'sets' not in r: continue
                        out.append({'sets': r['sets'], 'vals': r['vals'], 'm': r.get('m') or 1 + max(map(max, r['sets'])),
                                    'src': r.get('src', os.path.basename(a)), 'f': r.get('f')})
                except (EOFError, ValueError, OSError):
                    pass                      # a torn end of a checkpoint
    return out


def read_done(out):
    done = []
    if os.path.exists(out):
        try:
            for line in gzip.open(out, 'rt'):
                try: done.append(json.loads(line))
                except ValueError: break
        except (EOFError, OSError, gzip.BadGzipFile):
            pass
    return done


def main(argv):
    if not argv: print(__doc__); return
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    rest = [a for a in argv if not a.startswith('--')]
    out, inputs = rest[0], rest[1:]
    o = {'fmin': int(opt.get('fmin', 1)), 'fmax': int(opt.get('fmax', 99)), 'all': '--all' in argv}
    verify = int(opt.get('verify', 1)); indep = int(opt.get('indep', 0))
    part, nparts = map(int, opt.get('part', '0/1').split('/'))
    profs = read_inputs(inputs)
    seen = set(); uniq = []
    for i, d in enumerate(profs):
        kk = json.dumps([d['sets'], d['vals'], d['m']])
        if kk in seen and '--nodedup' not in argv: continue
        seen.add(kk); uniq.append((i, d))
    uniq = [(i, d) for i, d in uniq if d.get('f') is None or o['fmin'] <= d['f'] <= o['fmax']]
    if 'maxn' in opt: uniq = [(i, d) for i, d in uniq if len(d['sets']) <= int(opt['maxn'])]
    if 'minn' in opt: uniq = [(i, d) for i, d in uniq if len(d['sets']) >= int(opt['minn'])]
    mine = uniq[part::nparts]
    if 'max' in opt: mine = mine[:int(opt['max'])]
    good = read_done(out)
    done = set(r['i'] for r in good)
    print('# command: python3 k4/zmove_check.py ' + ' '.join(argv))
    print('# %d input records, %d distinct in range, part %d/%d: %d, already done %d' % (
        len(profs), len(uniq), part, nparts, len(mine), len(done & set(i for i, _ in mine))), flush=True)
    if good:                     # rewrite the readable part (a torn gzip member cannot be appended to)
        with gzip.open(out + '.tmp', 'wt') as fo:
            for r in good: fo.write(json.dumps(r, separators=(',', ':')) + '\n')
        os.replace(out + '.tmp', out)
    t0 = time.time(); cnt = collections.Counter(); hist = collections.Counter()
    fo = gzip.open(out, 'at')
    for j, (i, d) in enumerate(mine):
        if i in done: continue
        o['verify_now'] = verify and j % verify == 0
        try:
            rec, kp = check_profile(d, o)
        except AssertionError as e:
            rec = {'sets': d['sets'], 'vals': d['vals'], 'm': d['m'], 'src': d.get('src'), 'assert': repr(e.args)[:2000]}
            print('ASSERT', json.dumps(rec), flush=True); cnt['ASSERT'] += 1
        if indep and j % indep == 0 and 'keys' in rec:
            try:
                rec['indep'] = compare_indep(d, rec); cnt['indep agree'] += 1
            except AssertionError as e:
                rec['indep'] = 'DIFFER ' + repr(e.args)[:1500]; cnt['INDEP-DIFFER'] += 1
                print('INDEP-DIFFER', json.dumps({x: rec[x] for x in ('sets', 'vals', 'm')}), rec['indep'], flush=True)
        rec['i'] = i
        fo.write(json.dumps(rec, separators=(',', ':')) + '\n')
        if j % 20 == 0: fo.flush()
        for kr in rec.get('keys', []):
            cnt['keys f=%d' % rec['f']] += 1
            hist[kr['margin']] += 1
            if not kr['pass']:
                cnt['ZMOVE-FAIL f=%d' % rec['f']] += 1
                print('ZMOVE-FAIL', json.dumps({x: rec[x] for x in ('sets', 'vals', 'm', 'f')}), json.dumps(kr)[:3000],
                      flush=True)
            elif kr['margin'] == 'inf' or kr['margin'] > 0:
                cnt['passes by T4 only'] += 1
        cnt['profiles'] += 1
    fo.close()
    for k in sorted(cnt): print('%-30s %d' % (k, cnt[k]))
    print('margin histogram (this run):', dict(sorted(hist.items(), key=lambda t: (isinstance(t[0], str), t[0]))))
    print('# time %.1f s' % (time.time() - t0))


if __name__ == '__main__':
    main(sys.argv[1:])
