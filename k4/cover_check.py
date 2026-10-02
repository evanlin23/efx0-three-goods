#!/usr/bin/env python3
"""COVER (f = 1) and COVER⁺ (f >= 2) on data: one checker for both statements (workstream compute/k4-cover). EVIDENCE
tooling.

The statements (DL on the key graph, Lean on main: EFX/KeyFrame.lean, EFX/MovesC.lean, follows from them):
  COVER   (k4/sx.md §5 on proof/k4-sx, PR #80; K4.SX.COVER): at some Z′-maximum Q (a configuration maximizing (r′, Λ′))
          of every key κ = (g, x) with def*(κ) > 0 and f = 1, one of Lemmas A, B (threat path length 1), B′ (length 1),
          C, C′ applies at P_Q with its exact hypotheses (B′: X″ contains a pair for x and (H_B′); C: (H); C′: (H′)).
          Lemma C's τ₁ need not be a leaf (k4/sx.md §3); PR #80's tool tests leaves only, so lemma_c_nonleaf below adds
          the θ-b terminals that are not leaves, with the same construction and assertions.
  COVER⁺  (k4/f2.md §5, §7 on proof/k4-f2, PR #82; the hypothesis of Theorem Z′⁺): for every strict profile with f >= 2
          and ω >= 1, every key κ with def*(κ) > 0 has a maximum Q of (r′, Λ′) at which Lemma A⁺ (any chain length j),
          Lemma B⁺ (threat path length 1), Lemma C⁺ or Lemma C′⁺ (any need path length k) applies at P_Q.

The lemma tests are the proof workstreams' own, imported unchanged and called once per maximum (the key's
configuration list restricted to that maximum), so every per-maximum verdict is theirs:
  f = 1:  PR #80's k4/sx_zprime.analyse_key: A (o a terminal leaf, not θ-b), B and B′ along every threat path from a
          non-leaf terminal (path length recorded), C (θ-b terminal leaf τ₁, another leaf owns; exact (H), and the
          structural (H*)), C′ (exactly two terminals; exact (H′), and (H′*)). Labels: A, B1, B1' / B1'x, C / Cx, C' / C'x
          (x = only the exact hypothesis holds), Bk... (paths of length >= 2, not part of COVER).
  f >= 2: PR #80's k4/sx_f2.analyse_key (A⁺ with its chain length j; B⁺ with chain j and threat path k; only k = 1 is
          part of COVER⁺) and PR #82's k4/f2_cc.test_max (C⁺ with need path length k; C′⁺ with the kind of the good q
          that pays: φ(x), φ(a_k) or φ(w) of a frozen w off the move; and 'full', a safe bundle of ω + 2 goods for some
          owner after the swap, which is Lemma H1 alone and not part of COVER⁺). f2_cc.test_max is run at every
          maximum here (k4/f2_cc.py runs it only where A⁺ and B⁺ fail).
Each library asserts every repair it claims: the new configuration is a configuration at its key, the owner is valid
with C = ∅ (or Lemma H1's count for C′ / C′⁺), and the image state of P_Q has deficit <= 0. Those deficits are Lemma
H1's (k4/dl2_classify.PA); with --verify (default) every min-frozen state's deficit is first checked against main's
k4/suite/model.py direct removal-only deficit, and with --indep=E every E-th profile's whole deficit table and every
key's def* are checked against k4/rt4_n5_indep.py (the PR #86 auditor's repo-free implementation). A failed library
assertion is caught and reported as LEMMA-ASSERT with the profile (it would refute a written lemma or its tool).

Per key with def* > 0: the maxima, at each the lemmas that apply, the key's verdict (covered, by which lemmas at
which maxima, or UNCOVERED). For an UNCOVERED key also: DLKey at the key (some state of κ has a (T3), (T3⁺) or (T4)
move to a min-frozen state whose key has smaller def*; the move classes found, with the least |W| and helper use),
and, as a diagnostic, k4/f2_cc.test_max's C⁺ / C′⁺ at f = 1.

Inputs: dumps of k4/sx_keygraph.py --dump, k4/sx_hunt.py or k4/cover_screen_run.py (gzip JSON lines with sets, vals,
m), JSON instance lists ({sets, vals, m}), or #53-style catalogues (records with core.sets, core.m, vals).
Output: gzip JSON lines, one per profile (the profile, f, ω, and one record per key with def* > 0); this file is also the
run's checkpoint: a rerun skips the profiles already in it. Summaries: k4/cover_summary.py.

usage: python3 k4/cover_check.py OUT.jsonl.gz [--part=i/N] [--fmin=F] [--fmax=F] [--max=N] [--no-verify]
           [--indep=E] [--dlk] [--nodedup] [--maxn=N] INPUT ...        (INPUT: DUMP.jsonl.gz | inst:LIST.json | catalog:FILE.json.gz)
--dlk computes DLKey at every key, not only at the uncovered ones. --nodedup keeps repeated profiles (as k4/f2_cc.py
counts them; k4/cover_summary.py --nodedup counts them too).

Requires PR #80's files in k4/suite/.cache/sx/ (k4/f2.md §8):
  for f in $(git ls-tree -r --name-only origin/proof/k4-sx | grep -v ^lean/); do mkdir -p k4/suite/.cache/sx/$(dirname $f);
    git show origin/proof/k4-sx:$f > k4/suite/.cache/sx/$f; done"""
import collections, gzip, itertools, json, os, re, sys, time, traceback

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, 'suite'))
if not os.path.exists(os.path.join(HERE, 'suite', '.cache', 'sx', 'k4', 'sx_zprime.py')):
    sys.exit('k4/suite/.cache/sx/ is missing PR #80\'s files; see the usage note in this file')
import f2_cc                                     # PR #82's tool (imports PR #80's sx_f2 from the cache)
from f2_lib import Prof, lst
from model import bits, pc, mask
from dl2_classify import INF
import sx_f2, sx_zprime                          # PR #80's tools, unchanged (k4/suite/.cache/sx/k4/)
from sx_keygraph import keyof

COVER = {'A', 'B1', "B1'", 'C', "C'"}
COVER_PLUS = {'A+', 'B+1', 'C+', "C'+"}
F1_LABEL = {'A': ('A', 1), 'B1': ('B1', 1), "B1'": ("B1'", 1), "B1'x": ("B1'", 0), 'C': ('C', 1), 'Cx': ('C', 0),
            "C'": ("C'", 1), "C'x": ("C'", 0), 'Bk-adj': ('Bk', 1), 'Bk-nonadj': ('Bk', 1), "Bk'": ("Bk'", 1),
            "Bk'x": ("Bk'", 0)}


class _NB(dict):
    """the neighbour table sx_zprime.gpm_check reads (only for the adjacency label of paths of length >= 2)"""
    def __missing__(self, k): return collections.defaultdict(set)


def one_max(I, c, fn, *args):
    """run a PR #80 analyse_key restricted to the single maximum c; returns its counter"""
    cnt = collections.Counter(); ex = collections.defaultdict(list)
    I.configs = lambda keys=None, _c=c: [_c]
    try:
        fn(*args[:2], cnt, ex, 0, *args[2:])
    finally:
        del I.configs
    return cnt


def lemma_c_nonleaf(kp, k, c):
    """Lemma C (k4/sx.md §3) with τ₁ a θ-b terminal that is not a leaf: the statement allows it ("τ₁ need not be a
    leaf"), PR #80's sx_zprime tests leaves only. The same construction and assertions as sx_zprime's C, over the
    terminals outside V. Returns 0 (no), 1 (with the structural (H*)), or 0.5 (with the exact (H) only)."""
    I = kp.I
    x = next(i for i in range(I.n) if k[i] is not None); g = k[x]; gm = 1 << g; om = I.omega
    free = [i for i in range(I.n) if i != x]
    U = {y: I.R[y] & ~gm for y in range(I.n)}
    Bs = tuple(gm if i == x else (c.Q[i] & U[i]) for i in range(I.n))
    P = kp.PA[Bs]
    X = {o: c.Q[o] | c.L for o in free}
    V = [o for o in free if not any(I.threat(y, X[o], c.hv(y)) for y in free if y != o)]
    T = [z for z in free if P.N[z] & gm]
    best = 0
    for t1 in T:
        if t1 in V or not (sx_zprime.bigtop_on(I, t1, g) and not (U[t1] & ~X[t1]) and om >= 2): continue
        key2 = tuple(g if i == t1 else None for i in range(I.n))
        for o in V:
            if o == t1: continue
            for pr in itertools.combinations(list(bits(X[t1])), 2):
                Px = mask(pr)
                if not (Px & U[x] and I.admissible(x, Px & U[x], U[x])): continue
                if I.val(x, Px) < I.val(x, U[x] & ~Px) or not Px & U[t1]: continue
                Y = c.Q[o] | (X[t1] & ~Px)
                hstar = not any(I.R[y] & c.Q[t1] & ~Px for y in free if y not in (o, t1))
                if any(I.threat(y, Y, c.hv(y)) for y in free if y not in (o, t1)): continue      # (H)
                Q2 = dict(c.Q); del Q2[t1]; Q2[x] = Px
                c2 = sx_zprime.M.Config(I, key2, Q2)
                assert key2 in kp.K and c2.owner(o) == 0, ('Lemma C (non-leaf tau1) failed', kp.d, k, repr(c), t1, o, Px)
                b2 = list(Bs); b2[t1] = gm; b2[x] = Px & U[x]; b2 = tuple(b2)
                assert b2 in kp.S and kp.D[b2] <= 0, 'Lemma C (non-leaf tau1): the T3 image'
                best = max(best, 1 if hstar else 0.5)
    return best


def f1_lemmas(kp, k, c):
    cnt = one_max(kp.I, c, sx_zprime.analyse_key, kp, k, _NB())
    cases = [key.split(' cases ', 1)[1] for key in cnt if ' cases ' in key]
    assert len(cases) == 1
    raw = [] if cases[0] == 'none' else cases[0].split(',')
    lem = {}; detail = {'raw': sorted(raw)}
    for r in raw:
        if r in F1_LABEL:
            name, structural = F1_LABEL[r]
            lem[name] = max(lem.get(name, 0), structural)
    cn = lemma_c_nonleaf(kp, k, c)
    if cn:
        detail['C with a non-leaf tau1'] = 'structural (H*)' if cn == 1 else 'exact (H) only'
        lem['C'] = max(lem.get('C', 0), 1 if cn == 1 else 0)
    return lem, detail


def f2_lemmas(pr, kp, k, c, Bs, V, X):
    cnt = one_max(kp.I, c, sx_f2.analyse_key, kp, k)
    lem = {}; detail = {}
    for key, v in cnt.items():
        mm = re.match(r'A\+ applies, chain length j=(\d+)$', key)
        if mm and v: lem['A+'] = 1; detail.setdefault('A+ j', []).append(int(mm.group(1)))
        mm = re.match(r'B\+ applies, chain j=(\d+), path k=(\d+)$', key)
        if mm and v:
            j, kk = int(mm.group(1)), int(mm.group(2))
            lem['B+1' if kk == 1 else 'B+k'] = 1; detail.setdefault('B+ (j,k)', []).append((j, kk))
    applied, why = f2_cc.test_max(pr, c, Bs, V, X, collections.Counter(), None)
    for a in applied:
        if a[0] == 'C+':
            lem['C+'] = 1; detail.setdefault('C+ k', set()).add(a[1])
            detail.setdefault('C+ forms', set()).add('%s/%s/%s' % a[2:5])
        elif a[0] == "C'+":
            lem["C'+"] = 1; detail.setdefault("C'+ k", set()).add(a[1])
            for q in a[3].split('+'): detail.setdefault("C'+ q", set()).add(q)
            detail.setdefault("C'+ owner", set()).add(a[2])
        elif a[0] == 'full':
            lem['full'] = 1; detail.setdefault('full k', set()).add(a[1])
    for kk in list(detail):
        if isinstance(detail[kk], set): detail[kk] = sorted(detail[kk])
    return lem, detail


def dlkey(kp, k):
    """DLKey at k: every (T3), (T3⁺), (T4) move from a state of k to a min-frozen state with a smaller def*"""
    ds = kp.dstar[k]; out = collections.Counter(); ex = None
    for Bs in kp.K[k]:
        for b2, x, z, W, h in kp.t3plus_moves(Bs):
            k2 = keyof(kp.PA[b2])
            if kp.dstar[k2] >= ds: continue
            cl = ('T3' if not W else 'T3+|W|=%d' % len(W)) + ('' if h is None else '+helper')
            out[cl] += 1
            if ex is None or (len(W), h is not None) < ex[0]:
                ex = ((len(W), h is not None), cl, lst(Bs), lst(b2), kp.D[b2], kp.dstar[k2])
        if kp.I.f >= 2:
            for b2 in kp.t4_moves(Bs):
                k2 = keyof(kp.PA[b2])
                if kp.dstar[k2] < ds:
                    out['T4'] += 1
                    if ex is None: ex = ((99, 0), 'T4', lst(Bs), lst(b2), kp.D[b2], kp.dstar[k2])
    return {'holds': bool(out), 'moves': dict(out), 'example': ex[1:] if ex else None}


def keystr(k): return [None if g is None else g for g in k]


def check_profile(d, opt):
    pr = Prof(d, fmin=1)
    rec = {'sets': d['sets'], 'vals': d['vals'], 'm': d['m']}
    if 'src' in d: rec['src'] = d['src']
    if not pr.ok:
        rec.update(f=getattr(pr.I, 'f', None), skip='f = 0 or omega <= 0'); return rec
    I = pr.I
    rec.update(n=I.n, f=I.f, omega=I.omega)
    if not opt['fmin'] <= I.f <= opt['fmax']:
        rec['skip'] = 'f outside the range'; return rec
    if opt['verify']:
        for Bs in pr.mp:
            ref = I.deficit(Bs)
            assert pr.D[Bs] == (INF if ref is None else ref), ('deficit mismatch (dl2_classify vs model.py)', lst(Bs))
    kp = f2_cc.keyprofile(pr)
    if opt.get('indep_now'):
        rec['indep'] = indep_check(d, kp)
    keys = []
    for k in kp.K:
        if kp.dstar[k] <= 0: continue
        kr = {'key': keystr(k), 'dstar': kp.dstar[k], 'states': len(kp.K[k]), 'maxima': []}
        try:
            for c, Bs, V, X in f2_cc.maxima(kp, k):
                mr = {'Q': repr(c).split('Q=', 1)[1].rstrip(')'), 'defPQ': kp.D[Bs], 'leaves': V}
                if I.f == 1: lem, det = f1_lemmas(kp, k, c)
                else: lem, det = f2_lemmas(pr, kp, k, c, Bs, V, X)
                mr['lemmas'] = lem; mr['detail'] = det
                kr['maxima'].append(mr)
        except AssertionError as e:
            kr['assert'] = repr(e.args)[:2000]; kr['trace'] = traceback.format_exc()[-1500:]
        target = COVER if I.f == 1 else COVER_PLUS
        cov = sorted(set(l for mr in kr['maxima'] for l in mr['lemmas'] if l in target))
        kr['cover'] = cov
        kr['covered'] = bool(cov)
        kr['maxima_covered'] = sum(1 for mr in kr['maxima'] if set(mr['lemmas']) & target)
        if not cov or opt['dlk'] or 'assert' in kr:
            kr['dlkey'] = dlkey(kp, k)
        if not cov and I.f == 1 and 'assert' not in kr:     # diagnostic: C⁺ / C′⁺ of k4/f2.md §5 at f = 1
            fb = set()
            for c, Bs, V, X in f2_cc.maxima(kp, k):
                applied, _ = f2_cc.test_max(pr, c, Bs, V, X, collections.Counter(), None)
                fb |= set(a[0] for a in applied)
            kr['f1_fallback_Cplus'] = sorted(fb)
        keys.append(kr)
    rec['keys'] = keys
    return rec


# ---------------------------------------------------------------------------- second implementation of the deficits
def indep_check(d, kp):
    """k4/rt4_n5_indep.py (no repository code) on the profile: its f, its min-frozen states and deficits, and its def*
    per key, compared with kp's; returns a short verdict"""
    import rt4_n5_indep as R
    ns = R.analyse(d['sets'], d['vals'], d['m'])
    assert ns['f'] == kp.I.f, ('indep: f', ns['f'], kp.I.f)
    Dn = {tuple(mask(B) for B in P): v for P, v in ns['D'].items()}
    assert set(Dn) == set(kp.D), ('indep: the min-frozen class differs', len(Dn), len(kp.D))
    for b, v in Dn.items():
        assert (INF if v == float('inf') else v) == kp.D[b], ('indep: deficit', lst(b), v, kp.D[b])
    return 'agree (%d states)' % len(Dn)


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
            for line in gzip.open(a, 'rt'):
                r = json.loads(line)
                out.append({'sets': r['sets'], 'vals': r['vals'], 'm': r['m'], 'src': r.get('src', os.path.basename(a)),
                            'f': r.get('f')})
    return out


def main(argv):
    if not argv: print(__doc__); return
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    rest = [a for a in argv if not a.startswith('--')]
    out, inputs = rest[0], rest[1:]
    o = {'fmin': int(opt.get('fmin', 1)), 'fmax': int(opt.get('fmax', 99)), 'verify': '--no-verify' not in argv,
         'dlk': '--dlk' in argv}
    indep = int(opt.get('indep', 0))
    part, nparts = map(int, opt.get('part', '0/1').split('/'))
    profs = read_inputs(inputs)
    seen = set(); uniq = []
    for i, d in enumerate(profs):                   # deduplicate (the dumps overlap), unless --nodedup
        kk = json.dumps([d['sets'], d['vals'], d['m']])
        if kk in seen and '--nodedup' not in argv: continue
        seen.add(kk); uniq.append((i, d))
    uniq = [(i, d) for i, d in uniq if d.get('f') is None or o['fmin'] <= d['f'] <= o['fmax']]
    if 'maxn' in opt: uniq = [(i, d) for i, d in uniq if len(d['sets']) <= int(opt['maxn'])]
    mine = uniq[part::nparts]
    if 'max' in opt: mine = mine[:int(opt['max'])]
    done = set()
    if os.path.exists(out):
        try:
            for line in gzip.open(out, 'rt'):
                try: done.add(json.loads(line)['i'])
                except ValueError: break
        except (EOFError, OSError, gzip.BadGzipFile):
            pass
    print('# command: python3 k4/cover_check.py ' + ' '.join(argv))
    print('# %d input records, %d distinct in range, part %d/%d: %d, already done %d' % (
        len(profs), len(uniq), part, nparts, len(mine), len(done & set(i for i, _ in mine))), flush=True)
    t0 = time.time(); cnt = collections.Counter()
    # a torn gzip member at the end cannot be appended to safely: rewrite the readable part first
    if done:
        good = []
        try:
            for line in gzip.open(out, 'rt'):
                try: good.append(json.loads(line))
                except ValueError: break
        except (EOFError, OSError, gzip.BadGzipFile):
            pass
        with gzip.open(out + '.tmp', 'wt') as fo:
            for r in good: fo.write(json.dumps(r, separators=(',', ':')) + '\n')
        os.replace(out + '.tmp', out)
    fo = gzip.open(out, 'at')
    for j, (i, d) in enumerate(mine):
        if i in done: continue
        o['indep_now'] = indep and j % indep == 0
        rec = check_profile(d, o)
        rec['i'] = i
        fo.write(json.dumps(rec, separators=(',', ':')) + '\n')
        if j % 20 == 0: fo.flush()
        for kr in rec.get('keys', []):
            cnt['keys f=%d' % rec['f']] += 1
            if 'assert' in kr: cnt['LEMMA-ASSERT'] += 1; print('LEMMA-ASSERT', json.dumps(rec)[:3000], flush=True)
            if not kr['covered']:
                cnt['UNCOVERED f=%d' % rec['f']] += 1
                print('UNCOVERED', json.dumps({x: rec[x] for x in ('sets', 'vals', 'm', 'f')}), json.dumps(kr)[:3000],
                      flush=True)
        cnt['profiles'] += 1
    fo.close()
    for k in sorted(cnt): print('%-30s %d' % (k, cnt[k]))
    print('# time %.1f s' % (time.time() - t0))


if __name__ == '__main__':
    main(sys.argv[1:])
