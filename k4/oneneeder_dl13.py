#!/usr/bin/env python3
"""k4/oneneeder.md on the T1-stuck dumps of k4/dl13.md §1 (results/k4_dl13_stuck/stuck_*.jsonl.gz). EVIDENCE tooling.

The dumps are deduplicated to their strict profiles; those with f = 1 and omega >= 1 are used.

  xcheck   per profile, the number of one-needer T3-stage states and of those where Corollary 8.2 applies with at most
           one helper, computed twice: by k4/dl13_stuck.py's Profile with k4/dl13_lemmas.py's C3 test (Python, the model
           of k4/dl13.md), and by k4/oneneeder.c (through k4/oneneeder_run.py). Every mismatch is printed.
  counts   at every state with def > 0, one needer z of the frozen good, x big-top and an x-alone triple (on
           k4/oneneeder_check.py): per state, whether Proposition C or D applies at some triple and whether Corollary 8.2
           applies (def = 1), split into T3-stage / T1-stuck but not T3-stage / not T1-stuck; per triple with owner
           o != z, whether o has an escape (Proposition D). These are the counts of attempts/k4-oneneeder-escape-t1.md
           and k4/oneneeder.md §8.

usage: python3 k4/oneneeder_dl13.py xcheck|counts"""
import collections, glob, gzip, itertools, json, os, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, 'suite'))
from model import bits, pc, mask

FILES = sorted(glob.glob(os.path.join(ROOT, 'results', 'k4_dl13_stuck', 'stuck_*.jsonl.gz')))


def profiles():
    seen = set()
    for fn in FILES:
        for l in gzip.open(fn, 'rt'):
            r = json.loads(l)
            key = json.dumps([r['sets'], r['vals']])
            if key in seen: continue
            seen.add(key)
            yield {'id': r.get('src'), 'sets': r['sets'], 'vals': r['vals'], 'm': r['m']}


def xcheck():
    from dl13_stuck import Profile
    from dl13_lemmas import Ctx
    import oneneeder_run as R
    R.build()
    insts = []
    for d in profiles():
        pr = Profile(d)
        if not pr.ok or pr.I.f != 1: continue
        keymin = {}
        for B in pr.mp:
            x = pr.PA[B].frozen.index(True); k = (x, B[x])
            keymin[k] = min(keymin.get(k, 10 ** 9), pr.D[B])
        t3s1 = c3 = 0
        for B in pr.mp:
            if pr.D[B] <= 0: continue
            P = pr.PA[B]; x = P.frozen.index(True)
            if pr.D[B] != keymin[(x, B[x])]: continue
            if len([i for i in range(pr.I.n) if P.N[i] & B[x]]) != 1: continue
            t3s1 += 1
            if Ctx(pr, B).C3(): c3 += 1
        d['py'] = (t3s1, c3); insts.append(d)
    inp = ''.join(R.block(d['sets'], d['m'], [[dict(zip(S, V))] for S, V in zip(d['sets'], d['vals'])], k, 0)
                  for k, d in enumerate(insts))
    bad = 0; tot = {}
    for b in R.run(inp, ['-r0']):
        d = insts[b['tag']]; R.add(tot, b['K'])
        c = (b['K']['t3stage_1needer'], b['K']['c3'])
        if c != d['py']:
            bad += 1; print('MISMATCH', d['id'], 'C', c, 'Python', d['py'])
    print('profiles (f = 1, omega >= 1):', len(insts))
    print('one-needer T3-stage states: Python %d, C %d; Corollary 8.2 (<= 1 helper): Python %d, C %d' % (
        sum(d['py'][0] for d in insts), tot.get('t3stage_1needer', 0), sum(d['py'][1] for d in insts), tot.get('c3', 0)))
    print('C totals:', tot)
    print('mismatches', bad)


def counts():
    import oneneeder_check as C
    st = collections.Counter(); tr = collections.Counter()
    for d in profiles():
        pr = C.Prof(d)
        if not pr.ok: continue
        I = pr.I
        for Bs, s in pr.st.items():
            if s['def'] <= 0: continue
            x = s['x']; gm = Bs[x]; g = next(bits(gm))
            nd = [i for i in range(I.n) if s['N'][i] & gm]
            if len(nd) != 1 or not C.bigtop_on(I, x, g): continue
            z = nd[0]; L = I.R[x] & ~gm; J = s['J']; hv = s['hv']
            t3 = s['def'] == pr.keymin[(x, gm)]
            stuck = True
            for y in range(I.n):
                if s['F'][y]: continue
                for k in (1, 2):
                    for S in itertools.combinations(list(bits((Bs[y] | J) & I.R[y])), k):
                        S = mask(S)
                        if S == Bs[y] or I.needs(y, S) & ~s['NA']: continue
                        b2 = list(Bs); b2[y] = S; b2 = tuple(b2)
                        if pr.st[b2]['def'] < s['def']: stuck = False
            cat = 'T3-stage' if t3 else ('T1-stuck, not T3-stage' if stuck else 'not T1-stuck')
            trip = []
            for o, (val, arg) in s['own'].items():
                if val != s['V']: continue
                for X, u in arg:
                    for c in bits(J & ~X):
                        Y = X | (1 << c)
                        if I.threat(x, Y, hv[x]) and not any(I.threat(w, Y, hv[w]) for w in range(I.n) if w not in (o, x)):
                            trip.append((o, X, u, c))
            if not trip: continue
            # per triple with o != z: an escape (Proposition D)
            for o, X, u, c in trip:
                if o == z: continue
                Y = X | (1 << c); Rest = (J & ~Y) | Bs[z]
                reg = list(bits((Y | Rest) & ~L & I.R[o] & ~gm))
                esc = False
                for k in (1, 2):
                    for S in itertools.combinations(reg, k):
                        S = mask(S)
                        if pc(S & Y) > 1 or I.needs(o, S): continue
                        helper = bool(Bs[o] & ~S)
                        if not helper and not (S == Bs[o] and not (L & Bs[o]) and pc(S) == 1): continue
                        if I.threat(o, Y & ~S, I.val(o, S)): continue
                        esc = True
                tr[(cat, 'def %d' % s['def'], 'escape' if esc else 'no escape')] += 1
            # per state: Proposition C or D at some triple; Corollary 8.2 with at most one helper
            if s['def'] == 1:   # Propositions C, D and Corollary 8.2's test assert their conclusions (def(P') <= 0)
                rule = 'Prop. C or D' if C.rules(pr, Bs, x, z, g, L, trip) else 'neither'
                c3 = 'Cor. 8.2' if C.c3(pr, Bs, x, z, g, L) else 'no Cor. 8.2'
            else:
                rule = c3 = '-'
            st[(cat, 'def %d' % s['def'], rule, c3)] += 1
    print('states (def > 0, one needer, x big-top, an x-alone triple):')
    for k in sorted(st): print('  %-80s %d' % (' / '.join(k), st[k]))
    print('triples with owner o != z:')
    for k in sorted(tr): print('  %-80s %d' % (' / '.join(k), tr[k]))


if __name__ == '__main__':
    T0 = time.time()
    print('# command: python3 k4/oneneeder_dl13.py ' + ' '.join(sys.argv[1:]), flush=True)
    {'xcheck': xcheck, 'counts': counts}[sys.argv[1]]()
    print('[%.0f s]' % (time.time() - T0))
