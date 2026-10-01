#!/usr/bin/env python3
"""T1-stuck states of DL13 and their (T3) repairs (workstream proof/k4-dl13; k4/dl13.md).

For every strict profile in the input whose fewest frozen agents is f >= 1 (with omega >= 1), and every min-frozen
P in the space 𝒫 of k4/c4x.md §1 with def(P) > 0, decide whether P is *T1-stuck*: no (T1) move (a re-base of one
free agent y to B' ⊆ (B_y ∪ J) ∩ R_y, |B'| <= 2, B' != B_y, N_y(B') ⊆ NA(P), k4/dl2.md Lemma 1(c)) gives a P' with
def(P') < def(P). For each T1-stuck P, list every (T3) move that lowers the deficit: a min-frozen P' with
def(P') < def(P) obtained by a role swap with a needer (a frozen x with base {g} unfreezes, a free z with g ∈ N_z
takes {g}) plus at most one helper (a free agent that gives up at least one good of its base), the needed set
unchanged (k4/dl2.md §3, relation R_13; the shape test is k4/dl2_relations.py's). A T1-stuck P without such a move
refutes DL13 (K4.DL2.T13). For every def > 0 state the tool also records whether P is T4-optimal (the need digraph
on the frozen agents is acyclic: no frozen rotation, k4/dl13.md Lemma 12) and the (T4) moves that lower the deficit
(the frozen agents' goods permuted among them, all staying frozen, NA unchanged; the coordinator's R_134), and
asserts Lemma 12 (a frozen rotation in which every moved agent gains never raises the deficit). Printed: DL13-FAILS
(T1-stuck, no (T3) repair, not T4-optimal), FAILURE-OPT (the same at a T4-optimal state: it refutes DL13-opt of
k4/dl13.md §2.2) and FAILURE-134 (no (T1), (T3) or (T4) repair).

Deficits are k4/dl2_classify.PA.deficit (Lemma H1 of k4/hall.md); --check also asserts equality with
k4/suite/model.py's direct removal-only deficit.

usage: python3 k4/dl13_stuck.py suite [--out=FILE]
       python3 k4/dl13_stuck.py catalog FILE [--every=E] [--max=N] [--fmin=F] [--out=FILE]
       python3 k4/dl13_stuck.py certs FILE --rand=K [--seed=S] [--out=FILE]
       python3 k4/dl13_stuck.py tsv FILE [--out=FILE]     (compute/k4-dl13's n4_failures_*.tsv: file, sets, vals, m)
Output (--out, gzip JSON lines): one record per T1-stuck state with its profile and every improving (T3) move."""
import gzip, itertools, json, os, sys, collections

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, 'suite'))
import model as M
from model import bits, pc, mask
from dl2_classify import PA, INF, rebases, best_owners
from dl2_relations import shape, items_of


def is_t3(s):
    """(T3) of k4/dl2.md §3: role swap with a needer, at most one helper, every helper gives up a good, NA kept"""
    return s['swap'] and s['needer'] and not s['nt'] and len(s['Y']) <= 1 and s['gives']


class Profile:
    """the min-frozen class of one strict profile, with deficits and owner tables"""

    def __init__(self, d, check=False, skip_f0=False):
        I = M.Inst(d['sets'], d['vals'], d.get('m'))
        I.preallocs()
        self.I = I
        self.ok = I.omega >= 1
        if not self.ok or (skip_f0 and I.f == 0): self.ok = False; return
        self.mp = [Bs for Bs, NA in I.minP]
        self.PA = {Bs: PA(I, Bs) for Bs in self.mp}
        self.D, self.OWN = {}, {}
        for Bs in self.mp:
            dv, res = self.PA[Bs].deficit()
            if check:
                ref = I.deficit(Bs)
                assert dv == (INF if ref is None else ref), ('deficit mismatch', Bs)
            self.D[Bs], self.OWN[Bs] = dv, res

    def t1_moves(self, Bs):
        """the improving (T1) moves at Bs: (y, B') with def(P') < def(P)"""
        I, P, out = self.I, self.PA[Bs], []
        for y in P.free:
            for B2 in rebases(I, P, y):
                b2 = list(Bs); b2[y] = B2; b2 = tuple(b2)
                assert b2 in self.D, ('Lemma 1(c) violated', Bs, y, B2)
                if self.D[b2] < self.D[Bs]: out.append((y, B2))
        return out

    def t3_moves(self, Bs):
        """the improving (T3) moves at Bs: (B2, x, z, helper or None)"""
        P, out = self.PA[Bs], []
        for B2 in self.mp:
            if self.D[B2] >= self.D[Bs]: continue
            P2 = self.PA[B2]
            if not is_t3(shape(P, P2)): continue
            ch = [i for i in range(self.I.n) if Bs[i] != B2[i]]
            x = next(i for i in ch if P.frozen[i]); z = next(i for i in ch if P2.frozen[i])
            h = [i for i in ch if i not in (x, z)]
            out.append((B2, x, z, h[0] if h else None))
        return out


    def t4_optimal(self, Bs):
        """no cycle in the need digraph restricted to the frozen agents (x -> y iff x needs B_y): equivalently no
        frozen rotation (Lemma 12 of k4/dl13.md) applies"""
        P = self.PA[Bs]; I = self.I
        F = [i for i in range(I.n) if P.frozen[i]]
        succ = {x: [y for y in F if y != x and P.N[x] & Bs[y]] for x in F}
        state = {}

        def cyc(u):
            state[u] = 1
            for w in succ[u]:
                if state.get(w) == 1 or (w not in state and cyc(w)): return True
            state[u] = 2
            return False
        return not any(x not in state and cyc(x) for x in F)

    def t4_moves(self, Bs, improving=True):
        """(T4) moves at Bs (the coordinator's R_134): only frozen agents change, their bases are a permutation of
        their goods, all stay frozen, NA unchanged. Returns [(B2, pareto)] (pareto: every changed agent prefers its new
        good); with improving=True only those with a smaller deficit. Lemma 12 (k4/dl13.md) is asserted: every pareto
        move has def(P') <= def(P)."""
        P = self.PA[Bs]; I = self.I; out = []
        for B2 in self.mp:
            ch = [i for i in range(I.n) if Bs[i] != B2[i]]
            if not ch or any(not P.frozen[i] for i in ch): continue
            if sorted(Bs[i] for i in ch) != sorted(B2[i] for i in ch): continue
            P2 = self.PA[B2]
            if P2.NA != P.NA or any(not P2.frozen[i] for i in ch): continue
            pareto = all(I.val(i, B2[i]) > I.val(i, Bs[i]) for i in ch)
            if pareto:
                assert self.D[B2] <= self.D[Bs], ('Lemma 12 violated', Bs, B2)
            if improving and self.D[B2] >= self.D[Bs]: continue
            out.append((B2, pareto))
        return out


def run_profile(args):
    d, src, check = args
    pr = Profile(d, check, skip_f0=True)
    if not pr.ok or pr.I.f == 0: return src, d, None, []
    recs = []
    for Bs in pr.mp:
        if pr.D[Bs] <= 0: continue
        t1 = pr.t1_moves(Bs)
        t4 = pr.t4_moves(Bs) if pr.I.f >= 2 else []
        rec = {'Bs': [sorted(bits(B)) for B in Bs], 'def': pr.D[Bs], 'f': pr.I.f, 'omega': pr.I.omega,
               'stuck': not t1, 't4opt': pr.t4_optimal(Bs),
               't4': [{'Bs': [sorted(bits(B)) for B in B2], 'def': pr.D[B2], 'pareto': pa} for B2, pa in t4]}
        if not t1:
            t3 = pr.t3_moves(Bs)
            rec['t3'] = [{'Bs': [sorted(bits(B)) for B in B2], 'def': pr.D[B2], 'x': x, 'z': z, 'h': h}
                         for B2, x, z, h in t3]
            rec['best'] = best_owners(pr.OWN[Bs])
        recs.append(rec)
    return src, d, pr.I.f, recs


def main(argv):
    if not argv: print(__doc__); return
    mode = argv[0]; rest = [a for a in argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) for a in argv[1:] if a.startswith('--') and '=' in a)
    check = '--check' in argv
    if mode == 'catalog':
        recs = json.load(gzip.open(rest[0], 'rt'))['records']
        fmin = int(opt.get('fmin', 1))
        recs = [r for r in recs if r.get('f', 1) >= fmin][::int(opt.get('every', 1))]
        if 'max' in opt: recs = recs[:int(opt['max'])]
        base = os.path.basename(rest[0]).replace('.json.gz', '')
        items = [({'sets': r['core']['sets'], 'vals': r['vals'], 'm': r['core']['m']},
                  '%s:%s[m=%d,idx=%d]:%s' % (base, r['core']['file'], r['core']['m'], r['core']['idx'],
                                             ','.join(map(str, r['prof'])))) for r in recs]
    elif mode == 'tsv':
        items = []
        lines = open(rest[0]).read().splitlines()
        hdr = lines[0].split('\t')
        for l in lines[1:]:
            c = dict(zip(hdr, l.split('\t')))
            items.append(({'sets': json.loads(c['sets']), 'vals': json.loads(c['vals']), 'm': int(c['m'])},
                          '%s[m=%s,idx=%s]:%s' % (c['file'].replace('.json.gz', ''), c['m'], c['idx'], c['profile'])))
    else:
        items = items_of(mode, rest, opt)
    out = opt.get('out')
    print('# command: python3 k4/dl13_stuck.py ' + ' '.join(argv), flush=True)
    fo = gzip.open(out, 'wt') if out else None
    cnt = collections.Counter(); fails = []
    for src, d, f, recs in map(run_profile, ((d, s, check) for d, s in items)):
        cnt['profiles'] += 1
        if f is None: continue
        cnt['profiles f>=1, omega>=1'] += 1
        for r in recs:
            cnt['def>0 states'] += 1; cnt['def>0 states f=%d' % r['f']] += 1
            if not r['t4opt']:
                cnt['def>0 states, not T4-optimal'] += 1
                if r['t4']: cnt['def>0 states, not T4-optimal, a (T4) move lowers def'] += 1
                if any(m['pareto'] for m in r['t4']):
                    cnt['def>0 states, not T4-optimal, a frozen rotation lowers def'] += 1
            if not r['stuck']: continue
            cnt['T1-stuck'] += 1; cnt['T1-stuck f=%d' % r['f']] += 1
            if not r['t4opt']: cnt['T1-stuck, not T4-optimal'] += 1
            if not r['t3']:
                fails.append((src, d, r))
                if r['t4opt']:
                    cnt['FAILURE of DL13 at a T4-optimal state'] += 1
                    print('FAILURE-OPT', src, json.dumps(d), r['Bs'], flush=True)
                else:
                    cnt['DL13 fails (not T4-optimal)'] += 1
                    print('DL13-FAILS', src, json.dumps(d), r['Bs'], 'T4 repairs: %d' % len(r['t4']), flush=True)
                if not r['t4']:
                    cnt['FAILURE of DL134 (no T1, T3, T4 repair)'] += 1
                    print('FAILURE-134', src, json.dumps(d), r['Bs'], flush=True)
            elif all(m['h'] is not None for m in r['t3']):
                cnt['T1-stuck, every T3 repair has a helper'] += 1
            if fo:
                r2 = dict(r); r2['src'] = src; r2.update({'sets': d['sets'], 'vals': d['vals'], 'm': d['m']})
                fo.write(json.dumps(r2, separators=(',', ':')) + '\n')
    if fo: fo.close()
    for k in sorted(cnt): print('%-45s %d' % (k, cnt[k]))
    print('DL13 failures: %d (of which at T4-optimal states: %d)' % (
        len(fails), sum(1 for _, _, r in fails if r['t4opt'])), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
