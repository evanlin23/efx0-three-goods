"""Short Berge cycles at the OC1^max failures (coordinator's question, burst 5; k4/girth.md section 7).

At a serial-dictatorship start with picks Y (one good per agent, a maximum matching; here perfect, nu = n):
  J = junk (unpicked goods); i WANTS g if v_i(g) > v_i(Y_i); F = frozen agents (someone wants their pick);
  D = dangerous agents (frozen, valuing a junk good); D_T = truly dangerous (J threatens them at their pick value:
  v_d(J - h) > p_d for some h in J); U = unfrozen agents (receivers).  (Definitions of k4/oc1_hall.md, k4/oc1max_multi.md.)
Berge 2-cycle: two agents sharing at least two goods; a pick swap: a 2-cycle whose agents both value both picks.  Berge 3-cycle: three agents a, b, c and three distinct goods,
one shared by each pair.

For every failing start (all 112,880 n = 4 ones of results/k4_oc1max/two_move_starts_n4.json.gz, the 24 n = 5 ones of
results/k4_oc1max/oc1prime_cex_n5_partial.jsonl) and for perfect starts where OC1^max holds (n = 4: random strict
profiles of the same 11 cores and of the other 991 cores, every SD order, minus the failing set; n = 5: random 5_pure
profiles, every SD order, OC1^max status unknown), it records which cycle patterns are present, and prints, per pattern, the fraction of
failing and of non-failing starts that contain it.  EVIDENCE (the n = 4 failing set is complete, the contrast sample
is random).

    python3 k4/girth/oc1_cycles.py [SAMPLES_PER_CORE] [SEED]
"""
import collections
import gzip
import itertools
import json
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)


def signature(vals):
    d = len(vals)
    out = []
    for A in range(1, 1 << d):
        for B in range(A + 1, 1 << d):
            if A & B == 0:
                a = sum(vals[k] for k in range(d) if A >> k & 1)
                b = sum(vals[k] for k in range(d) if B >> k & 1)
                out.append(1 if a > b else -1)
    return tuple(out)


def roles(sets, vals, picks):
    """per-agent role at the start: 'DT', 'Dp' (pick-dangerous), 'F' (frozen, not dangerous), 'U' (unfrozen)"""
    n = len(sets)
    v = [dict(zip(sets[i], vals[i])) for i in range(n)]
    p = [v[i].get(picks[i], 0) for i in range(n)]
    allg = set(g for S in sets for g in S)
    J = allg - set(picks)
    out = []
    for i in range(n):
        frozen = any(v[j].get(picks[i], 0) > p[j] for j in range(n) if j != i)
        if not frozen:
            out.append('U')
            continue
        if not any(g in v[i] for g in J):
            out.append('F')
            continue
        # truly dangerous: J threatens i at p_i
        if any(g not in v[i] for g in J):
            thr = sum(v[i].get(g, 0) for g in J) > p[i]
        else:
            s = sum(v[i][g] for g in J)
            thr = s - min(v[i][g] for g in J) > p[i]
        out.append('DT' if thr else 'Dp')
    return out, J


def features(sets, vals, picks):
    n = len(sets)
    R = [set(S) for S in sets]
    rl, J = roles(sets, vals, picks)
    holder = {picks[i]: i for i in range(n)}
    D = {i for i in range(n) if rl[i] in ('DT', 'Dp')}
    DT = {i for i in range(n) if rl[i] == 'DT'}
    U = {i for i in range(n) if rl[i] == 'U'}
    f = set()
    f.add('|D| = %d' % len(D))
    f.add('|D_T| = %d' % len(DT))
    f.add('|U| = %d' % len(U))
    two = []
    for a, b in itertools.combinations(range(n), 2):
        sh = R[a] & R[b]
        if len(sh) >= 2:
            gr = []
            for g in sh:
                if g in J:
                    gr.append('J')
                elif holder.get(g) in (a, b):
                    gr.append('P')
                else:
                    gr.append('Po')
            two.append((a, b, sorted(gr)))
    f.add('some 2-cycle' if two else 'no 2-cycle')
    for a, b, gr in two:
        pair = '-'.join(sorted([('D' if x in D else rl[x]) for x in (a, b)]))
        f.add('2-cycle %s' % pair)
        if a in D and b in D:
            f.add('2-cycle D-D')
            if gr.count('J') >= 1:
                f.add('2-cycle D-D sharing a junk good')
            if gr.count('J') >= 2:
                f.add('2-cycle D-D sharing two junk goods')
            if 'P' in gr:
                f.add('2-cycle D-D sharing a pick of the pair')
        if a in DT and b in DT:
            f.add('2-cycle DT-DT')
        if (a in D) != (b in D) and (a in U or b in U):
            f.add('2-cycle D-U')
            if gr.count('J') >= 1:
                f.add('2-cycle D-U sharing a junk good')
        if gr.count('J') >= 2:
            f.add('2-cycle sharing two junk goods')
        if 'P' in gr and 'J' in gr:
            f.add('2-cycle sharing a pick of the pair and a junk good')
    # pick swaps: a 2-cycle whose two agents both value both of their picks
    swaps = [(a, b) for a, b, gr in two if picks[a] in R[b] and picks[b] in R[a]]
    for a, b in swaps:
        if a in D or b in D:
            f.add('pick swap through a dangerous agent')
            other = b if a in D else a
            f.add('pick swap D-%s' % ('D' if other in D else rl[other]))
    dswaps = [(a, b) for a, b in swaps if a in D or b in D]
    if any(not ({a, b} & {c, d}) for (a, b), (c, d) in itertools.combinations(dswaps, 2)):
        f.add('two vertex-disjoint pick swaps through dangerous agents')
    if dswaps or any(a in D and b in D for a, b, gr in two):
        f.add('2-cycle D-D or pick swap through a dangerous agent')
    tt = any(a in DT and b in DT and gr.count('J') >= 2 for a, b, gr in two)
    du = any((a in D and b in U) or (b in D and a in U) for a, b in swaps)
    if len(U) == 1 and (tt or du):
        f.add('P*: |U| = 1 and (D_T pair sharing two junk goods or D-U pick swap)')
    if len(U) == 1 and tt:
        f.add('|U| = 1 and D_T pair sharing two junk goods')
    if len(U) == 1 and du:
        f.add('|U| = 1 and D-U pick swap')
    # Berge 3-cycles
    tri = []
    for a, b, c in itertools.combinations(range(n), 3):
        ab, bc, ca = R[a] & R[b], R[b] & R[c], R[c] & R[a]
        if any(len({x, y, z}) == 3 for x in ab for y in bc for z in ca):
            tri.append((a, b, c))
    f.add('some 3-cycle' if tri else 'no 3-cycle')
    for t in tri:
        nd = sum(1 for x in t if x in D)
        f.add('3-cycle with %d dangerous' % nd)
        if any(x in U for x in t):
            f.add('3-cycle through U')
    # dangerous agents sharing a junk good
    for a, b in itertools.combinations(sorted(D), 2):
        if R[a] & R[b] & J:
            f.add('two dangerous agents share a junk good')
        if R[a] & R[b]:
            f.add('two dangerous agents share some good')
    return f


def sd_picks(sets, v, order):
    taken = set()
    picks = [None] * len(sets)
    for i in order:
        cand = [g for g in sets[i] if g not in taken]
        if cand:
            g = max(cand, key=lambda h: v[i][h])
            picks[i] = g
            taken.add(g)
    return picks


def max_matching(sets):
    n = len(sets)
    match = {}

    def aug(i, seen):
        for g in sets[i]:
            if g in seen:
                continue
            seen.add(g)
            if g not in match or aug(match[g], seen):
                match[g] = i
                return True
        return False

    return sum(1 for i in range(n) if aug(i, set()))


def main():
    per = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    print('$ python3 k4/girth/oc1_cycles.py', *sys.argv[1:], flush=True)
    from sources import cores, domains
    d = json.load(gzip.open(os.path.join(ROOT, 'results/k4_oc1max/two_move_starts_n4.json.gz')))
    FAIL = collections.Counter()
    nfail = 0
    failkeys = set()
    failcores = set()
    for h in d['hypergraphs']:
        failcores.add((h['list'], h['idx']))
        for st in h['starts']:
            nfail += 1
            failkeys.add((h['list'], h['idx'], tuple(signature(v) for v in st['vals']), tuple(st['picks'])))
            for x in features(h['sets'], st['vals'], st['picks']):
                FAIL[x] += 1
    # contrast: perfect SD starts where OC1^max holds
    OK_SAME, OK_OTHER = collections.Counter(), collections.Counter()
    nsame = nother = 0
    allc = cores(4)
    for f, idx, sets, m in allc:
        lst = f.replace('k4_certs_', '').replace('.json.gz', '')
        same = (lst, idx) in failcores
        if not same and rng.random() > 0.15:
            continue
        doms = domains(sets, m)
        nu = max_matching(sets)
        for t in range(per if same else max(1, per // 10)):
            ds = [rng.choice(D) for D in doms]
            vals = [[dd[g] for g in sorted(dd)] for dd in ds]
            v = [dict(dd) for dd in ds]
            sig = tuple(signature(x) for x in vals)
            seen = set()
            for order in itertools.permutations(range(len(sets))):
                pk = sd_picks(sets, v, order)
                if None in pk or tuple(pk) in seen:
                    continue
                seen.add(tuple(pk))
                if len(set(pk)) != nu:
                    continue
                if (lst, idx, sig, tuple(pk)) in failkeys:
                    continue
                fe = features(sets, vals, pk)
                if same:
                    nsame += 1
                    OK_SAME.update(fe)
                else:
                    nother += 1
                    OK_OTHER.update(fe)
    # n = 5 random perfect starts (OC1^max status unknown; failures are rare)
    R5 = collections.Counter()
    nr5 = 0
    c5 = cores(5, pure=True)
    for t in range(per // 3):
        f, idx, sets, m = rng.choice(c5)
        doms = domains(sets, m)
        nu = max_matching(sets)
        ds = [rng.choice(D) for D in doms]
        vals = [[dd[g] for g in sorted(dd)] for dd in ds]
        v = [dict(dd) for dd in ds]
        seen = set()
        for order in itertools.permutations(range(len(sets))):
            pk = sd_picks(sets, v, order)
            if None in pk or tuple(pk) in seen or len(set(pk)) != nu:
                continue
            seen.add(tuple(pk))
            nr5 += 1
            R5.update(features(sets, vals, pk))
    # n = 5 failures
    F5 = collections.Counter()
    n5 = 0
    for line in open(os.path.join(ROOT, 'results/k4_oc1max/oc1prime_cex_n5_partial.jsonl')):
        r = json.loads(line)
        n5 += 1
        F5.update(features(r['sets'], r['vals'], r['picks']))
    keys = sorted(set(FAIL) | set(OK_SAME) | set(OK_OTHER) | set(F5) | set(R5))
    print('failing starts: n = 4: %d (11 cores); n = 5: %d.  OC1^max-holding perfect starts sampled: %d on the 11 cores, '
          '%d on other n = 4 cores; random perfect n = 5 pure starts: %d' % (nfail, n5, nsame, nother, nr5))
    print('%-66s %10s %9s %10s %10s %10s' % ('pattern', 'fail n=4', 'fail n=5', 'ok same', 'ok other', 'rand n=5'))
    for k in keys:
        print('%-66s %9.2f%% %8.1f%% %9.2f%% %9.2f%% %9.2f%%' % (
            k, 100.0 * FAIL[k] / nfail, 100.0 * F5[k] / max(n5, 1), 100.0 * OK_SAME[k] / max(nsame, 1),
            100.0 * OK_OTHER[k] / max(nother, 1), 100.0 * R5[k] / max(nr5, 1)))
    print('patterns in EVERY failing start (n = 4 and n = 5):',
          [k for k in keys if FAIL[k] == nfail and F5[k] == n5], flush=True)


if __name__ == '__main__':
    main()
