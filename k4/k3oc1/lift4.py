"""Lifting the k = 3 structure (k4/k3_oc1.md) to k = 4, on the k = 4 data of k4/sdc (every order, n <= NMAX).

Completions of a state (bases B, junk J), all exact by SAT on sdclib's EFX0 encoding:
  exact : OC1's one-absorber completion (k4/sdc/oc_absorb.extends_A, A = 1)
  DE    : the same, and in addition no frozen agent receives junk (frozen: some other agent values one of its base
          goods above its own base) -- the shape of Lemma 1 / DE's finishing: wanted goods stay alone
Questions, for every order's picks:
  Q1 picks pass DE-shape, or one improving chain (k4/sdc/de_free.iter_chains) gives a DE-shape completion?
  Q2 on the starts that need a chain: does every chain of largest rank score (the sum over agents of the rank of
     v_i(B_i) among the subset sums of R_i, the k = 4 form of DE's score) repair (exact)?  every chain of least
     omega = |J| - |T| (T: agents outside the frozen ones)?  some chain (exact)?
  With 'detype': only DE-type chains (de_type below), the class on which the k = 3 rules hold.
    python3 k4/k3oc1/lift4.py screen|suite|special [NMAX] [detype [comp] [anyjunk]]
    python3 k4/k3oc1/lift4.py cores:FILES NMAX COUNT SEED [detype ...]   (random strict profiles of k = 4 cores)"""
import sys, os, itertools, collections, json, time
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
SDC = os.path.join(ROOT, 'k4', 'sdc'); sys.path.insert(0, SDC)
import _paths
import de_free as DF
from sdclib import Enc
from sdc_need import instances
from sdc_orders import sd
from nof_var import SPECIAL
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
DF.CHAIN_ONLY = True

def frozen(E, base):
    B = DF.bundles(E, base); n = E.n
    val = lambda i, S: sum(E.v[i].get(g, 0) for g in S)
    return [j for j in range(n) if any(i != j and E.v[i].get(g, 0) > val(i, B[i]) for i in range(n) for g in B[j])]

def complete(E, base, de_shape):
    cl = list(E.cl); top = E.top
    J = [g for g in range(E.m) if base[g] < 0]
    for g in range(E.m):
        cl.append([-E.x[g][E.n]])
        if base[g] >= 0: cl.append([E.x[g][base[g]]])
    if de_shape:
        for j in frozen(E, base):
            for g in J: cl.append([-E.x[g][j]])
    bigs = []
    for i in range(E.n):
        top += 1; b = top; bigs.append(b)
        for g, h in itertools.combinations(J, 2): cl.append([-E.x[g][i], -E.x[h][i], b])
    enc = CardEnc.atmost(lits=bigs, bound=1, top_id=top, encoding=EncType.seqcounter); cl.extend(enc.clauses)
    S = Cadical153(bootstrap_with=cl); ok = S.solve(); S.delete(); return ok

def de_type(E, base):
    """the k = 4 analogue of DE's trades: improving chains with t >= 1 (k4/sdc/de_free.moves) in which an agent may
    receive junk only if it held exactly its top (a single good it values most) and gives it away: want arrows pass
    the predecessor's base unchanged, pair-arrow analogues add junk for an agent holding its top; and the result is
    valid (wanted goods are held alone), as DE's trades always are at k = 3 (paper/k3-simple Lemmas ring, chain)"""
    B = DF.bundles(E, base); out = set()
    top = [max(E.R[i], key=lambda g: E.v[i][g]) for i in range(E.n)]
    for nb, descs in DF.moves(E, base, describe=True, all_desc=True).items():
        for kind, path, H in descs:
            if len(path) < 2: continue
            if (ANYJUNK or all(not H.get(t) or B[path[t]] == [top[path[t]]] for t in range(len(path)))) and (valid_star if COMP else valid)(E, nb):
                out.add(nb); break
    return out

ANYJUNK = False   # 'anyjunk': every agent of a t >= 1 chain may take junk (it gives its whole base away)
COMP = False   # 'comp' on the command line: compensable validity (valid_star) in place of validity

def valid_star(E, base):
    """compensable validity: a good g that agent i values above its base may sit in a bundle of two or more goods
    if some junk good z of i gives v_i(B_i) + v_i(z) >= v_i(g) (i takes z in the completion); junk goods are never
    wanted"""
    B = DF.bundles(E, base); owner = {g: a for g, a in enumerate(base)}
    J = [g for g in range(E.m) if base[g] < 0]
    for i in range(E.n):
        vi = sum(E.v[i].get(g, 0) for g in B[i])
        for g in E.R[i]:
            if g in B[i] or E.v[i][g] <= vi: continue
            a = owner[g]
            if a < 0: return False
            if len(B[a]) != 1 and not any(vi + E.v[i].get(z, 0) >= E.v[i][g] for z in J if z in E.v[i]): return False
    return True

def valid(E, base):
    """DE's validity at k = 4: every good some agent values above its own base is the whole base of another agent"""
    B = DF.bundles(E, base); owner = {g: a for g, a in enumerate(base)}
    for i in range(E.n):
        vi = sum(E.v[i].get(g, 0) for g in B[i])
        for g in E.R[i]:
            if g in B[i] or E.v[i][g] <= vi: continue
            a = owner[g]
            if a < 0 or len(B[a]) != 1: return False
    return True

def rankscore(E, base):
    B = DF.bundles(E, base); s = 0
    for i in range(E.n):
        sums = sorted(set(sum(E.v[i][g] for g in S) for r in range(len(E.R[i]) + 1) for S in itertools.combinations(E.R[i], r)))
        s += sums.index(sum(E.v[i].get(g, 0) for g in B[i]))
    return s

def omega(E, base):
    B = DF.bundles(E, base); fr = set(frozen(E, base))
    return sum(1 for g in base if g < 0) - sum(1 for i in range(E.n) if i not in fr and len(B[i]) <= 1)

if __name__ == '__main__':
    DETYPE = 'detype' in sys.argv[1:]; COMP = 'comp' in sys.argv[1:]; ANYJUNK = 'anyjunk' in sys.argv[1:]
    src = sys.argv[1]; NMAX = int(sys.argv[2]) if len(sys.argv) > 2 and sys.argv[2].isdigit() else 4
    C = collections.Counter(); t0 = time.time(); shown = collections.Counter()
    print('$ python3 k4/k3oc1/lift4.py', *sys.argv[1:], flush=True)
    if src == 'special': items = SPECIAL
    elif src.startswith('cores:'):
        import random, gzip
        N, seed = int(sys.argv[3]), int(sys.argv[4]); rng = random.Random(seed); items = []
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        from de4lib import random_profile
        os.chdir(cwd)
        cores = []
        for fn in src[6:].split(','):
            cores += [c['sets'] for c in json.load(gzip.open(os.path.join(ROOT, 'results', fn)))['cores']]
        for t in range(N):
            sets = rng.choice(cores); items.append(('r%d' % t, sets, random_profile(sets, rng), 1 + max(max(x) for x in sets)))
    else: items = instances(src)
    for name, sets, vals, m in items:
        n = len(sets)
        if n > NMAX: continue
        E = Enc(sets, vals, m); C['instances'] += 1; res = {}
        for o in itertools.permutations(range(n)):
            Y = tuple(sd(E, list(o))[0])
            if Y in res: C[res[Y]] += 1; C['starts'] += 1; continue
            base = [-1] * m
            for i, g in enumerate(Y):
                if g is not None: base[g] = i
            base = tuple(base)
            if complete(E, base, True): r = 'picks pass DE-shape'
            else:
                ch = list(set(DF.iter_chains(E, base))) if not DETYPE else list(de_type(E, base))
                de_ok = [b2 for b2 in ch if complete(E, b2, True)]
                ex_ok = set(b2 for b2 in ch if complete(E, b2, False))
                ex0 = complete(E, base, False)
                r = 'hard (DE-shape); picks exact %s; one chain DE-shape %s; one chain exact %s' % (ex0, bool(de_ok), bool(ex_ok))
                if ch and not ex0:
                    rs = [rankscore(E, b2) for b2 in ch]; w = [omega(E, b2) for b2 in ch]
                    C['exact-hard: every max rank-score chain repairs (exact) %s' % all(b2 in ex_ok for b2, s in zip(ch, rs) if s == max(rs))] += 1
                    C['exact-hard: every least-omega chain repairs (exact) %s' % all(b2 in ex_ok for b2, s in zip(ch, w) if s == min(w))] += 1
                if not de_ok and shown['de'] < 3:
                    shown['de'] += 1; print('NO CHAIN WITH DE-SHAPE COMPLETION', name, json.dumps((sets, vals)), 'order', o, 'picks', Y, 'exact after one chain', bool(ex_ok), flush=True)
            res[Y] = r; C[r] += 1; C['starts'] += 1
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
