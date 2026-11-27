"""The greedy round process GR of proof/k4-base-phantom (k4/base_phantom.md, PR #139), implemented here
independently on this note's round code (round_rsd.py, rsd.py; k4/matching.md §6).  The definitions follow that
session's message of 2026-11-27 05:04.
  state       present agents hold one good each (a perfect SD start of the present instance); phantoms (settled
              agents) hold their T.
  settlement  k dangerous in the present instance (frozen by a present wanter, values a junk good); a canonical chain
              P = (k, x1, ..., xt); T inside (J + B_xt) and R_k, improving for k (round_rsd.settlements).
  admissible round  1 or 2 settlements with vertex-disjoint chains and disjoint T, applied at once, with:
              - (L*) at the round's end toward every agent present at its start (round-mates at v(T));
              - (P2) no T threatens an earlier phantom at its value;
              - a perfect SD reduced state (all orders).
  P1-free     every good of R_k minus T is worth at most v_k(T) to k (no "l alone" constraint of Lemma PHANTOM).
  lifted completion  one present owner takes any junk, every other present agent at most one junk good, phantoms
              nothing, raw EFX0 in I (rsd.lifted_completion).
  final round any admissible round (P1 settlements allowed) followed by a lifted completion at once.
  ED repair   one move of the present instance, then a lifted completion:
              - x0 dangerous; the links x1..x_{t-1} canonical (each wants its predecessor's single good, no junk);
              - the last agent x_t takes x_{t-1}'s good plus junk H_t inside J and R_{x_t}, and gains;
              - x0 takes H0 inside ((J - H_t) + B_{x_t}) and R_{x0}, improving;
              - t = 1 is allowed.
GR at a state: stop at the first of (lifted completion, final round, ED repair); otherwise expand every admissible
P1-free round (exhaustive DFS, memo over states).  A start is STUCK if some visited state has none of the four.

    [KNOWN_HARD=1] python3 k4/matching/gr.py INPUT [INPUT ...]     (inputs as in n5_census.py)"""
import sys, os, json, itertools, collections, time, multiprocessing as mp
import _mpaths  # noqa: F401
from mlib import M, subsets
from n5_census import load
from rsd import sub_instance, lifted_completion
from round_rsd import settlements


def p1_free(I, k, T):
    vT = I.V(k, T)
    return all(I.v[k][g] <= vT for g in I.R[k] if g not in T)


def admissible_rounds(I, alive, goods, B, dead):
    """(combo in labels of I, new full state, P1-free?) for every admissible round."""
    Im, g2 = sub_instance(I, alive, goods); inv = {t: g for g, t in g2.items()}
    Bm = [[g2[g] for g in B[i]] for i in alive]
    S = settlements(Im, Bm)
    for r in (1, 2):
        for combo in itertools.combinations(S, r):
            agents = [x for _, P, _ in combo for x in P]
            if len(agents) != len(set(agents)): continue
            Ts = [g for _, _, T in combo for g in T]
            if len(Ts) != len(set(Ts)): continue
            nb = [list(b) for b in Bm]
            for km, P, T in combo:
                nb[km] = list(T)
                for t in range(1, len(P)): nb[P[t]] = list(Bm[P[t - 1]])
            if any(Im.threat(i, list(T), Im.V(i, nb[i])) for km, _, T in combo for i in range(Im.n) if i != km): continue
            full = [list(b) for b in B]
            for a, i in enumerate(alive): full[i] = [inv[g] for g in nb[a]]
            Tg = [[inv[g] for g in T] for _, _, T in combo]
            if any(I.threat(f, T, I.V(f, B[f])) for f in dead for T in Tg): continue                      # (P2)
            K = [alive[km] for km, _, _ in combo]; Tall = set(g for T in Tg for g in T)
            alive2 = [a for a in alive if a not in K]; goods2 = [g for g in goods if g not in Tall]
            if any(len(full[i]) != 1 for i in alive2): continue
            if alive2:
                I2, h2 = sub_instance(I, alive2, goods2)
                Y2 = tuple(h2[full[i][0]] for i in alive2)
                if not any(I2.sd(p) == Y2 for p in itertools.permutations(range(I2.n))): continue
            free = all(p1_free(I, alive[km], T) for (km, _, _), T in zip(combo, Tg))
            yield K, Tall, full, free


def ed_repair(I, alive, goods, B, dead):
    """Some ED move of the present instance followed by a lifted completion."""
    Im, g2 = sub_instance(I, alive, goods); inv = {t: g for g, t in g2.items()}
    Bm = [[g2[g] for g in B[i]] for i in alive]; Jm = Im.junk(Bm)
    for x0 in Im.dangerous(Bm):
        paths = [[x0]]

        def ext(path):
            for w in range(Im.n):
                if w in path or not Bm[path[-1]]: continue
                yield path + [w]
        stack = [[x0]]
        while stack:
            path = stack.pop()
            for p2 in ext(path):
                xt, prev = p2[-1], p2[-2]
                # x_t is the last agent: takes B_prev + H_t (H_t inside junk and R_xt) and gains
                for Ht in subsets([g for g in Jm if g in Im.R[xt]]):
                    new_t = list(Bm[prev]) + list(Ht)
                    if Im.V(xt, new_t) <= Im.V(xt, Bm[xt]): continue
                    pool = [g for g in Jm if g not in Ht] + list(Bm[xt])
                    for H0 in subsets([g for g in pool if g in Im.R[x0]], 1):
                        if Im.V(x0, H0) <= Im.V(x0, Bm[x0]): continue
                        nb = [list(b) for b in Bm]; nb[x0] = list(H0); nb[xt] = new_t
                        for t in range(1, len(p2) - 1): nb[p2[t]] = list(Bm[p2[t - 1]])
                        full = [list(b) for b in B]
                        for a, i in enumerate(alive): full[i] = [inv[g] for g in nb[a]]
                        if lifted_completion(I, full, dead) is not None: return True
                # extend as a canonical link: w wants prev's single good alone (no junk)
                if len(p2) < Im.n and len(Bm[prev]) == 1 and Im.wants(xt, Bm[prev][0], Bm):
                    stack.append(p2)
    return False


def gr(I, alive, goods, B, dead, memo, C, root_hard):
    key = (tuple(alive), json.dumps(B))
    if key in memo: return memo[key]
    memo[key] = True   # cycles are impossible (agents only leave), this guards recursion
    if not (root_hard and not dead) and lifted_completion(I, B, dead) is not None:
        C['stop: completion'] += 1; return True
    rounds = list(admissible_rounds(I, alive, goods, B, dead))
    for K, Tall, full, free in sorted(rounds, key=lambda r: not r[3]):   # P1-free final rounds first
        if lifted_completion(I, full, dead | set(K)) is not None:
            C['stop: final round' + ('' if free else ' (with a P1 settlement)')] += 1; return True
    if ed_repair(I, alive, goods, B, dead):
        C['stop: ED repair'] += 1; return True
    nxt = [(K, Tall, full) for K, Tall, full, free in rounds if free]
    if not nxt:
        C['STUCK state'] += 1; memo[key] = False; return False
    ok = True
    for K, Tall, full in nxt:
        ok &= gr(I, [a for a in alive if a not in K], [g for g in goods if g not in Tall], full, dead | set(K), memo, C, root_hard)
    memo[key] = ok; return ok


def job(row):
    I = M(row['sets'], row['vals']); B = [[g] for g in row['picks']]; C = collections.Counter()
    ok = gr(I, list(range(I.n)), list(range(I.m)), B, frozenset(), {}, C, os.environ.get('KNOWN_HARD') == '1')
    out = collections.Counter({'GR safe %s' % ok: 1})
    for k, v in C.items(): out['states, ' + k] += v
    tag = '%s m=%s #%s' % (row.get('list'), row.get('m'), row.get('idx')) if row.get('idx') is not None else 'all'
    out['GR safe %s | %s' % (ok, tag)] += 1
    if not ok:
        sys.stdout.write('GR STUCK %s\n' % json.dumps({'sets': row['sets'], 'vals': row['vals'], 'picks': list(row['picks'])}))
        sys.stdout.flush()
    return out


if __name__ == '__main__':
    rows = []
    for a in sys.argv[1:]: rows += load(a)
    seen = set(); R = []
    for r in rows:
        key = json.dumps([r['sets'], r['vals'], list(r['picks'])])
        if key not in seen: seen.add(key); R.append(r)
    print('$ KNOWN_HARD=%s python3 k4/matching/gr.py' % os.environ.get('KNOWN_HARD', ''), *sys.argv[1:], '|', len(R),
          'distinct starts', flush=True)
    T = collections.Counter(); t0 = time.time()
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for t, C in enumerate(pool.imap_unordered(job, R, chunksize=8 if len(R) > 1000 else 1)):
            T.update(C)
            if (t + 1) % 20000 == 0: print('...', t + 1, '%.0f s' % (time.time() - t0), flush=True)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
