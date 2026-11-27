"""The greedy process GR of k4/base_phantom.md section 5, run fast on large start sets, with the lemma census.

GR at a state S (start: a hard perfect start):
  1. a lifted completion exists                     -> stop (end: completion)
  2. a final round exists (an admissible round of any kind after which a lifted completion exists)
                                                    -> stop (end: final round)
  3. an ED repair exists (base.py class ED: x0 dangerous, links before the last canonical with no junk, the last
     agent taking its predecessor's good plus any junk; then a lifted one-absorber completion)
                                                    -> stop (end: ED)
  4. otherwise take every admissible round whose settlements are all P1-free (each is explored: GR may take any).
     None -> STUCK.
At every state where GR stops in 2 or 3, the census records which of BASE-R's lemmas the stop instantiates:
  B1  no admissible round at all (the stop is an ED repair);
  B2  admissible rounds exist, none P1-free;
  --  a P1-free round exists as well (the base was not needed).
MODE=GRR keeps taking P1-free rounds wherever one exists and uses steps 2-3 only where none does (the strong form of
BASE-R; refuted).  MODE=GRRE is GRR with every chain of a taken round an E-prefix (a prefix of the earliest-wanter
chain E(k) for some SD order of the current state, as in Lemma SD-E(round)); final rounds stay any admissible round.

    [MODE=GR|GRR] python3 k4/base_phantom/gr.py NAME FILE [STRIDE] [OFFSET]
       log to stdout; stuck starts to results/k4_base_phantom/gr_stuck_NAME.jsonl
"""
import sys, os, json, gzip, time, collections, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bplib import (Inst, State, start_state, bits, load_rows, row_key, rounds, lifted_completion, dangerous,
                   canonical_chains, submasks, wants)

MODE = os.environ.get('MODE', 'GR')
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'results', 'k4_base_phantom')


def p1free(I, k, T):
    t = I.V(k, T)
    return all(I.val[k][g] <= t for g in bits(I.R[k] & ~T))


def ed_repair(I, S):
    """Some ED move followed by a lifted completion (built directly, not by filtering all official moves)."""
    J = S.junk()
    for k in dangerous(I, S):
        vk = I.V(k, S.B[k])
        for P in [(k,)] + canonical_chains(I, S, k):
            a = S.B[P[-1]]
            for z in S.alive:
                if z in P:
                    continue
                vz = I.V(z, S.B[z])
                for Ht in [0] + list(submasks(J & I.R[z])):
                    if I.V(z, a | Ht) <= vz:
                        continue
                    pool = ((J & ~Ht) | S.B[z]) & I.R[k]
                    for H0 in submasks(pool):
                        if I.V(k, H0) <= vk:
                            continue
                        nb = list(S.B)
                        nb[k] = H0
                        for l in range(1, len(P)):
                            nb[P[l]] = S.B[P[l - 1]]
                        nb[z] = a | Ht
                        if lifted_completion(I, State(S.alive, S.goods, nb, S.dead)) is not None:
                            return (P + (z,), bits(H0), bits(Ht))
    return None


def sd_orders(I, S):
    import itertools
    tgt = {i: S.B[i].bit_length() - 1 for i in S.alive}
    return [o for o in itertools.permutations(S.alive) if I.sd(o, S.goods) == tgt]


def e_prefix(I, S, orders, k, P):
    for o in orders:
        pos = {a: t for t, a in enumerate(o)}
        E = [k]
        while len(E) < len(P):
            g = S.B[E[-1]].bit_length() - 1
            w = [a for a in S.alive if a not in E and wants(I, S.B, a, g)]
            if not w:
                break
            E.append(min(w, key=lambda a: pos[a]))
        if tuple(E) == tuple(P):
            return True
    return False


def gr(I, S0):
    C = collections.Counter()
    seen = set()
    stack = [S0]
    stuck = None
    while stack:
        S = stack.pop()
        k = S.key()
        if k in seen:
            continue
        seen.add(k)
        C['states visited'] += 1
        if lifted_completion(I, S) is not None:
            C['end: completion, %d phantoms' % len(S.dead)] += 1
            continue
        rs = list(rounds(I, S))
        free = [S2 for combo, S2 in rs if all(p1free(I, kk, T) for kk, P, T in combo)]
        if MODE == 'GRRE':
            orders = sd_orders(I, S)
            free = [S2 for combo, S2 in rs if all(p1free(I, kk, T) and e_prefix(I, S, orders, kk, P)
                                                  for kk, P, T in combo)]
        sit = 'B1 (no admissible round)' if not rs else 'B2 (no P1-free round)' if not free else '-- (a P1-free round exists)'
        base = None
        if MODE == 'GR' or not free:
            if any(lifted_completion(I, S2) is not None for combo, S2 in rs):
                base = 'final round'
            elif ed_repair(I, S) is not None:
                base = 'ED repair'
        if base is not None:
            C['end: %s, %s, %d phantoms' % (base, sit, len(S.dead))] += 1
            continue
        if not free:
            C['STUCK: %s, %d phantoms' % (sit, len(S.dead))] += 1
            if stuck is None:
                stuck = dict(alive=list(S.alive), B=[bits(b) for b in S.B], junk=bits(S.junk()))
            continue
        stack.extend(free)
    return C, stuck


def job(r):
    I = Inst(r['sets'], r['vals'])
    S = start_state(I, r['picks'])
    C, stuck = gr(I, S)
    C['starts'] += 1
    C['SAFE' if stuck is None else 'STUCK start'] += 1
    return C, (None if stuck is None else dict(sets=r['sets'], vals=r['vals'], picks=r['picks'], name=r['name'], at=stuck))


if __name__ == '__main__':
    name, fn = sys.argv[1], sys.argv[2]
    stride = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    off = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    print('$ MODE=%s python3 k4/base_phantom/gr.py' % MODE, name, os.path.relpath(fn), stride, off)
    seen = set()
    rows = []
    for t, r in enumerate(load_rows(fn)):
        if t % stride != off:
            continue
        k = row_key(r)
        if k not in seen:
            seen.add(k)
            rows.append(r)
    print('distinct starts:', len(rows))
    sys.stdout.flush()
    C = collections.Counter()
    t0 = time.time()
    with open(os.path.join(OUT, 'gr_stuck_%s.jsonl' % name), 'w') as fo, mp.Pool(4) as pool:
        for i, (c, st) in enumerate(pool.imap_unordered(job, rows, chunksize=64)):
            C.update(c)
            if st is not None:
                fo.write(json.dumps(st) + '\n')
                fo.flush()
            if (i + 1) % 50000 == 0:
                print('  ... %d starts, %d stuck, %.0f s' % (i + 1, C['STUCK start'], time.time() - t0))
                sys.stdout.flush()
    for k in sorted(C):
        print('  %8d  %s' % (C[k], k))
    print('time %.0f s' % (time.time() - t0))
