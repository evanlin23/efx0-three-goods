"""Independent re-check of "the P1-free greedy process never dead-ends" (second implementation of rules.py's
strict noP1 rule with completions as the only terminal states).

It reuses only the self-contained primitives of check_deadends.py (raw definitions, Python sets; nothing from bplib,
base or rules).  A settlement (k, P, T) is *P1-free* when every good of R_k outside T is worth at most v_k(T) to k
(Lemma PHANTOM: the phantom k then carries no "l alone" constraint).  From each start it walks every state reachable
by admissible rounds all of whose settlements are P1-free, and checks that each such state has a one-absorber
completion over the present agents (phantoms receive nothing; raw EFX0 in the whole instance) or a P1-free admissible
round.  The start counts as SAFE if so (then every greedy choice of P1-free rounds ends in a completion).

With MODE=GR (the greedy process GR of k4/base_phantom.md) a state without a P1-free admissible round is also accepted
when it has a *final round* (an admissible round of any kind after which a one-absorber completion exists) or an *ED
repair* (an official move whose first agent is dangerous, whose links before the last are canonical with no junk, the
last agent taking its predecessor's good plus any junk, then a one-absorber completion).  GR stops at the first state
with a completion, a final round or an ED repair (MODE=GR).  MODE=GRR instead keeps taking P1-free rounds while any
exists and uses the base only where none does (more states visited; a stronger requirement, false on 8 of the 280
sampled 5_pure starts).

    [MODE=GR|GRR] python3 k4/base_phantom/check_rules.py FILE [STRIDE] [OFFSET]
"""
import sys, os, json, gzip, collections, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_deadends import Instance, one_absorber, admissible_rounds, official_moves, wants, junk_of

MODE = os.environ.get('MODE', 'plain')


def dangerous_at(I, X, alive):
    J = junk_of(I, X, alive)
    out = []
    for k in alive:
        if len(X[k]) != 1:
            continue
        y = next(iter(X[k]))
        if any(a != k and wants(I, X, a, y) for a in alive) and any(I.v[k].get(g, 0) > 0 for g in J):
            out.append(k)
    return out


def ed_repair(I, X, alive):
    D = dangerous_at(I, X, alive)
    for P, H0, Hs, Y in official_moves(I, X, alive):
        if P[0] not in D:
            continue
        ok = True
        for l in range(1, len(P) - 1):
            if Hs[l - 1] or len(X[P[l - 1]]) != 1 or not wants(I, X, P[l], next(iter(X[P[l - 1]]))):
                ok = False
                break
        if ok and one_absorber(I, Y, alive) is not None:
            return True
    return False


def base_ok(I, X, alive, C):
    if any(one_absorber(I, Y, al2) is not None for combo, Y, al2 in admissible_rounds(I, X, alive)):
        C['base used: final round'] += 1
        return True
    if ed_repair(I, X, alive):
        C['base used: ED repair'] += 1
        return True
    return False


def rows_of(fn):
    op = gzip.open if fn.endswith('.gz') else open
    with op(fn, 'rt') as f:
        if '.jsonl' in fn:
            for line in f:
                r = json.loads(line)
                yield r['sets'], r['vals'], r['picks']
        else:
            for h in json.load(f)['hypergraphs']:
                for s in h['starts']:
                    yield h['sets'], s['vals'], s['picks']


def p1free(I, k, T):
    t = I.val(k, T)
    return all(v <= t for g, v in I.v[k].items() if g not in T)


def job(row):
    sets, vals, picks = row
    I = Instance(sets, vals)
    X0 = [{g} for g in picks]
    seen = set()
    stack = [(X0, list(range(I.n)))]
    states = 0
    C = collections.Counter()
    while stack:
        X, alive = stack.pop()
        key = (tuple(tuple(sorted(b)) for b in X), tuple(alive))
        if key in seen:
            continue
        seen.add(key)
        states += 1
        if one_absorber(I, X, alive) is not None:
            continue
        if MODE == 'GR' and base_ok(I, X, alive, C):
            continue
        nxt = [(Y, al2) for combo, Y, al2 in admissible_rounds(I, X, alive)
               if all(p1free(I, k, T) for k, P, T in combo)]
        if not nxt:
            if MODE == 'GRR' and base_ok(I, X, alive, C):
                continue
            return False, states, C
        stack.extend(nxt)
    return True, states, C


if __name__ == '__main__':
    fn = sys.argv[1]
    stride = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    off = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    print('$ MODE=%s python3 k4/base_phantom/check_rules.py' % MODE, fn, stride, off)
    seen = set()
    rows = []
    for r in rows_of(fn):
        k = json.dumps(r)
        if k not in seen:
            seen.add(k)
            rows.append(r)
    rows = rows[off::stride]
    print('distinct starts checked:', len(rows))
    C = collections.Counter()
    with mp.Pool(4) as pool:
        for ok, st, c in pool.imap_unordered(job, rows, chunksize=64):
            C['SAFE' if ok else 'UNSAFE'] += 1
            C['states visited'] += st
            C.update(c)
    for k in sorted(C):
        print('  %8d  %s' % (C[k], k))
