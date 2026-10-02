"""Block counts of k4/lemmam_x.md §7.1 recomputed on PR #33's model (k4/c4_verify_H/lb4r.py, via k4/lemmam_x_check.py),
without code from k4/lemmam_x.c: for a profile and an insertion prefix (agents), the block every unprocessed agent
would start next, with its frozen and threatened agents, rho, kappa0, the slot count delta and the chain-end count.
A second implementation for small instances (the (L0) and (L1∃) examples of §7.3), not for the exhaustive runs.
Usage: lemmam_x_blocks.py 'sets' 'vals' [prefix, e.g. 0,3]      (prints one line per candidate agent)"""
import itertools, json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lemmam_x_check as C
RM, M = C.RM, C.M


def run_blocks(inst, ids):
    """Phase 1 with the insertion sequence ids (agent ids, then index order): list of blocks [(agent, pick)], picks"""
    U = list(range(inst.n)); G0 = list(range(inst.m)); k = 0; blocks = []; pick = [-1] * inst.n
    while U:
        lost = [i for i in U if any(g not in G0 for g in inst.R[i])]
        if lost:
            def key(i):
                f = M.fav(inst, i, G0)
                r = len(inst.R[i]) if f is None else sum(1 for h in inst.R[i] if inst.v[i][f] < inst.v[i][h])
                return (r, sum(1 for g in G0 if inst.v[i][g] > 0), i)
            x = min(lost, key=key)
        else:
            x = ids[k] if k < len(ids) else U[0]
            k += 1
            blocks.append([])
        f = M.fav(inst, x, G0)
        blocks[-1].append(x); pick[x] = -1 if f is None else f
        U.remove(x)
        if f is not None:
            G0.remove(f)
    return blocks, pick


def val(inst, x, S):
    return sum(inst.v[x][g] for g in S)


def counts(inst, blk, pick, G, last):
    """the slot count and the chain-end count of block blk (agents) against the unpicked goods G"""
    needs = {y: {g for g in inst.R[y] if pick[y] < 0 or inst.v[y][g] > inst.v[y][pick[y]]} for y in blk}
    frozen = {x for x in blk if pick[x] >= 0 and any(pick[x] in needs[y] for y in blk if y != x)}
    r = blk[-1] if last else None
    W = set(G) | ({pick[r]} if last and pick[r] >= 0 else set())
    thr = {x for x in blk if x != r and pick[x] >= 0 and RM.threatened(inst, x, W, [pick[x]])}
    X = [x for x in blk if x in frozen and x in thr]
    rho = {}
    for x in X:
        cand = [g for g in G if g in inst.R[x]]
        worst = 0
        for h in ([None] if last else [None] + cand):
            ch = [g for g in cand if g != h]
            best = next(s for s in range(len(ch) + 1) for D in itertools.combinations(ch, s)
                        if not RM.threatened(inst, x, W - set(D), [pick[x]]))
            worst = max(worst, best)
        rho[x] = worst
    k0 = sum(1 if pick[y] >= 0 else 2 for y in blk if y not in frozen and y not in thr and y != r)
    # chain ends: non-frozen agents reached from x by needs, not threatened, not r
    def ends(x):
        out, stack, seen = set(), [x], {x}
        while stack:
            z = stack.pop()
            for y in blk:
                if y in seen or pick[z] < 0 or pick[z] not in needs[y]:
                    continue
                seen.add(y)
                if y in frozen:
                    stack.append(y)
                elif y not in thr and y != r:
                    out.add(y)
        return out
    E = {x: ends(x) for x in X}
    de = 0
    for s in range(1, len(X) + 1):
        for Xp in itertools.combinations(X, s):
            de = max(de, sum(rho[x] for x in Xp) - len(set().union(*(E[x] for x in Xp))))
    return max(0, sum(rho.values()) - k0), de, dict(frozen=sorted(frozen), threatened=sorted(thr), rho=rho, kappa0=k0,
                                                   ends={x: sorted(E[x]) for x in X})


def main():
    sets, vals = json.loads(sys.argv[1]), json.loads(sys.argv[2])
    prefix = [int(a) for a in sys.argv[3].split(',')] if len(sys.argv) > 3 and sys.argv[3] else []
    inst = RM.make_inst(sets, vals)
    blocks, pick = run_blocks(inst, prefix)
    done = [x for b in blocks[:len(prefix)] for x in b]
    for c in range(inst.n):
        if c in done:
            continue
        bl, pk = run_blocks(inst, prefix + [c])
        b = bl[len(prefix)]
        picked = {pk[x] for bb in bl[:len(prefix) + 1] for x in bb if pk[x] >= 0}
        G = [g for g in range(inst.m) if g not in picked]
        last = len(bl) == len(prefix) + 1
        d, de, info = counts(inst, b, pk, G, last)
        print(f"prefix {prefix} insert {c}: block {b} picks {[pk[x] for x in b]} {'last' if last else 'not last'};"
              f" slot count {d}, chain-end count {de}; {info}")


if __name__ == '__main__':
    main()
