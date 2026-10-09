"""Leader rules for Phase 1's insertion steps, tested with NO rotation (fix='none'): how often is r not a valid
owner? Also checks the counting fact: r invalid => every block's leader is exposed for r."""
import sys, os, collections, multiprocessing, random
sys.path.insert(0, os.path.dirname(__file__))
from lbx import State, lbx, LEADERS, core_profiles, efx0, owner_step

def others_tops(st, unproc, x): return {st.rank[y][0] for y in unproc if y != x}
def others_valued(st, unproc, x): return {g for y in unproc if y != x for g in st.rank[y]}

def lead_tops2(st, unproc, free):
    """prefer a leader whose b and c are both tops of other unprocessed agents (it can then never be exposed)"""
    for x in unproc:
        T = others_tops(st, unproc, x)
        if st.rank[x][1] in T and st.rank[x][2] in T: return x
    return unproc[0]

def lead_tops_score(st, unproc, free):
    """prefer the leader with the most of b, c among other agents' tops (2, then 1, then 0), then index"""
    return max(unproc, key=lambda x: (sum(g in others_tops(st, unproc, x) for g in st.rank[x][1:]), -x))

def lead_untop(st, unproc, free):
    """prefer a leader whose top no other unprocessed agent values (it can then never be frozen)"""
    for x in unproc:
        if st.rank[x][0] not in others_valued(st, unproc, x): return x
    return unproc[0]

def lead_combo(st, unproc, free):
    """tops2, else untop, else index"""
    for x in unproc:
        T = others_tops(st, unproc, x)
        if st.rank[x][1] in T and st.rank[x][2] in T: return x
    return lead_untop(st, unproc, free)

def lead_valued2(st, unproc, free):
    """prefer a leader whose b and c are both valued (any rank) by other unprocessed agents"""
    for x in unproc:
        V = others_valued(st, unproc, x)
        if st.rank[x][1] in V and st.rank[x][2] in V: return x
    return unproc[0]

def lead_rev(st, unproc, free): return unproc[-1]

LEADERS.update(tops2=lead_tops2, topscore=lead_tops_score, untop=lead_untop, combo=lead_combo,
               valued2=lead_valued2, rev=lead_rev)
RULES = ['index', 'tops2', 'topscore', 'untop', 'combo', 'valued2', 'rev']

def check_fact(rank, m):
    """index order; in the bad case, is every block's leader exposed for r (and each block's slots exactly 1)?"""
    st = State(rank, m); order, Y, blk, _ = st.phase1(LEADERS['index']); U = st.upgrades(Y, [])
    tag, r = owner_step(st, Y, U, order, blk)
    if tag != 'bad': return None
    E = set(st.exposed(r, Y, U)); nblocks = max(blk)
    leaders = {i for i in range(st.n) if blk[i] and (order.index(i) == 0 or blk[order[order.index(i) - 1]] != blk[i])}
    return E == leaders and len(leaders) == nblocks

def work(args):
    n, m, rank = args
    out = []
    for rule in RULES:
        X, tag = lbx(rank, m, leader=rule, fix='none')
        out.append((rule, tag, X is None or efx0(rank, m, X)))
    return n, out, check_fact(rank, m), (rank, m)

if __name__ == '__main__':
    maxn = int(sys.argv[1]); sample = int(sys.argv[2]) if len(sys.argv) > 2 else 0; minn = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    bad = collections.Counter(); tot = collections.Counter(); notefx = collections.Counter()
    fact = collections.Counter(); first = {}
    with multiprocessing.Pool(4) as pool:
        for n, out, f, inst in pool.imap_unordered(work, core_profiles(maxn, sample=sample, minn=minn), chunksize=500):
            tot[n] += 1; fact[f] += 1
            for rule, tag, ok in out:
                if tag == 'bad':
                    bad[(rule, n)] += 1; first.setdefault(rule, inst)
                if not ok: notefx[rule] += 1
    ns = sorted(tot)
    print(f"profiles: {dict(tot)} ({'every profile' if not sample else f'{sample} random per core'})")
    print("fact check (index order, bad cases): every leader exposed for r =", dict(fact))
    for rule in RULES:
        print(f"  {rule:9s} r invalid (would need a rotation): " + "  ".join(f"n={n}: {bad[(rule, n)]}" for n in ns)
              + (f"   NOT EFX0 outputs: {notefx[rule]}" if notefx[rule] else ""))
        if rule in first: print(f"            first: {first[rule]}")
