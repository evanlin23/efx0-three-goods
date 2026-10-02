"""Replace the rotation by a restart: when r is not a valid owner, let x = k* (the exposed leader of r's block,
equivalently the last exposed agent) and redo the draft. Variants:
  pre_x   : x takes {b_x, c_x} up front (upgraded), the others redo Phase 1 on the remaining goods; owner x if needed
  pre_r   : same, but the owner is the new r (last non-upgraded agent) if valid, else x
  demote  : redo Phase 1 with x never chosen as a leader (unless it is the only agent left); owner r
Counts outputs that are not EFX0 or where no valid owner exists."""
import sys, os, collections, multiprocessing
sys.path.insert(0, os.path.dirname(__file__))
from lbx import State, lbx, LEADERS, FIXES, core_profiles, efx0, owner_step

def kstar(st, Y, U, blk, r):
    return next(x for x in st.exposed(r, Y, U) if blk[x] == blk[r])

def finish(st, Y, U, owners):
    """complete with the first valid owner among `owners` (HitSet test), or no owner if the junk fits"""
    J = st.junk(Y, U); cap = st.caps(Y, U)
    if len(J) <= sum(cap): return st.complete(Y, U, None, []), 'noowner'
    for o in owners:
        if o is None: continue
        H = st.hitset(st.exposed(o, Y, U), Y, U)
        # an exposed agent whose pair has no junk good cannot be protected
        if all((st.rank[z][1] in J or st.rank[z][2] in J) for z in st.exposed(o, Y, U)) and len(H) <= sum(cap) - cap[o]:
            return st.complete(Y, U, o, H), 'owner'
    return None, 'fail'

def fix_pre(owner_first):
    def f(st, lead, Y, U, order, blk, r):
        x = kstar(st, Y, U, blk, r)
        order2, Y2, blk2, _ = st.phase1(lead, pre=(x,))
        Y2[x] = st.rank[x][1]
        U2 = st.upgrades(Y2, [x])
        r2 = [i for i in order2 if i not in U2]
        r2 = r2[-1] if r2 else None
        return finish(st, Y2, U2, [x, r2] if owner_first == 'x' else [r2, x])
    return f

def fix_demote(st, lead, Y, U, order, blk, r):
    x = kstar(st, Y, U, blk, r)
    def lead2(st_, unproc, free):
        c = [i for i in unproc if i != x]
        return lead(st_, c, free) if c else x
    order2, Y2, blk2, _ = st.phase1(lead2)
    U2 = st.upgrades(Y2, [])
    r2 = [i for i in order2 if i not in U2][-1]
    return finish(st, Y2, U2, [r2])

FIXES.update(pre_x=fix_pre('x'), pre_r=fix_pre('r'), demote=fix_demote)
VARIANTS = ['rotate', 'pre_x', 'pre_r', 'demote']

def work(args):
    n, m, rank = args
    out = []
    for fx in VARIANTS:
        X, tag = lbx(rank, m, fix=fx)
        out.append((fx, tag, X is not None and efx0(rank, m, X)))
    return n, out, (rank, m)

if __name__ == '__main__':
    maxn = int(sys.argv[1]); sample = int(sys.argv[2]) if len(sys.argv) > 2 else 0; minn = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    tot = collections.Counter(); fails = collections.Counter(); first = {}; rot = collections.Counter()
    with multiprocessing.Pool(4) as pool:
        for n, out, inst in pool.imap_unordered(work, core_profiles(maxn, sample=sample, minn=minn), chunksize=500):
            tot[n] += 1
            if out[0][1].startswith('rot'): rot[n] += 1
            for fx, tag, ok in out:
                if not ok: fails[(fx, n)] += 1; first.setdefault(fx, (inst, tag))
    ns = sorted(tot)
    print(f"profiles {dict(tot)} ({'every profile' if not sample else f'{sample} random per core'}); K3ALG rotates on {dict(rot)}")
    for fx in VARIANTS:
        print(f"  {fx:7s} failures: " + "  ".join(f"n={n}: {fails[(fx, n)]}" for n in ns))
        if fx in first: print(f"          first: {first[fx]}")
