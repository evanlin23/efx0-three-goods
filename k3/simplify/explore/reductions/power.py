"""Power check for Conjecture PO: profiles that HAVE a valid but non-completable state (so restricting to Pareto-optimal
states is what makes the test pass). python3 power.py N M"""
import sys
from engine import gen_small
from po_fast import states
from po_states import completable
n, m = int(sys.argv[1]), int(sys.argv[2]); tot = withbad = nb = 0
for rank in gen_small(n, m):
    tot += 1; bad = [s for s in states(rank, m) if not completable(rank, m, s[0], s[1])]
    withbad += bool(bad); nb += len(bad)
print(f"n={n} m={m}: {withbad} of {tot} profiles have a valid state that is not completable ({nb} such states, none Pareto optimal)")
