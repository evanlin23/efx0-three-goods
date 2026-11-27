"""Print the hard starts (picks with no one-absorber completion) in readable form: rankings, picks, wants, frozen
agents, junk, and the repairing chains (k4/sdc/de_free.py moves followed by a one-absorber completion).

    python3 k4/oc1_hall/dump_hard.py SRC [NMAX] [LIMIT]
"""
import sys, os, itertools, collections, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, slot_test, bundles_of
from sdclib import Enc
from oc_absorb import extends_A
from min_frozen import load
import de_free as DF
DF.CHAIN_ONLY = True


def describe(I, P):
    out = []
    for i in range(I.n):
        r = sorted(I.R[i], key=lambda g: I.key[i][g], reverse=True)
        s = ' > '.join('%d(%d)%s' % (g, I.v[i][g], '*' if g == P.Y[i] else ('j' if g in P.J else '')) for g in r)
        out.append('  agent %d: %s   pick %s  wanted by %s%s' % (i, s, P.Y[i], P.W[i], '  FROZEN' if i in P.F else ''))
    return '\n'.join(out)


if __name__ == '__main__':
    src = sys.argv[1]; NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 3; LIMIT = int(sys.argv[3]) if len(sys.argv) > 3 else 10
    shown = 0
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > NMAX: continue
        I = Inst(sets, vals, m, name); E = Enc(sets, vals, m); seen = set()
        for od in itertools.permutations(range(n)):
            Y = picks(I, od)
            if Y in seen: continue
            seen.add(Y); P = Picks(I, Y); base = base_of_picks(I, Y)
            if extends_A(E, base, 1): continue
            print('HARD', name, json.dumps((sets, vals)), 'order', od, 'picks', Y, 'J', P.J)
            print(describe(I, P))
            for b2, ds in DF.moves(E, base, describe=True, all_desc=True).items():
                if not extends_A(E, b2, 1): continue
                for kind, path, H in ds:
                    B2 = bundles_of(I, b2)
                    print('   repair: chain %s H %s -> bases %s' % (path, {k: list(v) for k, v in H.items() if v}, B2))
            shown += 1
            if shown >= LIMIT: sys.exit()
