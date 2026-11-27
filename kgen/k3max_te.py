"""Independent check of k3-oc1's T-E for one terminal (kgen/n3.md §15.10): for EVERY k in E_t, rotate along k's
Rule E chain into t, apply LB's maximal upgrades, then a one-absorber completion exists with owner o in {none, t, k}
(if t was upgraded, owner t means t as a pair holder) where every terminal other than o, and k if k is not o, takes at
most one junk good; k's good g must leave no other top-holder's pair inside {b_k, c_k, g}.

The completion test is written here, separately from lbtest.lb2.  It is a bipartite matching of a hitting part of
the junk into the slots, with the owner taking the rest, checked against the threats of LB+'s Theorem 1' (a bundle of
three or more goods may not contain {b_x, c_x} of a top-holder x other than its owner).  Only parts/upgrade/exposed
and the Rule E chain come from shared code.  Needs K3OC1 as kgen/k3max_t1.py.

    K3OC1=... python3 kgen/k3max_te.py GAPFILE [SHARD NSHARDS]"""
import sys, os, json, re, ast, gzip, itertools, collections, time
K = os.environ.get('K3OC1', os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'k4', 'k3oc1'))
sys.path.insert(0, K); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3lib import base_of
from lbtest import parts, exposed, upgrade
from k3max_t1 import rotate
from k3max_ruleE import topo, rule_e_chain


def complete(rk, m, base, owners, kslot):
    """one-absorber completion with the given owners (None = no owner); slots: every terminal (cap 1), and kslot
    (an agent, cap 1, good must keep it threat-free) unless it is the owner"""
    n = len(rk); B, J, U, NA, F, T = parts(rk, m, base)
    A = [x for x in range(n) if not U[x] and B[x] == [rk[x][0]]]           # top-holders
    def safe(bundle, holder):
        s = set(bundle)
        return len(s) <= 2 or not any(x != holder and rk[x][1] in s and rk[x][2] in s for x in A)
    for o in owners:
        if o is not None and not (o in T or U[o]): continue
        slots = [(a, set(J)) for a in T if a != o]
        if kslot is not None and kslot != o and U[kslot]:
            slots.append((kslot, set(g for g in J if safe(B[kslot] + [g], kslot))))
        for r in range(len(J), -1, -1):
            for C in itertools.combinations(J, r):
                rest = [g for g in J if g not in C]
                if o is None and rest: continue
                if o is not None and not safe(B[o] + rest, o): continue
                match = {}
                def aug(g, seen):
                    for i, (a, allowed) in enumerate(slots):
                        if g in allowed and i not in seen:
                            seen.add(i)
                            if i not in match or aug(match[i], seen): match[i] = g; return True
                    return False
                if all(aug(g, set()) for g in C): return o if o is not None else 'none'
    return None


if __name__ == '__main__':
    fn = sys.argv[1]; shard, nsh = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (0, 1)
    C = collections.Counter(); shown = 0; t0 = time.time()
    print('$ python3 kgen/k3max_te.py', os.path.basename(fn), *sys.argv[2:], flush=True)
    for li, line in enumerate(gzip.open(fn, 'rt')):
        if li % nsh != shard: continue
        mt = re.match(r'GAP (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+)', line)
        if not mt or int(mt.group(5)) != 1: continue
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); Y = ast.literal_eval(mt.group(4))
        ub = upgrade(rk, m, base_of(Y, m)); B, J, U, NA, F, T = parts(rk, m, ub); t = T[0]
        E = exposed(rk, ub, t, B, J, U); pos = topo(rk, B, U); C['drafts'] += 1; alldraft = True
        chainks = [k for k in E if rk[k][1] in J and rk[k][2] in J]          # pair inside the junk: a DE chain
        C['drafts with some k whose pair lies in J (a DE chain): %s' % bool(chainks)] += 1
        okchain = []
        for k in E:
            P = rule_e_chain(rk, B, U, k, t, pos); nb = upgrade(rk, m, rotate(rk, ub, B, k, P))
            r = complete(rk, m, nb, [None, t], k)
            if r is None: r = complete(rk, m, nb, [k], k)
            if k in chainks: okchain.append(r is not None)
            C['rotations'] += 1; C['rotations completing with owner %s' % ('none' if r == 'none' else ('t' if r == t else ('k' if r == k else 'NONE FOUND')))] += 1
            if r is None:
                alldraft = False
                if shown < 3: shown += 1; print('T-E FAILS', line.strip(), 'k', k, 'chain', P, flush=True)
        C['drafts where every k works (T-E)'] += alldraft
        if chainks: C['drafts where every k with pair in J works: %s' % all(okchain)] += 1
    for k in sorted(C): print(C[k], k)
    print('time %.0f s' % (time.time() - t0))
