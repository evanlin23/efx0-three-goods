"""E19: an explicit lookahead rule for the reverse-SD insertion in TP shape (k4/sd_induct.md §8).

For a start Y and an unfrozen absorber o of some TP-shaped completion (pick-frozen agents alone): orders pi producing
Y with all pick-frozen agents first and pi_n = o.  Insert o (all junk), then the unfrozen agents (reverse pi), then
the frozen ones (no junk).  An unfrozen agent f, on arrival, may take one junk good g of o's bundle (Theorem PR-TP:
always allowed); the rule chooses
  - if f is threatened: among the goods that make it safe, the one with the highest demand, then f's own value;
  - else: the good with the highest demand if that demand is positive, else nothing;
where demand(g) = the number of frozen agents x still to come with v_x(g) > 0 whose danger is not yet cleared
(x threatened by o's current bundle) -- variant 'need' -- or simply with v_x(g) > 0 -- variant 'val'.
Success: every frozen agent unthreatened at its arrival (then the result is EFX0 by Corollary TP).

    python3 k4/sdind/e19_lookahead.py special|screen|suite|logs|cores:FILES:N:SEED [NMAX]"""
import sys, itertools, collections, json, time
import numpy as np
import _paths
from sdilib import Inst, sd, wanted_by, completions, picks_base, bundles_of
from e1_delete import load
from e3_suffix import absorber


def thr(I, bundle, i, own):
    vs = [int(I.V[i, g]) for g in bundle]
    return bool(vs) and sum(vs) - min(vs) > own


def run(I, Y, J, pi, o, fr, variant):
    seq = list(pi)[::-1]
    Bo = [Y[o]] + list(J) if Y[o] is not None else list(J)
    held = {}
    frozen_future = [x for x in seq if fr[x]]
    for k, f in enumerate(seq[1:], 1):
        own = I.val(f, [Y[f]] if Y[f] is not None else [])
        junkBo = [g for g in Bo if g in J]
        if fr[f]:
            if thr(I, Bo, f, own): return False
            continue
        future = [x for x in seq[k + 1:] if fr[x]]
        def demand(g):
            if variant == 'val': return sum(1 for x in future if I.V[x, g] > 0)
            return sum(1 for x in future if I.V[x, g] > 0 and thr(I, Bo, x, I.val(x, [Y[x]])))
        threatened = thr(I, Bo, f, own)
        if threatened:
            safe = [g for g in junkBo if not thr(I, [h for h in Bo if h != g], f, own + int(I.V[f, g]))]
            if not safe: return False
            g = max(safe, key=lambda g: (demand(g), int(I.V[f, g]), -g))
        else:
            if not junkBo: continue
            g = max(junkBo, key=lambda g: (demand(g), int(I.V[f, g]), -g))
            if demand(g) == 0: continue
        Bo = [h for h in Bo if h != g]; held[f] = g
    return True


if __name__ == '__main__':
    src = sys.argv[1]; NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    C = collections.Counter(); t0 = time.time(); shown = collections.Counter()
    print('$ python3 k4/sdind/e19_lookahead.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src):
        if len(sets) > NMAX or len(sets) < 2: continue
        I = Inst(sets, vals, m); C['instances'] += 1
        byY = collections.defaultdict(list)
        for o_ in itertools.permutations(range(I.n)):
            byY[tuple(sd(I, o_)[0])].append(o_)
        for Y, orders in byY.items():
            Y = list(Y)
            try:
                J, A = completions(I, picks_base(I, Y), 1)
            except ValueError:
                continue
            if len(A) == 0: continue
            W = wanted_by(I, Y); fr = [bool(w) for w in W]
            tpo = set()
            for x in A:
                ab = absorber(x, I.n)
                if ab is not None and fr[ab]: continue
                if any(fr[x[t]] for t in range(len(J)) if x[t] != ab): continue
                tpo |= ({ab} if ab is not None else set(i for i in range(I.n) if not fr[i]))
            for o in sorted(tpo):
                ords = [pi for pi in orders if pi[-1] == o and
                        all(fr[pi[t]] or not any(fr[pi[s]] for s in range(t + 1, I.n)) for t in range(I.n))]
                if not ords: C['(Y, o) with no frozen-first order'] += 1; continue
                C['(Y, o) cases (o absorbs a TP completion, or none needed)'] += 1
                for variant in ('need', 'val'):
                    rs = [run(I, Y, J, pi, o, fr, variant) for pi in ords]
                    C[variant + ': some frozen-first order works'] += any(rs)
                    C[variant + ': every frozen-first order works'] += all(rs)
                    if not any(rs) and shown[variant] < 3:
                        shown[variant] += 1
                        print('LOOKAHEAD FAILS', variant, name, json.dumps((sets, vals)), 'picks', Y, 'o', o, flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
