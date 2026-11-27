"""E10: the two-phase shape (k4/sd_induct.md §3).  Among the one-absorber completions of the picks, is there one in
which (TP) every pick-frozen agent (pick wanted by someone) holds its pick alone and the absorber (if any) is not
frozen?  Variants: TP-o (additionally the absorber is a prescribed unfrozen agent: some / every unfrozen agent that
absorbs somewhere).  Under TP, EFX0 reduces to: every agent other than the absorber o is unthreatened by o's bundle
(Lemma TP, written proof in the note); this is checked too (reduce == brute force).

    python3 k4/sdind/e10_twophase.py special|screen|suite|cores:FILES:N:SEED [NMAX]"""
import sys, itertools, collections, json, time
import numpy as np
import _paths
from sdilib import Inst, sd, wanted_by, completions, picks_base, bundles_of, efx0
from e1_delete import load
from e3_suffix import absorber

if __name__ == '__main__':
    src = sys.argv[1]; NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    C = collections.Counter(); t0 = time.time(); shown = collections.Counter()
    print('$ python3 k4/sdind/e10_twophase.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src):
        if len(sets) > NMAX or len(sets) < 2: continue
        I = Inst(sets, vals, m); C['instances'] += 1
        seen = set()
        for o_ in itertools.permutations(range(I.n)):
            Y = list(sd(I, o_)[0])
            if tuple(Y) in seen: continue
            seen.add(tuple(Y))
            try:
                J, A = completions(I, picks_base(I, Y), 1)
            except ValueError:
                continue
            if len(A) == 0: continue
            C['starts'] += 1
            W = wanted_by(I, Y); fr = [bool(w) for w in W]
            tp = []
            for x in A:
                o = absorber(x, I.n)
                if o is not None and fr[o]: continue
                if any(fr[x[t]] for t in range(len(J)) if x[t] != o): continue
                tp.append((o, x))
            C['starts with a TP completion'] += bool(tp)
            absA = set(absorber(x, I.n) for x in A)
            tpo = set(o for o, x in tp)
            C['starts: every unfrozen absorber of some completion is the absorber of a TP completion'] += \
                all((o in tpo) for o in absA if o is not None and not fr[o]) and (None not in absA or None in tpo or bool(tp))
            if not tp and shown['tp'] < 4:
                shown['tp'] += 1
                print('NO TP COMPLETION', name, json.dumps((sets, vals)), 'picks', Y, 'frozen', [i for i in range(I.n) if fr[i]],
                      'absorbers', sorted(map(str, absA)), flush=True)
            # Lemma TP check on random TP-shaped assignments
            if tp:
                unf = [i for i in range(I.n) if not fr[i]]
                for o in set(o for o, _ in tp) - {None}:
                    for x in itertools.islice(itertools.product(unf, repeat=len(J)), 200):
                        x = np.array(x)
                        cnt = np.bincount(x, minlength=I.n)
                        if any(cnt[i] >= 2 for i in range(I.n) if i != o): continue
                        B = bundles_of(picks_base(I, Y), J, x)
                        red = all((lambda vs: not vs or sum(vs) - min(vs) <= I.val(i, B[i]))([int(I.V[i, g]) for g in B[o]])
                                  for i in range(I.n) if i != o)
                        C['Lemma TP check: agree' if red == efx0(I, B) else 'LEMMA TP MISMATCH'] += 1
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
