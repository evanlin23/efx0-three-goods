"""W-walks (k4/haxell.md §7): from given states, apply Conjecture W's steps (ht_wlocal.Loc.check, augmenting first)
until the allocation is complete, re-checking every step independently (EFX0 and the strict decrease of
(|pool|, -welfare)).  Sources: chf (the stranded welfare maxima of CH-F); sprime:SMAX (the stranded states of S(sigma, k) and
S'(sigma, k), sigma = 2..SMAX, k = 3, 4, default values, from kgen/charity via ext_sprime.py).

    python3 k4/haxell/ht_wwalk.py chf | sprime:SMAX"""
import sys, time
import ext_instances as X
from ht_wlocal import Loc, walk

if __name__ == '__main__':
    print('$ python3 k4/haxell/ht_wwalk.py', *sys.argv[1:], flush=True)
    src = sys.argv[1] if len(sys.argv) > 1 else 'chf'
    if src.startswith('sprime'):
        import ext_sprime as SP
        smax = int(src.split(':')[1]) if ':' in src else 4
        items = [SP.sprime(sg, k, own) for sg in range(2, smax + 1) for k in (3, 4) for own in (True, False)]
    else:
        items = X.chf()
    for name, sets, vals, m, own in items:
        L = Loc(sets, vals, m); t0 = time.time()
        ok, steps = walk(L, own)
        print(name, 'n', L.n, 'm', m, 'pool', own.count(-1), 'walk from the stranded state:', 'complete EFX0 allocation reached' if ok else 'STUCK' if ok is False else 'step cap',
              'after', steps, 'steps (%.1f s)' % (time.time() - t0), flush=True)
