"""Smallest instances (by n, then m, then sum of |R_i|) of three kinds, from a source of vm_test.items_for:
  skel : no Phase I-II matching of V-M extends to an EFX0 allocation
  late : some matching extends, but no run of V-M (any resolution of its choices) is EFX0
  lit  : the literal reading (aout=all) has a run that is not EFX
    python3 k4/vm/vm_smallest.py SOURCE [K]"""
import sys, os, json, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
from vm_test import items_for
from vm_extend import completable, Enc


def one(it):
    name, sets, vals, m = it
    I = V.Inst(sets, vals, m); E = Enc(sets, vals, m)
    ext = False
    for ch, res in V.all_runs(V.vm_run, I, limit=3000, stop='II'):
        if not isinstance(res, V.Stuck) and completable(E, res[0]):
            ext = True; break
    anyz = any(not isinstance(r, V.Stuck) and V.is_efx0(I, r[0]) for ch, r in V.all_runs(V.vm_run, I, limit=3000))
    lit = False if os.environ.get('NOLIT') else any(not isinstance(r, V.Stuck) and not V.is_efx(I, r[0]) for ch, r in V.all_runs(V.vm_run, I, limit=3000, aout='all'))
    size = (I.n, I.m, sum(len(s) for s in sets))
    return name, sets, vals, m, size, (not ext), (ext and not anyz), lit


if __name__ == '__main__':
    K = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    best = {'skel': [], 'late': [], 'lit': []}
    with mp.Pool(os.cpu_count()) as pool:
        for name, sets, vals, m, size, sk, late, lit in pool.imap_unordered(one, items_for(sys.argv[1]), chunksize=8):
            for key, flag in (('skel', sk), ('late', late), ('lit', lit)):
                if flag:
                    best[key].append((size, name, sets, vals, m))
    print('$ python3 k4/vm/vm_smallest.py', ' '.join(sys.argv[1:]))
    for key, L in best.items():
        L.sort()
        print(key, 'count', len(L))
        for size, name, sets, vals, m in L[:K]:
            print('  ', name, 'n=%d m=%d sum|R|=%d' % size, json.dumps({'sets': sets, 'vals': vals, 'm': m}))
