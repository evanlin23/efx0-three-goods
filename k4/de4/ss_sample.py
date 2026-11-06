"""DE4, DE4 + v3 and DE4 + v3 + CD (attempts/k4-de4-ss.md) on the larger suite instances (n <= 6, m <= 15, not in the
screen set) or on random strict profiles of certified cores. EVIDENCE only.
  python3 k4/de4/ss_sample.py suite 0 0
  python3 k4/de4/ss_sample.py CORE_FILES PER SEED   (comma-separated files under results/)"""
import sys, json, glob, random, collections, multiprocessing as mp
import os
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import ss_screen as ss
from de4lib import Inst, load_cores, random_profile
V = ss.Variant
VARIANTS = [V('DE4', {'LP': 3}), V('DE4+v3', {'LP': 3}, ['v3']), V('LP3+v3+CD2.5', {'LP': 3, 'CD': 2.5}, ['v3'])]
def job(arg):
    name, I = arg
    C = ss.Comp(I)
    return name, [(Vr.name,) + ss.screen(Vr, I, C)[:2] + (ss.screen(Vr, I, C)[3],) for Vr in VARIANTS]
def tasks(mode, per, seed):
    if mode == 'suite':
        for f in sorted(glob.glob(os.path.join(ROOT, 'k4/suite/instances/*.json'))):
            d = json.load(open(f))
            if d['n'] <= 6 and d['m'] <= 15 and d.get('vals') and not (d['n'] <= 5 and d['m'] <= 11):
                yield d['id'], Inst.from_json(d)
    else:
        rng = random.Random(seed)
        cores = []
        for f in mode.split(','):
            cores += load_cores(os.path.join(ROOT, 'results', f))
        for t in range(per):
            s = rng.choice(cores)
            yield '%s#%d' % (mode, t), Inst(s, random_profile(s, rng))
if __name__ == '__main__':
    mode, per, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    fails = collections.Counter(); some = collections.Counter(); ex = collections.defaultdict(list); tot = 0
    with mp.Pool(2) as p:
        for name, out in p.imap_unordered(job, tasks(mode, per, seed), chunksize=4):
            tot += 1
            for vn, ok, nmx, sm in out:
                if not ok: fails[vn] += 1; ex[vn].append(name)
                if not sm: some[vn] += 1
    print(mode, 'instances', tot)
    for Vr in VARIANTS:
        print('  %-14s every-fail %d some-fail %d %s' % (Vr.name, fails[Vr.name], some[Vr.name], ex[Vr.name][:5]))
