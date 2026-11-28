"""Certify the 6 graphical all-P4 cores of K4.MC7 (n = 6, m = 15; k4/MINCEX.md §8) directly with the frontier CEGAR
(k4/frontier/search.py, scanner scan2.c), instead of through the multigraph theorem of Afshinmehr et al.  Same core
model, type domains, inner D2 model and certificate record format as search.py, so k4/check4_fast.py-style checks apply.
Writes one JSON record per core to the output (append; already present cores are skipped).
    python3 k4/frontier/graphical6.py OUT.jsonl [INDEX ...]"""
import gzip, json, os, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
import search as SF
from multiprocessing import Pool
SF.TRIES = 2                                              # as the frontier runs (--tries=2)
RES = os.path.join(HERE, '..', '..', 'results', 'k4_min_cex_cores_4.json.gz')


def cores():
    return [r for r in json.load(gzip.open(RES)) if r.get('d2_fails') is None]


if __name__ == '__main__':
    out = sys.argv[1]; want = [int(a) for a in sys.argv[2:]] or list(range(6))
    done = set()
    if os.path.exists(out):
        for l in open(out): done.add(json.loads(l)['idx'])
    print('$ python3 k4/frontier/graphical6.py', *sys.argv[1:], flush=True)
    tasks = [(r['n'], r['m'], i, r['sets'], 20) for i, r in enumerate(cores()) if i in want and i not in done]
    with Pool(min(4, len(tasks) or 1)) as pool:
        for rec in pool.imap_unordered(SF.solve, tasks):
            print('core %d %s: model %s, D2 fails %s, %d allocations, counterexample %s, %.0f s' % (
                rec['idx'], rec['sets'], rec['model'], rec.get('D2_fails'), len(rec['allocs']), rec['counterexample'],
                rec['time']), flush=True)
            with open(out, 'a') as f: f.write(json.dumps(rec, separators=(',', ':')) + '\n')
