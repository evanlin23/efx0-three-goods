"""Sensitivity test of k4/check4.py: the n = 3 certificate passes, and each of these corruptions is rejected:
(a) the only core with m = 9 dropped (a whole m group missing), (b) a non-D2 allocation added (two bundles of more
than 2 goods), (c) malformed allocations (too short; an owner out of range), (d) one allocation deleted,
(e) one core deleted, (f) --expect with the wrong number of cores. Usage: test_check4.py (about 1 min)"""
import copy, gzip, json, os, sys, tempfile
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check4

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
base = json.load(gzip.open(os.path.join(ROOT, 'results', 'k4_certs_3.json.gz'), 'rt'))
tmp = tempfile.mkdtemp()

def run(data, expect=None):
    p = os.path.join(tmp, 'c.json.gz')
    with gzip.open(p, 'wt') as f: json.dump(data, f)
    with Pool(os.cpu_count()) as pool: return check4.check_file(p, pool, expect)[0]

def variant(f):
    d = copy.deepcopy(base); f(d); return d

cases = {
    'original': (base, None, True),
    '(a) m = 9 group dropped': (variant(lambda d: d.__setitem__('cores', [c for c in d['cores'] if c['m'] != 9])), None, False),
    '(b) non-D2 allocation added': (variant(lambda d: d['cores'][-1]['allocs'].append([0, 0, 0, 1, 1, 1, 2, 2, 2])), None, False),
    '(c1) allocation too short': (variant(lambda d: d['cores'][5]['allocs'].append(d['cores'][5]['allocs'][0][:-1])), None, False),
    '(c2) owner out of range': (variant(lambda d: d['cores'][5]['allocs'].append([3] * d['cores'][5]['m'])), None, False),
    '(d) one allocation deleted': (variant(lambda d: d['cores'][20]['allocs'].pop()), None, False),
    '(e) one core deleted': (variant(lambda d: d['cores'].pop(10)), None, False),
    '(f) wrong --expect': (base, {(3, 'any'): 50}, False),
}
assert base['cores'][-1]['m'] == 9 and sum(c['m'] == 9 for c in base['cores']) == 1
bad = 0
for name, (data, expect, want) in cases.items():
    got = run(data, expect)
    print(f"{name}: checker says {'OK' if got else 'FAILED'} (expected {'OK' if want else 'FAILED'})", flush=True)
    bad += got != want
print("all sensitivity cases behave as expected" if not bad else f"{bad} cases WRONG")
sys.exit(1 if bad else 0)
