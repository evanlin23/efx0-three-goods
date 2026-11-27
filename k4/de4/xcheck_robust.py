"""Cross-check of k4/de4/de4r.c against the Python screen (k4/de4/ss_screen.py) on the same profiles: for each
variant, the number of maxima and of profiles with a non-completable maximum must agree.
  python3 k4/de4/xcheck_robust.py"""
import itertools, os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import ss_screen as S
from de4lib import Inst, load_cores, type_options
from check import write_input
_types = S.types
def types2(I, i, A):
    t = _types(I, i, A)
    if t == 'U' and I.val(i, A) >= I.val(i, [g for g in I.sets[i] if g not in A]):
        return 'UR'
    return t
S.types = types2
S.BASE_LEV['UR'] = 5
V = S.Variant
VARIANTS = [V('DE4^v3', {'LP': 3}, ['v3']), V('v3+rob6', {'LP': 3, 'UR': 6}, ['v3']),
            V('v3+rob5.5', {'LP': 3, 'UR': 5.5}, ['v3']), V('rob6', {'LP': 3, 'UR': 6})]
exe = os.path.join(HERE, 'de4r')
subprocess.run(['gcc', '-O2', '-w', '-o', exe, os.path.join(HERE, 'de4r.c')], check=True)
bad = 0
jobs = [('k4_certs_2.json.gz', range(5), 97), ('k4_certs_3.json.gz', range(0, 51, 10), 40009),
        ('k4_certs_4_n4_2.json.gz', [131, 127], 300007)]
for path, idxs, step in jobs:
    cores = load_cores(os.path.join(ROOT, 'results', path))
    for ci in idxs:
        sets = cores[ci]
        out = subprocess.run([exe, '3', str(step)], input=write_input(sets), capture_output=True, text=True).stdout
        line = [l for l in out.split('\n') if l.startswith('var0_maxima')][0].split()
        cd = dict(zip(line[0::2], map(int, line[1::2])))
        py = {}
        for idx, vals in enumerate(itertools.product(*[type_options(s) for s in sets])):
            if idx % step != 3:
                continue
            I = Inst(sets, list(vals)); C = S.Comp(I)
            for c, Vr in enumerate(VARIANTS):
                St = S.all_states(Vr, I); mx = S.maxima(Vr, I, St)
                py['var%d_maxima' % c] = py.get('var%d_maxima' % c, 0) + len(mx)
                py['var%d_every_fail' % c] = py.get('var%d_every_fail' % c, 0) + any(not C.ok(Y) for Y in mx)
        ok = all(cd[k] == py[k] for k in py)
        bad += not ok
        print('agree' if ok else 'DISAGREE', path, 'core', ci, {k: (cd[k], py[k]) for k in sorted(py)}, flush=True)
print('xcheck:', 'all agree' if not bad else '%d disagreements' % bad)
