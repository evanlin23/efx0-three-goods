"""Replay of the failed reductions of k4/c4min_reduce.md (attempts/k4-c4min-reduce-*.md), by both implementations:
k4/red_lib.py (Python, from the definitions) and k4/red.c (C, run on the one profile). Prints each check and ends with
"ALL CONFIRMED" if every check agrees. Usage: python3 attempts/k4_c4min_reduce_attempts.py (a few seconds)."""
import os, subprocess, sys, tempfile, hashlib
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'k4'))
from red_lib import Prof, Key, fewest_frozen_le1, bits, pc

INSTANCES = {
    # reduction (a), any fixed key: a key with no completable configuration (smallest n and m: n = 3, m = 6)
    'A1': dict(core='results/k4_certs_3.json.gz#17', m=6, sets=[[0, 1, 4, 5], [2, 3, 4, 5], [2, 3, 4, 5]],
               vals=[{0: 4, 1: 2, 4: 7, 5: 8}, {2: 2, 3: 3, 4: 4, 5: 8}, {2: 3, 3: 4, 4: 6, 5: 8}]),
    # reduction (a) with Theorem Z's potential at the best key, and (c) one role swap: every key fails (n = 3, m = 8)
    'A2': dict(core='results/k4_certs_3.json.gz#46', m=8, sets=[[0, 2, 6, 7], [1, 4, 6, 7], [3, 5, 6, 7]],
               vals=[{0: 3, 2: 4, 6: 2, 7: 8}, {1: 4, 4: 3, 6: 2, 7: 8}, {3: 3, 5: 4, 6: 2, 7: 8}]),
    # reduction (b), Theorem Z's argument at a fixed key under t = 0: a maximum of (-t, r', Lambda') without a
    # free-valid owner (n = 4; n <= 3 has none)
    'B1': dict(core='results/k4_certs_4_pure.json.gz#214', m=11, sets=[[0, 2, 7, 10], [1, 5, 8, 10], [3, 6, 9, 10], [4, 7, 8, 9]],
               vals=[{0: 4, 2: 3, 7: 2, 10: 8}, {1: 4, 5: 5, 8: 6, 10: 8}, {3: 3, 6: 2, 9: 4, 10: 8}, {4: 4, 7: 8, 8: 1, 9: 6}]),
}


def c_binary():
    src = os.path.join(HERE, '..', 'k4', 'red.c')
    h = hashlib.sha1(open(src, 'rb').read()).hexdigest()[:12]
    out = os.path.join(tempfile.gettempdir(), 'red_' + h)
    if not os.path.exists(out): subprocess.run(['gcc', '-O2', '-o', out, src], check=True)
    return out


def run_c(inst):
    n = len(inst['sets'])
    lines = ['%d %d' % (n, inst['m'])]
    for S, v in zip(inst['sets'], inst['vals']):
        lines.append('%d %s 1' % (len(S), ' '.join(map(str, S))))
        lines.append(' '.join(str(v[g]) for g in S))
    lines.append('0 1')
    out = subprocess.run([c_binary()], input='\n'.join(lines) + '\n', capture_output=True, text=True, check=True).stdout
    return {k: int(v) for k, v in (l.split() for l in out.splitlines() if not l.startswith('EX'))}


def configs(P, g, x):
    K = Key(P, g, x); out = []
    for Q, L in K.configs():
        st = [K.owner_status(Q, L, o) for o in K.free]
        out.append(dict(Q=Q, L=L, r=sum(K.robust(y, Q[y]) for y in K.free), lam=sum(K.level(y, Q[y]) for y in K.free),
                        t=int(P.v(x, L & K.Ux) > P.vals[x][g]), comp=any(s[2] for s in st), nfv=sum(s[0] for s in st)))
    return K, out


def maxima(cf, key):
    b = max(key(c) for c in cf)
    return [c for c in cf if key(c) == b]


ok = True
def check(name, cond):
    global ok
    print('  %-80s %s' % (name, 'yes' if cond else 'NO'))
    ok &= bool(cond)


for name, inst in INSTANCES.items():
    P = Prof(inst['vals'], inst['m'])
    f, keys = fewest_frozen_le1(P)
    C = run_c(inst)
    print('%s  %s  n=%d m=%d  f=%s  keys (g, x): %s' % (name, inst['core'], P.n, P.m, f, keys))
    check('f = 1 and omega >= 1 (Python; C: f1 = 1)', f == 1 and P.m - 2 * P.n + 1 >= 1 and C.get('f1') == 1)
    anyc = False
    per = {}
    for g, x in keys:
        K, cf = configs(P, g, x)
        per[x] = (K, cf)
        anyc |= any(c['comp'] for c in cf)
    check('C4min holds: some configuration completable (Python; C: prof_completable = 1)', anyc and C.get('prof_completable') == 1)
    if name == 'A1':
        bad = [x for x, (K, cf) in per.items() if not any(c['comp'] for c in cf)]
        check('key (5, 0) has no completable configuration (Python)', bad == [0])
        check('C: key_noncompletable = 1', C.get('key_noncompletable') == 1)
    if name == 'A2':
        for x, (K, cf) in per.items():
            mx = maxima(cf, lambda c: (c['r'], c['lam']))
            check('key (%d, %d): unique (r\', Lambda\')-maximum, t = 1, not completable, has a free-valid owner'
                  % (K.g, x), len(mx) == 1 and mx[0]['t'] == 1 and not mx[0]['comp'] and mx[0]['nfv'] >= 1)
            mx2 = maxima(cf, lambda c: (c['r'], -c['t'], c['lam']))
            check('key (%d, %d): every (r\', -t, Lambda\')-maximum completable' % (K.g, x), all(c['comp'] for c in mx2))
        check('C: FAIL_prof_some_key_every = 1 and FAIL_swap_some_terminal = 3', C.get('FAIL_prof_some_key_every') == 1 and C.get('FAIL_swap_some_terminal') == 3)
    if name == 'B1':
        K, cf = per[1]
        mx = maxima(cf, lambda c: (-c['t'], c['r'], c['lam']))
        check('key (10, 1): some (-t, r\', Lambda\')-maximum has no free-valid owner (Python)', any(c['nfv'] == 0 for c in mx))
        check('C: tmax_no_freevalid >= 1', C.get('tmax_no_freevalid', 0) >= 1)
        for c in mx:
            if c['nfv'] == 0:
                print('    witness: pairs %s, pool %s' % ({y: sorted(bits(q)) for y, q in c['Q'].items()}, sorted(bits(c['L']))))
print('ALL CONFIRMED' if ok else 'SOME CHECK FAILED')
