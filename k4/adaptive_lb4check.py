"""Cross-check of k4/adaptive.c against k4/lb4.c (PR #32), per core (k4/adaptive.md §1): on every core of the given
certificate files, LB4r with index insertion (adaptive.c -A0 -r3 against lb4.c -i0 -u3 -o0 -r3 -d2 -w1 -c1) and with
every insertion sequence run separately (adaptive.c -i1 -r3 against lb4.c -i1 ... ); compares, core by core, the
profile count (runs of LB4r with -i1), fails, the histogram of the fewest rotations (0 .. 3; lb4.c -d2: the bound
outermost, least over the policies) and the histogram of the policy that succeeded. (The numbers of leaves and of runs
of the lazy tester are not compared: they depend on which comparisons each implementation asks, and adaptive.c's owner
search is pruned.)
Usage: adaptive_lb4check.py FILE [FILE ...] [--jobs=J]"""
import gzip, json, os, subprocess, sys, time
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import adaptive_run as A
import lb4_run as L

MODES = [('index', ['-A0', '-r3'], ['-i0', '-u3', '-o0', '-r3', '-d2', '-w1', '-c1']),
         ('every sequence', ['-i1', '-r3'], ['-i1', '-u3', '-o0', '-r3', '-d2', '-w1', '-c1'])]

def lb4(line_h, line_t):
    h = list(map(int, line_h.split()[1:])); t = line_t.split()
    return dict(total=int(t[1]), leaves=int(t[3]), runs=int(t[5]), fails=int(t[7]), pol=h[:3], rot=h[3:7])

def ad(line):
    t = line.split(); d = A.parse(line)
    return dict(total=d['total'], leaves=int(t[3]), runs=int(t[5]), fails=d['fails'], pol=d['pol'], rot=d['rot'])

def run(task):
    c, mi = task
    inp = A.encode_core(c['sets'], c['m'])
    _, ao, lo = MODES[mi]
    pa = subprocess.run([A.BIN] + ao, input=inp, capture_output=True, text=True)
    pl = subprocess.run([L.BIN] + lo, input=inp, capture_output=True, text=True)
    la = [l for l in pa.stdout.split('\n') if l.startswith('total ')]
    ll = [l for l in pl.stdout.split('\n') if l.startswith('H ') or l.startswith('total ')]
    return c, ad(la[-1]), lb4(ll[-2], ll[-1])

def main():
    args = sys.argv[1:]
    jobs = int(next((a.split('=')[1] for a in args if a.startswith('--jobs=')), os.cpu_count()))
    A.build(); L.build()
    print('# adaptive_lb4check.py', ' '.join(args), '# adaptive.c sha256', A.SHA, '# lb4.c sha256', os.path.basename(L.BIN).split('_')[-1], flush=True)
    allok = True
    for f in [a for a in args if not a.startswith('--')]:
        cores = json.load(gzip.open(f, 'rt'))['cores']
        for mi, (name, ao, lo) in enumerate(MODES):
            t0 = time.time(); agree = 0; sa = None; sl = None
            with Pool(jobs) as pool:
                for c, a, l in pool.imap(run, [(c, mi) for c in cores]):
                    key = lambda d: (d['total'], d['fails'], d['rot'], d['pol'])
                    if key(a) == key(l): agree += 1
                    else: allok = False; print('  DISAGREE', c['sets'], c['m'], a, l)
                    sa = a if sa is None else {k: (sa[k] + a[k] if isinstance(a[k], int) else [x + y for x, y in zip(sa[k], a[k])]) for k in a}
                    sl = l if sl is None else {k: (sl[k] + l[k] if isinstance(l[k], int) else [x + y for x, y in zip(sl[k], l[k])]) for k in l}
            print(f"{os.path.basename(f)} {name}: adaptive.c {' '.join(ao)} / lb4.c {' '.join(lo)}: {agree} of {len(cores)} cores agree; "
                  f"adaptive.c total={sa['total']} fails={sa['fails']} rot={sa['rot']} pol={sa['pol']}; "
                  f"lb4.c total={sl['total']} fails={sl['fails']} rot={sl['rot']} pol={sl['pol']} time {time.time() - t0:.0f}s", flush=True)
    print('ALL CORES AGREE' if allok else 'DISAGREEMENT')

if __name__ == '__main__':
    main()
