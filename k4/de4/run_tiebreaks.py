"""Exhaustive check of DE4 with tie-breaks after the level sum (k4/de4/de4m.c), all criteria at once
(attempts/k4-de4.md). Usage: python3 k4/de4/run_tiebreaks.py FILE [CHUNKS [TAKE]] > log
Each core is split into CHUNKS jobs; with TAKE, only the first TAKE chunks run (a deterministic sample)."""
import os, subprocess, sys, multiprocessing as mp, re
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from de4lib import load_cores
from check import write_input, ROOT
EXE = os.path.join(HERE, 'de4m')
def job(args):
    ci, sets, ch, nch = args
    out = subprocess.run([EXE, str(ch), str(nch)], input=write_input(sets), capture_output=True, text=True).stdout
    return ci, out
if __name__ == '__main__':
    path = sys.argv[1]; nch = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    take = int(sys.argv[3]) if len(sys.argv) > 3 else nch   # run only chunks 0..take-1 (a deterministic sample)
    subprocess.run(['gcc', '-O2', '-w', '-o', EXE, os.path.join(HERE, 'de4m.c')], check=True)
    cores = load_cores(path if os.path.exists(path) else os.path.join(ROOT, 'results', path))
    jobs = [(ci, s, ch, nch) for ci, s in enumerate(cores) for ch in range(take)]
    tot, per, fails = {}, {}, []
    with mp.Pool(os.cpu_count()) as p:
        for ci, out in p.imap_unordered(job, jobs):
            for line in out.splitlines():
                if line.startswith('FAIL'): fails.append((ci, line))
                w = line.split()
                if line.startswith('crit0_maxima'):
                    d = dict(zip(w[0::2], map(int, w[1::2])))
                    for k, x in d.items():
                        tot[k] = tot.get(k, 0) + x
                        if 'fail' in k and x: per.setdefault(ci, {}).__setitem__(k, per.get(ci, {}).get(k, 0) + x)
                if line.startswith('profiles'):
                    tot['profiles'] = tot.get('profiles', 0) + int(w[1])
    for ci in sorted(per): print('core', ci, cores[ci], per[ci])
    for f in fails[:40]: print('core', f[0], f[1])
    print('TOTAL', path, len(cores), 'cores;', ' '.join(f'{k} {v}' for k, v in tot.items()))
    print('criteria: 0 none (DE4), 1 fewest lower pairs, 2 most leftover goods (fewest goods held), 3 fewest holdings of two or more goods, 4 fewest frozen agents, 5 fewest lower pairs then most leftover goods')
