"""Provenance of results/k4_adaptive_gm4_profiles.jsonl (k4/adaptive.md §2: #30's GM4 profiles, one JSON object
{"sets": [...], "vals": [...]} per line): rebuilds the file from PR #30's result files and named instances and checks it
is identical to the committed one.
  1. the profiles listed in PR #30's results/k4_gm4_gmall_seeds_4.txt (148, the GMALL lines: pure n = 4 profiles whose
     level-sum maxima are all dead ends), results/k4_gm4_seeds_4.txt (7 GM4 seeds), results/k4_gm4_4_n4_2.log (274
     tagged lines of the n = 4 run with two 4-good agents, 271 of them new), results/k4_gm4_5_pure_sample.log (4) and
     results/k4_gm4_5_n4_4_sample.log (1), read with k4/adaptive_run.py's load_profiles, in this order, without
     repeats: 431 lines;
  2. the 11 named instances of k4/gm4_counterexample.py (A-H, P, Q, S), appended as they are: 8 of them already occur
     in part 1, so the file has 442 lines and 434 distinct profiles.
Usage: python3 k4/adaptive_gm4_profiles.py [--write]"""
import json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import adaptive_run as A, gm4_counterexample as G

SOURCES = ['results/k4_gm4_gmall_seeds_4.txt', 'results/k4_gm4_seeds_4.txt', 'results/k4_gm4_4_n4_2.log',
           'results/k4_gm4_5_pure_sample.log', 'results/k4_gm4_5_n4_4_sample.log']
OUT = os.path.join(ROOT, 'results', 'k4_adaptive_gm4_profiles.jsonl')

def build():
    P = []
    for f in SOURCES:
        L = A.load_profiles(os.path.join(ROOT, f))
        new = 0
        for s, v in L:
            if (s, v) not in P: P.append((s, v)); new += 1
        print(f"{f}: {len(L)} profiles, {new} new")
    for label, vals, Y, kind in G.INSTANCES:
        s = [sorted(d) for d in vals]; v = [[d[g] for g in sorted(d)] for d in vals]
        print(f"k4/gm4_counterexample.py instance {label.split(':')[0]}: {'already listed' if (s, v) in P else 'new'}")
        P.append((s, v))
    return ''.join(json.dumps({'sets': s, 'vals': v}) + '\n' for s, v in P)

def main():
    text = build()
    lines = text.splitlines()
    print(f"{len(lines)} lines, {len(set(lines))} distinct profiles")
    if '--write' in sys.argv[1:]:
        open(OUT, 'w').write(text); print('written', OUT)
    else:
        print('identical to the committed file' if open(OUT).read() == text else 'DIFFERS from the committed file')

if __name__ == '__main__':
    main()
