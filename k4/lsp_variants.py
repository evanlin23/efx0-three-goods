"""Run the LS4+ variants and the GM potentials on the 19 logged LS4 failure profiles (results/k4_ls4_failures_4_pure.tsv).

Variants (k4/ls4alg.c): LS4 (default), -DEARLY, -DCMOVE=2, -DCMOVE=3, -DCMOVE=8; potentials (k4/ls4_gm.c): -DPOT=0 (level
sum), 1 (leximin), 2 (fixed priority).  For each, the number of the 19 profiles that fail (LS4 variants: no placement
reached; GM: some maximal state without placement).  Usage: python3 k4/lsp_variants.py
"""
import os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from ls4alg_run import build
from ls4_attempts import parse

def one(s):
    vals = parse(s); n = len(vals); m = 1 + max(g for v in vals for g in v)
    out = [f"{n} {m}"] + [" ".join(map(str, [len(v)] + list(v))) for v in vals]
    for v in vals: out += ["1", " ".join(map(str, [0] + [v[g] for g in v]))]
    return "\n".join(out + ["0 0 1"]) + "\n"

def main():
    rows = [l.rstrip('\n').split('\t') for l in open(os.path.join(HERE, '..', 'results', 'k4_ls4_failures_4_pure.tsv'))
            if l.strip() and not l.startswith('#') and not l.startswith('m\t')]
    tests = [('LS4 (default rule)', '', 'ls4alg'), ('-DEARLY', '-DEARLY', 'ls4alg'), ('-DCMOVE=2', '-DCMOVE=2', 'ls4alg'),
             ('-DCMOVE=3', '-DCMOVE=3', 'ls4alg'), ('-DCMOVE=8 (LS4+_n)', '-DCMOVE=8', 'ls4alg'),
             ('GM, level sum (-DPOT=0)', '-DPOT=0', 'ls4_gm'), ('GM, leximin (-DPOT=1)', '-DPOT=1', 'ls4_gm'),
             ('GM, fixed priority (-DPOT=2)', '-DPOT=2', 'ls4_gm')]
    for name, defs, prog in tests:
        exe = build(defs, prog); failed = []
        for r, row in enumerate(rows, 1):
            out = subprocess.run([exe], input=one(row[1]), capture_output=True, text=True).stdout
            res = dict(x.split('=') for x in next(l for l in out.splitlines() if l.startswith('RESULT')).split()[1:])
            if int(res['fail']): failed.append(r)
        print(f"{name}: {len(failed)} of {len(rows)} profiles fail; rows {failed}", flush=True)

if __name__ == '__main__':
    main()
