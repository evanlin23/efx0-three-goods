"""Differential test of k4/check4.py's coverage check (minimal-type reduction, memo of covered prefix sets, smallest
sets first, last two agents by columns) against the version on main before these changes (git show 2039ab7:k4/check4.py,
a plain depth-first walk over every type). Random cores from the committed certificates, each with a random subset
of its allocations deleted (so many are no longer covered): both versions must give the same answer on every one.
Usage: test_check4_fast.py [trials_per_file] (writes a summary; exit status 1 on any disagreement)"""
import gzip, importlib.util, json, os, random, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.dirname(HERE))
import check4 as NEW

def load_old():
    src = subprocess.run(['git', '-C', ROOT, 'show', '2039ab7:k4/check4.py'], capture_output=True, text=True, check=True).stdout
    p = os.path.join(tempfile.mkdtemp(), 'check4_old.py')
    open(p, 'w').write(src)
    spec = importlib.util.spec_from_file_location('check4_old', p)
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
    return mod

if __name__ == '__main__':
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    OLD = load_old()
    rng = random.Random(2026)
    files = ['k4_certs_2.json.gz', 'k4_certs_3.json.gz', 'k4_certs_4_n4_1.json.gz', 'k4_certs_4_n4_2.json.gz',
             'k4_certs_4_n4_3.json.gz', 'k4_certs_5_n4_1.json.gz']
    tot, agree, cov = 0, 0, 0
    for fn in files:
        data = json.load(gzip.open(os.path.join(ROOT, 'results', fn), 'rt'))
        for _ in range(trials):
            r = rng.choice(data['cores'])
            A = [a for a in r['allocs'] if rng.random() < rng.choice([0.6, 0.9, 0.97, 1.0])] or r['allocs'][:1]
            task = (data['n'], r['m'], r['sets'], A, data.get('ties', False))
            a, b = OLD.covered(task), NEW.covered(task)
            tot += 1; agree += a == b; cov += b
            if a != b: print(f"DISAGREE {fn} m={r['m']} sets={r['sets']} kept {len(A)}/{len(r['allocs'])}: old {a}, new {b}")
        print(f"{fn}: {trials} trials done", flush=True)
    print(f"{tot} cores with random allocation subsets: old and new agree on {agree} ({cov} covered, {tot - cov} not covered)")
    sys.exit(0 if agree == tot else 1)
