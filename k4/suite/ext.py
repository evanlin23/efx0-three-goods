"""Adapters to the other workstreams' independent implementations, used by k4/suite/run.py as second implementations.

Each module is imported from the working tree if it is there (after its PR merges), otherwise extracted read-only with
`git show <pinned commit>:<path>` into k4/suite/.cache/<name>/ (gitignored). Nothing here edits another workstream's
files. The pinned commits are the branch heads read for k4/strategy.md:
- gap:    compute/k4-gap (PR #53)        245040b4227c0afb532ca4feb611bf98a2f56d33  k4/gap_model.py (configurations, Phi',
          owners with unfreezing, deficit, moves of k4/c4min.md §4 and #52's downgrade swap)
- red:    proof/k4-c4min-reduce (PR #51)  827c76f2a2d0b06ff4b630bf2afc7b81be34cd18  k4/red_lib.py, k4/red_lil.py (keys and
          configurations at f = 1, the moves M1 M2 M4 M5 of the local improvement lemma)
- induct: proof/k4-induct (PR #43)        29e91b4a0744012ac813196ce2736f99e32fcf26  k4/induct_sat.py (an own SAT encoding
          of EFX0, D2 and "w unenvied"; every model re-checked by the raw definition)
- adaptive: proof/k4-adaptive (PR #44) 146d31be66f73b49ac2812aad45d9cb047034fd6  k4/adaptive.c, k4/adaptive_run.py (LB4r with
          rule F: first agent by lookahead, then index insertion; at most R nested rotations)
- hall:   main                            k4/hall_check.py (valid pre-allocations, Pareto-maximality, (removal-only)
          completability by enumerating completions, raw EFX0 re-check) and k4/c4x_check.py (#36: every valid
          pre-allocation with its completability as Lean's Completion and the potentials of k4/c4x.md §2)
"""
import importlib, os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
CACHE = os.path.join(HERE, '.cache')

PINS = {
    'gap': ('245040b4227c0afb532ca4feb611bf98a2f56d33', ['k4/gap_model.py']),
    'red': ('827c76f2a2d0b06ff4b630bf2afc7b81be34cd18', ['k4/red_lib.py', 'k4/red_lil.py', 'k4/check4.py']),
    'induct': ('29e91b4a0744012ac813196ce2736f99e32fcf26', ['k4/induct_sat.py']),
    'hall': (None, ['k4/hall_check.py']),
    'adaptive': ('146d31be66f73b49ac2812aad45d9cb047034fd6', ['k4/adaptive.c', 'k4/adaptive_run.py', 'k4/check4.py']),
}


def _dir(name):
    sha, files = PINS[name]
    if sha is None or all(os.path.exists(os.path.join(ROOT, f)) for f in files):
        return os.path.join(ROOT, 'k4')          # on main, or merged: the working tree
    d = os.path.join(CACHE, name)
    os.makedirs(d, exist_ok=True)
    for f in files:
        out = os.path.join(d, os.path.basename(f))
        if not os.path.exists(out):
            try:
                src = subprocess.run(['git', '-C', ROOT, 'show', f'{sha}:{f}'], check=True, capture_output=True).stdout
            except subprocess.CalledProcessError:
                src = subprocess.run(['git', '-C', ROOT, 'fetch', '-q', 'origin', sha], capture_output=True)
                src = subprocess.run(['git', '-C', ROOT, 'show', f'{sha}:{f}'], check=True, capture_output=True).stdout
            with open(out, 'wb') as fh: fh.write(src)
    return d


_MOD = {}


def load(name, module):
    key = (name, module)
    if key not in _MOD:
        d = _dir(name)
        sys.path.insert(0, d)
        try:
            if module in sys.modules and not getattr(sys.modules[module], '__file__', '').startswith(d):
                del sys.modules[module]
            _MOD[key] = importlib.import_module(module)
        finally:
            sys.path.remove(d)
    return _MOD[key]


def gap(): return load('gap', 'gap_model')
def red_lib(): return load('red', 'red_lib')
def red_lil(): return load('red', 'red_lil')
def induct_sat(): return load('induct', 'induct_sat')
def hall(): return load('hall', 'hall_check')
def c4x_check(): return load('hall', 'c4x_check')
def adaptive_dir(): return _dir('adaptive')
