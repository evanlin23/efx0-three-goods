#!/usr/bin/env python3
"""Build the c4x binary used by `k4/hall_run.py --xcheck`: k4/c4x.c of branch proof/k4-c4x (PR #36) plus one line
that prints, per profile, the summary "X <types> valid V minfrozen F count C le0 Z least D" (valid pre-allocations,
fewest frozen agents, how many pre-allocations have that many, how many of those have deficit <= 0, least deficit),
computed by c4x's own enumeration and its own removal-only deficit (completable_ro). Nothing else is changed.

usage: python3 k4/hall_c4x_xcheck.py [OUT]   (reads k4/c4x.c from git at revision $C4X_REV, default efef349 of
       branch proof/k4-c4x, the one used for results/k4_hall_xcheck.log; or from the file $C4X_SRC)
prints the path of the binary."""
import os, subprocess, sys, tempfile

def main():
    out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(tempfile.gettempdir(), 'c4x_xcheck')
    src = os.environ.get('C4X_SRC')
    s = open(src).read() if src else subprocess.run(['git', 'show', os.environ.get('C4X_REV', 'efef349') + ':k4/c4x.c'], capture_output=True, text=True, check=True).stdout
    old = """    if (bestd > 0) {
      ronone++;"""
    new = """    { long long cnt = 0, le0 = 0; for (int k = 0; k < nv; k++) if (feat[(size_t)k * NFEAT + 6] == mf) { cnt++; if (-feat[(size_t)k * NFEAT + 17] <= 0) le0++; }
      printf("X"); for (int i = 0; i < n; i++) printf(" %d", cur[i]); printf(" valid %d minfrozen %lld count %lld le0 %lld least %lld\\n", nv, -mf, cnt, le0, bestd); }
    if (bestd > 0) {
      ronone++;"""
    assert s.count(old) == 1, 'k4/c4x.c changed: the patch point is gone'
    path = out + '.c'
    open(path, 'w').write(s.replace(old, new))
    subprocess.run(['gcc', '-O2', '-march=native', '-o', out, path], check=True)
    print(out)

if __name__ == '__main__':
    main()
