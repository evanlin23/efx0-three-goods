#!/usr/bin/env python3
"""Sensitivity of k4/dl134_ref.py's comparison (compute/k4-dl134): each mutation below is applied to a copy of
k4/dl134.c (in a temporary directory; k4/dl134.c is not touched), and the comparison is run on the 10 failing profiles
of results/k4_dl13/n4_failures_n4_1.tsv. Every mutation must give a mismatch (in the reference comparison, or in the
-DBIGPP=0 build for the hash-mode candidate generation).

  python3 results/k4_dl134/validate_mutations.py"""
import csv, json, os, sys, tempfile
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, 'k4'))
import dl134_ref as R

MUTS = {
    'T4 limited to 2-swaps': ('if (pc(ch) < 2 ||', 'if (pc(ch) != 2 ||'),
    'no T4': ('if (!k && t4test(p, q, &ty)) k = 4;', ''),
    'T4 without the NA / frozen-status conditions': ('if (pc(ch) < 2 || (ch & ~(Fa & Fb)) || Fa != Fb || PI[a].NA != PI[b].NA || ua != ub) return 0;',
                                                      'if (pc(ch) < 2 || ua != ub) return 0;'),
    'wrong cycle names (3 -> 4)': ('snprintf(w, sizeof w, x ? "+%d" : "%d", len[x]);',
                                   'snprintf(w, sizeof w, x ? "+%d" : "%d", len[x] + (len[x] == 3));'),
    'hash mode: no T4 candidates when f < 4': ('if (nf >= 2) perm_cand(ix, fl, nf, 0, G);', 'if (nf >= 4) perm_cand(ix, fl, nf, 0, G);'),
    'hash mode: first frozen agent takes only the least good': ('for (msk H = G & Rm[i]; H; H &= H - 1) {',
                                                                'for (msk H = G & Rm[i] & (t ? ~(msk)0 : (G & -G)); H; H &= H - 1) {'),
}


def main():
    print('# command: python3 results/k4_dl134/validate_mutations.py', flush=True)
    src = open(os.path.join(ROOT, 'k4', 'dl134.c')).read()
    insts, listed = [], {}
    for row in csv.DictReader(open(os.path.join(ROOT, 'results', 'k4_dl13', 'n4_failures_n4_1.tsv')), delimiter='\t'):
        listed[len(insts)] = json.loads(row['bases'])
        insts.append({'sets': json.loads(row['sets']), 'm': int(row['m']), 'vals': json.loads(row['vals']),
                      'id': f"{row['file']}#{row['pos']}:{row['profile']}"})
    orig = R.build
    ok = True
    with tempfile.TemporaryDirectory() as td:
        for name, (a, b) in MUTS.items():
            assert src.count(a) == 1, name
            mut = os.path.join(td, 'dl134.c')
            open(mut, 'w').write(src.replace(a, b))
            R.build = lambda s, extra=(): orig(mut, extra) if s.endswith('dl134.c') else orig(s, extra)
            st = R.compare(insts, 1, 'mutation: ' + name, listed)
            caught = st['mm_ref'] + st['mm_hash'] + st['mm_K'] + st['mm_L'] > 0
            ok &= caught
            print(f'=> mutation "{name}": {"CAUGHT" if caught else "NOT CAUGHT"}', flush=True)
    R.build = orig
    print('every mutation caught' if ok else 'SOME MUTATION NOT CAUGHT', flush=True)


if __name__ == '__main__':
    main()
