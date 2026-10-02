"""The profiles where "a big-top agent first, else index order" fails (k4/rulef.md §5.2, attempts/k4-rulef-bigtop-first.md).

Runs k4/rulef.c -A42 -Q0 -r1 -D1 on the given core file (OPEN lines: the rule's agent is in no class), then, for each
such leaf representative, k4/rulef.c -A41 -E1 -D5 (single profile) for the classes of every first agent, and tabulates
the agents by (in class K0 or K1, type, number of private goods, number of other agents with the same top, number of
other agents valuing its top), weighted by the leaf weights.
Usage: rulef_bigtop.py CORES.json.gz"""
import collections, json, os, re, subprocess, sys, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rulef_run as RR
import adaptive_run as AR
import gzip


def main():
    f = sys.argv[1]
    RR.build()
    print('# rulef_bigtop.py', f, '# rulef.c sha256', RR.SHA, flush=True)
    rows = []
    for c in json.load(gzip.open(f, 'rt'))['cores']:
        p = subprocess.run([RR.BIN, '-A42', '-Q0', '-r1', '-D1'], input=AR.encode_core(c['sets'], c['m']), capture_output=True, text=True)
        for l in p.stdout.split('\n'):
            if l.startswith('OPEN'):
                rows.append((int(re.search(r'w=(\d+)', l).group(1)), json.loads(re.search(r'sets=(\[\[.*?\]\])', l).group(1)),
                             json.loads(re.search(r'vals=(\[\[.*?\]\])', l).group(1))))
    tab = collections.Counter(); nbig = collections.Counter(); tot = 0
    for w, sets, vals in rows:
        tot += w
        p = subprocess.run([RR.BIN, '-A41', '-E1', '-D5', '-r1', '-T1'], input=AR.encode_profile(sets, vals), capture_output=True, text=True)
        idx = next(l for l in p.stdout.split('\n') if l.startswith('IDX'))
        fa = [list(map(int, x.split(':')[1].split(','))) for x in idx.split('fa=')[1].strip().split(';')]
        n = len(sets)
        rk = [[g for v, g in sorted(zip(vals[i], sets[i]), reverse=True)] for i in range(n)]
        tops = [r[0] for r in rk]
        nb = 0
        for i in range(n):
            v = sorted(vals[i], reverse=True)
            if len(v) == 4 and v[0] > v[1] + v[2]: nb += 1
            if len(v) == 3: typ = '3 goods'
            else: typ = 'flat (a < c+d)' if v[0] < v[2] + v[3] else ('c+d < a < b+d' if v[0] < v[1] + v[3] else 'b+d < a < b+c' if v[0] < v[1] + v[2] else 'big-top')
            priv = sum(1 for g in sets[i] if all(g not in sets[j] for j in range(n) if j != i))
            ok = fa[i][0] <= 0 or fa[i][1] <= 0 or fa[i][4] == 1
            tab[('in K0 or K1' if ok else 'in neither', typ, 'private %d' % priv,
                 'same top as %d other' % sum(1 for j in range(n) if j != i and tops[j] == tops[i]),
                 'top valued by %d other' % sum(1 for j in range(n) if j != i and tops[i] in sets[j]))] += w
        nbig[nb] += w
    print(f'{f}: {len(rows)} leaves, {tot} profiles; by number of big-top agents: {dict(nbig)}')
    for k in sorted(tab, key=lambda k: (k[1], k[2], k[3], k[4], k[0])):
        print('  ', ', '.join(k), tab[k])


if __name__ == '__main__':
    main()
