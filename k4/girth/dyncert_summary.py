"""Summary table of the dyncert / dyncert_sym logs (k4/girth.md section 6).

    python3 k4/girth/dyncert_summary.py results/k4_girth_dyncert_*.log
Per log: cores, how many CERTIFIED / NOT CERTIFIED / TIMEOUT, profiles, profiles covered, runs, and (dyncert logs with
labeling statistics) the cores on which the default labelings suffice and those on which labeling #0 alone (vertex 0
= agent 0, default order) does.
"""
import re
import sys


def main():
    pat = re.compile(r'^(\S+)\s+profiles\s+(\d+) covered\s+(\d+) runs\s+(\d+) boxes-without-labeling (\d+) ([\d.]+)s (.*)$')
    print('%-44s %6s %6s %5s %5s %16s %16s %10s %9s %8s' % ('log', 'cores', 'cert', 'not', 'tmout', 'profiles',
                                                              'covered', 'runs', 'default', 'lab #0'))
    for f in sys.argv[1:]:
        c = dict(cores=0, cert=0, notc=0, tmo=0, prof=0, cov=0, runs=0, dflt=0, zero=0, stats=0)
        for line in open(f):
            mt = pat.match(line.rstrip())
            if not mt:
                continue
            name, prof, cov, runs, ncx, secs, rest = mt.groups()
            c['cores'] += 1
            c['prof'] += int(prof)
            c['cov'] += int(cov)
            c['runs'] += int(runs)
            if rest.startswith('CERTIFIED'):
                c['cert'] += 1
            elif rest.startswith('TIMEOUT'):
                c['tmo'] += 1
            else:
                c['notc'] += 1
            ml = re.search(r'last used #(-?\d+), by default orders', rest)
            if ml:
                c['stats'] += 1
                mn = re.match(r'k4_certs_(\d+)', name)
                n = int(mn.group(1)) if mn else None
                last = int(ml.group(1))
                if rest.startswith('CERTIFIED'):
                    c['zero'] += last == 0
                    c['dflt'] += n is not None and last < n
        d = ('%d' % c['dflt']) if c['stats'] else '-'
        z = ('%d' % c['zero']) if c['stats'] else '-'
        print('%-44s %6d %6d %5d %5d %16d %16d %10d %9s %8s' % (f.split('/')[-1], c['cores'], c['cert'], c['notc'],
                                                                c['tmo'], c['prof'], c['cov'], c['runs'], d, z))


if __name__ == '__main__':
    main()
