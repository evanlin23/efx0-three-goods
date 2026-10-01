#!/usr/bin/env python3
"""Tables of the DL_RT4 runs (compute/k4-rt4) for results/k4_rt4/SUMMARY.md. EVIDENCE tooling.

usage: python3 k4/dlrt4_summary.py "LABEL=TABLES.json=LOG" ...   ("@TEXT" starts a new group heading)
Reads the merged counters and tables that k4/dlrt4_run.py / k4/dlrt4_nbhd.py write (--tables) and the wall times of the
report lines of the log ("[N s]"; summed over the invocations of a resumed run), and prints Markdown:
  1. per run: profiles, f >= 1 states (def > 0), DL_RT4 failures (f >= 1; f = 0 apart), the states at which R_13, R_T,
     R_13 + T4 fail, the time;
  2. per run: the states with an improving move of each branch, with that branch as the only one, and the smallest RT4
     move size;
  3. per run: the T4 cycle types: states by the least T4 size and the cycle types of the T4 moves of that size (table
     "C" of dlrt4.c), and states by each cycle type available (table "Y", entries "T4:...");
  4. per run: the branch combinations (table "M": branch | smallest move size)."""
import collections, json, re, sys


def load(spec):
    label, tj, log = spec.split('=', 2)
    d = json.load(open(tj))
    secs = 0
    for l in open(log):
        m = re.search(r'\[(\d+) s\]$', l.strip())
        if m and l.startswith(('  DL_RT4:',)): secs += int(m.group(1))
    return label, d['counters'], d['tab'], secs


def fmt_t(s):
    return '%d s' % s if s < 120 else '%.1f min' % (s / 60)


def main(argv):
    runs = []
    for a in argv:
        if a.startswith('@'): runs.append(a[1:])
        else: runs.append(load(a))
    out = []
    P = out.append
    P('### 1. Counts\n')
    P('| run | profiles | f >= 1 states (def > 0) | **DL_RT4 fails** | f = 0 states (RT4 fails) | R_13 fails | R_T fails | R_13 + T4 fails | time |')
    P('|---|---:|---:|---:|---:|---:|---:|---:|---:|')
    for r in runs:
        if isinstance(r, str): P('| *%s* | | | | | | | | |' % r); continue
        lab, c, tab, secs = r
        P('| %s | %s | %s | **%d** | %s (%d) | %s | %s | %s | %s |' % (
            lab, f"{c['prof']:,}", f"{c['st1']:,}", c['fail1'], f"{c['st0']:,}", c['fail0'], f"{c['r13fail']:,}",
            f"{c['rtfail']:,}", f"{c['r134fail']:,}", fmt_t(secs)))
    P('\n### 2. Repair branches (f >= 1 states)\n')
    P('"with": an improving move of that branch exists; "only": it is the only branch with one (T3 = T3p or T3h). '
      'Smallest move size: the least number of agents changed by an improving RT4 move.\n')
    P('| run | T1 | T2 | T3p | T3h | T4 | only T1 | only T2 | only T3 | only T4 | smallest size 1 / 2 / 3 / >= 4 | anomalies |')
    P('|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---:|')
    for r in runs:
        if isinstance(r, str): continue
        lab, c, tab, secs = r
        P('| %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s / %s / %s / %s | %d |' % (
            lab, *(f"{c[k]:,}" for k in ('t1', 't2', 't3p', 't3h', 't4', 't1only', 't2only', 't3only', 't4only', 'rd1', 'rd2',
                                          'rd3', 'rd4')), c['anom'] + c['anom4']))
    P('\n### 3. T4 cycle types (f >= 1 states with an improving T4 move)\n')
    P('"least size: cycle types": the states by the least |ch| of an improving T4 move and the cycle types of the improving '
      'T4 moves of that size; "available": the states with an improving T4 move of each cycle type; "T4 needed": the '
      'states at which T4 is the only branch, by their least T4 size and cycle types.\n')
    P('| run | states with T4 | least size: cycle types | available | T4 needed |')
    P('|---|---:|---|---|---|')
    for r in runs:
        if isinstance(r, str): continue
        lab, c, tab, secs = r
        if not c['t4']: P('| %s | 0 | | | |' % lab); continue
        C = collections.Counter(); A = collections.Counter(); N = collections.Counter()
        for k, v in tab.items():
            w = k.split(' ', 1)
            if w[0] == 'C':
                f, s, cy = w[1].split('|'); C['%s: %s' % (s, cy)] += v
            elif w[0] == 'Y' and '|T4:' in k:
                f, br, ty = w[1].split('|'); A[ty[3:]] += v
                if br == 'T4': N[ty[3:]] += v
        Cs = ', '.join('%s (%s)' % (k, f"{v:,}") for k, v in sorted(C.items()))
        As = ', '.join('%s: %s' % (k, f"{v:,}") for k, v in sorted(A.items(), key=lambda x: (len(x[0]), x[0])))
        Ns = ', '.join('%s: %s' % (k, f"{v:,}") for k, v in sorted(N.items(), key=lambda x: (len(x[0]), x[0])))
        Mn = collections.Counter()
        for k, v in tab.items():
            if k.startswith('M ') and k.split('|')[1] == 'T4': Mn['size ' + k.split('|')[2]] += v
        Mn = {k: f"{v:,}" for k, v in Mn.items()}
        P('| %s | %s | %s | %s | %s |' % (lab, f"{c['t4']:,}", Cs, As,
                                          ('%s states; %s; cycle types available: %s' % (f"{c['t4only']:,}", ', '.join(
                                              '%s: %s' % kv for kv in sorted(Mn.items())), Ns)) if c['t4only'] else '-'))
    P('\n### 4. Branch combinations (f >= 1 states: f, branches with an improving move: smallest RT4 move size: states)\n')
    P('| run | f, branch combination: smallest size: states |')
    P('|---|---|')
    for r in runs:
        if isinstance(r, str): continue
        lab, c, tab, secs = r
        M = sorted(((k[2:].split('|')[0], k.split('|')[1], int(k.split('|')[2]), v) for k, v in tab.items()
                    if k.startswith('M ')), key=lambda x: -x[3])
        P('| %s | %s |' % (lab, '; '.join('f = %s, %s: %d: %s' % (f, b, s, f"{v:,}") for f, b, s, v in M) or '-'))
    print('\n'.join(out))


if __name__ == '__main__':
    main(sys.argv[1:])
