#!/usr/bin/env python3
"""The tables of results/k4_dl134/SUMMARY.md, from the runs' tables JSON, logs and checkpoints (compute/k4-dl134).

  python3 results/k4_dl134/summary_table.py

Per run: profiles, f >= 1 states with def > 0, DL134 failures, DL13 failures (repaired by T4 only when DL134 holds),
the states with an improving T1 / T3 / T4 move, the R_134 branches as exclusive classes (T3 = T3p or T3h), the T4 cycle
types available (states with an improving T4 move of that type) and the time (wall time of the last invocation as
the log reports it, and the CPU time of the units summed over the checkpoint)."""
import collections, json, os, re
HERE = os.path.dirname(os.path.abspath(__file__))

RUNS = [('(a) the DL13 failures of results/k4_dl13 (1,131 profiles)', 'dl13fail', None),
        ('(b) `k4_certs_4_n4_1`, exhaustive', 'n4_1', 'ckpt_n4_1.jsonl'),
        ('(c) `k4_certs_4_n4_2`, exhaustive', 'n4_2', 'ckpt_n4_2.jsonl')]
for f in ('n4_3', 'pure'):
    for s in (1, 2, 3):
        RUNS.append((f'(d) `k4_certs_4_{f}`, 500 per core, seed {s}', f'{f}_s500_seed{s}', f'ckpt_{f}_s500_seed{s}.jsonl'))


def cls(br):
    if br == 'none': return 'none'
    has = [k for k, t in (('T1', ('T1',)), ('T3', ('T3p', 'T3h')), ('T4', ('T4',))) if any(x in br.split('+') for x in t)]
    return '+'.join(has)


def main():
    rows, brows, trows = [], [], []
    order = ['T1', 'T3', 'T4', 'T1+T3', 'T1+T4', 'T3+T4', 'T1+T3+T4', 'none']
    cyc_all = []
    for title, name, ck in RUNS:
        tj = os.path.join(HERE, f'tables_{name}.json')
        if not os.path.exists(tj): continue
        T = json.load(open(tj)); c = T['counters']; tab = T['tab']
        log = open(os.path.join(HERE, f'{name}.log')).read()
        wall = re.findall(r'\[(\d+) s\]\n', log)
        cpu = None
        if ck and os.path.exists(os.path.join(HERE, ck)):
            cpu = sum(json.loads(l)['secs'] for l in open(os.path.join(HERE, ck)) if l.strip())
        br = collections.Counter()
        for k, v in tab.items():
            if k.startswith('G '): br[cls(k.split('|')[2])] += v
        cyc = collections.Counter()
        for k, v in tab.items():
            if k.startswith('Y ') and '|T4:' in k: cyc[k.split('|T4:')[1]] += v
        for x in cyc:
            if x not in cyc_all: cyc_all.append(x)
        rows.append(f"| {title} | {c['prof']:,} | {c['st1']:,} | **{c['fail1']:,}** | {c['fail13_1']:,} | {c['t4only']:,} "
                    f"({c['t4only2']:,} / {c['t4onlyL']:,}) | {c['t1']:,} / {c['t3']:,} / {c['t4']:,} | "
                    f"{wall[-1] if wall else '?'} s" + (f" ({cpu:,.0f} s)" if cpu is not None else '') + ' |')
        brows.append((title, br))
        trows.append((title, cyc))
    print('| run | profiles | f >= 1 states, def > 0 | DL134 fails at | DL13 fails at | repaired by T4 only (a 2-swap / '
          'longer cycles only) | with an improving T1 / T3 / T4 move | wall time (CPU time of the units) |')
    print('|---|---:|---:|---:|---:|---:|---:|---|')
    for r in rows: print(r)
    print()
    print('| run | ' + ' | '.join(order) + ' |')
    print('|---|' + '---:|' * len(order))
    for title, br in brows: print(f'| {title} | ' + ' | '.join(f'{br.get(o, 0):,}' for o in order) + ' |')
    print()
    cyc_all.sort(key=lambda x: (sum(map(int, x.split('+'))) if x != 'other' else 99, x))
    print('| run | ' + ' | '.join(f'T4 "{x}"' for x in cyc_all) + ' |')
    print('|---|' + '---:|' * len(cyc_all))
    for title, cyc in trows: print(f'| {title} | ' + ' | '.join(f'{cyc.get(x, 0):,}' for x in cyc_all) + ' |')


if __name__ == '__main__':
    main()
