"""Collects the counts of k4/p3/t1_p2.py and k4/p3/keep2.py logs into the Markdown table of k4/p3.md section 6.
    python3 k4/p3/p2_table.py LABEL:T1LOG:KEEP2LOG [...]      (T1LOG may be '-' for the 210 starts of proof/k4-oc1max-multi)
"""
import sys, re


def counts(path):
    c = {}
    if path == '-': return c
    for line in open(path):
        m = re.match(r'^(.*?): (\d+)$', line.rstrip('\n'))
        if m: c[m.group(1).strip()] = int(m.group(2))
    return c


rows = []
for arg in sys.argv[1:]:
    label, t1, k2 = arg.split(':')
    a, b = counts(t1), counts(k2)
    hard = a.get('hard perfect starts', b.get('starts', 0))
    dt1 = a.get('D_T = {k}: U2 applies', 0) + a.get('D_T = {k}: no H0 avoids crowding', 0)
    u2 = a.get('D_T = {k}: U2 applies', 0); nou2 = a.get('D_T = {k}: no H0 avoids crowding', 0)
    u2rep = a.get('... of which one move repairs', 0); u2c = a.get('U2 (chain, H0) cases', 0); u2v = a.get('U2 VIOLATION', 0)
    kc = b.get('starts with a KEEP2 chain', 0); k2c = b.get('KEEP2 (chain, H0) cases', 0); k2v = b.get('KEEP2 VIOLATION', 0)
    cdt = b.get('no KEEP2: some P(k), k in D_T, repairs', 0); cpd = b.get('no KEEP2: only P(k) with k pick-dangerous repairs', 0)
    cno = b.get('no KEEP2: no canonical chain repairs', 0)
    unf = b.get('UNF2 tests', 0); cr = b.get('CR2 crowded holder: OTHER: CR2 VIOLATION', 0)
    u2s = (f'{u2:,} of {dt1:,} ({nou2} not; one move repairs {u2rep}); {u2c:,} cases, {u2v} violations' if t1 != '-' else 'n/a')
    rows.append(f'| {label} | {hard:,} | {u2s} | {kc:,}; {k2c:,} cases, {k2v} violations | {cdt:,} | {cpd:,} | {cno} | {unf:,}, CR₂ exceptions {cr} |')
print('| hard perfect starts | number | U₂ at D_T = {k} | starts with a KEEP₂ chain | no KEEP₂ chain, but P(k) repairs for some k ∈ D_T | ... only for some pick-dangerous k | no canonical chain repairs | UNF₂ tests |')
print('|---|---|---|---|---|---|---|---|')
print('\n'.join(rows))
