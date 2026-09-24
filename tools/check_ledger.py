"""Ledger lint: every row has a known status; every PROVED/CERTIFIED/REFUTED row lists existing artifact files."""
import os, re, sys
ALLOWED = ('PROVED', 'CERTIFIED', 'EVIDENCE', 'CONJECTURE', 'REFUTED', 'OPEN'); NEEDS = ('PROVED', 'CERTIFIED', 'REFUTED')
root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
rows = [l for l in open(os.path.join(root, 'LEDGER.md'), encoding='utf-8') if l.startswith('|') and not set(l.strip()) <= set('|-: ')]
cols = [c.strip().lower() for c in rows[0].strip().strip('|').split('|')]; si, ai = cols.index('status'), cols.index('artifact')
errors = 0
for r in rows[1:]:
    cells = [c.strip() for c in r.strip().strip('|').split('|')]
    word = cells[si].split()[0].rstrip(',') if cells[si] else ''
    if word not in ALLOWED: print('unknown status:', r.strip()); errors += 1; continue
    paths = [p.split()[0] for p in re.findall(r'`([^`]+)`', cells[ai])]
    if word in NEEDS and not paths: print('missing artifact:', r.strip()); errors += 1
    for p in paths:
        if not os.path.exists(os.path.join(root, p)): print('artifact not found:', p); errors += 1
print(f"ledger: {len(rows) - 1} rows, {errors} problems"); sys.exit(1 if errors else 0)
