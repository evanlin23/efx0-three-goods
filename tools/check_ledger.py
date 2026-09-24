"""Ledger lint: IDs are unique; every row has a known status; every PROVED/CERTIFIED/REFUTED row lists existing artifact files; every
name in the Lean column has a `#print axioms` certificate in lean/ (lean/check.sh checks the certificates themselves).
The v1 version is in archive/v1-ledger-lint/."""
import os, re, sys, glob
ALLOWED = ('PROVED', 'CERTIFIED', 'EVIDENCE', 'CONJECTURE', 'REFUTED', 'OPEN'); NEEDS = ('PROVED', 'CERTIFIED', 'REFUTED')
root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
rows = [l for l in open(os.path.join(root, 'LEDGER.md'), encoding='utf-8') if l.startswith('|') and not set(l.strip()) <= set('|-: ')]
cols = [c.strip().lower() for c in rows[0].strip().strip('|').split('|')]; si, ai = cols.index('status'), cols.index('artifact')
li = cols.index('lean') if 'lean' in cols else None
sources = [p for p in glob.glob(os.path.join(root, 'lean', '**', '*.lean'), recursive=True) if '.lake' not in p]
certified = set(re.findall(r'^#print axioms (\S+)', ''.join(open(p, encoding='utf-8').read() for p in sources), re.M))
errors = 0; seen = set()
for r in rows[1:]:
    cells = [c.strip() for c in r.strip().strip('|').split('|')]
    if cells[0] in seen: print('duplicate ID:', cells[0]); errors += 1
    seen.add(cells[0])
    word = cells[si].split()[0].rstrip(',') if cells[si] else ''
    if word not in ALLOWED: print('unknown status:', r.strip()); errors += 1; continue
    paths = [p.split()[0] for p in re.findall(r'`([^`]+)`', cells[ai])]
    if word in NEEDS and not paths: print('missing artifact:', r.strip()); errors += 1
    for p in paths:
        if not os.path.exists(os.path.join(root, p)): print('artifact not found:', p); errors += 1
    for name in (re.findall(r'`([^`]+)`', cells[li]) if li is not None else []):
        if name not in certified: print('Lean name without a #print axioms certificate in lean/:', name); errors += 1
print(f"ledger: {len(rows) - 1} rows, {errors} problems"); sys.exit(1 if errors else 0)
