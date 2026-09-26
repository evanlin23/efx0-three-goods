#!/usr/bin/env python3
"""Print the provenance table of the suite (k4/suite/README.md, section "Instances") from the instance records."""
import glob, json, os
HERE = os.path.dirname(os.path.abspath(__file__))


def short(s, k=150):
    s = ' '.join(str(s).split())
    return s if len(s) <= k else s[:k - 1] + '…'


def main():
    rows = []
    for f in sorted(glob.glob(os.path.join(HERE, 'instances', '*.json'))):
        d = json.load(open(f))
        src = d.get('source', {})
        pr = src.get('pr'); br = src.get('branch', '')
        files = ', '.join('`%s`' % x for x in (src.get('files') or [])[:2])
        core = 'local' if 'kind' in d else ('yes' if d.get('is_core') else 'NO')
        ref = '; '.join(short(r.get('statement', ''), 110) for r in d.get('refutes', [])[:2])
        if len(d.get('refutes', [])) > 2: ref += ' (+%d more)' % (len(d['refutes']) - 2)
        chk = ', '.join('`%s`' % p for p in d.get('expect_fail', []))
        rows.append((pr or 0, d['id'], '| `%s` | %d | %d | %s | %s | %s | %s | %s |' % (
            d['id'], d['n'], d['m'], core, ('#%s' % pr) if pr else br, files, ref, chk)))
    print('| id | n | m | core | PR | source files | refutes (as the source states it; full text in the record) | re-checked by `run.py --expected` |')
    print('|---|---|---|---|---|---|---|---|')
    for _, _, r in sorted(rows): print(r)


if __name__ == '__main__':
    main()
