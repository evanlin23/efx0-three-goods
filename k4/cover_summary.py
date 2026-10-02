#!/usr/bin/env python3
"""Summaries of k4/cover_check.py outputs (workstream compute/k4-cover). EVIDENCE tooling.

Per group of output files: profiles, keys with def* > 0 per f and n, coverage per lemma (keys with the lemma at some
maximum; maxima with it), keys covered by exactly one lemma (per lemma, with the smallest such key by (n, m, sum of
values)), the uncovered keys with their DLKey verdicts, library assertion failures, and at f = 1 the first lemma per
maximum in PR #80's order (A, B1, C, C′, B1′ with the structural hypotheses, then the exact-only forms), at f >= 2 the
A⁺/B⁺ versus C⁺/C′⁺ split of k4/f2.md §5 and the rare forms (B⁺ with k = 1 only, C′⁺ with q = φ(w) only).

usage: python3 k4/cover_summary.py NAME=GLOB [NAME=GLOB ...] [--nodedup]"""
import collections, glob, gzip, json, sys

COVER = ('A', 'B1', "B1'", 'C', "C'")
COVER_PLUS = ('A+', 'B+1', 'C+', "C'+")
PHIW = 'phi(w) of a frozen w off the move'


def size(r): return (len(r['sets']), r['m'], sum(map(sum, r['vals'])))


def first_f1(mr):
    lem = mr['lemmas']
    for name, need in (('A', 1), ('B1', 1), ('C', 1), ("C'", 1), ("B1'", 1), ('C', 0), ("C'", 0), ("B1'", 0)):
        if name in lem and lem[name] >= need: return name + ('' if need else ' (exact only)')
    return 'none'


def summarize(name, files):
    cnt = collections.Counter(); small = {}; unc = []; asserts = []; seen = set()
    def keep(tag, r, kr):
        s = size(r)
        if tag not in small or s < small[tag][0]: small[tag] = (s, r, kr)
    for fn in files:
        lines = []
        try:
            for line in gzip.open(fn, 'rt'): lines.append(line)
        except (EOFError, OSError): pass                      # a file still being written: its readable part
        for line in lines:
            try: r = json.loads(line)
            except ValueError: continue
            pk = json.dumps([r['sets'], r['vals'], r['m']])
            if pk in seen and not NODEDUP: cnt['duplicate profiles skipped'] += 1; continue
            seen.add(pk)
            cnt['profiles read'] += 1
            if 'skip' in r: cnt['profiles skipped: %s' % r['skip']] += 1; continue
            f = r['f']; n = r['n']
            cnt[('profiles', 'f=%d' % f, 'n=%d' % n)] += 1
            if r.get('indep'): cnt['profiles checked against k4/rt4_n5_indep.py: ' + r['indep'].split(' (')[0]] += 1
            for kr in r['keys']:
                cnt[('keys def*>0', 'f=%d' % f, 'n=%d' % n)] += 1
                cnt[('keys def*>0', 'f=%d' % f)] += 1
                if 'assert' in kr: asserts.append((r, kr)); cnt['LEMMA-ASSERT'] += 1
                target = COVER if f == 1 else COVER_PLUS
                mx = kr['maxima']
                cnt[('maxima', 'f=%d' % f)] += len(mx)
                per = collections.Counter()
                for mr in mx:
                    for l in mr['lemmas']:
                        cnt[('maxima with lemma', 'f=%d' % f, l)] += 1; per[l] += 1
                    if f == 1:
                        cnt[('f=1 maxima, first lemma (PR #80 order)', first_f1(mr))] += 1
                    else:
                        ab = bool({'A+', 'B+1'} & set(mr['lemmas']))
                        cc = bool({'C+', "C'+"} & set(mr['lemmas']))
                        cnt[('f>=2 maxima', 'A+/B+1' if ab else ('C+/C\'+ only' if cc else
                                                                ('full only' if 'full' in mr['lemmas'] else 'none')))] += 1
                        for j in mr['detail'].get('A+ j', []): cnt[('f>=2 maxima', 'A+ chain j=%d' % j)] += 1
                        for jk in mr['detail'].get('B+ (j,k)', []): cnt[('f>=2 maxima', 'B+ (j,k)=%s' % (tuple(jk),))] += 1
                        for k in mr['detail'].get('C+ k', []): cnt[('f>=2 maxima', 'C+ k=%d' % k)] += 1
                        for k in mr['detail'].get("C'+ k", []): cnt[('f>=2 maxima', "C'+ k=%d" % k)] += 1
                        for q in mr['detail'].get("C'+ q", []): cnt[('f>=2 maxima', "C'+ q=%s" % q)] += 1
                for l in per: cnt[('keys with lemma at some maximum', 'f=%d' % f, l)] += 1
                cov = [l for l in target if l in per]
                if f >= 2:
                    ab = bool({'A+', 'B+1'} & set(cov))
                    cnt[('f>=2 keys', 'A+ or B+1 at some maximum' if ab else
                         ('only C+/C\'+' if cov else 'UNCOVERED'))] += 1
                    if not ab and cov:
                        cnt[('f>=2 keys without A+/B+1', 'C+ at some max' if 'C+' in cov else "C'+ only")] += 1
                    qk = set(q for mr in mx if "C'+" in mr['lemmas'] for q in mr['detail'].get("C'+ q", []))
                    if cov == ["C'+"] and qk == {PHIW}:
                        cnt[('f>=2 keys', "only C'+ with q = phi(w)")] += 1; keep("only C'+ with q = phi(w)", r, kr)
                    if 'B+1' in cov and not {'A+', 'C+', "C'+"} & set(cov):
                        cnt[('f>=2 keys', 'only B+1')] += 1
                else:
                    struct = any(any(l in mr['lemmas'] and mr['lemmas'][l] == 1 for l in COVER) for mr in mx)
                    cnt[('f=1 keys', 'covered with the structural hypotheses' if struct else
                         ('covered with the exact hypotheses only' if cov else 'UNCOVERED'))] += 1
                    every = all(set(mr['lemmas']) & set(COVER) for mr in mx)
                    cnt[('f=1 keys', 'every maximum covered=%s' % every)] += 1
                if len(cov) == 1:
                    cnt[('keys covered by exactly one lemma', 'f=%d' % f, cov[0])] += 1
                    keep('only %s (f=%d)' % (cov[0], f), r, kr)
                for l in cov: keep('some %s (f=%d)' % (l, f), r, kr)
                if not cov:
                    unc.append((r, kr)); cnt[('UNCOVERED keys', 'f=%d' % f)] += 1
                    dk = kr.get('dlkey', {})
                    cnt[('UNCOVERED keys', 'DLKey holds=%s' % dk.get('holds'))] += 1
                    if f == 1: cnt[('UNCOVERED f=1 keys', 'C+/C\'+ fallback', ','.join(kr.get('f1_fallback_Cplus', [])) or 'none')] += 1
                if 'dlkey' in kr and kr['dlkey']['holds']:
                    cnt[('keys with DLKey computed', 'best move', kr['dlkey']['example'][0])] += 1
                elif 'dlkey' in kr:
                    cnt[('keys with DLKey computed', 'DLKey FAILS')] += 1
    return cnt, small, unc, asserts


def fmt(k): return ' | '.join(map(str, k)) if isinstance(k, tuple) else k


NODEDUP = False


def main(argv):
    global NODEDUP
    md = '--md' in argv; NODEDUP = '--nodedup' in argv
    for a in argv:
        if a.startswith('--'): continue
        name, g = a.split('=', 1)
        files = sorted(set(sum((glob.glob(x) for x in g.split(',')), [])))
        cnt, small, unc, asserts = summarize(name, files)
        print('### %s (%d files)' % (name, len(files)))
        for k in sorted(cnt, key=lambda k: fmt(k)): print('  %-110s %d' % (fmt(k), cnt[k]))
        for tag in sorted(small):
            s, r, kr = small[tag]
            mx = [(mr['Q'], sorted(mr['lemmas'])) for mr in kr['maxima']]
            print('  smallest [%s]: n=%d m=%d sum=%d f=%d sets=%s vals=%s key=%s def*=%d maxima=%s' % (
                tag, s[0], s[1], s[2], r['f'], r['sets'], r['vals'], kr['key'], kr['dstar'], mx))
        for r, kr in unc:
            print('  UNCOVERED f=%d sets=%s vals=%s m=%d key=%s def*=%d dlkey=%s maxima=%s' % (
                r['f'], r['sets'], r['vals'], r['m'], kr['key'], kr['dstar'], kr.get('dlkey'),
                [(mr['Q'], mr['lemmas']) for mr in kr['maxima']]))
        for r, kr in asserts:
            print('  LEMMA-ASSERT f=%d sets=%s vals=%s m=%d key=%s: %s' % (r['f'], r['sets'], r['vals'], r['m'],
                                                                         kr['key'], kr['assert']))


if __name__ == '__main__':
    main(sys.argv[1:])
