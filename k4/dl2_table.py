#!/usr/bin/env python3
"""Tables of the DL2 classification (k4/dl2.md §2) from the per-state records of k4/dl2_classify.py.
usage: python3 k4/dl2_table.py FILE.jsonl.gz [...] > results/k4_dl2_classify/table.md
Suite instances that are not k = 4 cores (k4/suite/instances/*.json, "is_core": false) are counted apart."""
import collections, glob, gzip, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))


def load(fn):
    op = gzip.open if fn.endswith('.gz') else open
    with op(fn, 'rt') as f:
        for l in f:
            yield json.loads(l)


def suite_cores():
    out = {}
    for f in glob.glob(os.path.join(HERE, 'suite', 'instances', '*.json')):
        d = json.load(open(f))
        out[d['id']] = d.get('is_core', True)
    return out


def lemma_class(r):
    """the strongest lemma family of k4/dl2.md that applies (None if none)"""
    L = r.get('lemmas') or {}
    if 'C4s' in L: return 'Cor 4 structural (private-to-{o,y} release)'
    if 'C4' in L: return 'Cor 4 (release)'
    if 'C5' in L: return 'Cor 5 (unblocking)'
    if 'L2' in L: return 'Lemma 2 (extension)'
    if 'L2o' in L: return 'Lemma 2 (extension, another owner)'
    if 'L3' in L: return 'Lemma 3 (owner re-base)'
    return None


def ex(r):
    return '%s P=%s' % (r['src'], r['Bs'])


def main(files):
    cores = suite_cores()
    print('# DL2 classification tables (generated)\n')
    print('command: `python3 k4/dl2_table.py %s`\n' % ' '.join(files))
    print('Every min-frozen P with def(P) > 0 of every profile in the inputs is one *state*. k = the least number of agents')
    print('whose bases change to reach a min-frozen P\' with a smaller deficit. Obstruction signature: the H3/H7 classes')
    print('(e1, e2, e3, G, G1, L; fU/fU2: a free exposed agent violating (U)/(U2); fO, O: other) of the agents exposed')
    print('w.r.t. the best owner with the fewest exposures; suffix 2: a frozen agent exposed w.r.t. two or more free')
    print('agents (the double threat of Lemma D). Repair kind: `k4/dl2_classify.py` `repair_kind` (primary kind of the')
    print('minimal repairs: release > unblock > owner > need-transfer for k = 1).\n')
    states = []; noncore = []
    per_src = collections.OrderedDict()
    for fn in files:
        name = os.path.basename(fn).replace('.jsonl.gz', '')
        c = collections.Counter(); profs = set(); profs_k = collections.defaultdict(set)
        for r in load(fn):
            r['_file'] = name
            if name == 'suite' and not cores.get(r['src'], True):
                noncore.append(r); continue
            states.append(r)
            c[r['k']] += 1; profs.add(r['src']); profs_k[r['k']].add(r['src'])
        per_src[name] = (c, len(profs), {k: len(v) for k, v in profs_k.items()})
    print('## Inputs\n')
    print('| input | profiles with a def > 0 state | states | k = 1 | k = 2 | k = 3 | profiles with k* = 3 |')
    print('|---|---|---|---|---|---|---|')
    tot = collections.Counter()
    for name, (c, np_, pk) in per_src.items():
        print('| %s | %d | %d | %d | %d | %d | %d |' % (name, np_, sum(c.values()), c[1], c[2], c[3], pk.get(3, 0)))
        tot.update(c)
    print('| **total (cores)** | | %d | %d | %d | %d | |' % (sum(tot.values()), tot[1], tot[2], tot[3]))
    if noncore:
        nc = collections.Counter(r['k'] for r in noncore)
        print('\nNot cores (suite, counted apart): %d states, k histogram %s, instances %s.' % (
            len(noncore), dict(sorted(nc.items())), sorted(set(r['src'] for r in noncore))))
    # A: group x k
    print('\n## A. Obstruction group × k\n')
    G = collections.defaultdict(collections.Counter); Gex = {}
    for r in states:
        G[r['group']][r['k']] += 1
        Gex.setdefault((r['group'], r['k']), ex(r))
    print('| obstruction group | k = 1 | k = 2 | k = 3 | example of the largest k |')
    print('|---|---|---|---|---|')
    for g, c in sorted(G.items(), key=lambda kv: -sum(kv[1].values())):
        kmax = max(c)
        print('| %s | %d | %d | %d | %s |' % (g, c[1], c[2], c[3], Gex[(g, kmax)]))
    # A': Pareto-maximal states
    print('\n## A′. The same, Pareto-maximal states only (where Lemmas H3 and H7 of `k4/hall.md` apply)\n')
    G = collections.defaultdict(collections.Counter)
    for r in states:
        if r['pareto']: G[r['group']][r['k']] += 1
    print('| obstruction group | k = 1 | k = 2 | k = 3 |')
    print('|---|---|---|---|')
    for g, c in sorted(G.items(), key=lambda kv: -sum(kv[1].values())):
        print('| %s | %d | %d | %d |' % (g, c[1], c[2], c[3]))
    # B: signature x repair kind
    print('\n## B. Obstruction signature × repair kind (primary kind of the minimal repairs)\n')
    kinds = collections.Counter(r['kind'] for r in states)
    korder = [k for k, _ in sorted(kinds.items(), key=lambda kv: (kv[0][:2], -kv[1]))]
    S = collections.defaultdict(collections.Counter); Sex = {}
    for r in states:
        S[r['sig']][r['kind']] += 1
        Sex.setdefault((r['sig'], r['kind']), ex(r))
    print('Repair kinds (columns): ' + ', '.join('`%s` (%d)' % (k, kinds[k]) for k in korder) + '.\n')
    print('| signature | states | ' + ' | '.join('`%s`' % k for k in korder) + ' |')
    print('|---|---|' + '---|' * len(korder))
    for s, c in sorted(S.items(), key=lambda kv: -sum(kv[1].values())):
        print('| %s | %d | ' % (s, sum(c.values())) + ' | '.join(str(c[k]) if c[k] else '' for k in korder) + ' |')
    print('\n### Examples (first state of each cell)\n')
    for s, c in sorted(S.items(), key=lambda kv: -sum(kv[1].values())):
        for k in korder:
            if c[k]: print('- %s × `%s` (%d): %s' % (s, k, c[k], Sex[(s, k)]))
    # C: lemma coverage
    print('\n## C. Coverage of the k = 1 states by the lemmas of `k4/dl2.md` §3\n')
    print('Each lemma\'s hypotheses are checked at every state; whenever they hold, its conclusion is asserted against')
    print('the exact deficits (no violation in any input), and no lemma applies at a state with k > 1.\n')
    k1 = [r for r in states if r['k'] == 1]
    flags = ['C4s', 'C4', 'C5', 'L2', 'L2o', 'L3']
    print('| input | k = 1 states | Cor 4 structural | Cor 4 (release) | Cor 5 (unblocking) | Lemma 2 at a best owner | Lemma 2 at another owner | Lemma 3 (owner re-base) | Lemma 2 or 3 | none |')
    print('|---|---|---|---|---|---|---|---|---|---|')
    def row(name, rs):
        n = len(rs)
        cnt = {f: sum(1 for r in rs if f in (r.get('lemmas') or {})) for f in flags}
        any23 = sum(1 for r in rs if set(r.get('lemmas') or {}) & {'L2', 'L2o', 'L3'})
        none = sum(1 for r in rs if not r.get('lemmas'))
        pct = lambda x: '%d (%.1f%%)' % (x, 100.0 * x / n) if n else '0'
        print('| %s | %d | %s | %s | %s | %s | %s | %s | %s | %s |' % (name, n, pct(cnt['C4s']), pct(cnt['C4']), pct(cnt['C5']),
              pct(cnt['L2']), pct(cnt['L2o']), pct(cnt['L3']), pct(any23), pct(none)))
    for name in per_src:
        row(name, [r for r in k1 if r['_file'] == name])
    row('**all**', k1)
    row('Pareto-maximal only', [r for r in k1 if r['pareto']])
    unc = [r for r in k1 if not r.get('lemmas')]
    if unc:
        print('\nk = 1 states that no lemma covers, by primary kind: %s; first examples:' % dict(
            collections.Counter(r['kind'] for r in unc)))
        for r in unc[:5]: print('- %s (%s)' % (ex(r), r['kind']))
    # D: the two- and three-agent cells
    print('\n## D. The states with k ≥ 2: kinds of their minimal repairs\n')
    D = collections.defaultdict(collections.Counter)
    for r in states:
        if r['k'] >= 2: D[r['k']][' | '.join(r['kinds'])] += 1
    for k in sorted(D):
        print('k = %d (%d states):\n' % (k, sum(D[k].values())))
        for s, c in D[k].most_common(): print('- %d: %s' % (c, s))
        print()


if __name__ == '__main__':
    main(sys.argv[1:])
