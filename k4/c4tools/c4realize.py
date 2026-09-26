"""k4/c4one.md §6: does the covering change "insert q at the step that started its block" realize a rotation?
For every core with exactly one 4-good agent q in the given certificate files, runs k4/c4check.c with
-X -Y -P2 -u2 -i20 -Z3 -K<cls> (every insertion sequence; for each run of class cls that the theorems leave open, the
change that inserts q at the step that started q's block; c4check.c prints both runs). For each such pair it recomputes
both runs with the independent tracer (c4trace.phase1, from the printed processing order) and asks whether the new
picks are those of a rotation of the old run along a need chain x_0 -> ... -> x_s = q (x_i takes Y_{x_{i-1}}, every
agent off the chain keeps its pick), with x_0 the leader of q's old block, which ends on a good it ranks lower.
Counts distinct printed cases (not weighted by profiles). Classes: 1 G2, 4 (Tc), 5 (Tb).
Usage: python3 k4/c4tools/c4realize.py FILE [FILE ...] [--classes=1,4,5] [--limit=100000]"""
import os, re, sys, gzip, json, subprocess, collections
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
import c4trace as T
import lb4_run, c4check_run
BIN = os.environ.get('C4CHECK_BIN') or c4check_run.BIN
CLS = {1: 'G2', 2: 'q frozen, no chain to r', 3: 'q frozen, B4w (i)/(ii) fail', 4: '(Tc)', 5: '(Tb)'}
args = [a for a in sys.argv[1:] if not a.startswith('--')]
opt = dict(a[2:].split('=') for a in sys.argv[1:] if a.startswith('--'))
CLASSES = [int(x) for x in opt.get('classes', '1,4,5').split(',')]; LIMIT = int(opt.get('limit', 100000))

def parse(line):
    g = lambda k: re.search(k + r'=(\S+)', line).group(1)
    order = [int(x) for x in re.search(r'order=([\d ]+?)  ', line).group(1).split()]
    return json.loads(g('sets')), json.loads(g('vals')), order, [int(x) for x in g('blocks').split(',')], \
        [int(x) for x in g('picks').split(',')]

def tau_of(n, order, blocks):
    """the insertion choices (index among the unprocessed agents, in index order) that give this processing order"""
    done = set(); tau = []; seen = set()
    for a in order:
        if blocks[a] not in seen:
            seen.add(blocks[a]); tau.append([i for i in range(n) if i not in done].index(a))
        done.add(a)
    return tau

def needs(I, i, y):
    return set(I.ord[i][:I.rank[i][y]]) if y is not None else set(I.R[i])

def chains_to(I, Y, dst):
    out = []
    def rec(p):
        out.append(list(reversed(p)))
        for z in range(I.n):
            if z not in p and Y[z] is not None and Y[z] in needs(I, p[-1], Y[p[-1]]): rec(p + [z])
    rec([dst]); return out

def analyse(a_line, b_line):
    sets, vals, order, blocks, picks = parse(a_line)
    I = T.Inst(sets, vals); n = I.n
    Y, pos, blk, J, _ = T.phase1(I, tau_of(n, order, blocks))
    assert [(-1 if y is None else y) for y in Y] == picks, 'tracer disagrees on the old run'
    s2, v2, order2, blocks2, picks2 = parse(b_line)
    Y2, _, _, _, _ = T.phase1(I, tau_of(n, order2, blocks2))
    assert [(-1 if y is None else y) for y in Y2] == picks2, 'tracer disagrees on the new run'
    q = next(i for i in range(n) if len(sets[i]) == 4)
    assert int(re.search(r'agent=(\d+)', b_line).group(1)) == q
    ell = min((i for i in range(n) if blk[i] == blk[q]), key=lambda i: pos[i])
    for p in chains_to(I, Y, q):
        if p[0] != ell or len(p) < 2: continue
        pred = list(Y)
        for k in range(1, len(p)): pred[p[k]] = Y[p[k - 1]]
        if all(Y2[i] == pred[i] for i in range(n) if i != ell) and \
           (Y2[ell] is None or I.rank[ell][Y2[ell]] > I.rank[ell][Y[ell]]):
            return 'realized: a rotation along a need chain from the old leader to q (length %d)' % (len(p) - 1)
    if Y[q] == I.ord[q][0]: return 'not a rotation: q already held its top'
    return 'not a rotation: other'

def run(c):
    out = collections.Counter(); seen = set()
    for K in CLASSES:
        p = subprocess.run([BIN, '-X', '-Y', '-P2', '-u2', '-i20', '-o0', '-r1', '-w0', '-c0', '-f3', '-Z3', '-K%d' % K,
                            '-KL%d' % LIMIT], input=lb4_run.encode(c['sets'], c['m'], False), capture_output=True, text=True)
        last = None
        for l in p.stderr.split('\n'):
            if l.startswith('KCASE'): last = l
            elif l.startswith('KNEW') and last:
                key = (K, last.split(' upg=')[0])
                if key not in seen: seen.add(key); out[(CLS[K], analyse(last, l))] += 1
                last = None
    return out

def main():
    c4check_run.build()
    print('# c4realize.py', ' '.join(sys.argv[1:]), flush=True)
    for fn in args:
        cs = [c for c in json.load(gzip.open(fn, 'rt'))['cores'] if sum(len(s) == 4 for s in c['sets']) == 1]
        tot = collections.Counter()
        with Pool(4) as pool:
            for o in pool.imap_unordered(run, cs): tot.update(o)
        print(f'{fn}: {len(cs)} cores', flush=True)
        for k in sorted(tot): print(f'   {k[0]:5s} {k[1]:80s} {tot[k]}', flush=True)

if __name__ == '__main__':
    main()
