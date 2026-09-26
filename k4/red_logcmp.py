"""Compare the counters of results/k4_red_lemmas.log (the rerun with the current k4/red.c) with the logs written before the
PR #51 review (results/k4_red_n3.log, _n4.log, _n5.log, _n4_2_all.log, _bt.log): for every command block of an old log
whose files, --rand and --seed match a block of the rerun (or whose blocks together cover it), print how many counters
both print and which of them differ. The amax_* counters depend on the first potential of --pots, so they differ where
an old command used other potentials. Usage: python3 k4/red_logcmp.py"""
import collections, os, re
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')


def blocks(path):
    out, cur = [], None
    for l in open(os.path.join(ROOT, path)):
        l = l.rstrip('\n')
        if l.startswith('# command:'):
            cmd = l[len('# command:'):].replace('"', '')
            pots = re.findall(r'--pots=(\S+)', cmd)
            cur = {'files': tuple(sorted(re.findall(r'results/\S+\.json\.gz', cmd))),
                   'rand': (re.findall(r'--rand=(\d+)', cmd) or ['0'])[0], 'seed': (re.findall(r'--seed=(\d+)', cmd) or ['1'])[0],
                   'pot1': pots[0].split(';')[0] if pots else '', 'cnt': {}}
            out.append(cur)
            continue
        m = re.match(r'^(\S+)\s+(\d+)$', l)
        if m and cur is not None and not m.group(1).startswith('k4_certs'): cur['cnt'][m.group(1)] = int(m.group(2))
    return out


new = {(b['files'], b['rand'], b['seed']): b for b in blocks('results/k4_red_lemmas.log')}
tot = diff = 0
for old in ['results/k4_red_n3.log', 'results/k4_red_n4.log', 'results/k4_red_n5.log', 'results/k4_red_n4_2_all.log',
            'results/k4_red_bt.log']:
    ob = blocks(old)
    for k, nb in new.items():
        exact = [b for b in ob if (b['files'], b['rand'], b['seed']) == k]
        if exact:
            groups = [[b] for b in exact]
        else:
            parts = [b for b in ob if b['rand'] == k[1] and b['seed'] == k[2] and set(b['files']) <= set(k[0])]
            groups = [parts] if parts and {f for b in parts for f in b['files']} == set(k[0]) else []
        for parts in groups:
            oc = collections.Counter()
            for b in parts: oc.update(b['cnt'])
            common = [c for c in oc if c in nb['cnt']]
            mis = [(c, oc[c], nb['cnt'][c]) for c in common if oc[c] != nb['cnt'][c]]
            samepot = all(b['pot1'] == nb['pot1'] for b in parts)
            tot += len(common); diff += len(mis)
            print('%s | %s rand=%s seed=%s | first potential %s | %d counters in common, %d different%s'
                  % (old, ' '.join(os.path.basename(f) for f in k[0]), k[1], k[2], 'the same' if samepot else 'DIFFERENT',
                     len(common), len(mis), (': %s' % mis) if mis else ''))
print('total: %d counter values compared, %d different' % (tot, diff))
