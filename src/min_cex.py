"""Reductions used in proofs/min_counterexample.md, §4 (two P-agents sharing a good of degree 2).

Two configurations, each under all 36 ranking profiles of its two agents:
  pair: P-agents e, f share the good g, valued by nobody else; e's goods are gl, g, p (p private), f's are g, y, pf
        (pf private), and gl != y (boundary goods, valued also by agents outside the pair);
  loop: the same with gl = y = G (a good valued by e, f and at least one outside agent).
Reductions (Lemma M1; 'source' = M1(b), an unenvied bundle of Y is used):
  RPT-e, RPT-f  delete e, f, g and both private goods; the agent whose private good is its top keeps it alone (Lemma M2)
  DEL           delete e, f, g and both private goods (no gadget), with source
  CON-e, CON-f  contract e (resp. f): the other agent values gl (resp. y) where it valued g; with source (pair only)
  GAD           replace e, f, g, p, pf by one agent h with v_h(G) = 2, v_h(q) = 1, q a new good; with source (loop only)
Writes the certificates (every admissible local state with its extension) for tools/check_reductions.py, and reports
for each configuration the profiles no reduction covers (there are none).
Usage: min_cex.py [certificate path, default ../results/min_cex_reductions.json.gz]"""
import itertools, sys, json, gzip, time, multiprocessing
from reduce import Reduction, certificate

PERMS = list(itertools.permutations(range(3)))


def order(p, goods):
    return tuple(goods[k] for k in p)


def sub(t, a, b):
    return tuple(b if g == a else g for g in t)


def build(conf, fam, pe, pf):
    """The reduction `fam` for configuration `conf` with rankings pe of e and pf of f (index permutations)."""
    gl, y = ('gl', 'y') if conf == 'pair' else ('G', 'G')
    e, f = order(pe, (gl, 'g', 'p')), order(pf, ('g', y, 'pf'))
    S, I, D = {'e': e, 'f': f}, {'g', 'p', 'pf'}, {gl, y}
    name = '%s|%s|e=%s|f=%s' % (conf, fam, '>'.join(e), '>'.join(f))
    if fam == 'RPT-e' and e[0] == 'p' or fam == 'RPT-f' and f[0] == 'pf':
        return Reduction(S, I, D, Sp={}, Ip=set(), name=name)
    if fam == 'DEL':
        return Reduction(S, I, D, Sp={}, Ip=set(), name=name, source=True)
    if fam == 'CON-e' and conf == 'pair':
        return Reduction(S, I, D, Sp={'f': sub(f, 'g', gl)}, Ip={'pf'}, name=name, source=True)
    if fam == 'CON-f' and conf == 'pair':
        return Reduction(S, I, D, Sp={'e': sub(e, 'g', y)}, Ip={'p'}, name=name, source=True)
    if fam == 'GAD' and conf == 'loop':
        return Reduction(S, I, D, Sp={'h': {'G': 2.0, 'q': 1.0}}, Ip={'q'}, name=name, source=True)
    return None


FAMS = ['RPT-e', 'RPT-f', 'DEL', 'CON-e', 'CON-f', 'GAD']


def job(args):
    conf, fam, pe, pf = args
    red = build(conf, fam, pe, pf)
    if red is None: return args, None, 0
    t = time.time(); cert = certificate(red)
    return args, cert, time.time() - t


if __name__ == '__main__':
    out = sys.argv[1] if len(sys.argv) > 1 else '../results/min_cex_reductions.json.gz'
    tasks = [(c, fam, pe, pf) for c in ('pair', 'loop') for pe in PERMS for pf in PERMS for fam in FAMS]
    t0 = time.time()
    with multiprocessing.Pool() as pool: res = pool.map(job, tasks)
    certs, cover = [], {}
    for (c, fam, pe, pf), cert, dt in res:
        if cert is None: continue
        certs.append(cert)
        cover.setdefault((c, pe, pf), []).append(fam)
    for c in ('pair', 'loop'):
        tried = sum(1 for (cc, fam, pe, pf), _, _ in res if cc == c and build(cc, fam, pe, pf))
        print('%s: %d reductions tried, %d reducible' % (c, tried, sum(1 for x in certs if x['name'].startswith(c + '|'))))
        for fam in FAMS:
            k = sum(1 for key, fams in cover.items() if key[0] == c and fam in fams)
            if k: print('  %-6s covers %2d of 36 profiles' % (fam, k))
        unc = [(order(pe, ('gl', 'g', 'p')), order(pf, ('g', 'y', 'pf'))) for pe in PERMS for pf in PERMS
               if (c, pe, pf) not in cover]
        print('  profiles covered by no reduction: %d %s' % (len(unc), unc))
    with gzip.open(out, 'wt') as fh: json.dump(certs, fh)
    print('wrote %d certificates, %d local states, to %s (%.0fs)'
          % (len(certs), sum(len(x['states']) for x in certs), out, time.time() - t0))
