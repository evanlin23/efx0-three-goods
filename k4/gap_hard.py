"""The smallest hard instances of the exposed-frozen gap (compute/k4-gap; k4/gap.md). EVIDENCE only.

  python3 k4/gap_hard.py CATALOG ... [--show=3] [--out=results/k4_gap/hard.json.gz]

Reads catalogs written by k4/gap_run.py and lists, per category, the smallest gap profiles (by n, then m, then the
number of configurations), for each n separately, with the full data of one Phi'-maximum (gap.c's record) and, for the listed ones, every
Phi'-maximum re-derived by the Python model k4/gap_model.py. Categories (per profile; a Phi'-maximum is "simple" if it
has a valid owner with C empty, i.e. without withheld goods and without unfreezing):
  W   no Phi'-maximum is simple, but some Phi'-maximum has a valid owner (the owner must withhold goods, C != 0, which
      needs frozen agents unfrozen by its bundle)
  N   no Phi'-maximum has a valid owner, some configuration has one (a counterexample to Conjecture Phi')
  X   no configuration has a valid owner (a counterexample to C4min in configuration form)
  T2  some Phi'-maximum has a frozen agent threatened by two owners (roadmap step (iv))
  NPO some Phi'-maximum is not pool-optimal (roadmap step (i))
  F2  f >= 2 (the gap beyond f = 1: every configuration has an exposed frozen agent, none frozen-robust)
--out writes the listed records (with the Python-derived maxima) as gzip JSON."""
import gzip, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gap_model as gm

CATS = {
    'W': lambda r: r['cat'] == 'W',
    'N': lambda r: r['cat'] == 'N',
    'X': lambda r: r['cat'] == 'X',
    'T2': lambda r: r['nmax_thr2'] > 0,
    'NPO': lambda r: r['nmax_po'] < r['nmax'],
    'F2': lambda r: r['f'] >= 2,
}

def describe(r, show_py=True):
    sets, vals = r['core']['sets'], r['vals']
    s = [f"    n={len(sets)} m={r['core']['m']} f={r['f']} omega={r['omega']} core {r['core']['file']}#{r['core']['pos']} "
         f"(idx {r['core']['idx']}); sets={sets}",
         f"    values: " + '; '.join(f"agent {i}: " + ', '.join(f"{g}:{x}" for g, x in zip(S, V)) for i, (S, V) in enumerate(zip(sets, vals))),
         f"    {r['ncfg']} configurations ({r['ncompl']} with a valid owner, {r['nsimple']} with C empty), {r['nmax']} Phi'-maxima "
         f"at Phi' = {r['phimax']} ({r['nmax_compl']} with a valid owner, {r['nmax_simple']} with C empty, {r['nmax_po']} "
         f"pool-optimal, {r['nmax_thr2']} with a frozen agent threatened by two owners)"]
    if show_py:
        prof = gm.Profile(sets, vals, r['core']['m'])
        cfgs = prof.configs()
        best = max(c.phi for c in cfgs)
        mx = [c for c in cfgs if c.phi == best]
        r['py_maxima'] = []
        for c in mx[:4]:
            own = {o: (c.owner(o)[0], sorted(c.owner(o)[1])) for o in c.owners}
            thr = [(o, x, c.h7(x, o) if c.key[x] is not None else c.kind(x)) for o, x in c.threat_edges]
            need = {c.key[x]: c.needers(c.key[x]) for x in c.frozen}
            s.append(f"    max {c}: owners (least |C|, C) {own}; threats (owner, agent, H7 class or kind) {thr}; "
                     f"needers {need}; pool-optimal {c.pool_optimal}; kinds {[c.kind(i) for i in range(prof.n)]}")
            r['py_maxima'].append({'key': list(c.key), 'Q': {y: sorted(q) for y, q in c.Q.items()}, 'L': sorted(c.L),
                                   'phi': list(c.phi), 'owners': {o: [k, C] for o, (k, C) in own.items()}, 'threats': thr})
    return '\n'.join(s)

def main():
    files = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in sys.argv[1:] if a.startswith('--'))
    show = int(opt.get('show', 3))
    print("command: python3 k4/gap_hard.py " + ' '.join(sys.argv[1:]), flush=True)
    recs = []
    for f in files:
        d = json.load(gzip.open(f, 'rt'))
        for r in d['records']: r['_cat'] = os.path.basename(f); recs.append(r)
    recs.sort(key=lambda r: (len(r['core']['sets']), r['core']['m'], r['ncfg']))
    out = {}
    for name, test in CATS.items():
        hit = [r for r in recs if test(r)]
        byfile = {}
        for r in hit: byfile[r['_cat']] = byfile.get(r['_cat'], 0) + 1
        print(f"\n== {name}: {len(hit)} profiles in the catalogs {byfile}")
        out[name] = []
        for nn in sorted({len(r['core']['sets']) for r in hit}):
            sub = [r for r in hit if len(r['core']['sets']) == nn]
            print(f"  n = {nn}: {len(sub)} profiles; the smallest {min(show, len(sub))}:")
            for r in sub[:show]:
                print(describe(r)); out[name].append(r)
    if 'out' in opt:
        with gzip.open(opt['out'], 'wt') as fo: json.dump(out, fo, separators=(',', ':'))
        print(f"\nwrote {sum(len(v) for v in out.values())} records to {opt['out']}")

if __name__ == '__main__':
    main()
