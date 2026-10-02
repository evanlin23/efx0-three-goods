"""Exhaustive two-type neighbourhoods of hard profiles (compute/k4-portfolio, Phase 3 complement). EVIDENCE only.

For a seed profile of a fixed core (domain indices of check4.core_domains), every profile that differs from it in the
types of at most two agents is evaluated with the fast path (k4/portfolio_dump.c + k4/portfolio_preds.py), every
predicate of the registry at every state and key. This is the systematic counterpart of the annealing in
k4/portfolio_hunt.py: around the profiles where the margins are smallest, no single or double type change is skipped.
Failures of the non-control predicates are written to results/k4_portfolio/nbhd_<LABEL>_fails.jsonl.gz (and must then
be confirmed with `python3 k4/portfolio_ref.py confirm`).

  python3 k4/portfolio_nbhd.py --seeds=hard5|fail10 [--k=K] [--jobs=J] [--name=LABEL] [--pairs]
      the first K seeds of k4/portfolio_hunt.py's seed list; --pairs adds every pair of agents (else single agents);
      --max=N evaluates a seeded random subset of N of each seed's neighbourhood instead"""
import collections, gzip, itertools, json, os, sys, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check4
import portfolio as PF
import portfolio_preds as PR
import portfolio_hunt as H

CONTROLS = {'RT4', 'D2', 'K1'}


def unit(task):
    name, sets, m, profs = task
    doms = check4.core_domains(sets, m, False)
    alive = [p for p in PR.SNAMES + PR.KNAMES if p not in CONTROLS]
    out = {'profiles': len(profs), 'with_states': 0, 'states': 0, 'keys': 0, 'fails': [], 'margin': {}}
    for prof, r in H.evaluate_batch(sets, m, doms, profs):
        out['with_states'] += 1; out['states'] += r['states']; out['keys'] += r['keys_pos']
        out['fails'] += H.failures_in(r, alive, sets, m, prof, name)
        for kind, names in (('single', PR.SNAMES), ('keyg', PR.KNAMES)):
            for nm in names:
                mg = r[kind][nm]['margin']
                if mg is not None and (nm not in out['margin'] or mg < out['margin'][nm]): out['margin'][nm] = mg
    return name, out


def main():
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in sys.argv[1:] if a.startswith('--'))
    name = opt.get('name', 'nbhd')
    print('# command: python3 k4/portfolio_nbhd.py ' + ' '.join(sys.argv[1:]), flush=True)
    src = opt.get('seeds', 'hard5')
    seeds = {'hard5': lambda: H.seeds_hard(12, 5), 'hard': H.seeds_hard, 'fail10': H.seeds_fail10}[src]()[:int(opt.get('k', 4))]
    tasks = []
    for sd in seeds:
        doms = check4.core_domains(sd['sets'], sd['m'], False)
        n = len(sd['sets']); cur = tuple(sd['start'])
        profs = set()
        for i in range(n):
            for t in range(len(doms[i])):
                p = list(cur); p[i] = t; profs.add(tuple(p))
        if 'pairs' in opt:
            for i, j in itertools.combinations(range(n), 2):
                for t in range(len(doms[i])):
                    for u in range(len(doms[j])):
                        p = list(cur); p[i] = t; p[j] = u; profs.add(tuple(p))
        profs = sorted(profs)
        if 'max' in opt and len(profs) > int(opt['max']):         # a seeded random subset (said in the log)
            import random
            profs = sorted(random.Random(1).sample(profs, int(opt['max'])))
        print(f"# seed {sd['name']}: {len(profs):,} profiles", flush=True)
        for k in range(0, len(profs), 4000): tasks.append((sd['name'], sd['sets'], sd['m'], profs[k:k + 4000]))
    tot = collections.defaultdict(lambda: {'profiles': 0, 'with_states': 0, 'states': 0, 'keys': 0, 'fails': 0, 'margin': {}})
    fpath = os.path.join(PF.OUT, f'nbhd_{name}_fails.jsonl.gz')
    t0 = time.time()
    with Pool(int(opt.get('jobs', 2))) as pool:
        for nm, out in pool.imap_unordered(unit, tasks):
            e = tot[nm]
            for k in ('profiles', 'with_states', 'states', 'keys'): e[k] += out[k]
            e['fails'] += len(out['fails'])
            for p, mg in out['margin'].items():
                if p not in e['margin'] or mg < e['margin'][p]: e['margin'][p] = mg
            if out['fails']:
                with gzip.open(fpath, 'at') as fo:
                    for r in out['fails']: fo.write(json.dumps(r, separators=(',', ':')) + '\n')
                print(f"  ** {nm}: {len(out['fails'])} failures: {sorted(set(r['pred'] for r in out['fails']))}", flush=True)
    for nm, e in tot.items():
        print(f"{nm}: profiles {e['profiles']:,}, with a state {e['with_states']:,}, states {e['states']:,}, keys {e['keys']:,}; "
              f"failures (non-control) {e['fails']}; least margins: "
              + ', '.join(f'{p} {e["margin"].get(p)}' for p in PR.SNAMES + PR.KNAMES), flush=True)
    print(f'# {time.time() - t0:.0f} s', flush=True)


if __name__ == '__main__':
    main()
