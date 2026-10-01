#!/usr/bin/env python3
"""DL13 on every profile near a given one (compute/k4-dl13; ledger K4.DL2.T13). EVIDENCE tooling.

usage: python3 k4/dl13_nbhd.py FILE POS PROF [--radius=R] [--jobs=J] [--ckpt=PATH] [--dump=PATH] [--tables=PATH]
         [--rt=R] [--ro=O]
FILE a certificate file results/k4_certs_*.json.gz, POS the core's position in its "cores" list, PROF the profile as
comma-separated indices into check4.core_domains (the "prof" of a catalogue record). Runs k4/dl13.c on every strict
profile of the core that differs from PROF in the types of at most R agents (default 2); one unit (one dl13.c process,
checkpointed) per set of changed agents. Prints dl13_run.py's report and tables."""
import gzip, itertools, json, os, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check4
import dl13_run as DRUN


def unit(task):
    key, sets, m, prof, S, opts = task
    t0 = time.time()
    doms = check4.core_domains(sets, m, False)
    profs = []
    for ts in itertools.product(*[[t for t in range(len(doms[i])) if t != prof[i]] for i in S]):
        p = list(prof)
        for i, t in zip(S, ts): p[i] = t
        profs.append(p)
    b = DRUN.run_blocks(DRUN.block(sets, m, doms, key['pos'], 0, profs), opts)[0]
    for d in b['D']: d['vals'] = [[doms[i][d['prof'][i]][g] for g in sets[i]] for i in range(len(sets))]
    return key, [b], time.time() - t0


def main(argv):
    rest = [a for a in argv if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in argv if a.startswith('--'))
    print('# command: python3 k4/dl13_nbhd.py ' + ' '.join(argv), flush=True)
    print(f'# {os.path.basename(DRUN.SRC)} sha256 {DRUN.SHA}', flush=True)
    DRUN.build()
    f, pos, prof = rest[0], int(rest[1]), [int(x) for x in rest[2].split(',')]
    core = json.load(gzip.open(f, 'rt'))['cores'][pos]
    sets, m = core['sets'], core['m']
    R = int(opt.get('radius', 2)); jobs = int(opt.get('jobs', 2))
    opts = [f"-r{int(opt.get('rt', 1))}", f"-o{int(opt.get('ro', 100))}"]
    ckey = {'mode': 'nbhd', 'file': os.path.basename(f), 'pos': pos, 'prof': prof, 'copts': opts}
    done = DRUN.load_ckpt(opt.get('ckpt'), ckey)
    tot = {}
    for bl in done.values():
        for b in bl: DRUN.merge(tot, b)
    tasks = []
    for r in range(R + 1):
        for S in itertools.combinations(range(len(sets)), r):
            key = {'pos': pos, 'S': list(S)}
            if json.dumps(key, sort_keys=True) in done: continue
            tasks.append((key, sets, m, prof, list(S), opts))
    print(f'# core {pos} of {os.path.basename(f)} (m = {m}, idx {core.get("idx")}), profile {prof}, radius {R}: '
          f'{len(tasks)} units to run, {len(done)} from the checkpoint', flush=True)
    t0 = time.time()

    def onres(key, bl, secs):
        for b in bl:
            DRUN.merge(tot, b)
            for d in b['D']:
                d['core'] = {'file': os.path.basename(f), 'pos': pos, 'idx': core.get('idx'), 'm': m, 'sets': sets}
            DRUN.dump_write(opt.get('dump'), b['D'])
            L = b['L']
            print(f"#   unit {key}: profiles {b['K']['prof']}, f >= 1 states {L['st1']}, DL13 FAILS at {L['fail1']} "
                  f"[{secs:.1f} s]", flush=True)
    DRUN.run_units(unit, tasks, jobs, opt.get('ckpt'), ckey, onres)
    DRUN.report(f'neighbourhood of {prof}', tot, time.time() - t0)
    DRUN.print_tables(tot)
    if 'tables' in opt:
        json.dump({'command': 'python3 k4/dl13_nbhd.py ' + ' '.join(argv), 'dl13_c_sha256': DRUN.SHA,
                   'counters': {k: tot.get(k, 0) for k in DRUN.KEYS + DRUN.LKEYS}, 'tab': tot.get('tab', {})},
                  open(opt['tables'], 'w'), indent=0, sort_keys=True)


if __name__ == '__main__':
    main(sys.argv[1:])
