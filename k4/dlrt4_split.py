"""Split-unit driver for k4/dlrt4.c (compute/k4-rt4, n4_3_x5): dlrt4_run.py's exhaustive certs mode with every core cut
into sub-units, so that no dlrt4.c process outlives a container restart. EVIDENCE only.

  python3 k4/dlrt4_split.py FILE --cores=A:B --split=S [--jobs=J] [--ckpt=PATH] [--dump=PATH.jsonl.gz] [--tables=PATH.json]
                                 [--rt=R] [--ro=O]

dlrt4_run.py runs one dlrt4.c process per core (P = 0: every profile of the product of the agents' domains) and
checkpoints whole cores; an m = 9 core of k4_certs_4_n4_3 with domains 144 x 288 x 288 x 6 takes 75 to 100 minutes in one
process, longer than the container survives. Here the agent with the largest domain (the first one on ties) has its
domain cut into S contiguous chunks; each (core, chunk) is one dlrt4.c process on the block whose domains are the core's
(check4.core_domains, as dlrt4_run.py) with that agent's domain replaced by the chunk. The chunks partition the agent's
domain, so the sub-units partition the core's profiles, and since dlrt4.c evaluates every profile on its own, the K and L
counters and the B/G/M/Z/C/Y tables of a core are the sums of its sub-units' (the largest least deficit, "maxmin", the
maximum), i.e. what dlrt4_run.py prints for the core. Only the dump differs: dlrt4.c dumps the first state of each
(signature, branch) cell and every R-th state outside R_13 per process, so a split core dumps more of those records (every
failing state is dumped either way). The dump's "prof" indexes the core's full domains (the chunk offset is added back)
and its "vals" are the profile's values, as in dlrt4_run.py.

The functions, counters, report and tables are dlrt4_run.py's (imported, unchanged). The checkpoint keys are
{"pos", "agent", "lo", "hi"} (the agent and its chunk [lo, hi) of domain indices), with the split in the checkpoint's ckey.
Validate against dlrt4_run.py on cores it has run (same counters and tables, up to "maxmin" on cores with omega = 0)."""
import gzip, json, os, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check4
import dlrt4_run as R


def unit_split(task):
    """one chunk of one core: every profile with the agent's type in its chunk"""
    key, sets, m, opts = task
    t0 = time.time()
    doms = check4.core_domains(sets, m, False)
    a, lo, hi = key['agent'], key['lo'], key['hi']
    sub = list(doms); sub[a] = doms[a][lo:hi]
    b = R.run_blocks(R.block(sets, m, sub, key['pos'], 0), opts + ['-S1'])[0]
    for d in b['D']:
        d['vals'] = [[D[p][g] for g in S] for S, D, p in zip(sets, sub, d['prof'])]
        d['prof'][a] += lo
    return key, [b], time.time() - t0


def main():
    argv = sys.argv[1:]
    args = [a for a in argv if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in argv if a.startswith('--'))
    print('# command: python3 k4/dlrt4_split.py ' + ' '.join(argv), flush=True)
    print(f'# {os.path.basename(R.SRC)} sha256 {R.SHA}', flush=True)
    R.build()
    jobs = int(opt.get('jobs', 2)); ck = opt.get('ckpt'); dump = opt.get('dump'); S = int(opt['split'])
    copts = [f"-r{int(opt.get('rt', 50))}", f"-o{int(opt.get('ro', 0))}"]
    f = args[0]
    cores = json.load(gzip.open(f, 'rt'))['cores']
    a, b = opt['cores'].split(':'); lo, hi = int(a or 0), int(b or len(cores))
    ckey = {'mode': 'certs-split', 'file': os.path.basename(f), 'P': 0, 'split': S, 'copts': copts}
    done = R.load_ckpt(ck, ckey)
    tot, tasks, cov = {}, [], {}
    for k in range(lo, hi):
        c = cores[k]
        doms = check4.core_domains(c['sets'], c['m'], False)
        ag = max(range(len(doms)), key=lambda i: (len(doms[i]), -i))
        N = len(doms[ag])
        cuts = [N * j // S for j in range(S + 1)]
        for j in range(S):
            key = {'pos': k, 'agent': ag, 'lo': cuts[j], 'hi': cuts[j + 1]}
            kj = json.dumps(key, sort_keys=True)
            if kj in done:
                for bl in done[kj]: R.merge(tot, bl)
                cov[k] = cov.get(k, 0) + 1
                continue
            tasks.append((key, c['sets'], c['m'], copts))
    print(f'# {os.path.basename(f)}: cores {lo}..{hi - 1}, split {S}, {len(tasks)} sub-units to run, {len(done)} from the '
          f'checkpoint; every profile', flush=True)
    t0 = time.time()

    def onres(key, bl, secs):
        for blk in bl:
            R.merge(tot, blk)
            c = cores[key['pos']]
            for d in blk['D']:
                d['core'] = {'file': os.path.basename(f), 'pos': key['pos'], 'idx': c.get('idx', key['pos']),
                             'm': c['m'], 'sets': c['sets']}
            R.dump_write(dump, blk['D'])
            if blk['L']['fail1']: print(f"#   DL_RT4 FAILS: core {key}: {blk['L']['fail1']} states", flush=True)
        cov[key['pos']] = cov.get(key['pos'], 0) + 1
        if cov[key['pos']] == S: print(f"#   core {key['pos']} complete", flush=True)
    R.run_units(unit_split, tasks, jobs, ck, ckey, onres)
    full = sorted(k for k, n in cov.items() if n == S)
    print(f'# cores complete: {len(full)} of {hi - lo}' + (f' ({full[0]}..{full[-1]})' if full else ''), flush=True)
    R.report(os.path.basename(f) + f' cores {lo}..{hi - 1} (split {S})', tot, time.time() - t0)
    R.print_tables(tot)
    if 'tables' in opt:
        json.dump({'command': 'python3 k4/dlrt4_split.py ' + ' '.join(argv), 'src': os.path.basename(R.SRC),
                   'src_sha256': R.SHA, 'cores_complete': full,
                   'counters': {k: tot.get(k, 0) for k in R.KEYS + R.LKEYS}, 'tab': tot.get('tab', {})},
                  open(opt['tables'], 'w'), indent=0, sort_keys=True)


if __name__ == '__main__':
    main()
