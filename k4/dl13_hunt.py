#!/usr/bin/env python3
"""Adversarial search for a counterexample to Conjecture DL13 (k4/dl2.md §3, ledger K4.DL2.T13; compute/k4-dl13).
EVIDENCE tooling: a hill-climb over the strict profiles of a core that drives DL13's slack down.

The slack of a profile (k4/dl13u.c, -v line "U"): over its f >= 1 states (min-frozen P with def > 0), the least number
of R_13 moves that lower the deficit (0 = DL13 fails there). A climb starts at a profile of a core and repeatedly
evaluates NB random neighbours (one agent's strict type replaced by another of the core's domain; with --bt, a
4-good agent's new type is big-top with probability 1/2), moving to the best one when it is not worse; the score,
smaller is closer to a failure, is (slack, -#states without an improving T1 move whose only R_13 moves are T3 moves
with a helper, -#states without an improving T1 move). A climb stops after --patience steps without a strict
improvement or after --steps steps. Every profile evaluated is a profile of a k = 4 core with its strict type (the
neighbours stay in check4.core_domains), so every state met counts as tested; the totals are dl13.c's counters over
the distinct profiles evaluated.

usage: python3 k4/dl13_hunt.py certs FILE [--climbs=C] [--steps=S] [--nb=NB] [--patience=Q] [--bt] [--seed=s]
                                          [--cores=A:B] [--mmin=M] [--mmax=M] [--jobs=J] [--out=FILE.jsonl.gz]
                                          [--ckpt=PATH] [--tables=PATH]          (--mmin/--mmax: cores with m in range)
       python3 k4/dl13_hunt.py suite [--maxn=N] ...      (climbs start at the suite's core instances, own profile first)
       python3 k4/dl13_hunt.py catalog FILE.json.gz [--every=E] [--max=N] ...  (climbs start at catalogue profiles of
                                          k4/gap_run.py, shuffled with --seed)
       python3 k4/dl13_hunt.py records FILE.jsonl.gz ...  (climbs start at the profiles of dl13 dump records)
A climb without a given start begins at the best of --init (default 256) random profiles of its core (with --bt,
each 4-good agent big-top with probability 1/2); a given start without an f >= 1 state with def > 0 is replaced by
the best of --init random profiles differing from it in one or two agents' types; if none has such a state, the climb
ends there.
Each climb is one unit (checkpointed with --ckpt); --out appends every D record of dl13.c (DL13 failures, the first
state of each cell per process) and the best profile of each climb."""
import gzip, json, os, random, sys, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check4
import dl13_run as DRUN
DRUN.configure('dl13u.c')             # the slack line "U" is in k4/dl13u.c only

BT = None


def is_bt(d, S):
    if len(S) != 4: return False
    w = sorted(d[g] for g in S); return w[3] > w[2] + w[1]


def type_index(D, S, vals):
    """the index in domain D of the strict order type of the values vals (on S), or None"""
    def key(v):
        sums = [sum(v[k] for k in range(len(v)) if s >> k & 1) for s in range(1, 1 << len(v))]
        order = sorted(set(sums)); return tuple(order.index(x) for x in sums)
    kv = key(vals)
    for t, d in enumerate(D):
        if key([d[g] for g in S]) == kv: return t
    return None


def evaluate(sets, m, doms, profs, tag=0):
    """dl13.c -v on the listed profiles -> [(prof, U or None)], D records, the block"""
    import subprocess
    inp = DRUN.block(sets, m, doms, tag, 0, profs)
    r = subprocess.run([DRUN.BIN, '-v', '-r0', '-o0'], input=inp, capture_output=True, text=True, check=True)
    b = DRUN.parse(r.stdout)
    out, Ds = [], []
    cur = None
    for l in r.stdout.splitlines():
        w = l.split()
        if w[0] == 'V':
            cur = [tuple(map(int, w[2:2 + len(sets)])), None]; out.append(cur)
        elif w[0] == 'U':
            u = list(map(int, w[2 + len(sets):])); cur[1] = {'f': u[0], 'st1': u[1], 't3only': u[2], 't3hOnly': u[3], 'minmv': u[4]}
        elif w[0] == 'D':
            Ds.append(json.loads(l[2:]))
    return out, Ds, b[0]


def score(u):
    if u is None or u['st1'] == 0: return (10 ** 9, 0, 0)
    return (u['minmv'], -u['t3hOnly'], -u['t3only'])


def climb(task):
    key, sets, m, start, steps, nb, patience, bt, seed, init = task
    rng = random.Random(seed)
    t0 = time.time()
    doms = check4.core_domains(sets, m, False)
    btidx = [[t for t, d in enumerate(D) if is_bt(d, S)] for D, S in zip(doms, sets)]
    seen = {}
    tot = {}
    recs = []

    def ev(profs):
        profs = [p for p in dict.fromkeys(profs) if p not in seen]
        if not profs: return
        out, Ds, blk = evaluate(sets, m, doms, profs, key['pos'])
        DRUN.merge(tot, blk)
        for p, u in out: seen[p] = u
        for d in Ds:
            d['vals'] = [[doms[i][d['prof'][i]][g] for g in sets[i]] for i in range(len(sets))]
            d['core'] = {'key': key, 'm': m, 'sets': sets}
            recs.append(d)
    if start is None:                 # the best of `init` random profiles
        rnd = lambda: tuple(rng.choice(btidx[i]) if bt and btidx[i] and rng.random() < 0.5 else rng.randrange(len(doms[i]))
                            for i in range(len(sets)))
        pool = [rnd() for _ in range(init)]
        ev(pool)
        start = min(pool, key=lambda p: score(seen[p]))
    else:
        ev([start])
        if score(seen[start])[0] >= 10 ** 9:  # no state at the given start: the best of `init` profiles near it
            near = []
            for _ in range(init):
                p = list(start)
                for i in rng.sample(range(len(sets)), rng.choice((1, 2))): p[i] = rng.randrange(len(doms[i]))
                near.append(tuple(p))
            ev(near)
            start = min([start] + near, key=lambda p: score(seen[p]))
    cur = start; best = score(seen[cur]); stale = 0; nsteps = 0
    if best[0] >= 10 ** 9: steps = 0          # no f >= 1 state with def > 0 to start from
    traj = [list(best)]
    while nsteps < steps and stale < patience and best[0] > 0:
        nsteps += 1
        cands = []
        for _ in range(nb):
            i = rng.randrange(len(sets))
            if bt and btidx[i] and rng.random() < 0.5: t = rng.choice(btidx[i])
            else: t = rng.randrange(len(doms[i]))
            if t == cur[i]: continue
            cands.append(cur[:i] + (t,) + cur[i + 1:])
        ev(cands)
        nxt = min(cands, key=lambda p: score(seen[p]), default=None)
        if nxt is None: stale += 1; continue
        s = score(seen[nxt])
        if s < best: best = s; cur = nxt; stale = 0; traj.append(list(best))
        elif s == best: cur = nxt; stale += 1
        else: stale += 1
    bestrec = {'best': True, 'key': key, 'prof': list(cur), 'score': list(best), 'U': seen[cur],
               'vals': [[doms[i][cur[i]][g] for g in sets[i]] for i in range(len(sets))], 'core': {'m': m, 'sets': sets},
               'steps': nsteps, 'evaluated': len(seen), 'traj': traj}
    return key, tot, recs + [bestrec], time.time() - t0, len(seen)


def main(argv):
    mode = argv[0]; rest = [a for a in argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in argv[1:] if a.startswith('--'))
    print('# command: python3 k4/dl13_hunt.py ' + ' '.join(argv), flush=True)
    print(f'# dl13u.c sha256 {DRUN.SHA}', flush=True)
    DRUN.build()
    C, S, NB, Q = int(opt.get('climbs', 100)), int(opt.get('steps', 200)), int(opt.get('nb', 48)), int(opt.get('patience', 25))
    bt = 'bt' in opt; seed = int(opt.get('seed', 1)); jobs = int(opt.get('jobs', 2)); I = int(opt.get('init', 256))
    rng = random.Random(seed)
    tasks = []
    if mode == 'certs':
        cores = json.load(gzip.open(rest[0], 'rt'))['cores']
        lo, hi = 0, len(cores)
        if 'cores' in opt: a, b = opt['cores'].split(':'); lo, hi = int(a or 0), int(b or len(cores))
        okc = [k for k in range(lo, hi) if int(opt.get('mmin', 0)) <= cores[k]['m'] <= int(opt.get('mmax', 99))]
        for c in range(C):
            k = rng.choice(okc)
            tasks.append(({'climb': c, 'pos': k, 'file': os.path.basename(rest[0])}, cores[k]['sets'], cores[k]['m'], None,
                          S, NB, Q, bt, rng.randrange(1 << 30), I))
    else:
        starts = []
        if mode == 'suite':
            import glob
            for fn in sorted(glob.glob(os.path.join(HERE, 'suite', 'instances', '*.json'))):
                d = json.load(open(fn))
                if 'kind' in d or not d.get('is_core', True) or len(d['sets']) > int(opt.get('maxn', 6)): continue
                starts.append((d['id'], d['sets'], d.get('m') or 1 + max(g for S_ in d['sets'] for g in S_), d['vals']))
        elif mode == 'catalog':
            recs = json.load(gzip.open(rest[0], 'rt'))['records'][::int(opt.get('every', 1))]
            for r in recs:
                c_ = r['core']
                if not int(opt.get('mmin', 0)) <= c_['m'] <= int(opt.get('mmax', 99)): continue
                starts.append((f"{c_['file']}#{c_.get('pos')}:{','.join(map(str, r['prof']))}", c_['sets'], c_['m'], r['vals']))
            rng.shuffle(starts)
            if 'max' in opt: starts = starts[:int(opt['max'])]
        else:
            for l in gzip.open(rest[0], 'rt'):
                d = json.loads(l)
                if 'core' not in d or 'vals' not in d: continue
                starts.append((str(d['core'].get('pos', d['core'].get('id'))) + ':' + ','.join(map(str, d.get('prof', []))),
                               d['core']['sets'], d['core']['m'], d['vals']))
            starts = list({s[0]: s for s in starts}.values())
            if 'max' in opt: starts = starts[:int(opt['max'])]
        c = 0
        for sid, sets, m, vals in starts:
            doms = check4.core_domains(sets, m, False)
            st = tuple(type_index(D, S_, V) for D, S_, V in zip(doms, sets, vals))
            if any(t is None for t in st): st = None
            for r in range(int(opt.get('per', 1))):
                tasks.append(({'climb': c, 'pos': c, 'start': sid}, sets, m, st if r == 0 else None, S, NB, Q, bt,
                              rng.randrange(1 << 30), I))
                c += 1
    ck = opt.get('ckpt'); done = set(); tot = {}
    if ck and os.path.exists(ck):
        for l in open(ck):
            try: d = json.loads(l)
            except ValueError: continue
            if d['cmd'] == argv: done.add(d['key']['climb']); DRUN.merge_tot(tot, d['tot'])
    tasks = [t for t in tasks if t[0]['climb'] not in done]
    print(f'# {len(tasks)} climbs to run, {len(done)} from the checkpoint; steps <= {S}, {NB} neighbours per step, '
          f'patience {Q}, big-top bias {bt}', flush=True)
    t0 = time.time(); nev = 0; best_all = []
    with Pool(jobs) as pool:
        for key, ctot, recs, secs, ne in pool.imap_unordered(climb, tasks):
            nev += ne
            DRUN.merge_tot(tot, ctot)
            br = recs[-1]
            best_all.append((tuple(br['score']), key))
            fails = [r for r in recs if not r.get('best') and r.get('br') == 'none' and r.get('f', 0) >= 1]
            print(f"#   climb {key}: best score {br['score']} after {br['steps']} steps, {ne} profiles, "
                  f"{ctot.get('st1', 0)} f >= 1 states, DL13 failures {ctot.get('fail1', 0)} [{secs:.1f} s]", flush=True)
            if fails: print(f'#   DL13 FAILS in climb {key}: {fails[0]}', flush=True)
            if 'out' in opt: DRUN.dump_write(opt['out'], recs)
            if ck:
                with open(ck, 'a') as fo: fo.write(json.dumps({'cmd': argv, 'key': key, 'tot': ctot}) + '\n')
    DRUN.report(f'hunt {mode} {" ".join(rest)}', tot, time.time() - t0)
    best_all.sort(key=lambda x: x[0])
    print(f'# profiles evaluated in this session (distinct within a climb): {nev}; the 5 smallest scores: {best_all[:5]}', flush=True)
    DRUN.print_tables(tot)
    if 'tables' in opt:
        json.dump({'command': 'python3 k4/dl13_hunt.py ' + ' '.join(argv), 'dl13_c_sha256': DRUN.SHA,
                   'counters': {k: tot.get(k, 0) for k in DRUN.KEYS + DRUN.LKEYS}, 'tab': tot.get('tab', {})},
                  open(opt['tables'], 'w'), indent=0, sort_keys=True)


if __name__ == '__main__':
    main(sys.argv[1:])
