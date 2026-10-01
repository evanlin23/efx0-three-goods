#!/usr/bin/env python3
"""Adversarial hunt for Conjecture DL_RC (compute/k4-rc). EVIDENCE only: a hunt that finds nothing proves nothing.

Hill-climbs (with plateau moves, occasional downhill moves and restarts from the best point) strict profiles of a fixed
core (types from k4/check4.py core_domains: one integer representative per strict balanced type, the private-pair
condition), evaluating every profile with k4/dlrc.c (-v -H; dlrc.c's header defines the fields), to maximize a
nearness-to-failure score, compared lexicographically:
  std:  (rcf, kf, chain, chain3, -gap, c3, kstar, -minmv, st1)
  w2:   (rcf, kf, chainw2, chain, chain3, -gap, c3, kstar, -minmv, st1)
  k3:   (rcf, kf, chain, chain3, c3, kstar, -gap, -minmv, st1)  (an addition: the distance terms first, as a gradient
        towards states whose nearest repair changes >= 3 agents, where every chain state found lies)
where, over the profile's def > 0 states with f >= 1: rcf = the states where DL_RC fails (a counterexample), kf = those
where the key form fails, chain = those whose only improving R_C moves are T3+ moves with |W| >= 1 (DL_RT4 fails, DL_RC
holds), chain3 = those with f >= 3, chainw2 = those whose least improving |W| is >= 2, gap = the least deficit gap
(the least def(P) - (the least deficit of an improving R_C move from P), 0 where DL_RC fails), c3 = the states whose
least R_C repair changes >= 3 agents, kstar = the largest nearest distance to a better state (dl2.c's k*), minmv = the
least number of improving R_C moves of a state, st1 = the number of states. The brief's three terms are chain, chain3
and -gap, in this order; rcf and kf come first (a failure beats everything), c3, kstar, -minmv and st1 break ties (a
gradient on the plateaus where the first terms are 0).

A move changes the type of one agent (two with probability 0.2); a 4-good agent's new type is big-top (top > second +
third) with probability --bt (default 0.5; every n = 5 DL_RT4 failure is on big-top profiles). Each step evaluates
--batch neighbours of the current profile in one dlrc.c call and moves to the best one if it is at least as good (or,
with probability 0.05, anyway); after --stale steps without a new best the climb restarts from the best profile.

usage: python3 k4/dlrc_hunt.py NAME MODE [ARGS] [--steps=S] [--batch=B] [--units=U] [--init=R] [--obj=std|w2]
                               [--bt=P] [--jobs=J] [--seed=X] [--stale=T]
modes (each unit is one climb; units already in the checkpoint are skipped, so re-running the command resumes):
  fail10 FILE.json [--reps=R]      start at each profile of the list (results/k4_rc/rt4_fail10_inst.json), R climbs each
  certs FILE.json.gz [--min4=K] [--cores=A:B] [--sample=N]
                                   the cores of a certificate file with >= K four-good agents (N of them at random, or
                                   all); start at the best of --init random profiles (half of them big-top)
  ranked FILE.json.gz CKPT.jsonl ... [--top=N]
                                   the N cores of FILE ranked highest by the dlrt4_run.py / dlrc_run.py checkpoints
                                   (chain states and DL_RT4 failures, then states with a least RT4 move of size >= 3 or
                                   none, then states whose nearest better state is at distance >= 2, then states)
  glue FILE.json [--pairs=N]       cores glued from two profiles of the list sharing one good (checked with check4.is_core),
                                   starting at the union of the two profiles; N random gluings
  extend FILE.json [--exts=N]      (an addition to the brief's seeds) n + 1 cores: a profile of the list plus one agent on 3
                                   or 4 goods (existing goods, and new private goods within the core's private-good limit),
                                   checked with check4.is_core; start at the list's profile with the new agent's type the
                                   best of --init random ones; N random extensions
Files: results/k4_rc/hunt_NAME.log (the caller redirects), results/k4_rc/ckpt_hunt_NAME.jsonl (one line per finished
unit: its best score and profile, its counts), results/k4_rc/dump_hunt_NAME.jsonl.gz (every distinct profile met with
a chain, key-form or DL_RC failing state, at most 300 per unit, with dlrc.c's H line; for a DL_RC or key-form failure
also dlrc.c's "D" records of the profile). A DL_RC failure is also printed at once ("DL_RC FAILS")."""
import gzip, hashlib, json, os, random, subprocess, sys, tempfile, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check4

SRC = os.path.join(HERE, 'dlrc.c')
SHA = hashlib.sha256(open(SRC, 'rb').read()).hexdigest()
BIN = os.path.join(tempfile.gettempdir(), 'k4_dlrc_hunt_' + SHA[:16])
OUT = os.path.join(os.path.dirname(HERE), 'results', 'k4_rc')
HF = 'f st1 rt4f rcf ch ch3 chw2 gap c3 mv kf kfk maxw'.split()


def build():
    if not os.path.exists(BIN):
        subprocess.run(['gcc', '-O2', '-o', BIN + '.tmp%d' % os.getpid(), SRC], check=True)
        os.replace(BIN + '.tmp%d' % os.getpid(), BIN)


def block(sets, m, doms, tag, profs):
    out = [f"{len(sets)} {m} {tag}"] + [f"{len(S)} {' '.join(map(str, S))}" for S in sets]
    out.append(' '.join(str(len(D)) for D in doms))
    for S, D in zip(sets, doms): out += [' '.join(str(d[g]) for g in S) for d in D]
    out.append(str(-len(profs))); out += [' '.join(map(str, p)) for p in profs]
    return '\n'.join(out) + '\n'


def evaluate(core, profs, extra=()):
    """dlrc.c -v -H on the profiles: per profile a dict of the H fields plus kstar (99 = inf), and the raw output"""
    sets, m, doms = core['sets'], core['m'], core['doms']
    r = subprocess.run([BIN, '-v', '-H'] + list(extra), input=block(sets, m, doms, 0, profs), capture_output=True, text=True)
    if r.returncode: raise RuntimeError(r.stderr)
    n = len(sets); res = []; kst = None
    for l in r.stdout.splitlines():
        if l.startswith('V '):
            w = l.split(); kst = int(w[2 + n]); kst = 99 if kst == -1 else kst
            if kst == -2: kst = 0
        elif l.startswith('H '):
            w = list(map(int, l.split()[2 + n:]))
            h = dict(zip(HF, w)); h['kstar'] = kst if kst is not None else 0; kst = None
            res.append(h)
    assert len(res) == len(profs), (len(res), len(profs))
    return res, r.stdout


def score(h, obj):
    gap = h['gap'] if h['st1'] else 10 ** 6
    mv = h['mv'] if h['st1'] else 10 ** 6
    s = (h['rcf'], h['kf'], h['ch'], h['ch3'], -gap, h['c3'], h['kstar'] if h['st1'] else 0, -mv, h['st1'])
    if obj == 'w2': s = s[:2] + (h['chw2'],) + s[2:]
    elif obj == 'k3': s = s[:4] + (s[5], s[6], s[4]) + s[7:]      # distance terms (c3, kstar) before -gap
    return s


def bigtop_idx(D, S):
    if len(S) != 4: return None
    return [t for t, d in enumerate(D) if (lambda w: w[3] > w[2] + w[1])(sorted(d[g] for g in S))]


def mk_core(sets, m, label):
    doms = check4.core_domains(sets, m, False)
    return {'sets': sets, 'm': m, 'doms': doms, 'bt': [bigtop_idx(D, S) for D, S in zip(doms, sets)], 'label': label}


def prof_of_vals(core, vals):
    return [next(t for t, d in enumerate(D) if [d[g] for g in S] == list(V)) for D, S, V in zip(core['doms'], core['sets'], vals)]


def rand_type(core, i, rng, pbt):
    bt = core['bt'][i]
    if bt and rng.random() < pbt: return rng.choice(bt)
    return rng.randrange(len(core['doms'][i]))


def mutate(core, p, rng, pbt):
    q = list(p); n = len(q)
    k = 2 if rng.random() < 0.2 and n >= 2 else 1
    for i in rng.sample(range(n), k):
        for _ in range(10):
            t = rand_type(core, i, rng, pbt)
            if t != q[i]: q[i] = t; break
    return q


def climb(task):
    """one unit: a climb on one core; returns its summary and the notable profiles"""
    key, core, start, opt = task
    build()
    rng = random.Random(json.dumps(key, sort_keys=True) + str(opt['seed']))
    steps, B, obj, pbt, stale_max = opt['steps'], opt['batch'], opt['obj'], opt['bt'], opt['stale']
    t0 = time.time(); nev = 0
    notable, seen = [], set()
    nfail = nkf = 0; maxw = 0; nchain_prof = 0; nchain_states = 0

    nstates = 0

    def note(profs, hs, out_raw=None):
        nonlocal nfail, nkf, maxw, nchain_prof, nchain_states, nstates
        for p, h in zip(profs, hs):
            nstates += h['st1']
            if not (h['ch'] or h['kf'] or h['rcf']): continue
            tp = tuple(p)
            if tp in seen: continue
            seen.add(tp)
            nchain_prof += h['ch'] > 0; nchain_states += h['ch']; maxw = max(maxw, h['maxw'])
            rec = {'unit': key, 'core': {k: core[k] for k in ('label', 'm', 'sets')}, 'prof': p,
                   'vals': [[core['doms'][i][p[i]][g] for g in core['sets'][i]] for i in range(len(p))], 'H': h}
            if h['rcf'] or h['kf']:
                nfail += h['rcf'] > 0; nkf += h['kf'] > 0
                _, raw = evaluate(core, [p], ('-r0', '-o0'))
                rec['D'] = [json.loads(l[2:]) for l in raw.splitlines() if l.startswith('D ')]
                print('# DL_RC FAILS' if h['rcf'] else '# KEY FORM FAILS', json.dumps({k: rec[k] for k in ('unit', 'core', 'prof', 'vals', 'H')}),
                      flush=True)
                notable.append(rec)
            elif len(notable) < 300: notable.append(rec)

    if start is not None and start[-1] is None:                    # extend: choose the last agent's type
        cands = [list(start[:-1]) + [rand_type(core, len(start) - 1, rng, 0.5)] for _ in range(opt['init'])]
        hs, _ = evaluate(core, cands); nev += len(cands); note(cands, hs)
        j = max(range(len(cands)), key=lambda j: (score(hs[j], obj), rng.random()))
        cur, ch = cands[j], hs[j]
    elif start is None:
        cands = [[rand_type(core, i, rng, 0.5) for i in range(len(core['sets']))] for _ in range(opt['init'])]
        hs, _ = evaluate(core, cands); nev += len(cands); note(cands, hs)
        j = max(range(len(cands)), key=lambda j: (score(hs[j], obj), rng.random()))
        cur, ch = cands[j], hs[j]
    else:
        cur = list(start); hs, _ = evaluate(core, [cur]); nev += 1; ch = hs[0]; note([cur], hs)
    cs = score(ch, obj); best, bs, bh = list(cur), cs, ch; stale = 0; first = cs
    for _ in range(steps):
        nb = [mutate(core, cur, rng, pbt) for _ in range(B)]
        hs, _ = evaluate(core, nb); nev += B; note(nb, hs)
        j = max(range(B), key=lambda j: (score(hs[j], obj), rng.random()))
        sj = score(hs[j], obj)
        if sj >= cs or rng.random() < 0.05: cur, cs, ch = nb[j], sj, hs[j]
        if sj > bs: best, bs, bh = list(nb[j]), sj, hs[j]; stale = 0
        else:
            stale += 1
            if stale >= stale_max: cur, cs, ch = list(best), bs, bh; stale = 0
    summ = {'key': key, 'label': core['label'], 'n': len(core['sets']), 'm': core['m'], 'start_score': list(first),
            'best_score': list(bs), 'best_prof': best, 'best_H': bh, 'evals': nev, 'states': nstates, 'secs': round(time.time() - t0, 1),
            'chain_profiles': nchain_prof, 'chain_states': nchain_states, 'maxw': maxw, 'rcfail_profiles': nfail,
            'keyfail_profiles': nkf}
    return summ, notable


def load_cores(fn):
    return json.load(gzip.open(fn, 'rt'))['cores']


def units_of(mode, args, opt, rng):
    """[(key, core, start)]"""
    out = []
    if mode == 'fail10':
        insts = json.load(open(args[0]))
        for r in range(int(opt.get('reps', 4))):
            for k, d in enumerate(insts):
                core = mk_core(d['sets'], d['m'], d['id'])
                out.append(({'inst': k, 'rep': r}, core, prof_of_vals(core, d['vals'])))
    elif mode == 'certs':
        cores = load_cores(args[0]); base = os.path.basename(args[0])
        lo, hi = 0, len(cores)
        if 'cores' in opt: a, b = opt['cores'].split(':'); lo, hi = int(a or 0), int(b or len(cores))
        sel = [k for k in range(lo, hi) if sum(len(S) == 4 for S in cores[k]['sets']) >= int(opt.get('min4', 0))]
        if 'sample' in opt: sel = sorted(rng.sample(sel, min(int(opt['sample']), len(sel))))
        for k in sel:
            c = cores[k]
            out.append(({'file': base, 'pos': k}, mk_core(c['sets'], c['m'], '%s#%d[m=%d,idx=%s]' % (base, k, c['m'], c.get('idx'))), None))
    elif mode == 'ranked':
        cores = load_cores(args[0]); base = os.path.basename(args[0])
        sc = {}
        for ck in args[1:]:
            for l in open(ck):
                try: d = json.loads(l)
                except ValueError: continue
                if d['ckey'].get('file') != base: continue
                for b in d['blocks']:
                    L = b['L']; C = b.get('LC', {}); K = b['K']
                    s = sc.setdefault(d['key']['pos'], [0, 0, 0, 0])
                    s[0] += C.get('chain', 0) + L['fail1']; s[1] += L['rd3'] + L['rd4'] + L['rdnone']
                    s[2] += K['pd2'] + K['pd3'] + K['pd4'] + K['pdinf']; s[3] += L['st1']
        rank = sorted(sc, key=lambda k: (-sc[k][0], -sc[k][1], -sc[k][2], -sc[k][3], k))[:int(opt.get('top', 100))]
        for k in rank:
            c = cores[k]
            out.append(({'file': base, 'pos': k, 'rank': sc[k]}, mk_core(c['sets'], c['m'], '%s#%d[m=%d,idx=%s]' % (base, k, c['m'], c.get('idx'))), None))
    elif mode == 'glue':
        insts = json.load(open(args[0]))
        tries = 0
        while len(out) < int(opt.get('pairs', 20)) and tries < 10000:
            tries += 1
            a, b = rng.randrange(len(insts)), rng.randrange(len(insts))
            A, Bd = insts[a], insts[b]
            gA, gB = rng.randrange(A['m']), rng.randrange(Bd['m'])
            relab, nxt = {}, A['m']
            for g in range(Bd['m']):
                if g == gB: relab[g] = gA
                else: relab[g] = nxt; nxt += 1
            sets = A['sets'] + [[relab[g] for g in S] for S in Bd['sets']]
            ok, _ = check4.is_core(len(sets), nxt, sets, False)
            key = {'a': a, 'b': b, 'gA': gA, 'gB': gB}
            if not ok or nxt > 32 or any(u[0] == key for u in out): continue
            core = mk_core(sets, nxt, 'glue(%d:%d,%d:%d)' % (a, gA, b, gB))
            out.append((key, core, prof_of_vals(core, A['vals'] + Bd['vals'])))
    elif mode == 'extend':
        insts = json.load(open(args[0]))
        tries = 0
        while len(out) < int(opt.get('exts', 20)) and tries < 100000:
            tries += 1
            a = rng.randrange(len(insts)); A = insts[a]
            d = rng.choice((3, 4)); npriv = rng.randrange(0, d - 1)          # at most d - 2 new private goods
            old = sorted(rng.sample(range(A['m']), d - npriv))
            S = old + list(range(A['m'], A['m'] + npriv)); m = A['m'] + npriv
            sets = A['sets'] + [S]
            key = {'a': a, 'S': S}
            ok, _ = check4.is_core(len(sets), m, sets, False)
            if not ok or any(u[0] == key for u in out): continue
            core = mk_core(sets, m, 'ext(%d:%s)' % (a, S))
            p0 = prof_of_vals(core, A['vals'] + [[core['doms'][-1][0][g] for g in S]])
            out.append((key, core, p0[:-1] + [None]))
    else:
        raise SystemExit(__doc__)
    if 'units' in opt: out = out[:int(opt['units'])]
    return out


def main(argv):
    name, mode = argv[0], argv[1]
    args = [a for a in argv[2:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in argv[2:] if a.startswith('--'))
    print('# command: python3 k4/dlrc_hunt.py ' + ' '.join(argv), flush=True)
    print('# dlrc.c sha256 ' + SHA + '; dlrc_hunt.py sha256 ' + hashlib.sha256(open(os.path.abspath(__file__), 'rb').read()).hexdigest(),
          flush=True)
    build()
    o = {'steps': int(opt.get('steps', 200)), 'batch': int(opt.get('batch', 24)), 'obj': opt.get('obj', 'std'),
         'bt': float(opt.get('bt', 0.5)), 'seed': int(opt.get('seed', 1)), 'init': int(opt.get('init', 200)),
         'stale': int(opt.get('stale', 40))}
    rng = random.Random(o['seed'])
    units = units_of(mode, args, opt, rng)
    ck = os.path.join(OUT, 'ckpt_hunt_%s.jsonl' % name); dump = os.path.join(OUT, 'dump_hunt_%s.jsonl.gz' % name)
    done = {}
    if os.path.exists(ck):
        for l in open(ck):
            try: d = json.loads(l)
            except ValueError: continue
            done[json.dumps(d['key'], sort_keys=True)] = d
    tasks = [(k, c, s, o) for k, c, s in units if json.dumps(k, sort_keys=True) not in done]
    print('# %s %s: %d units, %d to run, %d from the checkpoint; options %s' % (mode, ' '.join(args), len(units), len(tasks),
                                                                               len(done), o), flush=True)
    t0 = time.time()
    with Pool(int(opt.get('jobs', os.cpu_count()))) as pool:
        for summ, notable in pool.imap_unordered(climb, tasks):
            if notable:
                with gzip.open(dump, 'at') as fo:
                    for r in notable: fo.write(json.dumps(r, separators=(',', ':')) + '\n')
            with open(ck, 'a') as fo: fo.write(json.dumps(summ) + '\n')
            done[json.dumps(summ['key'], sort_keys=True)] = summ
            print('#   unit %s %s: start %s best %s chain profiles %d (states %d), maxw %d, DL_RC fails %d, key form fails '
                  '%d; %d evals [%.0f s]' % (json.dumps(summ['key']), summ['label'], summ['start_score'], summ['best_score'],
                                             summ['chain_profiles'], summ['chain_states'], summ['maxw'],
                                             summ['rcfail_profiles'], summ['keyfail_profiles'], summ['evals'], summ['secs']),
                  flush=True)
    S = list(done.values())
    print('TOTAL %s: units %d, profiles evaluated %d (with repeats; def > 0 states with f >= 1 in them: %s), unit time %.0f s (this session %.0f s wall); units reaching a chain '
          'state %d, distinct chain profiles %d (chain states %d), largest least |W| at a chain state %d; units with a '
          'DL_RC failure %d, with a key-form failure %d'
          % (name, len(S), sum(s['evals'] for s in S), sum(s.get('states', 0) for s in S) if all('states' in s for s in S)
             else 'not counted for every unit', sum(s['secs'] for s in S), time.time() - t0,
             sum(1 for s in S if s['chain_profiles']), sum(s['chain_profiles'] for s in S), sum(s['chain_states'] for s in S),
             max([s['maxw'] for s in S] or [0]), sum(1 for s in S if s['rcfail_profiles']),
             sum(1 for s in S if s['keyfail_profiles'])), flush=True)
    print('best units (score order %s):' % {'w2': 'rcf kf chainw2 chain chain3 -gap c3 kstar -minmv st1',
                                            'k3': 'rcf kf chain chain3 c3 kstar -gap -minmv st1'}.get(
                                                o['obj'], 'rcf kf chain chain3 -gap c3 kstar -minmv st1'))
    for s in sorted(S, key=lambda s: s['best_score'], reverse=True)[:15]:
        print('  %s %s n=%d m=%d best %s prof %s H %s' % (json.dumps(s['key']), s['label'], s['n'], s['m'], s['best_score'],
                                                          s['best_prof'], s['best_H']), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
