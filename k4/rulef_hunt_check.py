"""Second implementation of the classes of k4/rulef_hunt.py: for every first agent a of a profile, rule RK's classes K0
and K1 recomputed with k4/rulef_model.py (Lemma K written from k4/rulef.md §2 on PR #33's independent model
k4/c4_verify_H/lb4r.py, a transcription of lean/EFX/LB4R.lean; no code of k4/rulef.c), with XKEEP = True (kept-out sets
of Remark 4, as rulef_hunt's default -Y1):
  K0: deficit_K(state after Phase 1(tau_a) and upgrades of pol) <= 0 for pol = shrink or envyFree (omega <= 0 included);
  K1: rot_deficit_K(that state) <= 0 (some single RotStep reaches a state of deficit <= 0) for one of those policies;
  and, for RK3 (rulef.c -N1), the same with pol = none.
Every deficit <= 0 found (at the state, or at the best state one RotStep reaches) gets its completion built (witness_K)
and checked by lb4r.output_check (Output of LB4R.lean, owner's needs from the bundle) and the raw EFX0 definition.
Compares with the classes the dump records (cls, from k4/rulef_hunt_eval.c) and prints one line per profile.
Usage: rulef_hunt_check.py DUMP.jsonl.gz [...] [--max=N] [--nwork=K] (profiles with nwork <= K, default 1) [--jobs=J]
Each distinct profile (sets, vals) is checked once."""
import gzip, json, os, sys, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import rulef_model as RM
import lb4r as M

RM.XKEEP = True


def classes(o):
    inst = RM.make_inst(o['sets'], o['vals'])
    out = []
    bad = 0
    for a in range(inst.n):
        r = {}
        for pol in ('shrink', 'envyFree', 'none'):
            s, _ = RM.run_state(inst, a, pol)
            d = RM.deficit_K(inst, s)
            r['d_' + pol] = d
            if d <= 0:
                o_, X = RM.witness_K(inst, s)
                if not ((o_ is None or M.output_check(inst, s, o_, X, 'bundle')) and RM.check_efx0(inst, X)):
                    bad += 1
                r['k1_' + pol] = None
            else:
                d1, arg = RM.rot_deficit_K(inst, s)
                r['k1_' + pol] = d1 <= 0
                if d1 <= 0:              # the completion at the rotated state, checked like the others
                    o_, X = RM.witness_K(inst, arg[0])
                    if not ((o_ is None or M.output_check(inst, arg[0], o_, X, 'bundle')) and RM.check_efx0(inst, X)):
                        bad += 1
        k0 = r['d_shrink'] <= 0 or r['d_envyFree'] <= 0
        k1 = (not k0) and bool(r['k1_shrink'] or r['k1_envyFree'])
        k03 = k0 or r['d_none'] <= 0
        k13 = (not k03) and bool(r['k1_shrink'] or r['k1_envyFree'] or r['k1_none'])
        out.append({'cls': 0 if k0 else (1 if k1 else 9), 'cls3': 0 if k03 else (1 if k13 else 9),
                    'd': [r['d_shrink'], r['d_envyFree'], r['d_none']]})
    return out, bad


def work(o):
    t0 = time.time()
    res, bad = classes(o)
    return o, res, bad, time.time() - t0


def fmt(x):
    return 'neg' if x == float('-inf') else ('inf' if x == float('inf') else str(int(x)))


def main():
    files = [a for a in sys.argv[1:] if not a.startswith('--')]
    mx = int(next((a.split('=')[1] for a in sys.argv[1:] if a.startswith('--max=')), 10 ** 9))
    nw = int(next((a.split('=')[1] for a in sys.argv[1:] if a.startswith('--nwork=')), 1))
    jobs = int(next((a.split('=')[1] for a in sys.argv[1:] if a.startswith('--jobs=')), os.cpu_count()))
    print('# command: python3 k4/rulef_hunt_check.py ' + ' '.join(sys.argv[1:]), flush=True)
    profs = []; seen = set()
    for f in files:
        op = gzip.open if f.endswith('.gz') else open
        for line in op(f, 'rt'):
            o = json.loads(line)
            k = json.dumps([o['sets'], o['vals']])
            if k in seen: continue                 # each distinct profile once
            seen.add(k)
            if o['nwork'] <= nw and len(profs) < mx: profs.append(o)
    agree = dis = bad = 0; nw0 = 0
    with Pool(jobs) as pool:
        for o, res, b, dt in pool.imap(work, profs):
            py = [r['cls'] for r in res]
            pyw = sum(c != 9 for c in py)
            same = [c if c != 9 else 9 for c in o['cls']] == py
            agree += same; dis += not same; bad += b
            if pyw == 0: nw0 += 1
            print(f"{o['unit']} nwork C={o['nwork']} python={pyw} classes C={o['cls']} python={py} RK3 python="
                  f"{[r['cls3'] for r in res]} deficits(shrink,envyFree,none)={[[fmt(x) for x in r['d']] for r in res]}"
                  f" {'agree' if same else 'DISAGREE'} witness failures {b} time {dt:.1f}s"
                  + ('' if same else f" sets={json.dumps(o['sets'])} vals={json.dumps(o['vals'])}"), flush=True)
    print(f'# profiles {len(profs)}: classes agree {agree}, disagree {dis}, witness failures {bad}, '
          f'no first agent in K0 or K1 by the second implementation: {nw0}', flush=True)


if __name__ == '__main__':
    main()
