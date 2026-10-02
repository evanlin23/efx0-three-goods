"""Rule F with Lean's exact owner step on the tight profiles: for every first agent a and every policy (shrink,
envyFree, none), does LB4R(tau_a) succeed with at most one rotation in the sense of lean/EFX/LB4R.lean
(`SucceedsR 1`: some policy, at most one RotStep, then some owner (or none) with an Output)? Computed on PR #33's
independent model k4/c4_verify_H/lb4r.py: `any_output` (SAT, every owner and none, owner's needs from the bundle) at the
state after Phase 1(tau_a) and the upgrades, and at every state one RotStep reaches. No code of k4/rulef.c.
This is the exact counterpart of rulef.c's LB4r count (which gives rotated agents no slot place, see
results/k4_rulef_hunt/SUMMARY.md).
Usage: rulef_hunt_rulef1.py DUMP.jsonl.gz [--every=K] [--jobs=J]   (each distinct profile once, every K-th of them)"""
import gzip, json, os, sys, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import rulef_model as RM
import lb4r as M


def least_rot(inst, a):
    """0 or 1 (least rotations with an Output over the three policies), 2 meaning: more than one"""
    best = 2
    for pol in ('shrink', 'envyFree', 'none'):
        s, _ = RM.run_state(inst, a, pol)
        if M.any_output(inst, s, 'bundle'):
            return 0
        if best > 1:
            for s2 in M.rot_steps(inst, s):
                if M.any_output(inst, s2, 'bundle'):
                    best = 1; break
    return best


def work(o):
    t0 = time.time()
    inst = RM.make_inst(o['sets'], o['vals'])
    return o, [least_rot(inst, a) for a in range(inst.n)], time.time() - t0


def main():
    f = sys.argv[1]
    every = int(next((a.split('=')[1] for a in sys.argv[2:] if a.startswith('--every=')), 1))
    jobs = int(next((a.split('=')[1] for a in sys.argv[2:] if a.startswith('--jobs=')), os.cpu_count()))
    print('# command: python3 k4/rulef_hunt_rulef1.py ' + ' '.join(sys.argv[1:]), flush=True)
    seen, profs = set(), []
    for line in gzip.open(f, 'rt'):
        o = json.loads(line)
        k = json.dumps([o['sets'], o['vals']])
        if k in seen: continue
        seen.add(k)
        if (len(seen) - 1) % every == 0: profs.append(o)
    hist = {}; agree = 0; worse = 0
    with Pool(jobs) as pool:
        for o, rots, dt in pool.imap(work, profs):
            nok = sum(r <= 1 for r in rots)
            hist[nok] = hist.get(nok, 0) + 1
            c = [d['rot'] for d in o['detail']]            # rulef.c's LB4r fewest rotations (cap 0 for rotated agents)
            agree += [min(x, 2) for x in c] == rots
            worse += any(r > min(x, 2) for r, x in zip(rots, c))
            print(f"{o['unit']} m={o['m']} Lean rule F rotations per first agent {rots} (rulef.c {c}) "
                  f"first agents with <= 1: {nok} time {dt:.1f}s", flush=True)
    print(f'# profiles {len(profs)} (every {every}-th distinct): first agents succeeding with <= 1 rotation in Lean\'s '
          f'sense, histogram {dict(sorted(hist.items()))}; equal to rulef.c\'s counts on {agree}; exact count above '
          f'rulef.c\'s on {worse} (must be 0)', flush=True)


if __name__ == '__main__':
    main()
