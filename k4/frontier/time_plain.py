"""Cost of a full check with the plain checker k4/check4.py: time check4.covered (coverage only, the part whose cost
grows with the profile count) on a random sample of cores of a certificate, and extrapolate to the file (mean time per
core times the number of cores; heavy tails make this a rough estimate). Usage: time_plain.py FILE SAMPLE [SEED]"""
import gzip, json, os, random, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import check4 as PLAIN

if __name__ == '__main__':
    fn, k = sys.argv[1], int(sys.argv[2])
    rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
    data = json.load(gzip.open(fn, 'rt'))
    print(f"command: python3 k4/frontier/time_plain.py {' '.join(sys.argv[1:])}", flush=True)
    ts = []
    for r in rng.sample(data['cores'], k):
        t = time.time(); ok = PLAIN.covered((data['n'], r['m'], r['sets'], r['allocs'], data.get('ties', False)))
        ts.append(time.time() - t)
        print(f"  m={r['m']} allocations={len(r['allocs'])} covered={ok} {ts[-1]:.2f}s", flush=True)
    ts.sort()
    print(f"{os.path.basename(fn)}: {k} of {len(data['cores'])} cores, check4.covered per core: mean {sum(ts) / k:.2f}s, "
          f"median {ts[k // 2]:.2f}s, max {ts[-1]:.2f}s; extrapolated {sum(ts) / k * len(data['cores']) / 3600:.1f} CPU-hours",
          flush=True)
