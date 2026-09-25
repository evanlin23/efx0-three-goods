"""LS4+ (k4/ls4alg.c -DCMOVE=8, its default choice rule; PR #29's program, used unchanged) on the K-agent
neighbourhoods of the profiles in GMFAIL lines: every profile that changes the strict types of K agents of such a
profile (exhaustive over those agents' types, the others fixed).  EVIDENCE only (k4/gm4.md §3).
Usage: gm4_ls4plus_around.py LOG[,LOG...] K"""
import sys, json, itertools, subprocess, os
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check4 import core_domains
exe = os.path.expanduser("~/.cache/gm4/ls4alg_cm8")
if not os.path.exists(exe) or os.path.getmtime(exe) < os.path.getmtime(os.path.join(os.path.dirname(os.path.abspath(__file__)), "ls4alg.c")):
    os.makedirs(os.path.dirname(exe), exist_ok=True)
    subprocess.run(["gcc", "-O2", "-DCMOVE=8", "-o", exe, os.path.join(os.path.dirname(os.path.abspath(__file__)), "ls4alg.c")], check=True)
def task(args):
    sets, m, fixed = args
    doms = core_domains(sets, m, False)
    lines = [f"{len(sets)} {m}"] + [" ".join(map(str, [len(S)] + S)) for S in sets]
    for S, D, f in zip(sets, doms, fixed):
        L = [f] if f is not None else [[d[g] for g in S] for d in D]
        lines.append(str(len(L)))
        lines += ["0 " + " ".join(map(str, v)) for v in L]
    lines.append("0 0 1")
    out = subprocess.run([exe], input="\n".join(lines) + "\n", capture_output=True, text=True)
    return out.returncode, out.stdout
tasks, seen = [], set()
for logf in sys.argv[1].split(','):
    for line in open(logf):
        if not line.startswith('GMFAIL '): continue
        body, meta = line.split(' # ')
        vals = [list(map(int, t.split(','))) for t in body.split(' | ')[0].split()[1:]]
        m = int(meta.split()[0][2:]); sets = json.loads(meta.split('sets=')[1])
        k = (json.dumps(sets), json.dumps(vals))
        if k in seen: continue
        seen.add(k)
        for A in itertools.combinations(range(len(sets)), int(sys.argv[2])):
            tasks.append((sets, m, [None if i in A else vals[i] for i in range(len(sets))]))
print(f"# LS4+ (ls4alg.c -DCMOVE=8, default rule) on the {sys.argv[2]}-agent neighbourhoods of {len(seen)} profiles ({len(tasks)} tasks)", flush=True)
tot = {}
with Pool(4) as p:
    for rc, out in p.imap_unordered(task, tasks):
        for l in out.splitlines():
            if l.startswith('RESULT') or l.startswith('CMOVES'):
                for kv in l.split()[1:]:
                    k, v = kv.split('='); tot[k] = max(tot.get(k, 0), int(v)) if k.startswith('max') else tot.get(k, 0) + int(v)
            elif l.strip(): print(l, flush=True)
print('TOTAL', ' '.join(f"{k}={v}" for k, v in tot.items()))
