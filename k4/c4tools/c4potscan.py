"""attempts/k4-c4one-potential.md: for every run with no valid owner after envy-free upgrades (the FAIL lines of
lb4.c -i1 -u2 -o0 -r0 -w1 -c1, one representative profile per leaf), rebuild the state in the tracer c4trace.py and
test whether some valid single rotation strictly raises Phi (the best A4+ slack over owners) or the owner-free count
(c4pot.py). Usage: python3 k4/c4tools/c4potscan.py FILE [FILE ...]"""
import sys, re, json, gzip, subprocess
import os
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..'))
from c4trace import *
import lb4_run
from c4pot import Phi, count as total
def state_from(line):
    sets = json.loads(re.search(r'sets=(\[\[.*?\]\])', line).group(1)); vals = json.loads(re.search(r'vals=(\[\[.*?\]\])', line).group(1))
    order = list(map(int, re.search(r'order=([\d ]+?)\s+picks', line).group(1).split()))
    picks = list(map(int, re.search(r'picks=([-\d,]+)', line).group(1).split(',')))
    blocks = list(map(int, re.search(r'blocks=([\d,]+)', line).group(1).split(',')))
    J = int(re.search(r' J=([0-9a-f]+)', line).group(1), 16)
    upg = re.findall(r'(\d+):([0-9a-f]+)', re.search(r'upg=(.*?) frozen=', line).group(1))
    I = Inst(sets, vals); n = I.n
    pos = [0] * n
    for p, a in enumerate(order): pos[a] = p
    Y = [p if p >= 0 else None for p in picks]
    base = [frozenset([y]) if y is not None else frozenset() for y in Y]; kind = ['pick'] * n
    for a, h in upg:
        a = int(a); b = int(h, 16); base[a] = frozenset(g for g in range(I.m) if b >> g & 1); kind[a] = 'upg'
    st = State(I, base, kind, frozenset(g for g in range(I.m) if J >> g & 1), pos, blocks, Y)
    return I, st
if __name__ == '__main__':
    files = sys.argv[1:]
    for fn in files:
        cs = json.load(gzip.open(fn, 'rt'))['cores']
        lb4_run.build(); nleaf = nbad = nbadT = 0; ex = None; by4 = {}
        for c in cs:
            p = subprocess.run([lb4_run.BIN, '-i1', '-u2', '-o0', '-r0', '-w1', '-c1', '-f1000000'], input=lb4_run.encode(c['sets'], c['m'], False), capture_output=True, text=True)
            for line in p.stderr.split('\n'):
                if not line.startswith('FAIL'): continue
                I, st = state_from(line)
                if try_owners(st, w1=True, rot_slot=True) is not None: continue   # the tracer finds an owner: skip
                nleaf += 1
                f0, t0 = Phi(st), total(st); bestF = bestT = -999
                fr = st.frozen()
                for k in range(I.n):
                    if not fr[k]: continue
                    for ch in chains_from(st, k):
                        for O in rot_options(st, ch):
                            ns = rotate(st, ch, O)
                            if ns.valid(): bestF = max(bestF, Phi(ns)); bestT = max(bestT, total(ns))
                k4 = sum(len(S) == 4 for S in I.sets); by4.setdefault(k4, [0, 0]); by4[k4][0] += 1
                if bestF <= f0:
                    nbad += 1; by4[k4][1] += 1
                    if ex is None or len(I.sets) < len(ex[0].sets) or (len(I.sets) == len(ex[0].sets) and I.m < ex[0].m): ex = (I, line, f0, bestF, t0, bestT)
                if bestT <= t0: nbadT += 1
        print(f'{fn}: {nleaf} leaves with no valid owner; no rotation raises Phi in {nbad}, the owner-free count in {nbadT}', flush=True)
        print('   by number of 4-good agents: (leaves, no Phi increase):', dict(sorted(by4.items())))
        if ex: print('   smallest:', ex[1][:300], f'Phi {ex[2]} -> best {ex[3]}, count {ex[4]} -> best {ex[5]}')
