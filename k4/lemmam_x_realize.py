"""How the run of the exchange agent relates to the bad run (k4/lemmam_x.md §5), on PR #33's model
(k4/c4_verify_H/lb4r.py), for BAD lines of k4/lemmam_x.c -A43 -D43 (or k4/lemmam_x_check.py).

For a bad first agent a and a candidate a' = x (the candidate of rule --cand, default endEF_maxload), compares the
Phase 1 picks of tau_x with the picks predicted from the run of tau_a by
  Psi:   x takes its top a_x; the fall chain y_0 (holder of a_x), y_1, ... takes g_i = y_i's best good outside
         {Y_y0, ..., Y_yi}, continuing while g_i is another agent's pick, stopping at junk or Y_x (Lemma Psi of
         k4/c4one.md §6, K4.C4.PSI); every other agent keeps its pick;
  cycle: the changed agents form one cycle and each takes the tau_a-pick of the next (a rotation of picks);
and reports, per class of tau_a's run (single block or not), how often tau_x's picks are exactly Psi's, a cycle, or
neither, and how often x lies in a's block.
Usage: lemmam_x_realize.py FILE [--cand=NAME] [--max=N]"""
import json, os, re, sys, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lemmam_x_check as C
RM, M = C.RM, C.M


def picks(inst, a):
    s0, run = M.phase1_state(inst, (a,))
    return list(s0[1]), run


def top(inst, i):
    return max(inst.R[i], key=lambda g: inst.v[i][g])


def psi_prediction(inst, Y, x):
    holder = {Y[i]: i for i in range(inst.n) if Y[i] >= 0}
    ax = top(inst, x)
    if Y[x] == ax or ax not in holder:
        return None
    pred = list(Y)
    pred[x] = ax
    taken = []
    y = holder[ax]
    seen = set()
    while True:
        if y in seen or y == x:
            return None
        seen.add(y)
        taken.append(Y[y])
        cand = [g for g in inst.R[y] if g not in taken]
        if not cand:
            pred[y] = -1
            return pred
        g = max(cand, key=lambda h: inst.v[y][h])
        pred[y] = g
        if g == Y[x] or g not in holder:
            return pred
        y = holder[g]


def classify(inst, a, x):
    Y, run = picks(inst, a)
    Y2, run2 = picks(inst, x)
    nblocks = sum(1 for _, _, t in run if t == 'I')
    blk, b = {}, -1
    for i, f, t in run:
        if t == 'I':
            b += 1
        blk[i] = b
    kinds = []
    p = psi_prediction(inst, Y, x)
    if p is not None and p == Y2:
        kinds.append('Psi')
    holder = {Y[i]: i for i in range(inst.n) if Y[i] >= 0}
    changed = [i for i in range(inst.n) if Y2[i] != Y[i]]
    if changed and all(Y2[i] in holder and holder[Y2[i]] in changed for i in changed):
        perm = {i: holder[Y2[i]] for i in changed}
        cyc, i = [changed[0]], perm[changed[0]]
        while i != changed[0] and i not in cyc:
            cyc.append(i); i = perm[i]
        if len(cyc) == len(changed):
            kinds.append('cycle')
    return nblocks, blk[x] == blk[a], '+'.join(kinds) or 'neither'


def main():
    args = sys.argv[1:]
    f = args[0]
    cand = next((x.split('=')[1] for x in args if x.startswith('--cand=')), 'endEF_maxload')
    mx = int(next((x.split('=')[1] for x in args if x.startswith('--max=')), 10 ** 9))
    cnt = collections.Counter(); ex = {}
    k = 0
    for line in open(f):
        if not line.startswith('BAD'):
            continue
        k += 1
        if k > mx:
            break
        w = int(re.search(r'w=(\d+)', line).group(1)) if 'w=' in line else 1
        ms = re.search(r'sets=(\[\[.*?\]\])', line); mv = re.search(r'vals=(\[\[.*?\]\])', line)
        if ms:
            sets, vals = json.loads(ms.group(1)), json.loads(mv.group(1))
        else:
            o = json.loads(line[line.index('{'):]); sets, vals = o['sets'], o['vals']
        a = int(re.search(r' a=(\d+)', line).group(1))
        inst = RM.make_inst(sets, vals)
        c, v = C.candidates(inst, a)
        x = c[cand]
        if x is None:
            cnt[('undefined',)] += w
            continue
        nb, same, kind = classify(inst, a, x)
        key = ('one block' if nb == 1 else 'several blocks', "a' in a's block" if same else "a' in another block", kind)
        cnt[key] += w
        ex.setdefault(key, (sets, vals, a, x))
    print(f"# lemmam_x_realize.py {' '.join(args)}")
    for key, w in cnt.most_common():
        print(w, ' / '.join(key), ' e.g.', json.dumps(ex.get(key)))


if __name__ == '__main__':
    main()
