"""What the first agents of classes K0 and K1 have in common (k4/rulef.md §5.2).

Reads IDX lines of k4/rulef.c -A41 -E1 -D5 (leaf representatives where the index-order run, a = 0, is not in class
K0; per first agent a: kN, kE (Lemma K deficits, need-shrinking / envy-free), c40, omega after need-shrinking, K1 flag)
and tests candidate first-agent rules that need no Lemma K computation for other agents:
  static rules (from the profile only), and one-step rules (from the index-order run of PR #33's independent model
  k4/c4_verify_H/lb4r.py: an agent read off its state, e.g. the end of a need chain from agent 0).
A rule *covers* a profile when its agent is in class K0 or K1 (LB4r succeeds with at most one rotation, by Lemma K).
Prints, per rule, the weight of profiles it does not cover and the smallest such profile.
Usage: rulef_features.py IDXFILE [--max=N] [--every=K]  (--every=K: every K-th line only)"""
import collections, json, re, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rulef_model as RM
import lb4r as M


def load(path, mx, every=1):
    out = []; seen = 0
    for line in open(path):
        if not line.startswith('IDX'): continue
        seen += 1
        if (seen - 1) % every: continue
        if len(out) >= mx: break
        w = int(re.search(r'w=(\d+)', line).group(1))
        sets = json.loads(re.search(r'sets=(\[\[.*?\]\])', line).group(1))
        vals = json.loads(re.search(r'vals=(\[\[.*?\]\])', line).group(1))
        fa = []
        for x in line.split('fa=')[1].strip().split(';'):
            kN, kE, c40, om, k1 = map(int, x.split(':')[1].split(','))
            fa.append(dict(kN=kN, kE=kE, c40=c40, om=om, k1=k1, K0=(kN <= 0 or kE <= 0), K1=(k1 == 1)))
        out.append(dict(w=w, sets=sets, vals=vals, fa=fa))
    return out


def ranking(inst, i):
    return sorted(inst.R[i], key=lambda g: -inst.v[i][g])


def static_feats(inst):
    n = inst.n
    F = []
    tops = [ranking(inst, i)[0] for i in range(n)]
    for a in range(n):
        Ra = ranking(inst, a)
        v = inst.v[a]
        top = Ra[0]
        f = {}
        f['4good'] = len(Ra) == 4
        f['bigtop'] = len(Ra) == 4 and v[Ra[0]] > v[Ra[1]] + v[Ra[2]]
        f['flat'] = len(Ra) == 4 and v[Ra[0]] < v[Ra[2]] + v[Ra[3]]
        f['contest'] = sum(1 for i in range(n) if i != a and inst.v[i][top] > 0)          # others valuing a's top
        f['topcontest'] = sum(1 for i in range(n) if i != a and tops[i] == top)          # others with the same top
        f['private'] = sum(1 for g in Ra if all(inst.v[i][g] == 0 for i in range(n) if i != a))
        f['toplow'] = sum(1 for i in range(n) if i != a and inst.v[i][top] > 0 and ranking(inst, i)[-1] == top)
        F.append(f)
    return F


def argbest(F, key, n):
    return min(range(n), key=lambda a: (key(F[a]), a))


STATIC = {
    'index': lambda F: 0,
    '4good first': lambda F: argbest(F, lambda f: 0 if f['4good'] else 1, len(F)),
    '3good first': lambda F: argbest(F, lambda f: 0 if not f['4good'] else 1, len(F)),
    'bigtop first': lambda F: argbest(F, lambda f: 0 if f['bigtop'] else 1, len(F)),
    'least contested top': lambda F: argbest(F, lambda f: f['contest'], len(F)),
    'most contested top': lambda F: argbest(F, lambda f: -f['contest'], len(F)),
    'top shared by fewest tops': lambda F: argbest(F, lambda f: f['topcontest'], len(F)),
    'top shared by most tops': lambda F: argbest(F, lambda f: -f['topcontest'], len(F)),
    'most private goods': lambda F: argbest(F, lambda f: -f['private'], len(F)),
    'top is lowest for fewest': lambda F: argbest(F, lambda f: f['toplow'], len(F)),
}


def index_run(inst, pol):
    s, run = RM.run_state(inst, 0, pol)
    needs = M.all_needs(inst, s)
    NA = M.NA_of(needs)
    fr = M.frozen_at(inst, s, NA)
    chains = M.chains(inst, s, needs, NA)
    r = None
    for x, f, kind in run:
        if not s[2][x]: r = x
    return s, run, fr, chains, r


def onestep(inst):
    """agents read off the index-order run (need-shrinking policy), or None"""
    s, run, fr, chains, r = index_run(inst, 'shrink')
    out = {}
    from0 = [c for c in chains if c[0] == 0]
    out['end of a chain from agent 0'] = from0[0][-1] if from0 else None
    out['successor of agent 0 on a chain'] = from0[0][1] if from0 else None
    out['last agent r of the index run'] = r
    first_frozen4 = [c for c in chains if len(inst.R[c[0]]) == 4]
    out['end of a chain from a frozen 4-good agent'] = first_frozen4[0][-1] if first_frozen4 else None
    out['start of a chain ending at r'] = next((c[0] for c in chains if c[-1] == r), None)
    out['end of a chain from the frozen agent processed last'] = (max(chains, key=lambda c: [x for x, _, _ in run].index(c[0]))[-1]
                                                                   if chains else None)
    return out


def main():
    path = sys.argv[1]
    mx = int(next((a.split('=')[1] for a in sys.argv[2:] if a.startswith('--max=')), 10 ** 9))
    every = int(next((a.split('=')[1] for a in sys.argv[2:] if a.startswith('--every=')), 1))
    D = load(path, mx, every)
    miss = collections.Counter(); small = {}; tot = 0
    for d in D:
        tot += d['w']
        inst = RM.make_inst(d['sets'], d['vals'])
        F = static_feats(inst)
        ok = [f['K0'] or f['K1'] for f in d['fa']]
        picks = {k: fn(F) for k, fn in STATIC.items()}
        picks.update(onestep(inst))
        picks['index, else end of a chain from agent 0'] = 0 if ok[0] else picks['end of a chain from agent 0']
        for k, a in picks.items():
            if a is None or not ok[a]:
                miss[k] += d['w']
                key = (len(d['sets']), 1 + max(g for S in d['sets'] for g in S))
                if k not in small or key < small[k][0]: small[k] = (key, d['sets'], d['vals'], a)
    print(f'{path}: leaves {len(D)}, profiles {tot} (index order not in class K0)')
    for k in sorted(set(list(STATIC) + list(small)), key=lambda k: miss[k]):
        s = small.get(k)
        print(f'  {k:52s} not covered: {miss[k]:>10d}' + (f'   smallest n={s[0][0]} m={s[0][1]} sets={s[1]} vals={s[2]} agent={s[3]}' if s else ''))


if __name__ == '__main__':
    main()
