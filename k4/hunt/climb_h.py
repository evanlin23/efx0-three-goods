"""Adversarial climb over hypergraphs, each step evaluated exactly (every strict profile, cegar.py).

State: a connected k = 4 core (check.is_core). Moves: swap one good of an agent for another good (existing or new),
add a good to a 3-good agent, drop a good from a 4-good agent; the result must be a core with no agent holding two
private goods (K4.MC2) and, with --nongraphical, a good of degree >= 3 (the multigraph theorem covers the others).
Score: the number of allocations the CEGAR needs to certify the core (a proxy for how varied the EFX₀ allocations must
be across profiles); a step is accepted if the score does not drop by more than --slack. Any core whose CEGAR finds a
profile without an EFX₀ allocation is printed as FAIL (a counterexample candidate, to be re-checked independently).
Usage: climb_h.py START.json --steps=N [--limit=SEC] [--seed=S] [--nongraphical] --tag=NAME
START.json: a list of {"name", "sets"}; the climb starts from each in turn."""
import sys, os, json, time, random, collections
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
import cegar, check


def normalize(sets):
    goods = sorted(set(g for S in sets for g in S))
    ren = {g: k for k, g in enumerate(goods)}
    return [sorted(ren[g] for g in S) for S in sets], len(goods)


def ok_core(sets, m, nongraphical):
    n = len(sets)
    if not check.is_core(n, m, sets, sum(len(S) == 4 for S in sets)): return False
    deg = collections.Counter(g for S in sets for g in S)
    if any(sum(deg[g] == 1 for g in S) >= 2 for S in sets): return False          # K4.MC2
    if nongraphical and max(deg.values()) <= 2: return False
    return True


def neighbours(sets, m, rng, k=1):
    out = []
    n = len(sets)
    for _ in range(200):
        S = [list(x) for x in sets]
        i = rng.randrange(n)
        mv = rng.random()
        if mv < 0.6:                                                 # swap a good of agent i
            g = rng.choice(S[i]); h = rng.randrange(m + 1)
            if h in S[i]: continue
            S[i][S[i].index(g)] = h
        elif mv < 0.8 and len(S[i]) == 3:
            h = rng.randrange(m + 1)
            if h in S[i]: continue
            S[i].append(h)
        elif len(S[i]) == 4:
            S[i].remove(rng.choice(S[i]))
        else: continue
        T, mm = normalize(S)
        out.append((T, mm))
        if len(out) >= k: break
    return out


def evaluate(sets, m, limit):
    t0 = time.time()
    H = cegar.Hunt(sets, m, tries=2)
    st = H.run(cap=1, time_limit=limit)
    fails = [[list(H.dom[i][t]) for i, t in enumerate(p)] for p in H.fails]
    return st, len(H.allocs), round(time.time() - t0, 1), fails


def main():
    src = [a for a in sys.argv[1:] if not a.startswith('--')][0]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in sys.argv[1:] if a.startswith('--'))
    rng = random.Random(int(opt.get('seed', 1)))
    steps, limit, slack = int(opt.get('steps', 50)), float(opt.get('limit', 120)), int(opt.get('slack', 5))
    ng = 'nongraphical' in opt
    log = open(os.path.join(ROOT, 'results', 'k4_hunt', f"climb_{opt['tag']}.jsonl"), 'a')
    print('command: python3 k4/hunt/climb_h.py ' + ' '.join(sys.argv[1:]), flush=True)
    for rec in json.load(open(src)):
        sets, m = normalize(rec['sets'])
        st, score, t, fails = evaluate(sets, m, limit)
        print(f"start {rec['name']}: n={len(sets)} m={m} {st} score={score} {t}s", flush=True)
        best = (score, sets, m)
        for step in range(steps):
            cand = neighbours(sets, m, rng)
            if not cand: continue
            T, mm = cand[0]
            if not ok_core(T, mm, ng): continue
            st2, sc2, t2, f2 = evaluate(T, mm, limit)
            beta = sum(map(len, T)) - len(T) - mm + 1
            log.write(json.dumps({'start': rec['name'], 'step': step, 'sets': T, 'm': mm, 'beta': beta, 'status': st2,
                                  'score': sc2, 'time': t2, 'fails': f2}) + '\n'); log.flush()
            if st2 == 'counterexample':
                print(f"  FAIL step {step}: n={len(T)} m={mm} {T} {f2}", flush=True)
            if st2 == 'timeout':
                print(f"  timeout step {step}: n={len(T)} m={mm} beta={beta} {T} ({sc2} allocations in {t2}s)", flush=True)
            if st2 != 'certified' or sc2 >= score - slack:
                sets, m, score = T, mm, sc2
                if sc2 > best[0]: best = (sc2, T, mm)
                print(f"  step {step}: accept n={len(T)} m={mm} beta={beta} score={sc2} {st2} {t2}s", flush=True)
        print(f"best from {rec['name']}: score={best[0]} m={best[2]} {best[1]}", flush=True)


if __name__ == '__main__':
    main()
