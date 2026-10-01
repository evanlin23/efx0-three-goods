"""Adversarial search for a counterexample to Lemma M (k4/rulef.md §4, ledger row K4.RF.M): hill-climbing over the
strict profiles of fixed k = 4 cores, minimizing the number of first agents a whose run tau_a = (a, then index order)
is in class K0 or K1 of rule RK. A profile where that number is 0 refutes Lemma M (C40 is contained in K0 ∪ K1).

Evaluation: k4/rulef_hunt_eval.c, which #includes k4/rulef.c unchanged and applies its own Lemma K / one-rotation tests
to every first agent (as rulef.c -A41 -E1; options -Y1: kept-out sets of Remark 4, i.e. Lemma K itself, default on;
-T1: K1 as Lemma K's text counts slots (a rotated agent with a one-good base has one; rulef.c's k1_run gives it none),
default on, -T0 for rulef.c's k1_run; -N1: RK3's third policy). One persistent evaluator process per worker; profiles
are sent in batches.

Objective (lexicographic, minimized; --key=M, the default): key = (nwork, -mindef, nK0, -sumdef), where nwork =
|K0 ∪ K1| over the first agents, mindef = least Lemma K deficit over all first agents and policies (clamped to [-3, 12]:
the larger, the closer to failure), nK0 = |K0|, sumdef = sum of the clamped least deficits per first agent.
--key=R: (nwork, sum over the working first agents of 100 + 10 min(3, -deficit) for K0 and of the number of single
rotations that Lemma K certifies (evaluator -K1 -c30, summed over the policies, at most 60) for K1, -mindef);
--key=S: (nwork, nK0, -sumdef, -mindef); --key=W: (10 nwork + 3 nK0 - sum of the deficits clamped to [-3, 4], nwork,
-mindef); --key=E: simulated annealing (unit_sa) on the energy sum over first agents of phi_a, phi = 0 (neither K0
nor K1), 10 + min(rc, 30)/3 (K1, rc its certifying rotations), 25 + 3 min(3, -deficit) (K0 with omega >= 1), 40
(omega <= 0). The record's best_key is the key used.

Search per unit (a core, or a seed profile on its core): restarts; each restart starts from the best of R0 random
profiles (or the seed, or a kick of the best so far), then repeats: B neighbours of the current profile (one agent's type
redrawn, sometimes two or three), move to the best one if its key is not worse, stop after STAG batches without a
strict improvement. The types are those of k4/check4.py core_domains (strict balanced, with the private-goods
condition). Every profile with nwork <= 1 is re-evaluated in detail (every policy, frozen agents, C4^0, LB4r's fewest
rotations) and dumped.

Usage:
  rulef_hunt.py RUN --file=CERTS [--file=..] [--n4=K] [--mmin=M] [--mmax=M] [--cores=i,j,..|--top=CKFILE:K]
                [--first=K] [--every=K] [--evals=E] [--jobs=J] [--seed=S] [-Y0] [-N1]   the selected cores (every K-th,
                the first K), E evaluations each
  rulef_hunt.py RUN --seeds=JSONL [--evals=E] ...      each {"sets", "vals", "tag"} line: its core, starting at it
Search options: --relabel (after each restart, and after an --exhaust descent, the best profile is evaluated under all
n! orders of the agents: rule RK depends on the index order, and the certificate files list one labeling per core;
the best relabeling is recorded, every relabeled profile with nwork <= 1 dumped with its order 'relabel'), --exhaust (seed runs: all one- and two-agent type changes of the current profile, descending while the
key improves, at most 6 rounds; 'restarts' in the record counts the rounds), --key=M|R|S|W|E (below), --samep=P (ranking-preserving redraws), --kick=P (a restart starts from two
redraws of the best profile so far with probability P; default: every third restart).
The run writes (resumable: rerun the same command) results/k4_rulef_hunt/ck/RUN.jsonl (one line per finished unit) and
results/k4_rulef_hunt/tight_RUN.jsonl.gz (every profile with nwork <= 1, details included). The log goes to stdout."""
import gzip, hashlib, itertools, json, math, os, random, subprocess, sys, tempfile, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check4

ROOT = os.path.dirname(HERE)
OUT = os.path.join(ROOT, 'results', 'k4_rulef_hunt')
SRC = os.path.join(HERE, 'rulef.c')
EVAL_SRC = os.path.join(HERE, 'rulef_hunt_eval.c')
SHA = hashlib.sha256(open(SRC, 'rb').read()).hexdigest()
ESHA = hashlib.sha256(open(EVAL_SRC, 'rb').read()).hexdigest()
BIN = os.path.join(tempfile.gettempdir(), 'k4_rulef_hunt_' + hashlib.sha256((SHA + ESHA).encode()).hexdigest()[:16])
B, R0, STAG = 48, 96, 25
KICK = None                               # --kick=P: a restart kicks the best profile so far with probability P
SAMEP = 0.0                               # --samep=P: probability of a ranking-preserving redraw
EXR = 6                                   # --exhaust: at most this many descent rounds
SAEV = 4000                               # evaluations per annealing restart (--key=E)


def build():
    if not os.path.exists(BIN):
        tmp = BIN + f'.tmp{os.getpid()}'
        subprocess.run(['gcc', '-O2', '-w', '-o', tmp, EVAL_SRC], check=True)
        os.replace(tmp, BIN)


def clamp(x):
    return max(-3, min(12, x))


class Evaluator:
    def __init__(self, opts):
        self.p = subprocess.Popen([BIN] + opts, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
        self.core = None
        self.nev = 0

    def set_core(self, sets, m, doms):
        lines = [f"C {len(sets)} {m}"]
        for S, dom in zip(sets, doms):
            lines.append(f"{len(S)} {' '.join(map(str, S))} {len(dom)}")
            lines += [' '.join(str(v[g]) for g in S) for v in dom]
        self.p.stdin.write('\n'.join(lines) + '\n'); self.p.stdin.flush()

    def evaluate(self, profs):
        """profs: list of type tuples -> list of (key, nwork, nK0, cls, defs)"""
        out = []
        for k0 in range(0, len(profs), 200):
            chunk = profs[k0:k0 + 200]
            self.p.stdin.write(''.join(f"P {i} {' '.join(map(str, t))}\n" for i, t in enumerate(chunk)))
            self.p.stdin.flush()
            for _ in chunk:
                t = self.p.stdout.readline().split()
                if not t or t[0] != 'R': raise RuntimeError('evaluator: ' + ' '.join(t))
                out.append(self.parse(t))
        self.nev += len(profs)
        return out

    def parse(self, t):
        if True:
            if True:
                nwork, nk0, mind, sumd = int(t[2]), int(t[3]), int(t[4]), int(t[5])
                cls = [int(x) for x in t[6][4:].split(',')]
                defs = [int(x) for x in t[7][4:].split(',')]
                rc = [int(x) for x in t[8][3:].split(',')] if len(t) > 8 else None
                if KEY == 'E':           # energy: sum of phi over the first agents (annealed, see unit_sa)
                    e = 0.0
                    for a, (c, d) in enumerate(zip(cls, defs)):
                        if c == 1: e += 10 + min(rc[a], 30) / 3
                        elif c == 0: e += 40 if d <= -100 else 25 + 3 * min(3, -d)
                    key = (round(e, 3), nwork, -clamp(mind))
                elif KEY == 'R':           # working agents weighted: K0 100 + 10 min(3, -deficit), K1 its rotation count
                    w = sum((100 + 10 * min(3, -max(-3, d)) if c == 0 else (min(rc[a], 60) if c == 1 else 0))
                            for a, (c, d) in enumerate(zip(cls, defs)))
                    key = (nwork, w, -clamp(mind))
                elif KEY == 'S': key = (nwork, nk0, -sumd, -clamp(mind))
                elif KEY == 'W': key = (10 * nwork + 3 * nk0 - sum(max(-3, min(4, x)) for x in defs), nwork, -clamp(mind))
                else: key = (nwork, -clamp(mind), nk0, -sumd)
                return (key, nwork, nk0, cls, defs)

    def relabeled(self, sets, m, vals, perms, want_detail):
        """evaluate the profile (sets, vals) under each agent order pi (agent i becomes agent pi[i]), each as its own
        one-type core; the current core is lost (call set_core again). Returns [(pi, S, V, key-tuple)], and the
        detail lines for those with nwork <= 1 when want_detail."""
        n = len(sets)
        jobs = []
        for pi in perms:
            S = [None] * n; V = [None] * n
            for i in range(n): S[pi[i]] = sets[i]; V[pi[i]] = vals[i]
            jobs.append((pi, S, V))
        out = []
        for c0 in range(0, len(jobs), 100):
            chunk = jobs[c0:c0 + 100]
            txt = []
            for pi, S, V in chunk:
                txt.append(f"C {n} {m}")
                for Sx, Vx in zip(S, V):
                    txt.append(f"{len(Sx)} {' '.join(map(str, Sx))} 1"); txt.append(' '.join(map(str, Vx)))
                txt.append('P 0 ' + ' '.join('0' * n))
            self.p.stdin.write('\n'.join(txt) + '\n'); self.p.stdin.flush()
            for pi, S, V in chunk:
                t = self.p.stdout.readline().split()
                if not t or t[0] != 'R': raise RuntimeError('evaluator: ' + ' '.join(t))
                out.append((pi, S, V, self.parse(t)))
        self.nev += len(jobs)
        dets = {}
        if want_detail:
            for pi, S, V, r in out:
                if r[1] <= 1:
                    txt = [f"C {n} {m}"]
                    for Sx, Vx in zip(S, V):
                        txt.append(f"{len(Sx)} {' '.join(map(str, Sx))} 1"); txt.append(' '.join(map(str, Vx)))
                    self.p.stdin.write('\n'.join(txt) + '\n'); self.p.stdin.flush()
                    dets[tuple(pi)] = self.detail(tuple(0 for _ in range(n)))
        return out, dets

    def detail(self, prof):
        self.p.stdin.write(f"D 0 {' '.join(map(str, prof))}\n"); self.p.stdin.flush()
        res = []
        n = len(prof)
        for _ in range(n):
            t = self.p.stdout.readline().split()
            if not t or t[0] != 'X': raise RuntimeError('evaluator: ' + ' '.join(t))
            res.append({kv.split('=')[0]: int(kv.split('=')[1]) for kv in t[2:]})
        return res


EV = None
OPTS = None
KEY = 'M'


def init(opts, key='M', samep=0.0, kick=None, relabel=False):
    global EV, OPTS, KEY, SAMEP, KICK, RELABEL
    OPTS, KEY, SAMEP, KICK, RELABEL = opts, key, samep, kick, relabel
    EV = Evaluator(opts)


def rank_groups(doms):
    """per agent: type index -> the indices of the types with the same ranking of its goods"""
    out = []
    for D in doms:
        by = {}
        for q, v in enumerate(D):
            by.setdefault(tuple(sorted(v, key=lambda g: -v[g])), []).append(q)
        out.append([by[tuple(sorted(v, key=lambda g: -v[g]))] for v in D])
    return out


GROUPS = {}


def mutate(rng, cur, doms):
    """redraw the type of one agent (70%), two (25%) or three (5%); each redraw keeps the agent's ranking of its goods
    with probability SAMEP (only value comparisons change), else is uniform over the agent's types"""
    t = list(cur)
    r = rng.random()
    k = 1 if r < 0.7 else (2 if r < 0.95 else 3)
    grp = GROUPS.get(id(doms))
    for i in rng.sample(range(len(t)), min(k, len(t))):
        if grp is not None and rng.random() < SAMEP and len(grp[i][t[i]]) > 1:
            g = grp[i][t[i]]
            x = rng.randrange(len(g) - 1); y = g[x]
            t[i] = y if y != t[i] else g[-1]
        elif len(doms[i]) > 1:
            x = rng.randrange(len(doms[i]) - 1)
            t[i] = x + (x >= t[i])
    return tuple(t)


def vals_of(sets, doms, prof):
    return [[doms[i][prof[i]][g] for g in S] for i, S in enumerate(sets)]


def unit(task):
    """Hill-climb one core. task = (uid, sets, m, evals, seed, start_vals or None, meta)"""
    uid, sets, m, evals, seed, start, meta = task
    t0 = time.time()
    rng = random.Random(seed)
    doms = check4.core_domains(sets, m, False)
    extra = 0
    if start is not None:                 # the seed's own types, added to the domain where missing
        st = []
        for i, (S, V) in enumerate(zip(sets, start)):
            vd = dict(zip(S, V))
            hit = next((q for q, dv in enumerate(doms[i]) if same_type(dv, vd, S)), None)
            if hit is None:
                doms[i] = doms[i] + [vd]; hit = len(doms[i]) - 1; extra += 1
            st.append(hit)
        start = tuple(st)
    EV.set_core(sets, m, doms)
    GROUPS.clear(); GROUPS[id(doms)] = rank_groups(doms)
    nev0 = EV.nev
    tight = {}
    best = None
    hist = [0] * (len(sets) + 1)          # least nwork reached per restart

    def note(profs, res):
        for p, r in zip(profs, res):
            if r[1] <= 1 and p not in tight and len(tight) < 200:
                tight[p] = r

    restarts = 0
    rel = RelScan(uid, meta, sets, m, doms) if RELABEL else None
    while EV.nev - nev0 < evals:
        if restarts == 0 and start is not None:
            profs = [start]
        elif best is not None and (rng.random() < KICK if KICK is not None else restarts % 3 == 2):
            profs = [mutate(rng, mutate(rng, best[0], doms), doms) for _ in range(B)]
        else:
            profs = [tuple(rng.randrange(len(D)) for D in doms) for _ in range(R0)]
        res = EV.evaluate(profs); note(profs, res)
        j = min(range(len(profs)), key=lambda q: res[q][0])
        cur, ck, cnw = profs[j], res[j][0], res[j][1]
        stag = 0
        while stag < STAG and EV.nev - nev0 < evals:
            nb = [mutate(rng, cur, doms) for _ in range(B)]
            r2 = EV.evaluate(nb); note(nb, r2)
            q = min(range(len(nb)), key=lambda z: r2[z][0])
            if r2[q][0] < ck:
                cur, ck, cnw, stag = nb[q], r2[q][0], r2[q][1], 0
            else:
                if r2[q][0] == ck: cur = nb[q]
                stag += 1
        hist[cnw] += 1
        if best is None or ck < best[1]: best = (cur, ck, cnw)
        if rel is not None: rel.scan(cur)
        restarts += 1
    return finish(uid, meta, sets, m, doms, tight, best, hist, restarts, extra, nev0, t0, rel)


RELABEL = False                           # --relabel: scan every agent order of each restart's best profile


class RelScan:
    """the agent orders of restart-best profiles (--relabel): the best relabeled profile, and every relabeled
    profile with nwork <= 1 (dumped with its order and details)"""
    def __init__(self, uid, meta, sets, m, doms):
        self.uid, self.meta, self.sets, self.m, self.doms = uid, meta, sets, m, doms
        self.best = None; self.tl = []; self.seen = set(); self.scans = 0
        self.perms = list(itertools.permutations(range(len(sets))))

    def scan(self, prof):
        if prof in self.seen: return
        self.seen.add(prof); self.scans += 1
        vals = vals_of(self.sets, self.doms, prof)
        out, dets = EV.relabeled(self.sets, self.m, vals, self.perms, True)
        EV.set_core(self.sets, self.m, self.doms)
        for pi, S, V, r in out:
            if self.best is None or r[0] < self.best[0]:
                self.best = (r[0], r[1], list(pi), S, V)
            if r[1] <= 1 and len(self.tl) < 200:
                self.tl.append({'unit': self.uid, **self.meta, 'sets': S, 'm': self.m, 'vals': V, 'types': None,
                                'relabel': list(pi), 'base_types': list(prof), 'nwork': r[1], 'nK0': r[2],
                                'cls': r[3], 'def': r[4], 'detail': dets[tuple(pi)]})

    def record(self, rec):
        if self.best is not None:
            rec.update({'relabel_scans': self.scans, 'relabel_best_key': list(self.best[0]),
                        'relabel_best_nwork': self.best[1], 'relabel_best_perm': self.best[2],
                        'relabel_best_sets': self.best[3], 'relabel_best_vals': self.best[4]})
        return rec


def unit_sa(task):
    """Simulated annealing on one core (--key=E): heat-bath moves among B neighbours (probability ~ exp(-E/T)),
    T geometric from T0 to T1 over each restart of SAEV evaluations; restarts from random profiles, the best so far
    kicked, or the seed."""
    uid, sets, m, evals, seed, start, meta = task
    t0 = time.time()
    rng = random.Random(seed)
    doms, start, extra = domains_with(sets, m, start)
    EV.set_core(sets, m, doms)
    GROUPS.clear(); GROUPS[id(doms)] = rank_groups(doms)
    nev0 = EV.nev
    tight = {}
    best = None
    hist = [0] * (len(sets) + 1)
    restarts = 0
    T0, T1, BS = 6.0, 0.4, 16
    while EV.nev - nev0 < evals:
        if restarts == 0 and start is not None:
            cur = start
        elif best is not None and restarts % 3 == 2:
            cur = mutate(rng, mutate(rng, best[0], doms), doms)
        else:
            profs = [tuple(rng.randrange(len(D)) for D in doms) for _ in range(R0)]
            res = EV.evaluate(profs)
            for p, r in zip(profs, res):
                if r[1] <= 1 and p not in tight and len(tight) < 200: tight[p] = r
            cur = profs[min(range(len(profs)), key=lambda q: res[q][0])]
        cr = EV.evaluate([cur])[0]
        rbest = (cur, cr)
        budget = min(SAEV, evals - (EV.nev - nev0))
        e0 = EV.nev
        while EV.nev - e0 < budget:
            T = T0 * (T1 / T0) ** ((EV.nev - e0) / budget)
            nb = [mutate(rng, cur, doms) for _ in range(BS)]
            r2 = EV.evaluate(nb)
            for p, r in zip(nb, r2):
                if r[1] <= 1 and p not in tight and len(tight) < 200: tight[p] = r
            es = [r[0][0] for r in r2]
            lo = min(es)
            w = [math.exp(-(e - lo) / T) for e in es]
            q = rng.choices(range(len(nb)), weights=w)[0]
            cur, cr = nb[q], r2[q]
            if cr[0] < rbest[1][0]: rbest = (cur, cr)
        hist[rbest[1][1]] += 1
        if best is None or rbest[1][0] < best[1]: best = (rbest[0], rbest[1][0], rbest[1][1])
        restarts += 1
    return finish(uid, meta, sets, m, doms, tight, best, hist, restarts, extra, nev0, t0)


def unit_exh(task):
    """--exhaust (seed runs): every profile that differs from the current one in the types of one or two agents is
    evaluated; if the best of them has a smaller key, it becomes current and the enumeration is repeated (at most
    EXR rounds, and the unit's evaluation budget)."""
    uid, sets, m, evals, seed, start, meta = task
    t0 = time.time()
    doms, start, extra = domains_with(sets, m, start)
    EV.set_core(sets, m, doms)
    nev0 = EV.nev
    tight = {}
    n = len(sets)
    cur = start if start is not None else tuple(0 for _ in sets)
    ck = EV.evaluate([cur])[0]
    best = (cur, ck[0], ck[1])
    hist = [0] * (n + 1)
    rounds = 0
    while rounds < EXR and EV.nev - nev0 < evals:
        rounds += 1
        rb = None

        def gen():
            for i in range(n):
                for x in range(len(doms[i])):
                    if x != cur[i]:
                        t = list(cur); t[i] = x; yield tuple(t)
            for i, j in itertools.combinations(range(n), 2):
                for x in range(len(doms[i])):
                    if x == cur[i]: continue
                    for y in range(len(doms[j])):
                        if y == cur[j]: continue
                        t = list(cur); t[i] = x; t[j] = y; yield tuple(t)
        it = gen()
        while EV.nev - nev0 < evals:
            chunk = list(itertools.islice(it, 2000))
            if not chunk: break
            res = EV.evaluate(chunk)
            for p, r in zip(chunk, res):
                if r[1] <= 1 and p not in tight and len(tight) < 200: tight[p] = r
                if rb is None or r[0] < rb[1]: rb = (p, r[0], r[1])
        hist[rb[2]] += 1
        if rb[1] < best[1]:
            best = rb; cur = rb[0]
        else:
            break
    rel = None
    if RELABEL:
        rel = RelScan(uid, meta, sets, m, doms); rel.scan(best[0])
    return finish(uid, meta, sets, m, doms, tight, best, hist, rounds, extra, nev0, t0, rel)


def domains_with(sets, m, start):
    doms = check4.core_domains(sets, m, False)
    extra = 0
    if start is not None:                 # the seed's own types, added to the domain where missing
        st = []
        for i, (S, V) in enumerate(zip(sets, start)):
            vd = dict(zip(S, V))
            hit = next((q for q, dv in enumerate(doms[i]) if same_type(dv, vd, S)), None)
            if hit is None:
                doms[i] = doms[i] + [vd]; hit = len(doms[i]) - 1; extra += 1
            st.append(hit)
        start = tuple(st)
    return doms, start, extra


def finish(uid, meta, sets, m, doms, tight, best, hist, restarts, extra, nev0, t0, rel=None):
    tl = []
    for p, r in sorted(tight.items(), key=lambda z: z[1][0]):
        det = EV.detail(p)
        tl.append({'unit': uid, **meta, 'sets': sets, 'm': m, 'vals': vals_of(sets, doms, p), 'types': list(p),
                   'nwork': r[1], 'nK0': r[2], 'cls': r[3], 'def': r[4], 'detail': det})
    if rel is not None: tl += rel.tl
    rec = {'unit': uid, **meta, **({} if 'file' in meta else {'sets': sets}), 'm': m, 'n': len(sets),
           'evals': EV.nev - nev0, 'restarts': restarts, 'best_key': list(best[1]), 'best_nwork': best[2], 'best_types': list(best[0]),
           'best_vals': vals_of(sets, doms, best[0]), 'hist': hist, 'ntight': len(tight) + (len(rel.tl) if rel else 0),
           'extra_types': extra, 'time': round(time.time() - t0, 2)}
    return (rel.record(rec) if rel is not None else rec), tl


def same_type(dv, vd, S):
    """same strict order type: the dense ranking of all nonempty subset sums agrees"""
    def key(v):
        sums = [sum(v[g] for k, g in enumerate(S) if T >> k & 1) for T in range(1, 1 << len(S))]
        o = sorted(set(sums)); return tuple(o.index(s) for s in sums)
    return key(dv) == key(vd)


def arg(args, name, default=None, conv=str):
    v = [a.split('=', 1)[1] for a in args if a.startswith(f'--{name}=')]
    return conv(v[-1]) if v else default


def main():
    args = sys.argv[1:]
    run = args[0]
    jobs = arg(args, 'jobs', os.cpu_count(), int)
    evals = arg(args, 'evals', 3000, int)
    seed = arg(args, 'seed', 1, int)
    key = arg(args, 'key', 'M')
    samep = arg(args, 'samep', 0.0, float)
    kick = arg(args, 'kick', None, float)
    opts = [a for a in args[1:] if a.startswith('-') and not a.startswith('--')]
    if not any(o.startswith('-Y') for o in opts): opts.append('-Y1')
    if not any(o.startswith('-r') for o in opts): opts.append('-r2')
    if not any(o.startswith('-T') for o in opts): opts.append('-T1')
    if key in 'RE' and '-K1' not in opts: opts += ['-K1', '-c30']
    build()
    os.makedirs(os.path.join(OUT, 'ck'), exist_ok=True)
    ckp = os.path.join(OUT, 'ck', run + '.jsonl')
    dump = os.path.join(OUT, f'tight_{run}.jsonl.gz')
    print('# command: python3 k4/rulef_hunt.py ' + ' '.join(args), flush=True)
    print(f'# k4/rulef.c sha256 {SHA}', flush=True)
    print(f'# k4/rulef_hunt_eval.c sha256 {ESHA}; evaluator options {" ".join(opts)}; B={B} R0={R0} STAG={STAG}; key {key}; samep {samep}; kick {kick}; relabel {"--relabel" in args}',
          flush=True)
    tasks = []
    if arg(args, 'seeds'):
        for q, line in enumerate(open(arg(args, 'seeds'))):
            o = json.loads(line)
            S, V = o['sets'], o['vals']
            m = 1 + max(g for s in S for g in s)
            tasks.append((f"seed{q}", S, m, evals, seed * 1000003 + q, V, {'tag': o.get('tag', str(q))}))
    else:
        files = [a.split('=', 1)[1] for a in args if a.startswith('--file=')]
        n4 = arg(args, 'n4', None, int)
        mmin, mmax = arg(args, 'mmin', 0, int), arg(args, 'mmax', 999, int)
        sel = arg(args, 'cores')
        first, every = arg(args, 'first', None, int), arg(args, 'every', 1, int)
        top = arg(args, 'top')
        topset = None
        if top:                           # the K units with the least best key in a checkpoint file
            path, K = top.rsplit(':', 1)
            recs = [json.loads(l) for l in open(path)]
            recs.sort(key=lambda r: tuple(r['best_key']))
            topset = {(r['file'], r['core']) for r in recs[:int(K)]}
        for f in files:
            data = json.load(gzip.open(f, 'rt'))
            fb = os.path.basename(f)
            nsel = 0
            for i, c in enumerate(data['cores']):
                if n4 is not None and sum(len(S) == 4 for S in c['sets']) != n4: continue
                if not mmin <= c['m'] <= mmax: continue
                if sel and str(i) not in sel.split(','): continue
                if topset is not None and (fb, i) not in topset: continue
                nsel += 1
                if (nsel - 1) % every or (first is not None and nsel > first * every): continue
                tasks.append((f"{fb}:{i}", c['sets'], c['m'], evals, seed * 1000003 + i + 7919 * len(tasks), None,
                              {'file': fb, 'core': i}))
    done = set()
    if os.path.exists(ckp):
        for line in open(ckp):
            done.add(json.loads(line)['unit'])
    todo = [t for t in tasks if t[0] not in done]
    print(f'# units {len(tasks)}, done before {len(tasks) - len(todo)}, to do {len(todo)}, evals per unit {evals}, '
          f'jobs {jobs}', flush=True)
    t0 = time.time()
    nd = 0; tev = 0; ntl = 0; bestk = None; besthist = {}
    with Pool(jobs, initializer=init, initargs=(opts, key, samep, kick, '--relabel' in args)) as pool, open(ckp, 'a') as fc:
        fn = unit_exh if '--exhaust' in args else (unit_sa if key == 'E' else unit)
        for rec, tl in pool.imap_unordered(fn, todo, chunksize=1):
            nd += 1; tev += rec['evals']
            k = rec['best_nwork']; besthist[k] = besthist.get(k, 0) + 1
            if tl:
                with gzip.open(dump, 'at') as fd:
                    for t in tl: fd.write(json.dumps(t) + '\n')
                ntl += len(tl)
                for t in tl:
                    if t['nwork'] == 0:
                        print(f"COUNTEREXAMPLE unit={t['unit']} sets={json.dumps(t['sets'])} vals={json.dumps(t['vals'])}",
                              flush=True)
            fc.write(json.dumps(rec) + '\n'); fc.flush()
            if bestk is None or tuple(rec['best_key']) < tuple(bestk[0]): bestk = (rec['best_key'], rec['unit'])
            if nd in (1, 2, 4, 8) or nd % 200 == 0 or nd == len(todo):
                el = time.time() - t0
                print(f"[{el:7.0f}s] units {nd}/{len(todo)} evals {tev} ({tev / max(el, 1e-9):.0f}/s) "
                      f"est. total {el / nd * len(todo) / 60:.1f} min; best nwork per unit {dict(sorted(besthist.items()))}; "
                      f"tight profiles {ntl}; best key {bestk[0]} at {bestk[1]}", flush=True)
    print(f"# finished: units {nd} this session, evals {tev}, tight profiles dumped {ntl}, time {time.time() - t0:.0f}s",
          flush=True)


if __name__ == '__main__':
    main()
