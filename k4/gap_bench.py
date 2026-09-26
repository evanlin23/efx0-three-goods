"""A lemma test bench over the exposed-frozen gap of C4min (compute/k4-gap; k4/gap.md). EVIDENCE only.

The catalog files results/k4_gap/gap_*.json.gz hold profiles in the gap (k4/gap_run.py): f >= 1, omega >= 1, and every
configuration at the fewest frozen agents has an exposed frozen agent. The bench rebuilds every configuration of every
profile (k4/gap.c -C for speed; each counterexample is then re-derived by the pure Python model k4/gap_model.py, which
shares no code with gap.c) and runs a predicate on it.

API (from the repository root):
    import sys; sys.path.insert(0, 'k4'); import gap_bench as gb
    def my_lemma(prof, c):            # prof: gap_model.Profile, c: gap_model.Config
        if c.completable: return None  # None = hypothesis not met, skipped
        return any(c2.phi > c.phi for _, _, c2 in c.pool_moves())   # True = holds, False = counterexample
    res = gb.check(my_lemma, scope='all', catalogs=['results/k4_gap/gap_n3.json.gz'], name='my lemma')
    print(res.summary()); res.counterexamples[0]   # (prof, config, detail), smallest first

  scope: 'all' every configuration; 'max' the Phi'-maxima of the profile; 'max0' the maxima of the first form
         Phi = (-t, r, Lambda); 'noncompl' the configurations without a valid owner; 'pareto' the configurations that
         are Pareto-maximal (holdings' values) among all configurations of the profile; 'profile' the predicate gets
         (prof, list of all configurations) once per profile; or a callable (prof, cfgs) -> subset.
  Every configuration has the attributes of gap_model.Config: .key .frozen .free .N .Q .L .H(i) .hv(i) .U(i)
  .needs(i) .needers(g) .threatens(o, x, C) .owner(o) .owners .completable .simple .t .r .Lam .p .phi .phi0
  .pool_optimal .kind(i) .exposed .bigtop(x) .threat_edges .need_edges .chain_ends(x) .h7(x, o) .mult(x)
  .pool_moves() .cycle_moves(general, keep) .two_agent_moves() .downgrade_swaps() .pool_closure(); and prof: .n .m
  .R .v .f .omega .keys. gap_bench.pareto(cfgs) and gap_bench.reach(starts, swaps) are available to predicates.
  gb.check_instances(pred, scope) runs a predicate on the versioned instance suite results/k4_gap/instances_v1.json
  (every hard instance, with provenance, cross-checked between gap.c and gap_model; k4/gap.md section 5).
  Counterexamples are sorted by (n, m, number of configurations, catalog order): smallest first. --every=E keeps every
  E-th catalog record, --max-profiles=K the first K (after --every).

CLI:
    python3 k4/gap_bench.py [--catalog=F1,F2] [--only=NAME,...] [--every=E] [--max-profiles=K] [--show=2] [--list]
    python3 k4/gap_bench.py --selftest [--catalog=...] [--every=E] [--max-profiles=K]
    python3 k4/gap_bench.py --instances[=results/k4_gap/instances_v1.json] [--only=...]   # the versioned suite
    python3 k4/gap_bench.py --profile='{"sets": [[0,2,5,6], ...], "vals": [[2,6,3,10], ...]}' [--only=...]   # one profile     # gap.c vs gap_model, config by config
The seeded statements (STATEMENTS below) are the candidate steps of k4/c4min.md section 4 (PR #41: Conjecture Phi',
the roadmap steps (i)-(iv)) and of k4/hall.md section 5 (PR #46: BT, the trichotomy of Lemma H7)."""
import gzip, json, os, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gap_model as gm
import gap_run

DEFAULT = [os.path.join(HERE, '..', 'results', 'k4_gap', f) for f in ('gap_n2.json.gz', 'gap_n3.json.gz')]

def load(catalogs):
    recs = []
    for f in catalogs:
        d = json.load(gzip.open(f, 'rt'))
        for r in d['records']: r['_cat'] = os.path.basename(f); recs.append(r)
    return recs

def dump(recs):
    """gap.c -C on each record's profile: yields (record, head, [configuration dicts])"""
    gap_run.build()
    blocks = []
    for k, r in enumerate(recs):
        sets = r['core']['sets']
        doms = [[dict(zip(S, V))] for S, V in zip(sets, r['vals'])]
        blocks.append(gap_run.block(sets, r['core']['m'], doms, k, 0, profs=[[0] * len(sets)]))
    out = subprocess.run([gap_run.BIN, '-C'], input=''.join(blocks), capture_output=True, text=True, check=True).stdout
    k, head, cl = 0, None, []
    for l in out.splitlines():
        if l.startswith('P '): head = json.loads(l[2:]); cl = []
        elif l.startswith('C '): cl.append(json.loads(l[2:]))
        elif l.startswith('K '):
            yield recs[k], head, cl
            k += 1; head = None

def profiles(catalogs=None, max_profiles=None, recs=None):
    """yields (record, Profile, [Config]) for the catalog profiles; configurations built from gap.c's dump"""
    recs = recs if recs is not None else load(catalogs or DEFAULT)
    if max_profiles: recs = recs[:max_profiles]
    for i in range(0, len(recs), 2000):
        for r, head, cl in dump(recs[i:i + 2000]):
            if head is None: continue
            prof = gm.Profile(r['core']['sets'], r['vals'], r['core']['m'])
            prof.f, prof.omega = head['f'], head['omega']
            prof.keys = [tuple(None if g < 0 else g for g in k) for k in head['keys']]
            cfgs = []
            for d in cl:
                c = gm.Config(prof, [None if g < 0 else g for g in d['key']], {y: q for y, q in enumerate(d['Q']) if q is not None})
                c._phi_c = tuple(d['phi']); c._own_c = [o for o, C in d['own']]
                cfgs.append(c)
            yield r, prof, cfgs

def pareto(cfgs):
    vec = [tuple(c.hv(i) for i in range(c.P.n)) for c in cfgs]
    return [c for c, a in zip(cfgs, vec) if not any(b != a and all(x >= y for x, y in zip(b, a)) for b in vec)]

def select(scope, prof, cfgs):
    if callable(scope): return scope(prof, cfgs)
    if scope == 'all': return cfgs
    if scope == 'max':
        b = max(c._phi_c for c in cfgs); return [c for c in cfgs if c._phi_c == b]
    if scope == 'max0':
        b = max(c._phi_c[:3] for c in cfgs); return [c for c in cfgs if c._phi_c[:3] == b]
    if scope == 'noncompl': return [c for c in cfgs if not c._own_c]
    if scope == 'pareto': return pareto(cfgs)
    raise ValueError(scope)

def recheck(r, c, pred, scope):
    """re-derive a counterexample with the pure Python model: the profile's configurations from scratch"""
    prof = gm.Profile(r['core']['sets'], r['vals'], r['core']['m'])
    if not prof.in_gap: return 'not in the gap (Python)'
    cfgs = prof.configs()
    for c2 in cfgs: c2._phi_c = c2.phi; c2._own_c = c2.owners
    if scope == 'profile': return 'confirmed' if pred(prof, cfgs) is False else 'NOT confirmed'
    sel = select(scope, prof, cfgs)
    for c2 in sel:
        if c2.key == c.key and c2.Q == c.Q:
            return 'confirmed' if pred(prof, c2) is False else 'NOT confirmed'
    return 'NOT confirmed (configuration not in scope)'

class Result:
    def __init__(self, name): self.name, self.tested, self.skipped, self.profiles, self.counterexamples = name, 0, 0, 0, []
    @property
    def holds(self): return not self.counterexamples
    def summary(self, show=2):
        s = [f"{self.name}: {'HOLDS' if self.holds else 'FAILS'} on the data; {self.tested} cases tested, {self.skipped} "
             f"skipped (hypothesis not met), {self.profiles} profiles; {len(self.counterexamples)} counterexamples"]
        for prof, c, detail in self.counterexamples[:show]:
            s.append(f"  smallest: n={prof.n} m={prof.m} sets={[sorted(S) for S in prof.sets]} values={[[prof.v[i][g] for g in prof.sets[i]] for i in range(prof.n)]}")
            s.append(f"    {c if c is not None else ''} {detail}")
        return '\n'.join(s)

def check(pred, scope='all', catalogs=None, name='statement', max_profiles=None, recs=None, confirm=3):
    """run one predicate; see the module docstring"""
    return check_many([(name, scope, pred)], catalogs, max_profiles, recs, confirm)[0]

def check_many(stmts, catalogs=None, max_profiles=None, recs=None, confirm=3):
    """stmts: list of (name, scope, pred); one pass over the profiles; returns a list of Result"""
    res = [Result(nm) for nm, _, _ in stmts]
    found = [[] for _ in stmts]
    for r, prof, cfgs in profiles(catalogs, max_profiles, recs):
        sel = {}
        for k, (nm, scope, pred) in enumerate(stmts):
            res[k].profiles += 1
            if scope == 'profile':
                out = pred(prof, cfgs)
                if out is None: res[k].skipped += 1; continue
                res[k].tested += 1
                if out is False: found[k].append((prof.n, prof.m, len(cfgs), len(found[k]), r, prof, None))
                continue
            key = scope if isinstance(scope, str) else id(scope)
            if key not in sel: sel[key] = select(scope, prof, cfgs)
            for c in sel[key]:
                out = pred(prof, c)
                if out is None: res[k].skipped += 1; continue
                res[k].tested += 1
                if out is False: found[k].append((prof.n, prof.m, len(cfgs), len(found[k]), r, prof, c))
    for k, (nm, scope, pred) in enumerate(stmts):
        found[k].sort(key=lambda t: t[:4])
        for j, (_, _, _, _, r, prof, c) in enumerate(found[k]):
            detail = 'Python re-check: ' + recheck(r, c, pred, scope) if j < confirm else ''
            res[k].counterexamples.append((prof, c, detail))
    return res

# ---------------------------------------------------------------- the instance suite
INSTANCES = os.path.join(HERE, '..', 'results', 'k4_gap', 'instances_v1.json')

def check_instances(pred, scope='all', path=INSTANCES, ids=None, quiet=False):
    """Run pred on every instance of the versioned suite (k4/gap_instances.py; k4/gap.md section 5).

    For each instance: gap.c (-C dump) and gap_model build the configurations independently and must agree (class, f,
    omega, keys, every configuration's Phi', pool-optimality, owners with their least |C|, threat edges, H7 classes);
    then pred is evaluated on gap_model's configurations with the given scope (as in check). Instances not in the gap
    (e.g. cyc6, f = 0) are evaluated on gap_model's configurations only. Returns a list of dicts: id, tags,
    provenance, in_gap, agree (number of gap.c/gap_model mismatches, 0 if they agree), tested, skipped, fails (the
    failing configurations), highlighted (the outcome on the instance's highlighted configuration, if any)."""
    data = json.load(open(path))
    out = []
    for d in data['instances']:
        if ids and d['id'] not in ids: continue
        rec = {'core': {'sets': d['sets'], 'm': d['m'], 'file': d['id'], 'pos': 0, 'idx': 0}, 'vals': d['vals'], 'prof': [0] * d['n']}
        prof = gm.Profile(d['sets'], d['vals'], d['m'])
        ingap = prof.in_gap
        head, cl = next(((h, c) for _, h, c in dump([rec])), (None, []))
        if ingap:
            import io, contextlib
            with contextlib.redirect_stdout(io.StringIO()):
                bad = gm.selftest([rec], lambda r: (head, cl))
        else:
            bad = 0 if head is None else 1
        cfgs = prof.configs()
        for c in cfgs: c._phi_c = c.phi; c._own_c = c.owners
        res = {'id': d['id'], 'tags': d.get('tags', []), 'provenance': d.get('provenance', ''), 'in_gap': ingap, 'agree': bad,
               'tested': 0, 'skipped': 0, 'fails': [], 'highlighted': None}
        hl = d.get('config')
        hkey = (tuple(hl['key']), {int(y): frozenset(q) for y, q in hl['Q'].items()}) if hl else None
        if scope == 'profile':
            r = pred(prof, cfgs)
            res['tested' if r is not None else 'skipped'] += 1
            if r is False: res['fails'].append(None)
        else:
            for c in select(scope, prof, cfgs):
                r = pred(prof, c)
                if r is None: res['skipped'] += 1; continue
                res['tested'] += 1
                if r is False: res['fails'].append(c)
                if hkey and c.key == hkey[0] and c.Q == hkey[1]: res['highlighted'] = r
        out.append(res)
        if not quiet:
            print(f"  {d['id']}: {'in the gap' if ingap else 'NOT in the gap'}, gap.c/gap_model mismatches {bad}; tested "
                  f"{res['tested']}, skipped {res['skipped']}, fails {len(res['fails'])}"
                  + (f", highlighted configuration: {res['highlighted']}" if hl else '') + f"  [{', '.join(res['tags'])}]", flush=True)
    return out

# ---------------------------------------------------------------- seeded statements
def _f1_setting(prof, c):
    """the setting of the f = 1 roadmap (c4min.md section 4): f = 1, the frozen agent x has three goods, no valid owner,
    pool-optimal, t = 0"""
    return prof.f == 1 and len(prof.R[c.frozen[0]]) == 3 and not c.completable and c.pool_optimal and c.t == 0

def _threat_pred(c, y):
    return [o for o in c.free if o != y and c.threatens(o, y)]

def st_sigma_inj(prof, c):
    if not _f1_setting(prof, c): return None
    return all(len(_threat_pred(c, y)) <= 1 for y in range(prof.n))

def _closing_moves(c):
    """exchange-cycle moves through x: best pairs (every order) and any admissible pairs (this contains the roadmap's
    plain rotation, where p_{i+1} takes Q_{p_i} and x takes {b_x, c_x})"""
    x = c.frozen[0]
    return [(cyc, c2) for cyc, c2 in c.cycle_moves() + c.cycle_moves(general=True) if x in cyc]

def _ii_setting(prof, c):
    """the roadmap's setting for the path-closing step: f = 1 setting, x threatened, and no exchange-cycle move that
    avoids x raises Phi' (the roadmap first rotates such cycles; what remains has its terminals on the path into x)"""
    if not _f1_setting(prof, c) or not _threat_pred(c, c.frozen[0]): return False
    x = c.frozen[0]
    return not any(c2.phi > c.phi for cyc, c2 in c.cycle_moves() + c.cycle_moves(general=True) if x not in cyc)

def st_ii_t0(prof, c):
    if not _ii_setting(prof, c): return None
    return any(c2.t == 0 for _, c2 in _closing_moves(c))

def st_ii_phi(prof, c):
    if not _ii_setting(prof, c): return None
    return any(c2.phi > c.phi for _, c2 in _closing_moves(c))

def st_iii(prof, c):
    if not _f1_setting(prof, c): return None
    y, seen = c.frozen[0], set()
    while True:
        pr = _threat_pred(c, y)
        if len(pr) != 1 or pr[0] in seen: break
        y = pr[0]; seen.add(y)
        if c.kind(y) == 'R': return False
    return True if seen else None

def st_iv_setting(prof, c):
    if c.completable or not c.pool_optimal or c.t: return None
    xs = [x for x in c.frozen if len(prof.R[x]) == 4]
    if not xs: return None
    return all(c.mult(x) <= 1 for x in xs)

def raises(c):
    """some pool move or exchange-cycle move (best pairs, every order) raises Phi'"""
    return any(c2.phi > c.phi for _, _, c2 in c.pool_moves()) or any(c2.phi > c.phi for _, c2 in c.cycle_moves())

def raises_ext(c):
    """... or a cycle move with any admissible pairs, or a re-partition of two free agents' pairs and the pool"""
    return raises(c) or any(c2.phi > c.phi for _, c2 in c.cycle_moves(general=True)) \
        or any(c2.phi > c.phi for _, c2 in c.two_agent_moves())

def raises_closure(c):
    """... or a cycle move (best pairs, any order) followed by the pool closure (every free agent re-optimizes its pair
    from the pool until none can)"""
    return raises_ext(c) or any(c2.pool_closure().phi > c.phi for _, c2 in c.cycle_moves()) \
        or any(c2.pool_closure().phi > c.phi for _, c2 in c.cycle_moves(general=True))

def st_local_closure(prof, c):
    if c.completable: return None
    return raises_closure(c)

def st_local_all(prof, c):
    if c.completable: return None
    return raises_closure(c) or any(c2.phi > c.phi for _, _, c2 in c.downgrade_swaps())

def st_local(prof, c):
    if c.completable: return None
    return raises(c)

def st_local_ext(prof, c):
    if c.completable: return None
    return raises_ext(c)

def st_pool_local(prof, c):
    if c.completable or c.pool_optimal: return None
    return raises(c)

def st_t_local(prof, c):
    if c.completable or c.t == 0: return None
    return raises(c)

def st_bt(prof, c):
    if c.completable or not c.frozen: return None     # without frozen agents #46's alternative (a label collision) applies
    return any(c.bigtop(x) for x in c.frozen)

def st_h7(prof, c):
    edges = [(o, x) for o, x in c.threat_edges if c.key[x] is not None]
    if not edges: return None
    return all(c.h7(x, o) != 'O' for o, x in edges)

def st_btcyc(prof, c):
    """#52 K4.HALL.BTCYC: success is a removal-only completable pre-allocation (Config.p_completable), as in #52"""
    if c.completable: return None
    X = [x for x in c.frozen if c.bigtop(x) and not c.robust(x)]
    if not X: return None
    return any(c2.p_completable for cyc, c2 in c.cycle_moves(general=True, keep=True) if any(x in cyc for x in X))

def _sig(c): return (c.key, tuple(sorted((y, tuple(sorted(q))) for y, q in c.Q.items())))

def reach(starts, swaps=True, cap=20000):
    """breadth-first search from the start configurations over exchange-cycle moves (any admissible pairs, receivers may
    keep part of their pair) and, if swaps, downgrade swaps; True if a configuration with a valid owner, or whose
    pre-allocation is removal-only completable, is reached,
    None if more than cap configurations are visited"""
    seen = {_sig(c) for c in starts}; front = list(starts)
    while front:
        nxt = []
        for c in front:
            if c.completable or c.p_completable: return True
            moves = [c2 for _, c2 in c.cycle_moves(general=True, keep=True)]
            if swaps: moves += [c2 for _, _, c2 in c.downgrade_swaps()]
            for c2 in moves:
                k = _sig(c2)
                if k not in seen:
                    seen.add(k); nxt.append(c2)
                    if len(seen) > cap: return None
        front = nxt
    return False

def st_reach(prof, cfgs):
    """from the Pareto-maxima, exchange cycles and downgrade swaps reach a configuration with a valid owner"""
    par = pareto(cfgs)
    if any(c._own_c for c in par): return True
    return reach(par, swaps=True)

def st_reach_cyc(prof, cfgs):
    par = pareto(cfgs)
    if any(c._own_c for c in par): return None
    return reach(par, swaps=False)

def st_reach_each(prof, c):
    """from this non-completable Pareto-maximal configuration, cycles and downgrade swaps reach a valid owner"""
    if c._own_c: return None
    return reach([c], swaps=True)

def st_reach_each_cyc(prof, c):
    if c._own_c: return None
    return reach([c], swaps=False)

def scope_noncompl_samen(prof, cfgs):
    """the configurations without a valid owner, each marked with whether some configuration with the same needed set
    has a larger Phi'"""
    out = [c for c in cfgs if not c._own_c]
    for c in out: c._samen = any(x._phi_c > c._phi_c and x.N == c.N for x in cfgs)
    return out

def st_simple_max(prof, cfgs):
    b = max(c._phi_c for c in cfgs)
    return any(c.simple for c in cfgs if c._phi_c == b)

STATEMENTS = {
    'PHI_PRIME': ('max', lambda p, c: c.completable,
                  "#41 Conjecture Phi' (K4.C4MIN.PHI): every Phi'-maximum has a valid owner"),
    'PHI_FIRST': ('max0', lambda p, c: c.completable,
                  "#41 section 4, the first form Phi = (-t, r, Lambda) (known false at n = 4): every maximum has a valid owner"),
    'MAX_SIMPLE': ('profile', st_simple_max,
                   "#41 section 4 (-U0): some Phi'-maximum has a valid owner with C empty (no withheld goods, no unfreezing)"),
    'I_POOLOPT': ('max', lambda p, c: c.pool_optimal,
                  "roadmap (i), first half: every Phi'-maximum is pool-optimal"),
    'I_T0': ('max', lambda p, c: c.t == 0,
             "roadmap (i), second half: every Phi'-maximum has t = 0"),
    'I_POOL_LOCAL': ('all', st_pool_local,
                     "(i) as a local lemma: a configuration without a valid owner that is not pool-optimal has a Phi'-raising pool or cycle move"),
    'I_T_LOCAL': ('all', st_t_local,
                  "(i) as a local lemma: a configuration without a valid owner with t > 0 has a Phi'-raising pool or cycle move"),
    'SIGMA_INJ': ('all', st_sigma_inj,
                  "f = 1 roadmap, first bullet: in its setting (f = 1, x 3-good, no valid owner, pool-optimal, t = 0) every agent is threatened by at most one owner"),
    'II_T0': ('all', st_ii_t0,
              "roadmap (ii): in that setting with x threatened, once no exchange-cycle move avoiding x raises Phi', some exchange-cycle move through x (best pairs or any pairs, e.g. the plain rotation) leaves t = 0"),
    'II_PHI': ('all', st_ii_phi,
               "roadmap (ii) with (iii): in the same setting, some exchange-cycle move through x raises Phi'"),
    'III_NO_R': ('all', st_iii,
                 "roadmap (iii): in that setting, the threat path into x has no free agent of kind (R)"),
    'IV_MAX': ('max', lambda p, c: all(c.mult(x) <= 1 for x in c.frozen),
               "roadmap (iv): at every Phi'-maximum each frozen agent is threatened by at most one owner"),
    'IV_SETTING': ('all', st_iv_setting,
                   "roadmap (iv) in the proof's setting: without a valid owner, pool-optimal, t = 0: a 4-good frozen agent is threatened by at most one owner"),
    'LOCAL': ('all', st_local,
              "#41 section 4, the local improvement lemma with pool moves and exchange-cycle moves (best pairs, every order of the receivers): every configuration without a valid owner has a Phi'-raising move"),
    'LOCAL_EXT': ('all', st_local_ext,
                  "the same with a larger catalogue: also cycle moves with any admissible pairs, and re-partitions of two free agents' pairs and the pool (contains #41's pool-assisted two-agent exchange)"),
    'LOCAL_CLOSURE': ('all', st_local_closure,
                      "the same catalogue plus cycle moves followed by the pool closure (every free agent re-takes its best pair from the pool, repeatedly)"),
    'LOCAL_ALL': ('all', st_local_all,
                  "the same catalogue plus #52's downgrade swaps"),
    'SAME_N': (scope_noncompl_samen, lambda p, c: c._samen,
               "needed for any move catalogue that keeps the needed set (pool, cycle, two-agent moves, downgrade swaps): at every configuration without a valid owner some configuration with the same needed set has a larger Phi'"),
    'BTCYC': ('pareto', st_btcyc,
              "#52 K4.HALL.BTCYC: at a Pareto-maximal configuration without a valid owner that has an exposed frozen big-top agent, some exchange-cycle move through it (any admissible pairs; threat receivers may keep part of their pair) has a valid owner"),
    'REACH': ('profile', st_reach,
              "the coordinator's question (b): from the Pareto-maximal configurations, exchange-cycle moves (any admissible pairs, receivers may keep part of their pair) and #52's downgrade swaps reach a configuration with a valid owner"),
    'REACH_CYC': ('profile', st_reach_cyc,
                  "the same without downgrade swaps, on the profiles where no Pareto-maximal configuration has a valid owner"),
    'REACH_EACH': ('pareto', st_reach_each,
                   "the per-start form: from each Pareto-maximal configuration without a valid owner, exchange-cycle moves and downgrade swaps reach one with a valid owner"),
    'REACH_EACH_CYC': ('pareto', st_reach_each_cyc,
                       "the per-start form without downgrade swaps"),
    'BT': ('pareto', st_bt,
           "#46 K4.HALL.BT in configuration form: a Pareto-maximal configuration without a valid owner has a frozen big-top agent"),
    'H7': ('pareto', st_h7,
           "#46 Lemma H7: at a Pareto-maximal configuration every threat on a frozen agent is global (G), owner at a chain end (G1) or local (L)"),
}

def main():
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in sys.argv[1:] if a.startswith('--'))
    cats = opt['catalog'].split(',') if 'catalog' in opt else DEFAULT
    K = int(opt['max-profiles']) if 'max-profiles' in opt else None
    print("command: python3 k4/gap_bench.py " + ' '.join(sys.argv[1:]), flush=True)
    print(f"gap.c sha256 {gap_run.SHA}" + ("" if 'profile' in opt or 'instances' in opt else f"; catalogs {[os.path.basename(c) for c in cats]}"), flush=True)
    if 'list' in opt:
        for k, (s, _, d) in STATEMENTS.items(): print(f"{k} [{s}]: {d}")
        return
    if 'profile' in opt:                       # one given profile: {"sets": [...], "vals": [...], "m": M}
        d = json.loads(opt['profile'])
        recs = [{'core': {'sets': d['sets'], 'm': d.get('m', 1 + max(g for S in d['sets'] for g in S)), 'file': 'given',
                          'pos': 0, 'idx': 0}, 'vals': d['vals'], 'prof': [0] * len(d['sets'])}]
        for r, head, cl in dump(recs):
            print(f"gap.c: in the gap {head is not None}" + (f"; f {head['f']}, omega {head['omega']}, keys {head['keys']}, "
                  f"{len(cl)} configurations, {sum(1 for c in cl if c['own'])} with a valid owner" if head else ''))
            for c in cl: print('  C ' + json.dumps(c))
        prof = gm.Profile(d['sets'], d['vals'], recs[0]['core']['m'])
        print(f"gap_model: in the gap {prof.in_gap}; f {prof.f}, omega {prof.omega}, keys {prof.keys}")
    else:
        recs = load(cats)
    if 'every' in opt: recs = recs[::int(opt['every'])]
    if K: recs = recs[:K]
    if 'instances' in opt:
        path = opt['instances'] if isinstance(opt['instances'], str) else INSTANCES
        names = opt['only'].split(',') if 'only' in opt else list(STATEMENTS)
        print(f"instance suite {os.path.basename(path)}: {len(json.load(open(path))['instances'])} instances")
        for nm in names:
            print(f"== {nm}: {STATEMENTS[nm][2]}", flush=True)
            check_instances(STATEMENTS[nm][1], STATEMENTS[nm][0], path)
        return
    if 'selftest' in opt:
        def dmp(r):
            for _, head, cl in dump([r]): return head, cl
        t0 = time.time(); bad = gm.selftest(recs, dmp)
        print(f"selftest: {len(recs)} profiles, gap.c and gap_model agree on the class, f, omega, keys and every configuration's "
              f"Phi', pool-optimality, owners (least |C|), threat edges and H7 classes: {bad} mismatches [{time.time() - t0:.0f} s]")
        return
    names = opt['only'].split(',') if 'only' in opt else list(STATEMENTS)
    t0 = time.time()
    results = check_many([(nm, STATEMENTS[nm][0], STATEMENTS[nm][1]) for nm in names], recs=recs)
    for nm, res in zip(names, results):
        print(f"== {STATEMENTS[nm][2]}")
        print(res.summary(int(opt.get('show', 2))), flush=True)
    print(f"[{time.time() - t0:.0f} s]")

if __name__ == '__main__':
    main()
