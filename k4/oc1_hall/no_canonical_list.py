"""The configurations a proof of the chain lemma must handle beyond canonical chains (coordinator's step 3;
k4/oc1_hall.md §13): hard starts (no S* completion at the picks) on which no canonical chain from a dangerous agent
(k4/oc1_hall/greedy_rules.py: middle agents want their predecessor's pick, take no junk; any improving H_0; owner k
or the end) repairs.  Deduplicated over all data sets; for each, the repairing chains that do exist (every
description), with the features: middle junk, a middle agent that does not want its predecessor's good alone, the
owner's role.  Writes results/k4_oc1_hall/no_canonical.json.

    python3 k4/oc1_hall/no_canonical_list.py
"""
import sys, os, itertools, collections, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, bundles_of
from chain_shapes import s_star_owners
from greedy_rules import canonical_paths, apply_chain
from sdclib import Enc
from min_frozen import load
import de_free as DF
DF.CHAIN_ONLY = True
SRCS = [('special', []), ('screen', []), ('suite', []), ('logs', []),
        ('cores:k4_certs_2.json.gz,k4_certs_3.json.gz', ['3000', '91']),
        ('cores:k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz', ['1500', '92']),
        ('cores:k4_certs_5_n4_1.json.gz,k4_certs_5_n4_2.json.gz', ['150', '93'])]

if __name__ == '__main__':
    out = {}; C = collections.Counter()
    for src, extra in SRCS:
        for name, sets, vals, m in load(src, ['x', src] + extra):
            n = len(sets)
            if n > 5: continue
            I = Inst(sets, vals, m, name); E = Enc(sets, vals, m); seen = set()
            for od in itertools.permutations(range(n)):
                Y = picks(I, od)
                if Y in seen: continue
                seen.add(Y); base = base_of_picks(I, Y)
                key = json.dumps((sets, vals, Y))
                if key in out or s_star_owners(I, base): continue
                P = Picks(I, Y); ok = False
                for k in P.D:
                    for path in canonical_paths(I, P, k):
                        xt = path[-1]
                        pool = [g for g in P.J if g in I.R[k]] + ([Y[xt]] if Y[xt] is not None and Y[xt] in I.R[k] else [])
                        for r in range(1, len(pool) + 1):
                            for H0 in itertools.combinations(pool, r):
                                if I.val(k, H0) <= P.pv[k]: continue
                                ow = s_star_owners(I, apply_chain(I, P, base, path, H0))
                                if k in ow or xt in ow: ok = True; break
                            if ok: break
                        if ok: break
                    if ok: break
                if ok: continue
                B = bundles_of(I, base); reps = []
                for b2, ds in DF.moves(E, base, describe=True, all_desc=True).items():
                    ow = s_star_owners(I, b2)
                    if not ow: continue
                    for kind, path, H in ds:
                        mid = [i for i in range(1, len(path)) if H.get(i)]
                        nowant = [i for i in range(1, len(path)) if not (B[path[i - 1]] and I.v[path[i]].get(B[path[i - 1]][0], 0) > P.pv[path[i]])]
                        reps.append({'chain': list(path), 'H': {str(a): list(b) for a, b in H.items() if b},
                                     'middle junk at': mid, 'middle agents not wanting the good alone': nowant,
                                     'x0 dangerous': path[0] in P.D, 'owners': ow})
                out[key] = {'source': src, 'name': name, 'n': n, 'm': m, 'sets': sets, 'vals': vals, 'order': list(od),
                            'picks': list(Y), 'frozen': P.F, 'dangerous': P.D, 'repairs': reps}
                C['configurations'] += 1; C['n = %d' % n] += 1
                C['repaired with middle junk'] += any(r['middle junk at'] for r in reps)
                C['repaired by a chain from D whose middle agent does not want its good alone'] += any(r['middle agents not wanting the good alone'] and r['x0 dangerous'] for r in reps)
    path = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), 'results', 'k4_oc1_hall', 'no_canonical.json')
    json.dump(sorted(out.values(), key=lambda d: (d['n'], d['m'])), open(path, 'w'), indent=1)
    for k in sorted(C): print(k, C[k])
    sm = min(out.values(), key=lambda d: (d['n'], d['m']))
    print('smallest:', sm['name'], sm['n'], sm['m'], json.dumps((sm['sets'], sm['vals'])), 'picks', sm['picks'])
