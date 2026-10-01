"""The shape of every trapped repair (k* >= 3) in k4/dl2.c's dumps (compute/k4-dl2). EVIDENCE only.

  python3 k4/dl2_shapes.py OUT.jsonl.gz DUMP.jsonl.gz ...  [--jobs=J]

For every dumped profile with k* >= 3 and every min-frozen P in it at distance k(P) >= 3, everything is re-derived
from scratch with k4/suite/model.py (the suite's own implementation, not dl2.c): the min-frozen class, every deficit,
k(P) (a mismatch with dl2.c is reported and counted), and ALL repairs at the least distance: the min-frozen P' with
def(P') < def(P) whose bases differ from P's in exactly k(P) agents. For each repair:
  - flows: every good whose holder changes, as [good, from, to] with from/to an agent or "J" (the junk of P / P');
  - per changed agent: frozen in P / P' (F/f), gained and lost goods, and the labels
      unfreeze  frozen in P, free in P';            freeze  free in P, frozen in P';
      takeN     takes the base good of an agent frozen in P that it needed in P (a role-swap receiver);
      release   B'_i is a proper subset of B_i (it only gives goods up), with the number of goods released;
      rot       on a cycle of the transfer digraph (j -> i when i takes a good of B_j);
  - shape:
      SWAP+REL  some agent unfreezes and some agent takes its good (needing it); every changed agent is an
                unfreezing agent, a takeN receiver, or a release; the role-swap agents form need chains
                (receiver y of x's good g had g in N_y(P)); releases recorded with whether a released good is valued by
                a role-swap agent ("adjacent");
      ROT       no agent frozen in P or P' among the changed agents, and the transfer digraph on the changed agents
                is one directed cycle through all of them (a rotation along a cycle);
      ROT+REL   a rotation through some changed agents plus releases;
      OTHER     anything else (printed).
  - the exposures of P (owner, agent, class of k4/dl2.c) and its need edges (needer -> frozen agent).
Writes one JSON line per trapped P (with every repair) to OUT and prints the summary: per n, f and shape, how many
trapped P have SOME repair of each shape and how many have ALL repairs of it, and the role-swap chain lengths."""
import gzip, json, os, sys
from collections import Counter, defaultdict
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'suite'))
import model as M

INF = 10 ** 9


def bl(B): return sorted(M.bits(B))


def analyse(rec):
    sets, vals, m = rec['core']['sets'], rec['vals'], rec['core']['m']
    I = M.Inst(sets, vals, m); I.preallocs()
    n = I.n
    mp = [Bs for Bs, NA in I.minP]
    NAof = {Bs: NA for Bs, NA in I.minP}
    df = {Bs: (INF if (x := I.deficit(Bs)) is None else x) for Bs in mp}
    out = []
    for Prec in rec['P']:
        if Prec['k'] < 3 and Prec['k'] != -1: continue
        Bs = tuple(M.mask(B) for B in Prec['B'])
        if Bs not in df:
            out.append({'error': 'P not min-frozen in model.py', 'P': Prec['B']}); continue
        d0 = df[Bs]
        dist = lambda B2: sum(1 for a, b in zip(Bs, B2) if a != b)
        better = [B2 for B2 in mp if df[B2] < d0]
        k = min((dist(B2) for B2 in better), default=None)
        mism = (d0 if d0 < INF else -1) != Prec['def'] or (k if k is not None else -1) != Prec['k']
        NA = NAof[Bs]; N = [I.needs(i, Bs[i]) for i in range(n)]
        frozen = [M.pc(Bs[i]) == 1 and bool(Bs[i] & NA) for i in range(n)]
        used = 0
        for B in Bs: used |= B
        J = I.ALL & ~used
        needE = [[w, x] for x in range(n) if frozen[x] for w in range(n) if N[w] & Bs[x]]
        reps = []
        for B2 in better:
            if dist(B2) != k: continue
            NA2 = NAof[B2]; frozen2 = [M.pc(B2[i]) == 1 and bool(B2[i] & NA2) for i in range(n)]
            used2 = 0
            for B in B2: used2 |= B
            holder = lambda Bx, g: next((i for i in range(n) if Bx[i] >> g & 1), 'J')
            ch = [i for i in range(n) if Bs[i] != B2[i]]
            flows = []
            for g in range(m):
                a, b = holder(Bs, g), holder(B2, g)
                if a != b: flows.append([g, a, b])
            T = defaultdict(set)                 # transfer digraph j -> i
            for g, a, b in flows:
                if a != 'J' and b != 'J': T[a].add(b)
            agents = {}
            for i in ch:
                gain = bl(B2[i] & ~Bs[i]); lost = bl(Bs[i] & ~B2[i])
                lab = []
                if frozen[i] and not frozen2[i]: lab.append('unfreeze')
                if frozen2[i] and not frozen[i]: lab.append('freeze')
                if any(frozen[x] and Bs[x] & B2[i] and N[i] & Bs[x] for x in range(n) if x != i): lab.append('takeN')
                if B2[i] & ~Bs[i] == 0 and Bs[i] != B2[i]: lab.append('release%d' % len(lost))
                agents[i] = {'B': bl(Bs[i]), 'B2': bl(B2[i]), 'F': ('F' if frozen[i] else 'f') + '>' + ('F' if frozen2[i] else 'f'),
                             'gain': [[g, holder(Bs, g)] for g in gain], 'lost': [[g, holder(B2, g)] for g in lost], 'lab': lab}
            # cycles of T among changed agents
            def on_cycle(i):
                seen, stack = set(), [i]
                while stack:
                    u = stack.pop()
                    for w in T.get(u, ()):
                        if w == i: return True
                        if w not in seen: seen.add(w); stack.append(w)
                return False
            for i in ch:
                if on_cycle(i): agents[i]['lab'].append('rot')
            swap_ag = [i for i in ch if 'unfreeze' in agents[i]['lab'] or 'takeN' in agents[i]['lab']]
            rel_ag = [i for i in ch if any(l.startswith('release') for l in agents[i]['lab'])]
            rot_ag = [i for i in ch if 'rot' in agents[i]['lab']]
            has_unf = any('unfreeze' in agents[i]['lab'] for i in ch)
            has_take = any('takeN' in agents[i]['lab'] for i in ch)
            if has_unf and has_take and all(i in swap_ag or i in rel_ag for i in ch):
                shape = 'SWAP+REL' if rel_ag else 'SWAP'
            elif rot_ag and not any(frozen[i] or frozen2[i] for i in ch) and len(rot_ag) == len(ch) and \
                    all(len(T.get(i, ())) == 1 for i in ch):
                shape = 'ROT'
            elif rot_ag and all(i in rot_ag or i in rel_ag for i in ch) and not any(frozen[i] or frozen2[i] for i in rot_ag):
                shape = 'ROT+REL'
            else:
                shape = 'OTHER'
            # role-swap chain length: the agents that unfreeze or take a needed frozen good
            adj = []
            for i in rel_ag:
                relg = Bs[i] & ~B2[i]
                adj.append(any(relg & I.R[j] for j in swap_ag + rot_ag if j != i))
            reps.append({'B2': [bl(B) for B in B2], 'def2': df[B2], 'changed': ch, 'flows': flows, 'agents': agents,
                         'shape': shape, 'swap': swap_ag, 'release': rel_ag, 'rot': rot_ag, 'release_adjacent': adj})
        exp = Prec.get('exp', [])
        out.append({'core': rec['core'], 'vals': vals, 'prof': rec.get('prof'), 'n': n, 'm': m, 'f': I.f, 'omega': I.omega,
                    'P': Prec['B'], 'J': bl(J), 'def': d0 if d0 < INF else -1, 'k': k, 'nn': Prec.get('nn'), 'pm': Prec.get('pm'),
                    'sig': Prec.get('sig'), 'exp': exp, 'need': needE, 'frozen': [i for i in range(n) if frozen[i]],
                    'nrep': len(reps), 'shapes': sorted(set(r['shape'] for r in reps)), 'repairs': reps, 'mismatch': mism})
    return out


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[1:] if a.startswith('--') and '=' in a)
    out, dumps = args[0], args[1:]
    print('# command: python3 k4/dl2_shapes.py ' + ' '.join(sys.argv[1:]), flush=True)
    recs, seen = [], set()
    for fn in dumps:
        for l in gzip.open(fn, 'rt'):
            r = json.loads(l)
            if r['kstar'] < 3 and r['kstar'] != -1: continue
            key = (json.dumps(r['core']['sets']), json.dumps(r['vals']))
            if key in seen: continue             # a resumed run may have written a record twice
            seen.add(key); recs.append(r)
    print(f'profiles with k* >= 3 in the dumps: {len(recs)}', flush=True)
    some, every = Counter(), Counter(); nP = Counter(); mism = 0; chains = Counter(); per_inst = Counter(); kk = Counter()
    other_ex = []
    with gzip.open(out, 'wt') as fo, Pool(int(opt.get('jobs', 2))) as pool:
        for res in pool.imap(analyse, recs, chunksize=4):
            for t in res:
                if 'error' in t: print('ERROR', t); mism += 1; continue
                fo.write(json.dumps(t, separators=(',', ':')) + '\n')
                key = (t['n'], t['f'])
                nP[key] += 1; kk[(t['n'], t['k'])] += 1
                mism += t['mismatch']
                for s in t['shapes']: some[key + (s,)] += 1
                if len(t['shapes']) == 1: every[key + (t['shapes'][0],)] += 1
                for r in t['repairs']:
                    if r['shape'].startswith('SWAP'): chains[(t['n'], len(r['swap']), len(r['release']))] += 1
                if t['shapes'] == ['OTHER'] and len(other_ex) < 5: other_ex.append(t)
    print(f'trapped P (distance >= 3): {sum(nP.values())}; mismatches with dl2.c (def or k): {mism}')
    print('by (n, k): ' + ', '.join(f'n={a} k={b}: {c}' for (a, b), c in sorted(kk.items())))
    print('\n| n | f | trapped P | shape | P with some repair of this shape | P with every repair of this shape |')
    print('|---|---|---|---|---|---|')
    for key in sorted(nP):
        for s in ['SWAP', 'SWAP+REL', 'ROT', 'ROT+REL', 'OTHER']:
            if some[key + (s,)]:
                print(f'| {key[0]} | {key[1]} | {nP[key]} | {s} | {some[key + (s,)]} | {every[key + (s,)]} |')
    print('\nrole-swap repairs: (n, agents in the swap, releasing agents): count of repairs')
    for key, c in sorted(chains.items()): print(f'  n={key[0]} swap={key[1]} release={key[2]}: {c}')
    for t in other_ex:
        print('\nOTHER example:', json.dumps({k: t[k] for k in ('core', 'vals', 'P', 'J', 'def', 'k', 'exp', 'need', 'frozen')}))
        for r in t['repairs'][:3]: print('   repair', json.dumps({k: r[k] for k in ('B2', 'def2', 'flows', 'agents')}))


if __name__ == '__main__':
    main()
