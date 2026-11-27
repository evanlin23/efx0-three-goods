"""ROUND-IND: which round-choice rule never gets stuck? (k4/oc1max_multi.md §18)

At every start (two-move starts of a file), for every order, every admissible first round of round_e.admissible_rounds
(E-prefix chains, |K| <= 2, (H), (L*), (P2), (P3), SD-E(round)) is classified:
  - P1-free round (every settled k values each good outside T_k at most v_k(T_k)): SAFE if the resulting state is still
    repairable (round_e.search with P1FREE semantics, RMAX - 1 more rounds, completion at once);
  - P1 round: SAFE if the resulting state completes at once (it must be the final round).
The candidate rules, weakest first:
  (G0) some admissible round is safe;                          [existence; ROUND-IND as an existential statement]
  (G1) every P1-free admissible round is safe;                  [greedy over P1-free rounds never dead-ends]
  (G2) if no P1-free round is admissible, some P1 round completes at once.
  (G1') as (G1) for rounds of one settlement only.
Counts per start; the smallest start violating each rule.

    RMAX=2 python3 k4/oc1max_multi/round_safe.py ROWS.jsonl[.gz] | EXPORT.json.gz [...]
"""
import sys, os, json, gzip, collections, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
os.environ['P1FREE'] = '1'
from mmlib import Inst, base_from_picks
import round_e
from round_e import admissible_rounds, search, completes

RMAX = int(os.environ.get('RMAX', '2'))


def study(rec):
    I = Inst(rec['sets'], rec['vals']); b = base_from_picks(tuple(rec['picks'])); C = collections.Counter()
    some_safe = False; all_p1free_safe = True; all_single_safe = True; any_p1free = False; p1_completes = False
    for o in (rec.get('orders') or [rec['order']]):
        for p1, I2, b2, o2, ag2, go2, f2, rnd in admissible_rounds(I, I, b, list(o), list(range(I.n)), list(range(I.m)), {}, C):
            if p1:
                ok = completes(I, I2, b2, ag2, go2, f2) is not None
                C['P1 rounds'] += 1; C['P1 rounds completing at once'] += ok; p1_completes |= ok
            else:
                any_p1free = True
                ok = completes(I, I2, b2, ag2, go2, f2) is not None or search(I, I2, b2, o2, ag2, go2, f2, RMAX - 1, C) is not None
                C['P1-free rounds'] += 1; C['P1-free rounds safe'] += ok
                if not ok:
                    all_p1free_safe = False
                    if len(rnd['settled']) == 1: all_single_safe = False
            some_safe |= ok
    return C, {'G0 some round safe': some_safe, 'G1 every P1-free round safe': all_p1free_safe,
               "G1' every single P1-free round safe": all_single_safe,
               'G2 (if no P1-free round) some P1 round completes': any_p1free or p1_completes,
               'has a P1-free round': any_p1free}


def rows_of(fn):
    if fn.endswith('.json.gz'):
        d = json.load(gzip.open(fn))
        return [{'list': hg.get('list'), 'm': hg.get('m'), 'idx': hg.get('idx'), 'sets': hg['sets'], 'vals': s0['vals'],
                 'picks': s0['picks'], 'orders': s0['orders']} for hg in d['hypergraphs'] for s0 in hg['starts']]
    return [json.loads(l) for l in (gzip.open(fn, 'rt') if fn.endswith('.gz') else open(fn))]


if __name__ == '__main__':
    print('$ RMAX=%d python3 k4/oc1max_multi/round_safe.py' % RMAX, *sys.argv[1:])
    for fn in sys.argv[1:]:
        rows = rows_of(fn); T = collections.Counter(); R = collections.Counter(); ex = {}
        with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
            for (C, flags), row in zip(pool.imap(study, rows, chunksize=16), rows):
                T.update(C); R['starts'] += 1
                for k, v in flags.items():
                    R[k] += v
                    if not v and k not in ex: ex[k] = (row.get('list'), row.get('m'), row.get('idx'), row['picks'])
        print('==', fn); print('  rounds:', dict(T)); print('  rules (starts satisfying):', dict(R))
        for k, v in ex.items(): print('  first violation of [%s]:' % k, v)
