"""Lemma 1 (slot form of the one-absorber completion at serial-dictatorship picks) and its GDT-shaped restriction,
against the SAT test of k4/sdc/oc_absorb.extends_A and the raw brute force ohlib.absorb_brute (k4/oc1_hall.md §1).

For every order of every instance (n <= NMAX), at the picks Y:
  sat    = extends_A(E, picks, 1)                     (SAT on sdclib's EFX0 encoding)
  brute  = some absorber works in ohlib.absorb_brute  (raw definition, enumeration, no SAT; only if BRUTE=1)
  slot   = some o passes slot_test(P, o)              (Lemma 1)
  gdt    = some o outside F passes slot_test(P, o, frozen_slots=False)   (frozen agents take nothing, unfrozen owner)

    python3 k4/oc1_hall/slot_check.py special|screen|suite|logs|cores:FILES N SEED
"""
import sys, os, itertools, collections, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, absorb_brute, slot_test
from sdclib import Enc
from oc_absorb import extends_A
from min_frozen import load

NMAX = int(os.environ.get('NMAX', '5')); BRUTE = os.environ.get('BRUTE', '0') == '1'

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/oc1_hall/slot_check.py', *sys.argv[1:], '(BRUTE=%d)' % BRUTE, flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > NMAX: continue
        I = Inst(sets, vals, m, name); E = Enc(sets, vals, m); seen = set(); C['instances'] += 1
        for od in itertools.permutations(range(n)):
            Y = picks(I, od)
            if Y in seen: continue
            seen.add(Y); C['distinct starts'] += 1
            P = Picks(I, Y); base = base_of_picks(I, Y)
            sat = extends_A(E, base, 1)
            slot_owners = [o for o in range(n) if slot_test(P, o)]
            slot = bool(slot_owners)
            gdt_owners = [o for o in range(n) if o not in P.F and slot_test(P, o, frozen_slots=False)]
            gdt = bool(gdt_owners)
            C['sat yes'] += sat
            if sat != slot:
                C['MISMATCH sat/slot'] += 1
                print('MISMATCH sat/slot', name, json.dumps((sets, vals)), 'picks', Y, sat, slot, flush=True)
            if BRUTE:
                bo = absorb_brute(I, base)
                if bo != set(slot_owners):
                    C['MISMATCH brute/slot owners'] += 1
                    print('MISMATCH brute/slot', name, json.dumps((sets, vals)), 'picks', Y, sorted(bo), slot_owners, flush=True)
            if gdt and not sat: C['GDT-SHAPE YES BUT SAT NO (bug)'] += 1
            if sat and not gdt:
                C['sat yes, gdt shape no'] += 1
                frozen_own = any(o in P.F for o in slot_owners)
                # does a frozen agent need a slot, or a frozen owner?
                any_gdt_owner = any(slot_test(P, o, frozen_slots=False) for o in P.F)
                unf_owner_frozen_slot = any(o not in P.F for o in slot_owners)
                C['   ... an unfrozen owner works once frozen agents may take slots'] += unf_owner_frozen_slot
                C['   ... only frozen owners work'] += not unf_owner_frozen_slot
                C['   ... a frozen owner works with no frozen slots'] += any_gdt_owner
                if C['shown gap'] < 6:
                    C['shown gap'] += 1
                    print('GAP', name, json.dumps((sets, vals)), 'picks', Y, 'F', P.F, 'slot owners', slot_owners,
                          'witness', {o: slot_test(P, o, witness=True) for o in slot_owners[:2]}, flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
