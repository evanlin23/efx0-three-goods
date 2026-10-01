"""The counting gap of Lemma K (k4/rulef.md §2, Remark 5): profiles on which some first agent's run of LB4r succeeds
without rotation although no first agent is in class K0. Reads the DATA lines of `k4/rulef.c -A40 -C3 -r1 -Y1 -D4`
(every first agent has Lemma K deficit > 0; min=0: some first agent needs no rotation) and, on PR #33's independent
model (k4/c4_verify_H/lb4r.py), for every first agent a and every upgrade policy (need-shrinking, envy-free, none):

  dK   Lemma K's deficit (k4/rulef_model.py, kept-out sets with goods outside R_x)
  dK'  the deficit of Lemma K' (Remark 5: an agent may take a slot good and keep a set out at once)
  out  LB4r's exact owner test at the state (lb4r.any_output, owner's needs from the bundle)

and checks the exactness claim of Remark 5 on these states: dK' <= 0 exactly when the exact test finds an output
(Lemma K' allows one slot good per agent; the remark allows up to cap(x)). Every dK' <= 0 completion is built and
checked with lb4r.output_check and the raw EFX0 definition.
Usage: python3 k4/rulef_gap.py DATAFILE [--max=N]"""
import os, re, json, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import rulef_model as RM
M = RM.M
POLS = ('shrink', 'envyFree', 'none')


def main():
    args = sys.argv[1:]
    mx = next((int(a.split('=')[1]) for a in args if a.startswith('--max=')), 10 ** 9)
    path = next(a for a in args if not a.startswith('--'))
    RM.XKEEP = True
    prof = closedK = closedKp = mism = wfail = 0
    pol_used = {p: 0 for p in POLS}
    for line in open(path):
        if not line.startswith('DATA') or ' min=0 ' not in line:
            continue
        if prof >= mx:
            break
        prof += 1
        sets = json.loads(re.search(r'sets=(\[\[.*?\]\])', line).group(1))
        vals = json.loads(re.search(r'vals=(\[\[.*?\]\])', line).group(1))
        inst = RM.make_inst(sets, vals)
        bestK = bestKp = RM.INF
        rows = []
        for a in range(inst.n):
            for pol in POLS:
                s, _ = RM.run_state(inst, a, pol)
                RM.COMBO = False
                dK = RM.deficit_K(inst, s)
                RM.COMBO = True
                dKp = RM.deficit_K(inst, s)
                out = M.any_output(inst, s, 'bundle')
                if (dKp <= 0) != bool(out):
                    mism += 1
                if dKp <= 0:
                    o, X = RM.witness_K(inst, s)
                    if not (M.output_check(inst, s, o, X, 'bundle') and RM.check_efx0(inst, X)):
                        wfail += 1
                    pol_used[pol] += 1
                RM.COMBO = False
                bestK, bestKp = min(bestK, dK), min(bestKp, dKp)
                rows.append(f"{a}/{pol[0]}:{dK},{dKp},{out}")
        closedK += bestK <= 0
        closedKp += bestKp <= 0
        print(f"sets={sets} vals={vals} " + ' '.join(rows), flush=True)
    print(f"{path}: gap profiles {prof}; some (a, policy) with Lemma K deficit <= 0: {closedK}; with Lemma K' deficit "
          f"<= 0: {closedKp}; states where Lemma K' and the exact owner test disagree: {mism}; completions failing: "
          f"{wfail}; Lemma K' certificates by policy: {pol_used}")


if __name__ == '__main__':
    main()
