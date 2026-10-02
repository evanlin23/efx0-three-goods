"""Replays the smallest failing configurations of attempts/k4-lemmam-x-exchange.md and
attempts/k4-lemmam-x-local-forms.md (workstream proof/k4-lemmam-x, k4/lemmam_x.md), one worker, about a minute.
Each line prints the claim, what the tools compute, and OK / FAIL. Usage: python3 attempts/k4_lemmam_x_attempts.py"""
import json, os, re, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, 'k4'))
import adaptive_run as AR
import lemmam_x_run as LR
import lemmam_x_check as C
import lemmam_x_inst as INST

ok_all = True


def report(name, cond, detail):
    global ok_all
    ok_all &= bool(cond)
    print(f"{'OK  ' if cond else 'FAIL'} {name}: {detail}", flush=True)


def c_lines(sets, vals, opts):
    return LR.run(AR.encode_profile(sets, vals), opts + ['-T1'])


def main():
    LR.build()
    print('# k4_lemmam_x_attempts.py; lemmam_x.c sha256', LR.SHA, flush=True)
    # (x1), (x2): n = 3, m = 6; both implementations
    S, V = [[0, 1, 4, 5], [2, 3, 4, 5], [2, 3, 4, 5]], [[1, 4, 6, 8], [2, 3, 4, 8], [2, 7, 8, 4]]
    inst = C.RM.make_inst(S, V)
    cls = [C.klass(inst, a) for a in range(3)]
    cands = {a: C.candidates(inst, a)[0] for a in (0, 2)}
    nb = {a: C.shape(inst, a)[0] for a in (0, 2)}
    report('(x1), (x2) at n = 3, m = 6 (model)', cls == [2, 1, 2] and all(cls[cands[a]['EF4_minidx']] == 2 for a in (0, 2))
           and all(nb[a] == 1 for a in (0, 2)),
           f"classes {cls} (0 K0, 1 K1, 2 bad); EF4 of the bad agents {[cands[a]['EF4_minidx'] for a in (0, 2)]} is bad;"
           f" their runs are single blocks {nb}, so the leader of r's block is a")
    cl = next(l for l in c_lines(S, V, ['-A43', '-r1', '-Y1', '-D43']) if l.startswith('BAD'))
    report('(x1), (x2) at n = 3, m = 6 (lemmam_x.c)', 'cls=212' in cl, re.search(r'cls=\d+', cl).group(0))
    # (x4): H_4, first agent 0, r = 16, both bad in the model
    s4, v4, _ = INST.build('H4')
    i4 = C.RM.make_inst(s4, v4)
    k0, k16 = C.klass(i4, 0), C.klass(i4, 16)
    r0 = C.candidates(i4, 0)[0]['r']
    report('(x4) on H_4 (model)', k0 == 2 and r0 == 16 and k16 == 2, f"class of 0: {k0}, r of its run: {r0}, class of r: {k16}")
    # (L0): n = 3, m = 6, every first block has count 1 (the greedy's first count is the least over first blocks)
    S0, V0 = [[0, 2, 4, 5], [1, 3, 5], [2, 3, 4, 5]], [[3, 5, 7, 6], [2, 3, 4], [4, 2, 8, 3]]
    for g in ([], ['-G1']):
        run = next(l for l in c_lines(S0, V0, ['-A44', '-Y1', '-r1', '-D47'] + g) if l.startswith(('ADPRUN', 'ADPBAD')))
        dl = list(map(int, re.search(r'deltas=(\S+)', run).group(1).split(',')))
        tau = re.search(r'tau=(\S+)', run).group(1)
        report(f"(L0) at n = 3, m = 6 {'slot count' if g else 'chain-end count'}", dl[0] >= 1,
               f"least count over the first blocks {dl[0]} (greedy tau {tau})")
    # the greedy rule needs two rotations: n = 3, m = 6; both implementations
    S2, V2 = [[0, 1, 4, 5], [2, 3, 4, 5], [2, 3, 4, 5]], [[1, 4, 6, 8], [3, 5, 7, 6], [2, 3, 4, 8]]
    run = next(l for l in c_lines(S2, V2, ['-A44', '-Y1', '-r1', '-D47']) if l.startswith(('ADPRUN', 'ADPBAD')))
    d = int(re.search(r' d=(\d+)', run).group(1))
    ids = list(map(int, re.search(r'tau=(\S+)', run).group(1).split(',')))
    dm = C.seq_d(C.RM.make_inst(S2, V2), ids)
    report('greedy rule, two rotations at n = 3, m = 6', d == 2 and dm == 2,
           f"tau {ids}: lemmam_x.c d = {d} (2 = more than the cap 1), model d = {dm}")
    # (L1∃): no sequence of count-0 non-last blocks; chain-end count n = 4, m = 6; slot count: its smallest instance
    S3, V3 = [[0, 2, 5], [0, 3, 4, 5], [1, 2, 4, 5], [1, 3, 5]], [[2, 4, 3], [5, 2, 8, 4], [5, 2, 8, 4], [2, 4, 3]]
    h = next(l for l in c_lines(S3, V3, ['-A46', '-Y1', '-r1']) if l.startswith('L46 hist')).split()[2:]
    hg = next(l for l in c_lines(S3, V3, ['-A46', '-Y1', '-r1', '-G1']) if l.startswith('L46 hist')).split()[2:]
    report('(L1∃) chain-end count at n = 4, m = 6', h == ['0', '0', '0', '1'] and hg == ['1', '0', '0', '0'],
           f"L46 hist {h} (last: no sequence); with the slot count {hg}")
    S4, V4 = SLOTSMALL
    hs = next(l for l in c_lines(S4, V4, ['-A46', '-Y1', '-r1', '-G1']) if l.startswith('L46 hist')).split()[2:]
    run = next(l for l in c_lines(S4, V4, ['-A44', '-Y1', '-r1', '-G1', '-D47']) if l.startswith(('ADPRUN', 'ADPBAD')))
    tau = re.search(r'tau=.*', run).group(0)
    dd = re.search(r' d=(\d+)', run).group(1)
    report('(L1∃) slot count, smallest', hs == ['0', '0', '0', '1'], f"L46 hist {hs}; the greedy run: {tau}, d = {dd}")
    print('ALL OK' if ok_all else 'SOME FAILED', flush=True)
    sys.exit(0 if ok_all else 1)


SLOTSMALL = ([[0, 2, 3, 4], [1, 3, 5, 6], [2, 5, 6], [4, 5, 6]], [[6, 3, 7, 5], [6, 7, 3, 5], [4, 2, 3], [4, 2, 3]])

if __name__ == '__main__':
    main()
