"""Reproduce the two failures of attempts/k4-lemmam-bt-single-bigtop.md (part 1) and
attempts/k4-lemmam-bt-one-first-agent.md (part 2), on PR #33's model (k4/c4_verify_H/lb4r.py).
Part 1, H_3 + q: q is the only big-top agent; Lemma K's classes of q, and LB4r(tau_q) with at most one rotation exactly
(encoding A). Part 2, HH_3: the core, Lemma K's classes and the exact test at the best first agent (x^A_{1,2}, index 3:
least deficit 4, then 1 after the best rotation), and at l_A. The full runs (every first agent, both encodings, k4/rulef.c)
are k4/lemmam_bt_runs.sh. Usage: python3 attempts/k4_lemmam_bt_attempts.py [1|2]"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'k4'))
import lemmam_bt_hh as H


def main():
    parts = sys.argv[1:] or ['1', '2']
    if '1' in parts:
        print('== part 1: H_3 + q, the unique big-top agent q = 13 first')
        H.core('Hq3')
        H.classes('Hq3', [13])
        H.exact('Hq3', 'A', [13])
    if '2' in parts:
        print('== part 2: HH_3, first agents x^A_{1,2} (3) and l_A (0)')
        H.core('HH3')
        H.classes('HH3', [3, 0])
        H.exact('HH3', 'A', [3])


if __name__ == '__main__':
    main()
