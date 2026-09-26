#!/usr/bin/env python3
"""Replay of attempts/k4-c4min-w0-owner-base.md: C4min with the owner's needs taken from its base instead of its bundle
fails on a pure n = 4, m = 8 core; C4min as stated (needs from the bundle) holds there. Checked by the brute force
k4/c4min_brute.py, by k4/c4min_hunt.c -1 and by k4/c4x.c -1s -R -a (PR #36), each with and without -w0.
usage: python3 attempts/k4_c4min_w0_replay.py"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'k4'))
import c4min_brute as B
import c4min_common as cc

INSTANCES = [
    # (name, sets, values per agent in the order of its set)
    ('pure n = 4, m = 8 (core 120 of results/k4_certs_4_pure.json.gz)',
     [[0, 2, 4, 6], [0, 2, 5, 6], [1, 3, 4, 7], [1, 3, 5, 7]], [(2, 3, 8, 4), (2, 3, 8, 4), (2, 3, 8, 4), (2, 3, 8, 4)]),
    ('pure n = 4, m = 11 (core 217)',
     [[3, 6, 7, 8], [0, 2, 6, 10], [1, 5, 9, 10], [4, 7, 8, 9]], [(2, 8, 3, 4), (2, 3, 8, 4), (3, 4, 8, 2), (2, 3, 4, 8)]),
]


def main():
    ok = True
    for name, sets, values in INSTANCES:
        m = 1 + max(max(S) for S in sets)
        vals = [dict(zip(S, v)) for S, v in zip(sets, values)]
        assert cc.is_core(len(sets), m, sets, True)[0]
        for base in (True, False):
            b = B.brute(sets, vals, m, base=base)
            h = cc.hunt_one(sets, m, vals, ['-w0'] if base else [])
            x = cc.c4x_one(sets, m, vals, ['-w0'] if base else [])
            agree = all(b[k] == h[k] == x[k] for k in ('fstar', 'dstar', 'minfrozen', 'good')) and b['completable'] == h['completable']
            want = (b['dstar'] > 0 and b['completable'] == 0) if base else b['dstar'] <= 0
            print(f'{name}, owner needs from {"base  " if base else "bundle"}: f* {b["fstar"]} sigma {b["sigma"]} d* {b["dstar"]} '
                  f'min-frozen {b["minfrozen"]} with deficit <= 0: {b["good"]}; some min-frozen P completable: {b["completable"]}; '
                  f'three implementations {"agree" if agree else "DISAGREE"}')
            ok &= agree and want
    print('ALL CONFIRMED' if ok else 'NOT CONFIRMED')


if __name__ == '__main__':
    main()
