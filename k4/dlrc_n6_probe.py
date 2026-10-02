#!/usr/bin/env python3
"""Probe (compute/k4-rc): how often do the n = 6 cores of results/k4_certs_6_n4_1.json.gz have def > 0 states with
f >= 1? Per m: up to 30 random cores (all if fewer), 300 random strict profiles each, evaluated with k4/dlrc.c -H; prints
the distribution of f (-1: omega <= 0, not evaluated) and the number of def > 0 states with f >= 1. EVIDENCE only.
usage: python3 k4/dlrc_n6_probe.py"""
import collections, gzip, json, os, random, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dlrc_hunt as H
print('# command: python3 k4/dlrc_n6_probe.py; dlrc.c sha256 ' + H.SHA, flush=True)
H.build()
cores = json.load(gzip.open(os.path.join(os.path.dirname(H.HERE), 'results', 'k4_certs_6_n4_1.json.gz'), 'rt'))['cores']
rng = random.Random(3)
by_m = collections.defaultdict(list)
for k, c in enumerate(cores): by_m[c['m']].append(k)
for m in sorted(by_m):
    ks = by_m[m] if len(by_m[m]) <= 30 else rng.sample(by_m[m], 30)
    fc = collections.Counter(); st = 0; npro = 0
    for k in ks:
        c = cores[k]; core = H.mk_core(c['sets'], c['m'], str(k))
        profs = [[rng.randrange(len(D)) for D in core['doms']] for _ in range(300)]
        hs, _ = H.evaluate(core, profs)
        for h in hs: fc[h['f']] += 1; st += h['st1']; npro += 1
    print('m %d: %d cores, %d probed, %d profiles; f distribution %s; def > 0 states with f >= 1: %d'
          % (m, len(by_m[m]), len(ks), npro, dict(sorted(fc.items())), st), flush=True)
