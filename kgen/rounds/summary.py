"""Aggregate the climb logs of results/kgen_rounds/ (kgen/rounds.md §2-§4): per log family, climb rounds run, final
objective values, and the distinct one-round failures (FAIL lines) by (n, m).
    python3 kgen/rounds/summary.py"""
import os, re, json, glob, collections
R = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'results', 'kgen_rounds')
fam = collections.OrderedDict([
    ('campaign1 (ROUND+ climbs, counts only first)', 'campaign1_climb_*.log'),
    ('campaign2 (ROUND+, margin)', 'climb_n*.log'),
    ('campaign3 ROUND+ (n = 4, m = 8-12; n = 5, m = 8-10)', 'c3_rnd1_*.log'),
    ('campaign3 ROUND-X', 'c3_rndx_*.log'),
    ('twins (one or two identical pairs)', 'twins*.log'),
    ('small m (n = 4, m = 5, 6)', 'small_n4m*.log'),
    ('eps-lift KEPS = 4, 5', 'keps*.log'),
    ('eps-lift KEPS = 4, every good covered', 'kcover4_*.log'),
    ('eps-lift KEPS = 4, cores', 'kcore4_*.log'),
    ("eps-lift KEPS = 4, Lemma RED's I' shape", 'iprime_*.log'),
    ('three rounds, exact two-round count (climb3)', 'c4_3r_*.log'),
    ('three rounds, phased with margins (climb3)', 'c5_3r_*.log'),
    ('eps-lift KEPS = 4, cores, round 2', 'kcoreB_*.log'),
    ('k = 4 cores with zeros, OC1 (zclimb)', 'zcore_*.log'),
    ("k = 4 cores with zeros, OC1' (zclimb ZCLASS=OC1P)", 'oc1p_n*.log'),
    ("positive values, OC1' (zclimb ZFREE=1)", 'oc1p_pos_n*.log'),
])
for name, pat in fam.items():
    files = sorted(glob.glob(os.path.join(R, pat)))
    rounds = 0; fails = set(); bynm = collections.Counter(); cand = 0
    for f in files:
        for line in open(f):
            if line.startswith('round'): rounds += 1
            if line.startswith('FAIL') or line.startswith('ZFAIL'):
                mm = re.search(r'vals (\[\[.*?\]\]) picks (\[[^\]]*\])', line)
                if mm:
                    V = json.loads(mm.group(1)); key = mm.group(1) + mm.group(2)
                    if key not in fails: fails.add(key); bynm[(len(V), len(V[0]))] += 1
            if line.startswith('CAND3'): cand += 1
    print('%-55s logs %3d  climb rounds %5d  distinct failing starts %3d %s%s' % (
        name, len(files), rounds, len(fails), dict(sorted(bynm.items())), ('  CAND3 %d' % cand) if 'three' in name else ''))
