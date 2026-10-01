#!/usr/bin/env python3
"""The key-graph runs of k4/sx.md (workstream proof/k4-sx): k4/sx_keygraph.py over #53's catalogues in chunks of
CHUNK records, one process at a time, resumable (a chunk whose log ends with '# time' is skipped). Logs and dumps go to
results/k4_sx/chunks/; `python3 k4/sx_runs.py --sum` adds up the counters per input into results/k4_sx/keys_summary.md.

Inputs: #53's catalogues at 245040b (k4/strategy.md §4):
  mkdir -p k4/suite/.cache/gapbench && git archive 245040b results/k4_gap | tar -x -C k4/suite/.cache/gapbench
usage: python3 k4/sx_runs.py [NAME ...]      (default: every input below, in order)
       python3 k4/sx_runs.py --sum"""
import collections, glob, gzip, json, os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
C = 'k4/suite/.cache/gapbench/results/k4_gap'
OUT = 'results/k4_sx/chunks'
CHUNK = 4000
INPUTS = ['gap_n3', 'gap_n4_1', 'hunt_n4_2_all', 'gap_n4_2_s4000', 'gap_n4_3_s4000', 'hunt_n4_3_s400k',
          'gap_n4_pure_s4000', 'hunt_n4_pure_s400k', 'hard_hunt',
          'gap_n5_1_s100', 'gap_n5_2_s100', 'hunt_n5_3_s2000', 'hunt_n5_4_s2000', 'hunt_n5_pure_s2000']


def nrec(name):
    return len(json.load(gzip.open(os.path.join(ROOT, C, name + '.json.gz'), 'rt'))['records'])


def done(log):
    return os.path.exists(log) and any(l.startswith('# time') for l in open(log))


def run(name):
    n = nrec(name)
    for i, s in enumerate(range(0, n, CHUNK)):
        base = os.path.join(OUT, '%s_c%03d' % (name, i))
        if done(os.path.join(ROOT, base + '.log')): continue
        cmd = ['python3', 'k4/sx_keygraph.py', 'catalog', '%s/%s.json.gz' % (C, name), '--fmin=1',
               '--start=%d' % s, '--max=%d' % CHUNK, '--dump=%s.jsonl.gz' % base]
        with open(os.path.join(ROOT, base + '.log'), 'w') as fo:
            subprocess.run(cmd, cwd=ROOT, stdout=fo, stderr=subprocess.STDOUT, check=True)
        print('done', base, flush=True)


def summarize():
    per = collections.defaultdict(collections.Counter); fails = collections.defaultdict(list)
    for log in sorted(glob.glob(os.path.join(ROOT, OUT, '*.log'))):
        if not done(log): continue
        name = re.sub(r'_c\d+\.log$', '', os.path.basename(log))
        for line in open(log):
            m = re.match(r'^(\S.*?)\s{2,}(\d+)$', line.rstrip())
            if m: per[name][m.group(1)] += int(m.group(2))
            if line.startswith('  FAIL'): fails[name].append(line.rstrip())
            if line.startswith('# time'): per[name]['chunks'] += 1
    keys = sorted({k for c in per.values() for k in c})
    out = ['# Key-graph runs (k4/sx_runs.py --sum)', '',
           'Counters summed over the chunks of each input (`results/k4_sx/chunks/*.log`).', '']
    for name in [n for n in INPUTS if n in per] + [n for n in per if n not in INPUTS]:
        out.append('## %s (%d chunks of %d records; expected %d)' % (name, per[name]['chunks'], CHUNK,
                                                                      -(-nrec(name) // CHUNK)))
        out.append('')
        for k in keys:
            if k != 'chunks' and per[name][k]: out.append('- %s: %d' % (k, per[name][k]))
        for f in fails[name]: out.append('- ' + f.strip())
        out.append('')
    open(os.path.join(ROOT, 'results/k4_sx/keys_summary.md'), 'w').write('\n'.join(out) + '\n')
    print('\n'.join(out))


if __name__ == '__main__':
    os.makedirs(os.path.join(ROOT, OUT), exist_ok=True)
    if '--sum' in sys.argv: summarize()
    else:
        for name in (sys.argv[1:] or INPUTS): run(name)
