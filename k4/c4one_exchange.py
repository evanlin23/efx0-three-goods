"""k4/c4one.md §6: where the single changed insertion step of Lemmas X and X' lies, and which agent it inserts. Runs
k4/c4check.c with the given options (an insertion mode -i6, -i10, -i19 or -i20, and -E or -E3) on every strict profile of
every core with exactly one 4-good agent in the given certificate files, and adds up the categories that c4check.c
prints on stderr (lines "C4E cat=K n=W", W = weighted profile count).
-Z1 / -Z2 / -Z3 / -Z4 (with -i20) restrict the changes tried: only the step that started q's block / only q as the new
agent / both / only steps up to the one that started q's block.
Usage: python3 k4/c4one_exchange.py "OPTIONS" FILE [FILE ...]
  e.g. python3 k4/c4one_exchange.py "-X -P2 -u2 -i20 -o0 -r1 -w0 -c0 -f3 -E3" results/k4_certs_4_n4_1.json.gz
Categories. -i19/-i20: bit 1 covered, 2 omega drops, 4 q no longer frozen, 8 q later (a smaller key, -i19 only); bits
16/32/64: the changed step is the one that started q's block / an earlier one / a later one; with -E3, cat >> 7 is the
new agent at the changed step: 0 q, 1 the old r, 2 another agent of q's old block, 3 an agent of a later block, 4 of an
earlier block; with -E4 (needs -Y) also bits 10-11: omega of the new run is lower (0), equal (1) or higher (2), and
bits 12-14: the class of tau's run (k4/c4one.md §3: 1 G2, 2 q frozen with no need chain to r, 3 q frozen with (i)/(ii)
of B4w failing, 4 (Tc), 5 (Tb), 6 other). -i6/-i10: cat 0 the index run is covered; otherwise bit 16 set, bit 1 the new agent is q, bit 4 the
changed step was the last insertion step, and for -i6 bit 2 it started q's block and bit 8 it inserted q; 63 nothing
worked."""
import os, sys, gzip, json, subprocess, collections
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import lb4_run, c4check_run
BIN = os.environ.get('C4CHECK_BIN') or c4check_run.BIN; opts = sys.argv[1].split(); files = sys.argv[2:]
INS = next((o for o in opts if o.startswith('-i')), '-i2'); E34 = '-E3' in opts or '-E4' in opts

def run(c):
    p = subprocess.run([BIN] + opts, input=lb4_run.encode(c['sets'], c['m'], False), capture_output=True, text=True)
    E = collections.Counter()
    for l in p.stderr.split('\n'):
        if l.startswith('C4E'):
            kv = dict(x.split('=') for x in l.split()[1:]); E[int(kv['cat'])] += int(kv['n'])
    return E

def name(k):
    if INS in ('-i19', '-i20', '-i18'):
        if k & 1023 == 0 and k >= 4096:   # -E4: no change tried covers the run
            return f"{['proved', 'G2', 'G1F_nochain', 'G1F_cond', 'G1T_Tc', 'G1T_Tb', 'other', '-'][k >> 12 & 7]:12s} NOT COVERED"
        what = {1: 'covered', 2: 'omega drops', 4: 'q unfrozen', 8: 'q later'}.get(k & 15, '?')
        where = {16: "at the step that started q's block", 32: 'at an earlier step', 64: 'at a later step'}.get(k & 112, '?')
        rel = ['q', 'the old r', "another agent of q's old block", 'an agent of a later block',
               'an agent of an earlier block'][k >> 7 & 7] if E34 else ''
        s = f'{what:12s} {where:36s} {"new agent " + rel if rel else ""}'
        if k >= 1024:
            cls = ['proved', 'G2', 'G1F_nochain', 'G1F_cond', 'G1T_Tc', 'G1T_Tb', 'other', '-'][k >> 12 & 7]
            s = f'{cls:12s} ' + s + f'  omega {["lower", "equal", "higher"][k >> 10 & 3]}'
        return s
    if k == 0: return 'the index run is covered'
    if k == 63: return 'no single change covers it'
    s = ['changed step:']
    if k & 2: s.append("started q's block")
    if k & 8: s.append('inserted q')
    if k & 4: s.append('was the last insertion step')
    s.append('new agent q' if k & 1 else 'new agent not q')
    return ' '.join(s)

def main():
    c4check_run.build()
    print('# c4one_exchange.py', ' '.join(opts), flush=True)
    for fn in files:
        cs = [c for c in json.load(gzip.open(fn, 'rt'))['cores'] if sum(len(s) == 4 for s in c['sets']) == 1]
        E = collections.Counter()
        with Pool(4) as pool:
            for e in pool.imap_unordered(run, [c for c in cs]): E.update(e)
        print(f'{fn}: {len(cs)} cores, {sum(E.values())} weighted runs with a category', flush=True)
        for k in sorted(E): print(f'   cat {k:4d}  {name(k):110s} {E[k]}', flush=True)

if __name__ == '__main__':
    main()
