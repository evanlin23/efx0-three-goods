"""Constructed families tested against CONN_2 and Conjecture W (k4/haxell.md §6), through gstar.c (census) and
gstar_measure.c (stuck states per measure; steps of at most RADIUS moves, rotations if ROT = 1).

  CYC_n     agent i values its own g_i at 10, the next agent's g_{i+1} at 11, the pooled p at 1 (k = 3);
            state of interest: every agent holds its own good, p pooled
  CHAIN_t   agents 0..t; agent 0 values the pooled g at 12 and b_0 at 10; agent i values b_{i-1} at 11, b_i at 10
  OPEN_t    CHAIN_t plus an absorber z holding a good c that only z values (5); agent t also values g at 12

    python3 k4/haxell/ht_families.py"""
import os, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))


def cyc(n):
    parts = [n, n + 1]
    for i in range(n):
        parts += [3, i, 10, (i + 1) % n, 11, n, 1]
    return ' '.join(map(str, parts))


def chain(t):
    n = t + 1; g = n
    parts = [n, n + 1, 2, 0, 10, g, 12]
    for i in range(1, n):
        parts += [2, i - 1, 11, i, 10]
    return ' '.join(map(str, parts))


def open_(t):
    n = t + 2; m = t + 3; c = t + 1; g = t + 2
    parts = [n, m, 2, 0, 10, g, 12]
    for i in range(1, t + 1):
        extra = [g, 12] if i == t else []
        parts += [2 + len(extra) // 2, i - 1, 11, i, 10] + extra
    parts += [1, c, 5]
    return ' '.join(map(str, parts))


def run(prog, args, line):
    return subprocess.run([os.path.join(HERE, prog)] + args, input=line + '\n', capture_output=True, text=True).stdout.strip()


if __name__ == '__main__':
    print('$ python3 k4/haxell/ht_families.py', flush=True)
    for name, line in [('CYC_%d' % n, cyc(n)) for n in (4, 5, 6)] + [('CHAIN_%d' % t, chain(t)) for t in (3, 4, 5)] + \
                      [('OPEN_%d' % t, open_(t)) for t in (2, 3, 4)]:
        print(name, '| census:', run('gstar', [], line), flush=True)
        for r, rot in (('2', '0'), ('3', '0'), ('2', '1')):
            w = run('gstar_measure', [r, rot], line).split()
            d = dict(zip(w[4::2], w[5::2]))
            print('   radius %s rotations %s: stuck states welfare %s leximin %s envy pairs %s AUG %s' % (
                r, rot, d.get('phi1'), d.get('phi2'), d.get('phi5'), d.get('phi0')), flush=True)
