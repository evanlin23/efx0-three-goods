"""p <= 3 analogues of the hard cores H_t (k4/c4.md section 7): each gadget has TWO x's sharing g_j (H_t has three, which
gives g_j four valuers). Variants for y_j (the gadget's 'collector'):
  A: y_j = {a_j1, a_j2, e_j}, values (8, 6, 3)
  B: y_j = {a_j1, a_j2, p_j, e_j}, values (8, 6, 4, 3), p_j private
  C: y_j = {a_j1, a_j2, e_j, p_j}, values (8, 6, 4, 3), p_j private (e_j above p_j)
x_ji = {a_ji, b_ji, c_ji, g_j} with values (8, 6, 4, 3) as in H_t; l = {g_1, z, u, u'} with (8, 6, 5, 4).
Then g_j has the valuers x_j1, x_j2 and y_{j-1} (l for j = 1): p = 3.
  python3 k4/p3/ht3.py check A,B,C 1,2,3,4        core conditions (k4/c4_chain.core_ok) and p
  python3 k4/p3/ht3.py run A 1,2,...,8 'OPTS' ... run k4/c4_lb4w.c (LB4r) with each option string
"""
import os, sys, subprocess
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.dirname(HERE))
import c4_chain as C

def build(t, var='A'):
    nxt = [0]
    def new():
        g = nxt[0]; nxt[0] += 1; return g
    g = [new() for _ in range(t)]; z = new(); u = new(); u2 = new()
    sets = [[g[0], z, u, u2]]; vals = [[8, 6, 5, 4]]
    for j in range(t):
        a = [new() for _ in range(2)]; b = [new() for _ in range(2)]; c = [new() for _ in range(2)]
        for i in range(2):
            sets.append([a[i], b[i], c[i], g[j]]); vals.append([8, 6, 4, 3])
        e = g[j + 1] if j + 1 < t else z
        if var == 'A': sets.append([a[0], a[1], e]); vals.append([8, 6, 3])
        elif var == 'B': p = new(); sets.append([a[0], a[1], p, e]); vals.append([8, 6, 4, 3])
        elif var == 'C': p = new(); sets.append([a[0], a[1], e, p]); vals.append([8, 6, 4, 3])
    return sets, vals, nxt[0]

def pmax(sets, m): return max(sum(g in S for S in sets) for g in range(m))

if __name__ == '__main__':
    mode, vars_, ts = sys.argv[1], sys.argv[2].split(','), [int(x) for x in sys.argv[3].split(',')]
    for var in vars_:
        for t in ts:
            sets, vals, m = build(t, var)
            line = f'{var} t={t}: n = {len(sets)}, m = {m}, p = {pmax(sets, m)}'
            if mode == 'check':
                print(line, 'core:', C.core_ok(sets, vals, m), flush=True); continue
            print(line, flush=True)
            for opt in sys.argv[4:]:
                p = subprocess.run([C.binary()] + opt.split() + ['-f1'], input=C.encode(sets, vals, m),
                                   capture_output=True, text=True)
                o = p.stdout.split()
                print(f'  lb4 {opt}: ' + ' '.join(o[6:18]) + f'  largest bundle {o[-1] if o else "?"}', flush=True)
