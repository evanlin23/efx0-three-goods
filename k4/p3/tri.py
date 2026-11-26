"""Gadget chains against two owners (k4/p3.md section 5): three frozen agents whose threatening pairs form a triangle
of junk goods g, h, k inside one block.
Gadget j (agents x_j1, x_j2, x_j3, y_j), entered through the good s_j (l's top for j = 1, else y_{j-1}'s pick e_{j-1}):
  x_j1 = {a_j1, g_j, h_j, s_j}, x_j2 = {a_j2, h_j, k_j, s_j}, x_j3 = {a_j3, k_j, g_j, a_j1}, values (8, 6, 4, 3) each
  y_j  = {a_j1, a_j2, a_j3, e_j}, values (8, 6, 4, 3), e_j = s_{j+1} (j < t), e_t = z
  l    = {s_1, z, u, u'}, values (8, 6, 5, 4)
Valuers: s_j: x_j1, x_j2 and y_{j-1} (or l); a_j1: x_j1, x_j3, y_j; others two or one. So p = 3.
    python3 k4/p3/tri.py check T1,T2,...        core conditions
    python3 k4/p3/tri.py ts T1,... [--R=3]      rotations needed with one and with two owners (k4/p3/ts.py)
"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))

def build(t):
    nxt = [0]
    def new():
        g = nxt[0]; nxt[0] += 1; return g
    s = [new() for _ in range(t)]; z = new(); u = new(); u2 = new()
    sets = [[s[0], z, u, u2]]; vals = [[8, 6, 5, 4]]
    for j in range(t):
        a = [new() for _ in range(3)]; g, h, k = new(), new(), new()
        sets += [[a[0], g, h, s[j]], [a[1], h, k, s[j]], [a[2], k, g, a[0]]]; vals += [[8, 6, 4, 3]] * 3
        sets.append([a[0], a[1], a[2], s[j + 1] if j + 1 < t else z]); vals.append([8, 6, 4, 3])
    return sets, vals, nxt[0]

if __name__ == '__main__':
    import c4_chain, ts
    from p3lib import Inst, efx0, bundles
    mode, T = sys.argv[1], [int(x) for x in sys.argv[2].split(',')]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[3:] if a.startswith('--'))
    for t in T:
        sets, vals, m = build(t); I = Inst(sets, vals, m, f'TRI_{t}')
        print(f'TRI_{t}: n = {I.n}, m = {m}, p = {I.p()}, core: {c4_chain.core_ok(sets, vals, m)}', flush=True)
        if mode == 'ts':
            s0, order = ts.initial(I)
            print('   Phase 1 picks', [sorted(b) for b in s0.base], 'frozen', [i for i, f in enumerate(s0.frozen()) if f], flush=True)
            print('   rotations needed (B owners -> rotations, None = more than R):', ts.run(I, int(opt.get('R', 2)), [1, 2], None), flush=True)
