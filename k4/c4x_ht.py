#!/usr/bin/env python3
"""The cores H_t of `k4/c4.md` §7 (branch proof/k4-c4, PR #33), as input for k4/c4x.c or k4/c4x_one.c.

H_t: goods g_1..g_t, z, u, u', and a_{j,i}, b_{j,i}, c_{j,i} (1 <= j <= t, 1 <= i <= 3); agents, in this order:
  l with R = {g_1, z, u, u'} and values (8, 6, 5, 4);
  for each gadget j: x_{j,1}, x_{j,2}, x_{j,3} with R = {a_{j,i}, b_{j,i}, c_{j,i}, g_j} and values (8, 6, 4, 3), then
  y_j with R = {a_{j,1}, a_{j,2}, a_{j,3}, e_j} and values (8, 6, 4, 3), e_j = g_{j+1} (j < t), e_t = z.

usage: python3 k4/c4x_ht.py T            prints the c4x input (one profile) for H_T
       python3 k4/c4x_ht.py T --names    prints the good and agent names"""
import sys

def build(t):
    names = [f'g{j}' for j in range(1, t + 1)] + ['z', 'u', "u'"]
    for j in range(1, t + 1):
        for i in range(1, 4):
            names += [f'a{j}{i}', f'b{j}{i}', f'c{j}{i}']
    idx = {nm: k for k, nm in enumerate(names)}
    agents = [('l', ['g1', 'z', 'u', "u'"], [8, 6, 5, 4])]
    for j in range(1, t + 1):
        for i in range(1, 4):
            agents.append((f'x{j}{i}', [f'a{j}{i}', f'b{j}{i}', f'c{j}{i}', f'g{j}'], [8, 6, 4, 3]))
        e = f'g{j + 1}' if j < t else 'z'
        agents.append((f'y{j}', [f'a{j}1', f'a{j}2', f'a{j}3', e], [8, 6, 4, 3]))
    return names, idx, agents

def c4x_input(t):
    names, idx, agents = build(t)
    lines = [f'{len(agents)} {len(names)}']
    for (_, goods, vals) in agents:
        lines.append(f'4 ' + ' '.join(str(idx[g]) for g in goods) + ' 1')
        lines.append(' '.join(map(str, vals)))
    lines.append('0 1')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    t = int(sys.argv[1])
    if '--names' in sys.argv:
        names, idx, agents = build(t)
        print('goods:', ' '.join(f'{k}={nm}' for k, nm in enumerate(names)))
        print('agents:', ' '.join(f'{k}={a[0]}' for k, a in enumerate(agents)))
    else:
        sys.stdout.write(c4x_input(t))
