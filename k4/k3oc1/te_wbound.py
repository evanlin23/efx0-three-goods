"""The want-count bound for the release lemma (k4/k3_oc1.md §12.1).  W = #b-holders + 2 #c-holders (non-pair agents)
counts (agent, wanted good) pairs, so nu <= W and omega <= D := |J| - #a-holders + #c-holders at a perfect state.
A rotation whose receivers climb `steps` ranks in all, followed by u upgrades, has omega' <= D - steps - u.  On GAP
lines: D vs omega, and whether some valid Rule E rotation has D - steps - u <= 1 (the crude bound alone gives (R)).
    python3 k4/k3oc1/te_wbound.py gapfile:FILE..."""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines, bundles
from lbtest import upgrade, parts
from t2k_e import valid_rotations

def D_of(rk, m, base):
    n = len(rk); B = bundles(base, n); J = [g for g in range(m) if base[g] < 0]
    a = sum(1 for i in range(n) if len(B[i]) == 1 and B[i][0] == rk[i][0])
    c = sum(1 for i in range(n) if len(B[i]) == 1 and rk[i].index(B[i][0]) == 2)
    return len(J) - a + c

if __name__ == '__main__':
  C = collections.Counter()
  for arg in sys.argv[1:]:
      for line in read_lines(arg[8:] if arg.startswith('gapfile:') else arg):
          mt = re.search(r'GAP (\[\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+)', line)
          if not mt: continue
          rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); Y = ast.literal_eval(mt.group(4))
          bu = upgrade(rk, m, base_of(Y, m)); P = parts(rk, m, bu); om = len(P[1]) - len(P[5]); D = D_of(rk, m, bu)
          C['|T| %s: D - omega = %d' % (mt.group(5), D - om)] += 1
          best = None
          for k, p, nb in valid_rotations(rk, m, ast.literal_eval(mt.group(3)), Y):
              nu_ = upgrade(rk, m, nb); Dn = D_of(rk, m, nu_)
              Pn = parts(rk, m, nu_); omn = len(Pn[1]) - len(Pn[5])
              assert omn <= Dn, (line, k)
              best = Dn if best is None else min(best, Dn)
          if best is not None: C['|T| %s: crude bound gives (R) %s' % (mt.group(5), best <= 1)] += 1
  for k in sorted(C): print(C[k], k)
