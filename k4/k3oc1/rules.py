"""Selection rules for the repairing DE trade on hard starts (oc1_k3 HARD lines): for each rule, on how many hard starts
does every DE trade the rule selects repair (all), and some (any)?
    python3 k4/k3oc1/rules.py LOG..."""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import read_lines
from k3lib import base_of, completion, vals, bundles
from lbtest import lb2 as lb1
from de_moves import de_chains, de_rings, info

def score(rk, base):
    n = len(rk); B = bundles(base, n); s = 0
    for i in range(n):
        if len(B[i]) == 2: s += 4
        elif len(B[i]) == 1: s += 3 - rk[i].index(B[i][0])
    return s

def nfree(rk, m, base):
    return len(info(rk, m, base)[6])

RULES = {
    'max score': lambda rk, m, b, nb, d: score(rk, nb),
    'max free after': lambda rk, m, b, nb, d: nfree(rk, m, nb),
    'max (score, free)': lambda rk, m, b, nb, d: (score(rk, nb), nfree(rk, m, nb)),
    'max (free, score)': lambda rk, m, b, nb, d: (nfree(rk, m, nb), score(rk, nb)),
    'longest': lambda rk, m, b, nb, d: len(d[1]),
    'max junk left': lambda rk, m, b, nb, d: sum(1 for g in nb if g < 0),
    'min junk left': lambda rk, m, b, nb, d: -sum(1 for g in nb if g < 0),
}
if __name__ == '__main__':
  C = collections.Counter()
  for fn in sys.argv[1:]:
      for line in read_lines(fn):
          if not line.startswith('HARD'): continue
          mt = re.match(r'HARD (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) chain', line)
          rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2))
          Y = ast.literal_eval(mt.group(4)); V = vals(rk); b = base_of(Y, m)
          mv = de_chains(rk, m, b) + de_rings(rk, m, b)
          rep = {nb: lb1(rk, m, nb) is not None for nb, d in mv}
          C['hard'] += 1
          for name, f in RULES.items():
              keys = [f(rk, m, b, nb, d) for nb, d in mv]; best = max(keys)
              sel = [nb for (nb, d), k in zip(mv, keys) if k == best]
              C[name + ': all'] += all(rep[s] for s in sel); C[name + ': any'] += any(rep[s] for s in sel)
  for k in sorted(C): print(k, C[k])
