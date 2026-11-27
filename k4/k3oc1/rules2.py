"""More selection rules on hard starts (simple test): for each rule, does every selected DE trade repair?
Rules use the score vector s (E 0, C 1, B 2, A 3, pair 4) after the trade and the order pi.
    python3 k4/k3oc1/rules2.py LOG..."""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines
from de_moves import de_trades
from lbtest import lb_simple, parts
from pareto_rule import svec
from lbtest import parts as _parts
def _omega(rk, m, nb):
    B, J, U, NA, F, T = _parts(rk, m, nb); return len(J) - len(T)
RULES = {
    'max score': lambda s, o, s0, T: sum(s),
    'min omega after': None, 'max |T| after': None, 'min omega, then max score': None,
    'revlex (last agent first)': lambda s, o, s0, T: tuple(s[i] for i in reversed(o)),
    'lex (first agent first)': lambda s, o, s0, T: tuple(s[i] for i in o),
    'max sum of gains of the draft terminals': lambda s, o, s0, T: sum(s[t] - s0[t] for t in T),
    'max score, then revlex': lambda s, o, s0, T: (sum(s), tuple(s[i] for i in reversed(o))),
    'max number of agents gaining': lambda s, o, s0, T: sum(1 for a, b in zip(s, s0) if a > b),
    'max number of agents at score >= 3': lambda s, o, s0, T: sum(1 for a in s if a >= 3),
    'max sum of squared gains': lambda s, o, s0, T: sum((a - b) ** 2 for a, b in zip(s, s0)),
    'min number of agents below their top': lambda s, o, s0, T: -sum(1 for a in s if a < 3),
}
C = collections.Counter()
for fn in sys.argv[1:]:
    for line in read_lines(fn):
        if not line.startswith('HARD'): continue
        mt = re.match(r'HARD (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\))', line)
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); o = ast.literal_eval(mt.group(3))
        b = base_of(ast.literal_eval(mt.group(4)), m); mv = de_trades(rk, m, b); C['hard'] += 1
        s0 = svec(rk, b); T = parts(rk, m, b)[5]
        rep = {nb: bool(lb_simple(rk, m, nb)) for nb, d in mv}
        for name, f in RULES.items():
            if name == 'min omega after': keys = [-_omega(rk, m, nb) for nb, d in mv]
            elif name == 'max |T| after': keys = [len(_parts(rk, m, nb)[5]) for nb, d in mv]
            elif name == 'min omega, then max score': keys = [(-_omega(rk, m, nb), sum(svec(rk, nb))) for nb, d in mv]
            else: keys = [f(svec(rk, nb), o, s0, T) for nb, d in mv]
            best = max(keys)
            C[name + ': all selected repair'] += all(rep[nb] for (nb, d), k in zip(mv, keys) if k == best)
for k in sorted(C): print(k, C[k])
