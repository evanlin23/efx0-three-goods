"""The family of paper/k3-simple Appendix C: k free agents o_0..o_{k-1}, each the root of a binary tree of depth d
whose internal agents want the goods of their two children (a, b = the children's goods, c = own good); the leaves of
the tree of o_{i+1} hold their tops and are blockers of o_i (b = o_i's good, c = a leftover good of their own).
The state is the draft of any order with children before parents.  Test: does the draft pass the simple test, and
does every max-score DE trade (resp. some DE trade) lead to a state that passes it?
    python3 k4/k3oc1/trees.py K D"""
import sys, os, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import sd, base_of
from de_moves import de_trades
from lbtest import lb_simple
from rules import score

def build(k, d):
    agents = []; goods = [0]
    def new_good():
        goods[0] += 1; return goods[0] - 1
    trees = []
    for i in range(k):   # nodes: (depth, own good, children)
        own = {}; 
        def mk(depth):
            g = new_good(); node = {'g': g, 'ch': []}
            if depth < d: node['ch'] = [mk(depth + 1), mk(depth + 1)]
            return node
        trees.append(mk(0))
    rk = []; order = []
    def emit(node, i):
        for ch in node['ch']: emit(ch, i)
        if node['ch']:
            rk.append((node['ch'][0]['g'], node['ch'][1]['g'], node['g']))
        else:
            h = new_good()
            root_prev = trees[(i - 1) % k]['g']      # leaves of tree i are blockers of o_{i-1}
            rk.append((node['g'], root_prev, h))
        order.append(len(rk) - 1)
    for i in range(k): emit(trees[i], i)
    return rk, goods[0], order

if __name__ == '__main__':
    k, d = int(sys.argv[1]), int(sys.argv[2])
    rk, m, order = build(k, d); n = len(rk)
    b = base_of(sd(rk, m, order), m)
    print('n', n, 'm', m, 'draft passes', bool(lb_simple(rk, m, b)))
    mv = de_trades(rk, m, b); print('trades', len(mv))
    if mv:
        best = max(score(rk, nb) for nb, dd in mv)
        sel = [(nb, dd) for nb, dd in mv if score(rk, nb) == best]
        print('max score', best, 'every max-score trade passes', all(lb_simple(rk, m, nb) for nb, dd in sel),
              'some trade passes', any(lb_simple(rk, m, nb) for nb, dd in mv))
        print('a max-score trade', sel[0][1])
