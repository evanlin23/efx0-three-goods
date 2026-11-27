"""Certify Conjecture FC2 (k4/p3.md section 6) for every strict profile of a list of core hypergraphs, by the ordinal
CEGAR of compute/k4-oc1max-cert (k4/oc1cert/cegar.py) with its move set restricted to *forest chains* and additions,
and re-check the certificate with that workstream's independent checker (k4/oc1cert/check.py) with the same
restriction. Neither file is modified: both are imported from a checkout of compute/k4-oc1max-cert (commit cfb3c18d)
given by OC1CERT. Same mechanism as k4/p3/can2cert.py (which certifies the narrower CAN2), with a different restriction.

The statement certified (FC2 at maximum-matching starts): for every type profile and every serial-dictatorship order
whose picks Y form a maximum matching, the picks have a one-absorber EFX0 completion, or an addition or a *forest
chain* gives bases that have one. A forest chain is an official chain x_0, ..., x_t (t >= 1) in which every receiver
x_i (i >= 1) that adds junk (H_i nonempty) takes the base of an agent x_{i-1} that is *unfrozen at the picks*: every
other agent j that values a good of B_{x_{i-1}} holds a base it prefers, v_j(B_j) > v_j(B_{x_{i-1}}) (a baseless
valuer wants it, so that link is excluded). A receiver of a frozen agent's base therefore takes exactly that base and
wants it; at p <= 2 it is the unique wanter. So at p <= 2 a forest chain is a run of need paths of the want forest,
each one entered by an agent that takes a root's pick (with junk, or without), and x_0 takes H_0 inside
(J + B_{x_t}) & R_{x_0}. Rings are not allowed; the head x_t may be frozen. Canonical chains (CAN2) are the forest
chains that are one need path from x_0 to its root.

How the restriction is imposed.
  - Generation (FCCert.moves): only additions and the chains above, from cegar.Cert.moves. For every link with H_i
    nonempty and every other valuer j of B_{x_{i-1}}, the witness records the comparison v_j(B_j) > v_j(B_{x_{i-1}})
    and fixes j's pick (j is entered with its unchanged base), so that a witness found at one (profile, picks) blocks
    only (profile', picks') at which its chain is again a forest chain. A link with H_i empty is a forest link at every
    profile at which the official improving comparison v_{x_i}(B_{x_{i-1}}) > v_{x_i}(B_{x_i}) holds.
  - Checking (patched check.Hyper.apply_move): 'picks' and 'add' witnesses as before; a 'chain' witness is accepted
    only if, at the concrete picks being checked, every link with H_i nonempty has every other valuer j of B_{x_{i-1}}
    holding a base, and the comparisons v_j(B_j) > v_j(B_{x_{i-1}}) are added to the move's improving conditions (so to
    the type masks). 'ring' witnesses are rejected.
    OC1CERT=/path/to/compute-k4-oc1max-cert python3 k4/p3/fc2cert.py run LISTS --out=CERT.json.gz [--jobs=4] [...]
    OC1CERT=/path/to/compute-k4-oc1max-cert python3 k4/p3/fc2cert.py check CERT.json.gz [--lists=LISTS]
(LISTS as for k4/oc1cert/run.py: names of OC1CERT/results/k4_certs_<LIST>.json.gz.)
"""
import sys, os, gzip, json

SRC = os.environ.get('OC1CERT')
if not SRC: sys.exit('set OC1CERT to a checkout of compute/k4-oc1max-cert')
sys.path.insert(0, os.path.join(SRC, 'k4', 'oc1cert')); sys.path.insert(0, os.path.join(SRC, 'k4', 'sdc'))

STATEMENT = ('FC2 at maximum-matching starts (k4/p3.md section 6, proof/k4-p3): for every type profile and every SD '
             'order whose picks form a maximum matching, the picks have a one-absorber EFX0 completion, or an addition '
             'or one forest chain (an official chain in which a receiver adds junk only to the base of an agent '
             'unfrozen at the picks; no rings) gives bases that have one')


def run_main():
    import cegar, run as runmod

    class FCCert(cegar.Cert):
        def moves(self, base, vals):
            V = lambda i, S: sum(vals[i].get(g, 0) for g in S)
            for kind, path, Hs, nb, imp in cegar.Cert.moves(self, base, vals):
                if kind == 'add': yield kind, path, Hs, nb, imp; continue
                if kind != 'chain': continue
                nb = dict(nb); imp = list(imp); ok = True
                for i in range(1, len(path)):
                    if not Hs[i]: continue
                    u = path[i - 1]
                    for j in range(self.n):
                        if j == u or not any(g in self.R[j] for g in base[u]): continue
                        if not base[j] or V(j, base[u]) > V(j, base[j]): ok = False; break   # u frozen at the picks
                        imp.append((j, tuple(base[j]), tuple(base[u])))
                        nb.setdefault(j, tuple(base[j]))                                     # fixes j's pick
                    if not ok: break
                if ok: yield kind, path, Hs, nb, imp

    runmod.Cert = FCCert
    sys.argv = [sys.argv[0]] + sys.argv[2:]
    runmod.main()
    opt = dict(a[2:].split('=', 1) for a in sys.argv[1:] if a.startswith('--') and '=' in a)
    if opt.get('out'):
        d = json.load(gzip.open(opt['out'], 'rt'))
        d['statement'] = STATEMENT; d['generator'] = 'k4/p3/fc2cert.py run (k4/oc1cert/cegar.py, additions and forest chains only)'
        with gzip.open(opt['out'], 'wt') as f: json.dump(d, f)
        print('statement rewritten:', STATEMENT)


def check_main():
    import check as chk
    orig = chk.Hyper.apply_move

    def apply_move(self, base, w):
        if w['kind'] in ('picks', 'add'): return orig(self, base, w)
        if w['kind'] != 'chain': return None
        r = orig(self, base, w)
        if r is None: return None
        nb, imp = r
        path = w['path']
        for i in range(1, len(path)):
            if not w['H'][i]: continue
            u = path[i - 1]; Bu = base[u]
            for j in range(self.n):
                if j == u or not (set(Bu) & self.R[j]): continue
                if not base[j]: return None
                imp = imp + [(j, list(base[j]), list(Bu))]
        return nb, imp

    chk.Hyper.apply_move = apply_move
    sys.argv = [sys.argv[0]] + sys.argv[2:]
    print('[k4/p3/fc2cert.py check: k4/oc1cert/check.py with moves restricted to additions and forest chains]', flush=True)
    chk.main()


if __name__ == '__main__':
    {'run': run_main, 'check': check_main}[sys.argv[1]]()
