"""Certify Conjecture CAN2 (k4/p3.md section 6) for every strict profile of a list of core hypergraphs, by the ordinal
CEGAR of compute/k4-oc1max-cert (k4/oc1cert/cegar.py) with its move set restricted to *canonical chains*, and re-check
the certificate with that workstream's independent checker (k4/oc1cert/check.py) with the same restriction. Neither
file is modified: both are imported from a checkout of compute/k4-oc1max-cert (commit cfb3c18d) given by OC1CERT.

The statement certified (CAN2 at maximum-matching starts; the instances are the lists' hypergraphs, here the
multigraph cores of k4/p3/mg_cores.py): for every type profile and every serial-dictatorship order whose picks Y form
a maximum matching, the picks have a one-absorber EFX0 completion, or a *canonical chain* gives bases that have one.
A canonical chain is an official chain x_0, ..., x_t (t >= 1) in which
  - every x_i, i >= 1, takes exactly B_{x_{i-1}} (no junk): it wants Y_{x_{i-1}} at the picks (so x_0 is frozen);
  - x_0 takes a nonempty H_0, a subset of (J + B_{x_t}) & R_{x_0}, worth more than its pick;
  - the head x_t is unfrozen at the picks: every other agent that values a good of B_{x_t} holds a pick it prefers
    (a pickless agent that values it wants it, so such a chain is excluded).
Additions and rings are not allowed. (At p <= 2 the chain from x_0 is then the unique need path P(x_0).)

How the restriction is imposed.
  - Generation (CanCert.moves): only the moves above, from cegar.Cert.moves. For every other valuer j of B_{x_t}, the
    witness also records the comparison v_j(Y_j) > v_j(B_{x_t}) and fixes j's pick (j is entered with its unchanged
    base), so that a witness found at one (profile, picks) blocks only (profile', picks') at which its chain is again
    canonical. (The witness clause of cegar.py treats these entries like the movers' improving comparisons.)
  - Checking (patched check.Hyper.apply_move): a witness move is accepted only if it is a chain with empty H_i for
    i >= 1 and, at the concrete picks being checked, every other valuer j of B_{x_t} holds a pick; the comparison
    v_j(Y_j) > v_j(B_{x_t}) is added to the move's improving conditions (and so to the type masks). 'add' and 'ring'
    witnesses are rejected.
    OC1CERT=/path/to/compute-k4-oc1max-cert python3 k4/p3/can2cert.py run LISTS --out=CERT.json.gz [--jobs=4] [...]
    OC1CERT=/path/to/compute-k4-oc1max-cert python3 k4/p3/can2cert.py check CERT.json.gz [--lists=LISTS]
(LISTS as for k4/oc1cert/run.py: names of OC1CERT/results/k4_certs_<LIST>.json.gz.)
"""
import sys, os, gzip, json

SRC = os.environ.get('OC1CERT')
if not SRC: sys.exit('set OC1CERT to a checkout of compute/k4-oc1max-cert')
sys.path.insert(0, os.path.join(SRC, 'k4', 'oc1cert')); sys.path.insert(0, os.path.join(SRC, 'k4', 'sdc'))

STATEMENT = ('CAN2 at maximum-matching starts (k4/p3.md section 6, proof/k4-p3): for every type profile and every SD '
             'order whose picks form a maximum matching, the picks have a one-absorber EFX0 completion or one canonical '
             'chain (every receiver takes exactly its predecessor\'s base and wants it, x_0 takes H_0 inside '
             '(J + B_{x_t}) & R_{x_0}, the head is unfrozen at the picks) gives bases that have one')


def run_main():
    import cegar, run as runmod

    class CanCert(cegar.Cert):
        def moves(self, base, vals):
            V = lambda i, S: sum(vals[i].get(g, 0) for g in S)
            for kind, path, Hs, nb, imp in cegar.Cert.moves(self, base, vals):
                if kind != 'chain' or any(len(h) for h in Hs[1:]): continue
                z = path[-1]; nb = dict(nb); imp = list(imp); ok = True
                for j in range(self.n):
                    if j == z or not any(g in self.R[j] for g in base[z]): continue
                    if not base[j] or V(j, base[z]) > V(j, base[j]): ok = False; break     # j wants B_z: z frozen
                    imp.append((j, tuple(base[j]), tuple(base[z])))
                    nb.setdefault(j, tuple(base[j]))                                         # fixes j's pick
                if ok: yield kind, path, Hs, nb, imp

    runmod.Cert = CanCert
    sys.argv = [sys.argv[0]] + sys.argv[2:]
    runmod.main()
    opt = dict(a[2:].split('=', 1) for a in sys.argv[1:] if a.startswith('--') and '=' in a)
    if opt.get('out'):
        d = json.load(gzip.open(opt['out'], 'rt'))
        d['statement'] = STATEMENT; d['generator'] = 'k4/p3/can2cert.py run (k4/oc1cert/cegar.py, canonical chains only)'
        with gzip.open(opt['out'], 'wt') as f: json.dump(d, f)
        print('statement rewritten:', STATEMENT)


def check_main():
    import check as chk
    orig = chk.Hyper.apply_move

    def apply_move(self, base, w):
        if w['kind'] == 'picks': return orig(self, base, w)
        if w['kind'] != 'chain' or any(len(h) for h in w['H'][1:]): return None
        r = orig(self, base, w)
        if r is None: return None
        nb, imp = r
        z = w['path'][-1]; Bz = base[z]
        for j in range(self.n):
            if j == z or not (set(Bz) & self.R[j]): continue
            if not base[j]: return None
            imp = imp + [(j, list(base[j]), list(Bz))]
        return nb, imp

    chk.Hyper.apply_move = apply_move
    sys.argv = [sys.argv[0]] + sys.argv[2:]
    print('[k4/p3/can2cert.py check: k4/oc1cert/check.py with moves restricted to canonical chains]', flush=True)
    chk.main()


if __name__ == '__main__':
    {'run': run_main, 'check': check_main}[sys.argv[1]]()
