"""Independent check of NSW claims (compute/k4-nsw; k4/nsw.md), in the model of k4/c4_verify_H/lb4r.py: an independent
transcription of LB4r from its Lean definition (lean/EFX/LB4R.lean, PR #35), written by the C4 verifier with no code
of k4/lb4.c or k4/lb4_nsw.c. Nothing here reuses lb4_nsw.c: the potential, the search and the stuck test are new.

For one strict profile and one upgrade policy: from Phase 1 with index insertion, then the policy's upgrades
(lb4r.up_run), explore every state reachable by RotSteps (lb4r.rot_steps: need chains, O, RotChecks) that strictly
raise the potential Phi = (number of agents with a nonempty base, product of v_i(B_i) over them), compared
lexicographically. A state with an output (lb4r.any_output, owner's needs from its bundle, exact by SAT) is a success
and is not expanded. Reports
  - whether some explored state is a success (the existence form: an NSW-increasing path reaches an output), and
  - every explored state without an output that has RotStep successors, none of which raises Phi (the local form
    fails there), with the path of moves that reaches it.
Usage: nsw_verify.py [--lb4r=PATH] 'VALUES' POLICY   VALUES: a JSON list of {good: value} dicts, one per agent;
       POLICY: shrink (u1), envyFree (u2) or none (u0). Exit status 0 if the run completed."""
import importlib.util, hashlib, json, os, sys

PINNED = '6726d25aaa06d3e5944dc3e0640e006f758bde4c'   # git blob of k4/c4_verify_H/lb4r.py used by the committed logs

def load_lb4r(path):
    """k4/c4_verify_H/lb4r.py from the tree (on main since #33), or --lb4r=PATH; reports whether it is the pinned blob"""
    if path is None:
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'c4_verify_H', 'lb4r.py')
    data = open(path, 'rb').read()
    blob = hashlib.sha1(b'blob %d\0' % len(data) + data).hexdigest()
    if blob != PINNED: print(f"note: {path} is git blob {blob}, not the pinned {PINNED}", file=sys.stderr)
    spec = importlib.util.spec_from_file_location('lb4r', path)
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
    return mod, hashlib.sha256(data).hexdigest()

def phi(inst, s):
    base = s[0]
    z, p = 0, 1
    for i in range(inst.n):
        val = sum(inst.v[i][g] for g in range(inst.m) if base[g] == i)
        if any(base[g] == i for g in range(inst.m)): z += 1; p *= val
    return (z, p)

def describe(inst, s):
    base, pick, marked = s
    return ' '.join(f"{i}:{{{','.join(str(g) for g in range(inst.m) if base[g] == i)}}}{'*' if marked[i] else ''}" for i in range(inst.n))

def main():
    opt = dict(a[2:].split('=', 1) for a in sys.argv[1:] if a.startswith('--'))
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    L, sha = load_lb4r(opt.get('lb4r'))
    vals = [{int(g): x for g, x in d.items()} for d in json.loads(args[0])]
    pol = args[1]
    m = 1 + max(g for d in vals for g in d)
    v = [[d.get(g, 0) for g in range(m)] for d in vals]
    inst = L.Inst(v)
    print(f"lb4r.py sha256 {sha}; profile {json.dumps(vals)}; policy {pol}; potential (z, product)")
    s0, _ = L.phase1_state(inst, ())
    s1, ups = L.up_run(inst, s0, pol)
    print(f"Phase 1 + upgrades {ups}: {describe(inst, s1)}, Phi {phi(inst, s1)}")
    seen, stack, stuck, success = {s1: None}, [s1], [], 0
    while stack:
        s = stack.pop()
        if L.any_output(inst, s, 'bundle'): success += 1; continue
        succ = L.rot_steps(inst, s)
        P = phi(inst, s)
        up = {s2: how for s2, how in succ.items() if phi(inst, s2) > P}
        if succ and not up:
            path, t = [], s
            while seen[t] is not None: path.append(seen[t][1]); t = seen[t][0]
            stuck.append((s, len(succ), max(phi(inst, s2) for s2 in succ), path[::-1]))
        for s2, how in up.items():
            if s2 not in seen: seen[s2] = (s, how); stack.append(s2)
    print(f"explored {len(seen)} states by NSW-increasing RotSteps; states with an output: {success}")
    for s, k, best, path in stuck:
        print(f"LOCAL FORM FAILS: {describe(inst, s)} (* = marked), Phi {phi(inst, s)}, no output (owner's needs from its "
              f"bundle), {k} RotStep successors, largest Phi among them {best}; reached by (chain, O) moves {path}")
    print(f"summary: existence form {'holds' if success else 'FAILS'} here; local form fails at {len(stuck)} explored state(s)")

if __name__ == '__main__':
    main()
