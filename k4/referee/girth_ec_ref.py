#!/usr/bin/env python3
"""Referee check of Lemma EC and the stuck-state consequence (k4/girth.md §5, branch claude/k4-girth at 235bca4;
unchanged at ab906c8). Own code; nothing from k4/girth/ is run or imported. Raw EFX0 for monotone valuations.

Valuations: additive (k <= 4 relevant goods) or monotone non-additive (sum of the two largest values in the set).
States: FixProp3 from the empty allocation (gives (3)), then a random walk of dynamic-parking steps (a leftover good to a
non-envied agent, kept only if EFX0) and envy-cycle rotations.

  EC: at every rotation, EFX0 and (3) are kept and every value weakly rises (cycle agents strictly). Also on random
      EFX0 partial allocations without (3): EFX0 kept.
  STUCK: at every stuck state (leftovers, no placeable good on a non-envied agent, no envy cycle): a non-envied agent
      exists and every non-envied agent holds >= 2 goods.
  SLACK core: at every state with (3), every non-envied agent holding <= 1 good can absorb every leftover (EFX0).
  Control: on EFX0 partial allocations WITHOUT (3), the SLACK core fails (so (3) at the start of parking is needed).
"""
import itertools, random, sys, json

def make_val(w, kind):
    if kind == "add":
        return lambda S: sum(w[g] for g in S)
    return lambda S: sum(sorted((w[g] for g in S), reverse=True)[:2])

def efx0(V, X):
    n = len(X)
    for i in range(n):
        t = V[i](X[i])
        for j in range(n):
            if i != j and len(X[j]) >= 2 and any(V[i](X[j] - {g}) > t for g in X[j]):
                return False
    return True

def prop3(V, X, U):
    return all(V[i](X[i]) >= V[i]({e}) for i in range(len(X)) for e in U)

def envy(V, X):
    n = len(X)
    return {i: [j for j in range(n) if j != i and V[i](X[j]) > V[i](X[i])] for i in range(n)}

def find_cycle(G, n):
    for s in range(n):
        stack = [(s, [s])]
        while stack:
            u, path = stack.pop()
            for w in G[u]:
                if w == s:
                    return path
                if w not in path and w > s:
                    stack.append((w, path + [w]))
    return None

def fixprop3(V, X, U, m):
    n = len(X)
    for _ in range(10000):
        cand = [j for j in range(n) if any(V[j]({e}) > V[j](X[j]) for e in U)]
        if not cand:
            return
        j = max(cand)
        e = max(sorted(U), key=lambda e: V[j]({e}))
        U |= X[j]; U.discard(e); X[j] = {e}

def run(N, seed):
    rng = random.Random(seed)
    c = dict(instances=0, rotations=0, ec_fail=0, ec_free_tests=0, ec_free_fail=0, states=0, slack_tests=0,
             slack_fail=0, stuck=0, stuck_fail=0, ctrl_tests=0, ctrl_fail=0)
    ex = []
    for it in range(N):
        n = rng.randint(2, 5); m = rng.randint(n, n + 5)
        kind = "add" if it % 2 == 0 else "top2"
        W = []
        for i in range(n):
            w = [0] * m
            for g in rng.sample(range(m), rng.randint(1, min(4, m))):
                w[g] = rng.randint(1, 20)
            W.append(w)
        V = [make_val(W[i], kind) for i in range(n)]
        c["instances"] += 1
        starts = []
        X = [set() for _ in range(n)]; U = set(range(m))
        fixprop3(V, X, U, m)
        if not (efx0(V, X) and prop3(V, X, U)):
            ex.append(("fixprop3", W)); continue
        starts.append((X, U))
        for _ in range(40):     # random EFX0 partial allocations with (3)
            f = [rng.choice([-1] + list(range(n)) * 2) for _ in range(m)]
            Z = [{g for g in range(m) if f[g] == i} for i in range(n)]
            Uz = {g for g in range(m) if f[g] == -1}
            if Uz and efx0(V, Z) and prop3(V, Z, Uz):
                starts.append((Z, Uz))
                if len(starts) >= 4:
                    break
        for X, U in starts:
          for step in range(60):
              c["states"] += 1
              G = envy(V, X)
              nonenv = [u for u in range(n) if not any(u in G[i] for i in range(n))]
              # SLACK core
              for u in nonenv:
                  if len(X[u]) <= 1:
                      for e in U:
                          c["slack_tests"] += 1
                          Y = [set(b) for b in X]; Y[u].add(e)
                          if not efx0(V, Y):
                              c["slack_fail"] += 1; ex.append(("slack", W, kind))
              cyc = find_cycle(G, n)
              moves = [(u, e) for u in nonenv for e in U
                       if efx0(V, [x | {e} if a == u else x for a, x in enumerate(X)])]
              if U and not moves and not cyc:
                  c["stuck"] += 1
                  if not nonenv or any(len(X[u]) <= 1 for u in nonenv):
                      c["stuck_fail"] += 1; ex.append(("stuck", W, kind))
                  break
              if not U:
                  break
              if cyc and (not moves or rng.random() < 0.4):
                  before = [V[i](X[i]) for i in range(n)]
                  Y = [set(b) for b in X]
                  for a, b in zip(cyc, cyc[1:] + cyc[:1]):
                      Y[a] = set(X[b])
                  c["rotations"] += 1
                  ok = efx0(V, Y) and prop3(V, Y, U) and all(V[i](Y[i]) >= before[i] for i in range(n)) and \
                      all(V[a](Y[a]) > before[a] for a in cyc)
                  if not ok:
                      c["ec_fail"] += 1; ex.append(("EC", W, kind))
                  X = Y
              elif moves:
                  u, e = rng.choice(moves)
                  X[u].add(e); U.discard(e)
              else:
                  break
        # EC on arbitrary EFX0 partial allocations (no (3)), and the control for SLACK without (3)
        for _ in range(20):
            f = [rng.randint(-1, n - 1) for _ in range(m)]
            Z = [{g for g in range(m) if f[g] == i} for i in range(n)]
            Uz = {g for g in range(m) if f[g] == -1}
            if not efx0(V, Z):
                continue
            G = envy(V, Z); cyc = find_cycle(G, n)
            if cyc:
                Y = [set(b) for b in Z]
                for a, b in zip(cyc, cyc[1:] + cyc[:1]):
                    Y[a] = set(Z[b])
                c["ec_free_tests"] += 1
                if not efx0(V, Y):
                    c["ec_free_fail"] += 1; ex.append(("ECfree", W, kind))
            if not prop3(V, Z, Uz):
                nonenv = [u for u in range(n) if not any(u in G[i] for i in range(n))]
                for u in nonenv:
                    if len(Z[u]) == 1:
                        for e in Uz:
                            c["ctrl_tests"] += 1
                            Y = [set(b) for b in Z]; Y[u].add(e)
                            if not efx0(V, Y):
                                c["ctrl_fail"] += 1
    print(json.dumps(dict(source=f"Lemma EC / stuck states N={N} seed={seed}", **c)))
    for e in ex[:5]:
        print("EXAMPLE", e)

if __name__ == "__main__":
    run(int(sys.argv[1]), int(sys.argv[2]))
