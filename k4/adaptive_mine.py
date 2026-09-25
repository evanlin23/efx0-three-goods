"""Which first agent rule 16 (k4/adaptive.c -A16) chooses where index order needs a rotation (k4/adaptive.md §4).
Takes up to --per=K profiles per core (leaf representatives) on which LB4r with index insertion needs at least one
rotation (-A0 -K1), runs rule 16 on each, and classifies the first agent c rule 16 inserts against the index run's
Phase 1 state: is c the index run's first agent (leader), does c have 4 goods, the rank of c's pick in the index run
(0 = its top), is c reachable from the leader along need edges (x -> z when z needs x's pick), is c frozen there.
Usage: adaptive_mine.py FILE [--per=K] [--jobs=J]"""
import collections, json, os, re, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import adaptive_run as A

def parse(line):
    g = lambda k, pat: re.search(k + pat, line).group(1)
    return {'sets': json.loads(g('sets=', r'(\[\[.*?\]\])')), 'vals': json.loads(g('vals=', r'(\[\[.*?\]\])')),
            'tau': [int(x) for x in g('tau=', r'([\d,]*)').split(',') if x],
            'picks': [int(x) for x in g('picks=', r'([-\d,]*)').split(',')],
            'blocks': [int(x) for x in g('blocks=', r'([-\d,]*)').split(',')]}

def main():
    args = sys.argv[1:]
    f = args[0]
    per = int(next((a.split('=')[1] for a in args if a.startswith('--per=')), 60))
    A.build()
    print('# adaptive_mine.py', ' '.join(args), '# adaptive.c sha256', A.SHA, flush=True)
    p = subprocess.run([sys.executable, os.path.join(A.HERE, 'adaptive_run.py'), f, '-A0', '-r3', '-K1', f'-f{per}',
                        '--show=100000000', '--jobs=1'], capture_output=True, text=True)
    idx = [parse(l) for l in p.stdout.split('\n') if l.startswith('DEEP')]
    C = collections.Counter(); rots = collections.Counter()
    for a in idx:
        q = subprocess.run([A.BIN, '-A16', '-r3', '-T1', '-v'], input=A.encode_profile(a['sets'], a['vals']),
                           capture_output=True, text=True).stdout
        run = [l for l in q.split('\n') if l.startswith('RUN')][0]
        b = parse(run); rots[run.split()[1]] += 1
        S, V, P = a['sets'], a['vals'], a['picks']; n = len(S)
        val = [dict(zip(s, v)) for s, v in zip(S, V)]
        rank = [sorted(s, key=lambda g: -val[i][g]) for i, s in enumerate(S)]
        needs = [set(g for g in S[i] if P[i] < 0 or val[i][g] > val[i][P[i]]) for i in range(n)]
        NA = set().union(*needs)
        c, lead = b['tau'][0], a['tau'][0]
        seen = {lead}; st = [lead]
        while st:
            x = st.pop()
            if P[x] < 0: continue
            for z in range(n):
                if z not in seen and P[x] in needs[z]: seen.add(z); st.append(z)
        C[(c == lead, len(S[c]), rank[c].index(P[c]) if P[c] >= 0 else -1, c in seen, P[c] in NA)] += 1
    print(f"{f}: {len(idx)} profiles on which index order needs a rotation; rule 16 needs: {dict(rots)}")
    print("  count  c=leader  |R_c|  rank of c's index pick  reachable from leader  frozen in index run")
    for k, v in sorted(C.items(), key=lambda x: -x[1]):
        print(f"  {v:6d}  {str(k[0]):8s}  {k[1]:5d}  {k[2]:22d}  {str(k[3]):21s}  {k[4]}")

if __name__ == '__main__':
    main()
