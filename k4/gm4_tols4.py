"""Convert tagged profile lines (GMFAIL / GMALL lines of gm4_fast.c) to the input format of k4/ls4alg.c (one
task per distinct profile, each agent with its single type).  Usage: gm4_tols4.py FILE [TAG]"""
import sys, json
tag=sys.argv[2] if len(sys.argv)>2 else 'GMALL'
seen=set()
for line in open(sys.argv[1]):
    if not line.startswith(tag+' '): continue
    body,meta=line.split(' # ')
    vals=[list(map(int,t.split(','))) for t in body.split(' | ')[0].split()[1:]]
    m=int(meta.split()[0][2:]); sets=json.loads(meta.split('sets=')[1])
    k=(json.dumps(sets),json.dumps(vals))
    if k in seen: continue
    seen.add(k)
    print(len(sets),m)
    for S in sets: print(len(S),*S)
    for v in vals: print(1); print(0,*v)
    print(0,0,1)
