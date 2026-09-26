import re, json
def parse(line):
    sets=json.loads(re.search(r'sets=(\[\[.*?\]\])',line).group(1))
    vals=json.loads(re.search(r'vals=(\[\[.*?\]\])',line).group(1))
    order=list(map(int,re.search(r'order=([\d ]+?)\s+picks',line).group(1).split()))
    blocks=list(map(int,re.search(r'blocks=([\d,]+)',line).group(1).split(',')))
    # tau: leaders = first agent of each block in order
    done=set(); tau=[]; seen=set()
    for a in order:
        b=blocks[a]
        if b not in seen:
            seen.add(b)
            cand=[i for i in range(len(sets)) if i not in done]
            tau.append(cand.index(a))
        done.add(a)
    return sets,vals,tau,order
